"""Fixed-goal Lean workers: durable claims, frozen proofs and cgroup containment.

The controller/task cards are trusted. This is not a security proof against a
hostile agent: authenticated CLIs still need their own account state.
"""
from __future__ import annotations
import contextlib, fcntl, hashlib, json, math, os, re, shutil
from pathlib import Path, PurePosixPath
import socket, subprocess, sys, threading, time, uuid
from state import Store

try:
    import resources as _resources
except ImportError:  # pragma: no cover - package-style imports in downstream callers
    from . import resources as _resources


_LOCAL_LUNA_MODEL = 'gpt-5.6-luna'
_EFFORTS = frozenset(('high', 'xhigh', 'max'))
_DEFAULT_LEAN_OPTIONS = ('-j2', '-DmaxHeartbeats=800000')
_FORBIDDEN_LEAN_OPTION = re.compile(
    r'(?:skipkernel(?:tc|typeclass)|trust(?:[_-]?level)?|'
    r'(?:^|[=:_-])unsafe(?:$|[=:_-]))', re.I
)

BEGIN = '/- SWARM_PROOF_BEGIN -/'
END = '/- SWARM_PROOF_END -/'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
UNIT_RE = re.compile(r'lean-swarm-[0-9a-f]{32}\.service\Z')
QUOTA = ('usage_limit_reached', 'insufficient_quota', 'usage limit reached',
         'usage limit has been reached', 'quota exceeded')


def _policy_contract() -> tuple[str, object | None]:
    """Load the sibling policy module when the full scheduler is present.

    The runtime is also tested in this isolated workspace before that module
    lands.  The local defaults below intentionally implement the same narrow
    contract and are replaced by the canonical policy function when importable.
    """

    try:
        import importlib
        module = importlib.import_module('policy')
    except (ImportError, ModuleNotFoundError):
        return _LOCAL_LUNA_MODEL, None
    return getattr(module, 'LUNA_MODEL', _LOCAL_LUNA_MODEL), module


def resolve_effort(task: dict, config: dict | None = None) -> str:
    """Resolve the allowed Luna reasoning effort via the canonical contract."""

    model_name, policy = _policy_contract()
    if policy is not None and hasattr(policy, 'resolve_effort'):
        # Do not catch ValueError here: a policy rejection is deliberately
        # fail-closed and must reach the controller/job spec.
        effort = policy.resolve_effort(task, config=config)
        if not isinstance(effort, str) or effort not in _EFFORTS:
            raise ValueError('Luna reasoning effort must be one of high, xhigh, max')
        return effort
    config = config or {}
    explicit = task.get('reasoning_effort')
    if explicit is not None:
        effort = explicit
    else:
        difficulty = task.get('difficulty')
        effort = {'integration': 'high', 'proof': 'xhigh',
                  'foundation': 'max'}.get(difficulty,
                  config.get('luna_reasoning_effort', 'high'))
    if not isinstance(effort, str) or effort not in _EFFORTS:
        raise ValueError('Luna reasoning effort must be one of high, xhigh, max')
    return effort


def validate_lean_options(options: object) -> list[str]:
    """Validate the package-pinned Lean flags used by every compiler call."""

    if options is None:
        return list(_DEFAULT_LEAN_OPTIONS)
    if not isinstance(options, list) or any(not isinstance(option, str) or not option
                                            for option in options):
        raise ValueError('lean_options must be a list of non-empty strings')
    validated = list(options)
    for option in validated:
        if option in ('-o', '--output') or option.startswith('-o='):
            raise ValueError('lean_options must not select a compiler output path')
        if _FORBIDDEN_LEAN_OPTION.search(option):
            raise ValueError('lean_options contains a forbidden trust or unsafe flag')
    return validated


def _validate_luna_config(config: dict) -> str:
    model_name, _ = _policy_contract()
    configured = config.get('luna_model', model_name)
    if configured != model_name:
        raise ValueError('configured Luna model must be exactly '+model_name)
    return model_name


def _resource_limit(config: dict, name: str, default: int) -> int:
    aliases = (name, 'compile_slots' if name == 'compiler_slots' else name)
    value = next((config[key] for key in aliases if key in config), default)
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f'{name} must be a positive integer')
    return value


def atomic_json(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    with tmp.open('w') as stream:
        json.dump(data, stream, ensure_ascii=False, indent=2)
        stream.write('\n'); stream.flush(); os.fsync(stream.fileno())
    os.replace(tmp, path)


def checked(cmd: list[str], *, cwd: Path | None = None, env: dict | None = None,
            timeout: float = 180) -> str:
    result = subprocess.run(cmd, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f'{cmd[0]} exited {result.returncode}: {result.stdout[-5000:]}')
    return result.stdout


def git(repo: Path, *args: str) -> str:
    return checked(['git', '-C', str(repo), *args]).strip()


@contextlib.contextmanager
def file_lock(path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a') as stream:
        fcntl.flock(stream, fcntl.LOCK_EX)
        yield


def validate_task(task: dict) -> None:
    if 'model' in task and task['model'] not in ('luna', 'grok'):
        raise ValueError("model must be 'luna' or 'grok'")
    if task.get('model') == 'luna':
        resolve_effort(task, None)
    rel = PurePosixPath(task['target_path'])
    if (rel.is_absolute() or '..' in rel.parts or not rel.parts or rel.suffix != '.lean'
            or any(part.startswith('.') for part in rel.parts)):
        raise ValueError('target_path must be an ordinary relative .lean file')
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", task['target_name']):
        raise ValueError('invalid fully qualified Lean target')
    source = task['source']
    if source.count(BEGIN) != 1 or source.count(END) != 1:
        raise ValueError('exactly one pair of proof markers is required')
    before, rest = source.split(BEGIN); rest.split(END)
    if 'theorem ' not in before and 'lemma ' not in before:
        raise ValueError('template must contain a theorem or lemma')
    limit = task.get('timeout_seconds', 420)
    if isinstance(limit, bool) or not isinstance(limit, int) or not 5 <= limit <= 3600:
        raise ValueError('timeout_seconds must be an integer in [5,3600]')


def lean_code_without_comments(text: str) -> str:
    """Mask Lean line/nested block comments; keep all code and string literals.

    This is only the conservative policy scan. Frozen-statement reconstruction,
    independent Lean compilation and transitive-axiom checking remain mandatory.
    """
    out=[];i=0;depth=0;quoted=False;escaped=False
    while i<len(text):
        ch=text[i];two=text[i:i+2]
        if depth:
            if two=='/-':depth+=1;out.extend('  ');i+=2;continue
            if two=='-/':depth-=1;out.extend('  ');i+=2;continue
            out.append('\n' if ch=='\n' else ' ');i+=1;continue
        if quoted:
            out.append(ch)
            if escaped:escaped=False
            elif ch=='\\':escaped=True
            elif ch=='"':quoted=False
            i+=1;continue
        if ch=='"':quoted=True;out.append(ch);i+=1;continue
        if two=='/-':depth=1;out.extend('  ');i+=2;continue
        if two=='--':
            while i<len(text) and text[i]!='\n':out.append(' ');i+=1
            continue
        out.append(ch);i+=1
    if depth:raise ValueError('unterminated Lean block comment')
    return ''.join(out)


def reconstruct(template: str, candidate: str) -> str:
    """Only the proof body is accepted; all other bytes come from the template."""
    if candidate.count(BEGIN) != 1 or candidate.count(END) != 1:
        raise ValueError('missing or duplicated proof marker')
    prefix, remaining = candidate.split(BEGIN); proof, suffix = remaining.split(END)
    expected_prefix, remaining = template.split(BEGIN); _, expected_suffix = remaining.split(END)
    if prefix != expected_prefix or suffix != expected_suffix:
        norm = lambda text: re.sub(r'\s+', '', text)
        if norm(prefix) != norm(expected_prefix) or norm(suffix) != norm(expected_suffix):
            raise ValueError('frozen statement, definition, imports, or suffix changed')
    banned = (r'\b(sorry|admit|axiom|native_decide|unsafe|run_tac|run_elab|elab|'
              r'eval_expr|set_option|namespace|macro|syntax|attribute)\b|(^|\n)\s*#')
    if re.search(banned, lean_code_without_comments(proof)):
        raise ValueError('placeholder or unsupported environment-changing construct')
    return expected_prefix + BEGIN + proof + END + expected_suffix


def parse_axioms(output: str, target: str) -> list[str]:
    # Inspect every matching report, so an earlier printed imitation cannot mask a later bad audit.
    matches = re.findall(r"'"+re.escape(target)+r"' depends on axioms: \[([^]]*)\]", output, re.S)
    if not matches and f"'{target}' does not depend on any axioms" not in output:
        raise ValueError('target transitive-axiom audit missing')
    used = {part.strip() for match in matches for part in match.split(',') if part.strip()}
    if not used <= AXIOMS or 'sorryAx' in output or 'ofReduceBool' in output:
        raise ValueError('unapproved transitive proof dependency: '+str(sorted(used)))
    return sorted(used)


def seed_artifact_namespace(artifacts: Path, relative: str, baseline_path: str) -> None:
    """Create a complete, file-linked namespace view before writing new objects.

    Lean resolves a module's package directory, not every object independently.
    A partial first search root can hide the rest of that namespace in the pinned
    cache. Only files are linked; directories are always private to this attempt.
    """
    parts = PurePosixPath(relative).parts
    namespace = parts[0] if len(parts) > 1 else Path(relative).stem
    if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', namespace):
        raise ValueError('unsupported module namespace')
    artifacts.mkdir(parents=True, exist_ok=True)
    marker = artifacts / ('.namespace-' + namespace + '.json')
    identity = hashlib.sha256(baseline_path.encode()).hexdigest()
    if marker.exists():
        if json.loads(marker.read_text())['baseline_path_sha256'] != identity:
            raise ValueError('artifact namespace is already tied to another baseline')
        return
    source = None
    for root in baseline_path.split(os.pathsep):
        if root and (Path(root) / namespace).is_dir():
            source = (Path(root) / namespace).resolve(); break
    if source is not None:
        target = artifacts / namespace
        if target.is_symlink(): raise ValueError('artifact namespace must not alias a source directory')
        target.mkdir(parents=True, exist_ok=True)
        for directory, dirs, files in os.walk(source):
            destination = target / Path(directory).relative_to(source)
            if destination.is_symlink(): raise ValueError('artifact subdirectory must be private')
            destination.mkdir(parents=True, exist_ok=True)
            for name in files:
                link = destination / name
                if not link.exists() and not link.is_symlink():
                    link.symlink_to((Path(directory) / name).resolve())
    atomic_json(marker, {'namespace':namespace,'baseline_path_sha256':identity,
                         'source_present':source is not None})


def detach_object_links(module: Path) -> None:
    """Never write a generated object through a link into the pinned cache."""
    for path in [module, module.with_suffix('.ilean'),
                 Path(str(module)+'.private'), Path(str(module)+'.server')]:
        if path.is_symlink(): path.unlink()


def process_identity(pid: int) -> str | None:
    try:
        return Path(f'/proc/{pid}/stat').read_text().rsplit(') ', 1)[1].split()[19]
    except (OSError, IndexError):
        return None


class Controller:
    def __init__(self, store: Store, state_root: Path, project: str):
        self.store, self.root, self.project = store, state_root.resolve(), project
        self.cfg = store.get_project(project); self.repo = Path(self.cfg['repo']).resolve()
        self.luna_model = _validate_luna_config(self.cfg)
        self.lean_options = validate_lean_options(self.cfg.get('lean_options'))
        self.compiler_slots = _resource_limit(self.cfg, 'compiler_slots', 6)
        self.verifier_slots = _resource_limit(self.cfg, 'verifier_slots', 2)
        self.stop = threading.Event()
        self.owner = f'{socket.gethostname()}:{os.getpid()}:{process_identity(os.getpid())}'
        self.gitlock = self.root / 'locks' / (hashlib.sha256(str(self.repo).encode()).hexdigest()+'.lock')
        self.artifacts = self.root / 'attempts'; self.artifacts.mkdir(parents=True, exist_ok=True)
        self.worktree_lock = self.root / 'locks' / (hashlib.sha256(str(self.repo).encode()).hexdigest()+'.worktree.lock')

    def _environment(self, artifacts: Path | None = None) -> dict:
        env = dict(os.environ)
        for key in ('OPENAI_API_KEY','XAI_API_KEY','GROK_API_KEY','CODEX_API_KEY','GH_TOKEN','GITHUB_TOKEN'):
            env.pop(key, None)
        env['PATH'] = self.cfg['lean_bin']+':'+env.get('PATH','')
        env['LEAN_NUM_THREADS'] = '2'
        env['LEAN_PATH'] = (str(artifacts)+':' if artifacts else '')+self.cfg['lean_path']
        return env

    def _unit_info(self, unit: str) -> dict:
        if not UNIT_RE.fullmatch(unit):
            raise ValueError('refusing to operate on unrelated system service')
        result = subprocess.run(['systemctl','show',unit,'--no-pager','-p','ActiveState',
            '-p','SubState','-p','ControlGroup','-p','ExecMainStatus','-p','Result'], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
        return dict(line.split('=',1) for line in result.stdout.splitlines() if '=' in line)

    def _stop_unit(self, unit: str) -> dict:
        info = self._unit_info(unit)
        if info.get('ActiveState') not in ('inactive','failed',None,''):
            subprocess.run(['sudo','-n','systemctl','kill','--kill-who=all','--signal=SIGKILL',unit],
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=20)
        subprocess.run(['sudo','-n','systemctl','stop',unit], stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL, timeout=25)
        final = self._unit_info(unit)
        cg = info.get('ControlGroup','') or final.get('ControlGroup',''); populated=False
        if cg:
            events = Path('/sys/fs/cgroup')/cg.lstrip('/')/'cgroup.events'
            if events.exists(): populated = 'populated 1' in events.read_text()
        if final.get('ActiveState') not in ('inactive','failed',None,'') or populated:
            raise RuntimeError('containment has not stopped; slot remains reserved')
        return {'before':info,'after':final,'cgroup_populated':populated}

    def _freeze_capture(self, unit: str, candidate: Path, destination: Path, root: Path | None=None) -> dict:
        info = self._unit_info(unit); frozen=False
        if info.get('ActiveState') == 'active':
            result = subprocess.run(['sudo','-n','systemctl','freeze',unit],text=True,
                stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=20)
            frozen = result.returncode == 0
            if not frozen: self._stop_unit(unit)
        result={'captured_unix':time.time(),'frozen_before_capture':frozen,
                'candidate_present':candidate.is_file()}
        if candidate.is_symlink(): raise ValueError('candidate must not be a symlink')
        if root is not None and not candidate.resolve().is_relative_to(root.resolve()):
            raise ValueError('candidate escapes its worktree through a parent symlink')
        if candidate.is_file():
            data=candidate.read_bytes()
            if len(data)>2_000_000: raise ValueError('candidate exceeds size limit')
            destination.write_bytes(data);result['sha256']=hashlib.sha256(data).hexdigest()
        metadata_path=destination.with_suffix('.json')
        if metadata_path==destination:
            metadata_path=destination.with_name(destination.name+'.capture.json')
        atomic_json(metadata_path,result)
        return result

    def _dependencies(self, task: dict) -> list[dict]:
        rows={r['id']:r for r in self.store.list_tasks(self.project)};order=[];seen=set()
        def visit(task_id):
            if task_id in seen:return
            seen.add(task_id);row=rows[task_id]
            if row['status']!='INTEGRATED':raise ValueError('dependency not integrated: '+task_id)
            for parent in row['payload'].get('depends_on',[]):visit(parent)
            order.append(row['payload'])
        for task_id in task.get('depends_on',[]):visit(task_id)
        return order

    def _lean_identity(self) -> dict:
        binary = Path(self.cfg['lean_bin']) / 'lean'
        identity = {'path': str(binary)}
        try:
            data = binary.read_bytes()
        except OSError:
            identity['unavailable'] = True
        else:
            identity.update({'sha256': hashlib.sha256(data).hexdigest(), 'size': len(data)})
        toolchain = self.cfg.get('lean_toolchain')
        if toolchain:
            path = Path(toolchain)
            try:
                identity['toolchain_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
            except OSError:
                identity['toolchain'] = str(path)
        return identity

    def _package_identity(self, base: str | None = None) -> dict:
        """Identify package metadata without treating worker outputs as trusted."""

        identity = {'base_commit': base, 'package_dir': self.cfg.get('package_dir')}
        package = self.repo / str(self.cfg.get('package_dir', ''))
        files = []
        for name in ('lake-manifest.json', 'lakefile.toml', 'lakefile.lean', 'lean-toolchain'):
            path = package / name
            if path.is_file() and not path.is_symlink():
                files.append((name, hashlib.sha256(path.read_bytes()).hexdigest()))
        identity['manifest_hashes'] = files
        identity['lean_path'] = self.cfg.get('lean_path', '')
        return identity

    def _cache_key(self, source_bytes: bytes, target: str | None,
                   cache_context: dict | None) -> tuple[str, dict]:
        context = dict(cache_context or {})
        context.setdefault('recursive_dependency_hashes', [])
        payload = {
            'logical_module': context.get('logical_module'),
            'source_sha256': hashlib.sha256(source_bytes).hexdigest(),
            'recursive_dependency_hashes': context['recursive_dependency_hashes'],
            'lean_identity': self._lean_identity(),
            'lean_options': self.lean_options,
            'target_name': target,
            'relative_target_path': context.get('relative_target_path'),
            'package_identity': context.get('package_identity', self._package_identity()),
        }
        payload = json.loads(json.dumps(payload, ensure_ascii=False))
        encoded = json.dumps(payload, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()
        return hashlib.sha256(encoded).hexdigest(), payload

    def _cache_manifest(self, directory: Path, expected: dict,
                        source: Path, module: Path) -> dict | None:
        """Accept only an immutable, self-consistent trusted dependency entry."""

        manifest_path = directory / 'manifest.json'
        digest_path = directory / 'manifest.sha256'
        output_path = directory / 'output.olean'
        try:
            if any(path.is_symlink() for path in (manifest_path, digest_path, output_path)):
                return None
            manifest_bytes = manifest_path.read_bytes()
            if digest_path.read_text().strip() != hashlib.sha256(manifest_bytes).hexdigest():
                return None
            manifest = json.loads(manifest_bytes)
            if not isinstance(manifest, dict) or manifest.get('key') != expected.get('key'):
                return None
            for field in ('logical_module', 'source_sha256', 'recursive_dependency_hashes', 'lean_identity',
                          'lean_options', 'target_name', 'relative_target_path',
                          'package_identity'):
                if manifest.get(field) != expected.get(field):
                    return None
            if not output_path.is_file() or not module.parent.exists():
                return None
            if hashlib.sha256(output_path.read_bytes()).hexdigest() != manifest['output_sha256']:
                return None
            if hashlib.sha256(source.read_bytes()).hexdigest() != manifest['source_sha256']:
                return None
            if not isinstance(manifest['axioms'], list) or set(manifest['axioms']) - AXIOMS:
                return None
            if manifest.get('audit_source_sha256') != manifest['source_sha256']:
                return None
            bundle = manifest.get('output_bundle')
            if not isinstance(bundle, dict) or '' not in bundle or not set(bundle) <= {'', '.private', '.server'}:
                return None
            for suffix, digest in bundle.items():
                path = directory / ('output.olean' + suffix)
                if path.is_symlink() or not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                    return None
            detach_object_links(module)
            for suffix in ('', '.private', '.server'):
                destination = Path(str(module) + suffix)
                if suffix in bundle:
                    shutil.copyfile(directory / ('output.olean' + suffix), destination)
                elif destination.exists():
                    destination.unlink()
            return manifest
        except (OSError, ValueError, TypeError, json.JSONDecodeError, KeyError):
            return None

    def _compile(self, source: Path, artifacts: Path, relative: str,
                 target: str | None = None, *, cache_context: dict | None = None) -> dict:
        source_bytes = source.read_bytes()
        seed_artifact_namespace(artifacts, relative, self.cfg['lean_path'])
        module = artifacts / Path(relative).with_suffix('.olean')
        module.parent.mkdir(parents=True, exist_ok=True)
        detach_object_links(module)
        context = dict(cache_context or {})
        context.setdefault('relative_target_path', relative)
        cache_key, key_payload = self._cache_key(source_bytes, target, context)
        key_payload['key'] = cache_key
        cache_directory = self.root / 'cache' / 'trusted' / cache_key
        output = ''
        result = {'compile_passed': True, 'sha256': key_payload['source_sha256'],
                  'cache_key': cache_key}
        cache_allowed = cache_context is not None and self.cfg.get('trusted_dependency_cache', True)
        manifest = self._cache_manifest(cache_directory, key_payload, source, module) if cache_allowed else None
        if manifest is not None:
            result.update({'axioms': manifest['axioms'], 'cache_hit': True})
            output = 'trusted dependency cache hit '+cache_key
        else:
            result['cache_hit'] = False
            compiler_started = time.monotonic()
            with _resources.slot(self.root, 'compiler', self.compiler_slots, timeout=180) as lease:
                result['compiler_wait_seconds'] = round(lease.waited_seconds, 6)
                cmd = [str(Path(self.cfg['lean_bin']) / 'lean'), *self.lean_options,
                       '-o', str(module), str(source)]
                output = checked(cmd, cwd=source.parent, env=self._environment(artifacts), timeout=180)
            result['compile_seconds'] = round(time.monotonic() - compiler_started, 6)
            result['axioms'] = []
            if target:
                audit = artifacts / ('Audit_'+uuid.uuid4().hex+'.lean')
                audit.write_text(source.read_text()+'\n#print axioms '+target+'\n')
                with _resources.slot(self.root, 'compiler', self.compiler_slots, timeout=180) as lease:
                    result['audit_wait_seconds'] = round(lease.waited_seconds, 6)
                    audit_output = checked(
                        [str(Path(self.cfg['lean_bin']) / 'lean'), *self.lean_options, str(audit)],
                        cwd=source.parent, env=self._environment(artifacts), timeout=180)
                result['axioms'] = parse_axioms(audit_output, target)
                output += audit_output
            if cache_allowed and module.is_file() and not module.is_symlink() and target:
                cache_directory.mkdir(parents=True, exist_ok=True)
                bundle = {suffix: hashlib.sha256(Path(str(module)+suffix).read_bytes()).hexdigest()
                          for suffix in ('', '.private', '.server') if Path(str(module)+suffix).is_file()}
                manifest_data = dict(key_payload, output_bundle=bundle, axioms=result['axioms'],
                                     output_sha256=hashlib.sha256(module.read_bytes()).hexdigest(),
                                     audit_source_sha256=key_payload['source_sha256'])
                # A per-key lock prevents two controllers from publishing a
                # partially written cache entry at the same time.
                with file_lock(self.root / 'locks' / ('cache-'+cache_key+'.lock')):
                    if self._cache_manifest(cache_directory, key_payload, source, module) is None:
                        for suffix in bundle:
                            temporary = cache_directory / ('part-'+uuid.uuid4().hex)
                            temporary.write_bytes(Path(str(module)+suffix).read_bytes())
                            temporary.chmod(0o444)
                            os.replace(temporary, cache_directory / ('output.olean'+suffix))
                        atomic_json(cache_directory/'manifest.json', manifest_data)
                        digest = hashlib.sha256((cache_directory/'manifest.json').read_bytes()).hexdigest()
                        temporary = cache_directory / ('digest-'+uuid.uuid4().hex)
                        temporary.write_text(digest+'\n'); temporary.chmod(0o444)
                        os.replace(temporary, cache_directory/'manifest.sha256')
                        (cache_directory/'manifest.json').chmod(0o444)
        (artifacts / (Path(relative).stem+'.log')).write_text(output)
        return result

    def _prepare(self, claim: dict, folder: Path) -> dict:
        task=claim['task'];validate_task(task)
        if task.get('model') == 'luna':
            _validate_luna_config(self.cfg)
            effort = resolve_effort(task, self.cfg)
        else:
            effort = None
        work=folder/'work'
        # Read integrated dependencies before selecting a commit. Worktree creation
        # must not queue behind a full integration build of unrelated files.
        deps=self._dependencies(task)
        with file_lock(self.worktree_lock):
            base=git(self.repo,'rev-parse',self.cfg['integration_branch'])
            rows={r['id']:r for r in self.store.list_tasks(self.project)}
            for dep in deps:
                commit=rows[dep['id']]['integrated_commit']
                checked(['git','-C',str(self.repo),'merge-base','--is-ancestor',commit,base])
            checked(['git','-C',str(self.repo),'worktree','add','--detach',str(work),base])
        package=work/self.cfg['package_dir'];dep_artifacts=folder/'trusted-deps'
        dependency_hashes=[]
        for dep in deps:
            dep_source=package/dep['target_path']
            dependency_hashes.append({'task_id': dep['id'], 'target_name': dep['target_name'],
                                      'sha256': hashlib.sha256(dep_source.read_bytes()).hexdigest()})
        cache_context={'recursive_dependency_hashes': dependency_hashes,
                       'package_identity': self._package_identity(base)}
        dependency_compiles=[]
        for dep in deps:
            dependency_compiles.append(self._compile(
                package/dep['target_path'], dep_artifacts, dep['target_path'],
                dep['target_name'], cache_context=cache_context))
        candidate=package/task['target_path']
        if not candidate.resolve().is_relative_to(package.resolve()):raise ValueError('task path escapes package')
        candidate.parent.mkdir(parents=True,exist_ok=True)
        candidate.write_text(task['source'])
        mathlib=package/'Mathlib'
        if not mathlib.exists():mathlib.symlink_to(self.cfg['mathlib_source'],target_is_directory=True)
        prompt=('Complete ONLY the proof between SWARM_PROOF_BEGIN and SWARM_PROOF_END in '+
            task['target_path']+'. All imports, definitions, theorem statement, and other files are frozen. '+
            'This is a Lean 4.32.1 task, not permission to redesign the project. No sorry/admit, '+
            'added axioms, native_decide, unsafe or environment-altering metaprogramming. Standard '+
            'proof tactics are allowed. Run bash swarm-check.sh and fix errors. Do not commit, use '+
            'git remotes, access credentials, inspect other projects, use network tools, install '+
            'software, or spawn agents. Mathlib/ is read-only for library search. On failure '+
            'leave the best proof and explain the blocker; never claim success without compiling.\n'+
            'Task: '+task['id']+'\n'+task.get('hint',''))
        (package/'SWARM_TASK.md').write_text(prompt)
        import shlex
        lean_path=self._environment(dep_artifacts)['LEAN_PATH']
        resource_cli = Path(__file__).resolve().with_name('resources.py')
        compiler_command = [sys.executable, str(resource_cli), '--root', str(self.root),
                            '--resource', 'compiler', '--limit', str(self.compiler_slots), '--',
                            str(Path(self.cfg['lean_bin'])/'lean'), *self.lean_options,
                            task['target_path']]
        script=('#!/bin/bash\nset -euo pipefail\ncd "$(dirname "$0")"\nexport LEAN_PATH='+
            shlex.quote(lean_path)+'\nexec '+' '.join(shlex.quote(part) for part in compiler_command)+'\n')
        (package/'swarm-check.sh').write_text(script)
        logdir=work/'.swarm-runtime';logdir.mkdir()
        spec={'attempt_id':claim['attempt_id'],'model':task['model'],'cwd':str(package),
            'logdir':str(logdir),'prompt_file':str(package/'SWARM_TASK.md'),
            'codex':self.cfg['codex'],'grok':self.cfg['grok'],
            'luna_model':self.luna_model,
            'luna_reasoning_effort':effort,
            'grok_model':self.cfg.get('grok_model','grok-4.6'),'lean_bin':self.cfg['lean_bin'],
            'lean_path':lean_path,'lean_options':self.lean_options,
            'compiler_slots':self.compiler_slots,'verifier_slots':self.verifier_slots,
            'resource_root':str(self.root),'home':str(Path.home()),'path':self._environment()['PATH']}
        atomic_json(folder/'job.json',spec)
        return {'base_commit':base,'workspace':str(work),'package':str(package),
            'candidate':str(candidate),'dependencies':deps,'spec':spec,
            'dependency_hashes':dependency_hashes,'package_identity':cache_context['package_identity'],
            'dependency_compiles':dependency_compiles}

    def execute(self, claim: dict) -> None:
        attempt=claim['attempt_id'];folder=self.artifacts/attempt;folder.mkdir(parents=True,exist_ok=True)
        unit='lean-swarm-'+attempt.replace('-','')+'.service'
        if not UNIT_RE.fullmatch(unit):raise ValueError('attempt ID must be a UUID')
        task=claim['task'];status='FAILED';now=time.time()
        result={'timing':{'queue_wait_started_unix':claim.get('_dispatch_started_unix', now),
                           'claimed_unix':claim.get('_claimed_unix', now),
                           'prepare_started_unix':now}, 'resource_limits': {
                               'compiler_slots': self.compiler_slots,
                               'verifier_slots': self.verifier_slots}}
        result['timing']['queue_wait_seconds']=max(0.0, result['timing']['claimed_unix']-
                                                    result['timing']['queue_wait_started_unix'])
        started_service=False;stopped=True
        self.store.record_runtime(attempt,{'unit':unit,'folder':str(folder),'owner':self.owner})
        try:
            prepared=self._prepare(claim,folder);atomic_json(folder/'prepared.json',prepared)
            result['timing']['prepare_finished_unix']=time.time()
            result['prepare_dependency_compiles']=prepared.get('dependency_compiles', [])
            self.store.record_runtime(attempt,{'unit':unit,'folder':str(folder),
                'workspace':prepared['workspace'],'base_commit':prepared['base_commit'],'owner':self.owner})
            timeout=task.get('timeout_seconds',420)
            writable=[prepared['workspace'],str(Path.home()/'.codex'),str(Path.home()/'.grok'),str(_resources.resource_directory(self.root))]
            writable=list(dict.fromkeys(writable))
            for directory in writable:Path(directory).mkdir(parents=True,exist_ok=True)
            cmd=['sudo','-n','systemd-run','--quiet','--unit='+unit,'--service-type=exec',
                '-p','User='+str(os.getuid()),'-p','Group='+str(os.getgid()),
                '-p','KillMode=control-group','-p','TimeoutStopSec=5',
                '-p','RuntimeMaxSec='+str(timeout+60),'-p','MemoryMax=6G','-p','TasksMax=512',
                '-p','NoNewPrivileges=yes','-p','ProtectSystem=strict','-p','ProtectHome=read-only',
                '-p','PrivateTmp=yes','-p','ReadWritePaths='+' '.join(writable),
                '/usr/bin/python3',str(Path(__file__).resolve()),'_job',str(folder/'job.json')]
            if self.stop.is_set():
                status='INTERRUPTED';raise InterruptedError('controller stopped before service launch')
            started_service=True;stopped=False
            checked(cmd)
            start=time.monotonic();deadline=start+timeout
            result['timing']['service_started_unix']=time.time()
            atomic_json(folder/'timing.json',result['timing'])
            while True:
                self.store.heartbeat(attempt);info=self._unit_info(unit)
                if self.stop.is_set():status='INTERRUPTED';break
                if time.monotonic()>=deadline:status='TIMEOUT';break
                if info.get('ActiveState') in ('inactive','failed'):
                    status='FINISHED' if info.get('ExecMainStatus')=='0' else 'FAILED';break
                time.sleep(.5)
            result['elapsed_seconds']=round(time.monotonic()-start,3)
            result['capture']=self._freeze_capture(unit,Path(prepared['candidate']),folder/'frozen.lean',Path(prepared['workspace']))
            result['containment']=self._stop_unit(unit);stopped=True
            result['timing']['service_stopped_unix']=time.time()
            logs=Path(prepared['spec']['logdir']);text=''
            for name in ('agent.jsonl','agent.stderr','leader.stderr'):
                p=logs/name
                if p.exists():text+=p.read_text(errors='replace')[-1_000_000:]
            if any(q in text.lower() for q in QUOTA):
                self.store.pause_model(task['model'],'Subscription quota reported by CLI');status='QUOTA'
            if status=='FINISHED':
                result['timing']['verification_started_unix']=time.time()
                verified=folder/'verified'/task['target_path'];verified.parent.mkdir(parents=True,exist_ok=True)
                verified.write_text(reconstruct(task['source'],(folder/'frozen.lean').read_text()))
                artifacts=folder/'verification-artifacts'
                verification_started=time.monotonic()
                with _resources.slot(self.root, 'verifier', self.verifier_slots, timeout=180) as lease:
                    result['timing']['verification_resource_wait_seconds']=round(lease.waited_seconds, 6)
                    trusted_source=folder/'trusted-source'
                    for dep in prepared['dependencies']:
                        path=self.cfg['package_dir']+'/'+dep['target_path']
                        source=subprocess.check_output(['git','-C',str(self.repo),'show',prepared['base_commit']+':'+path])
                        dp=trusted_source/dep['target_path'];dp.parent.mkdir(parents=True,exist_ok=True)
                        dp.write_bytes(source)
                        self._compile(dp, artifacts, dep['target_path'], dep['target_name'],
                                      cache_context={'recursive_dependency_hashes': prepared.get('dependency_hashes', []),
                                                     'package_identity': prepared.get('package_identity')})
                    result['verification']=self._compile(verified,artifacts,task['target_path'],task['target_name'])
                result['verified_source']=str(verified);status='VERIFIED'
                result['timing']['verification_finished_unix']=time.time()
                result['timing']['verification_seconds']=round(time.monotonic()-verification_started, 6)
        except Exception as exc:
            result['error']=str(exc)
            if status not in ('TIMEOUT','INTERRUPTED','QUOTA'):status='FAILED'
        finally:
            if started_service and not stopped:
                try:result['containment']=self._stop_unit(unit);stopped=True
                except Exception as exc:result['containment_error']=str(exc)
            result['timing']['finished_unix']=time.time()
            atomic_json(folder/'timing.json',result['timing'])
            final_metadata={'unit':unit,'folder':str(folder),'owner':self.owner,
                            'timing':result['timing'],'resource_limits':result['resource_limits']}
            if 'prepared' in locals():
                final_metadata.update({'workspace':prepared.get('workspace'),
                                       'base_commit':prepared.get('base_commit')})
            self.store.record_runtime(attempt, final_metadata)
            atomic_json(folder/'result.json',dict(result,status=status,task_id=claim['task_id']))
            if stopped:self.store.finish(attempt,status,result)
            else:
                self.stop.set();raise RuntimeError('containment uncertain; RUNNING claim retained for recovery')
        print(json.dumps({'task':claim['task_id'],'status':status,'elapsed':result.get('elapsed_seconds'),
            'error':result.get('error')},ensure_ascii=False),flush=True)

    def reverify(self, task_id: str, reason: str | None=None) -> dict:
        """Recheck an immutable FAILED submission after explicit coordinator review.

        The original FAILED result and its event are retained. TIMEOUT candidates
        cannot be promoted with this operation. No model is called.
        """
        if reason is None:reason='Trusted verifier infrastructure repair; frozen submission unchanged'
        if not isinstance(reason,str) or not reason.strip() or len(reason)>2000:
            raise ValueError('review reason must be nonempty and at most 2000 characters')
        row=next(t for t in self.store.list_tasks(self.project) if t['id']==task_id)
        if row['status']!='FAILED':raise ValueError('reverify only accepts a FAILED task')
        attempt=next(a for a in self.store.list_attempts(self.project) if a['id']==row['attempt_id'])
        metadata=attempt['metadata'];folder=Path(metadata['folder'])
        self._stop_unit(metadata['unit'])
        result=attempt['result'];capture=result.get('capture',{})
        frozen=folder/'frozen.lean'
        if not capture.get('candidate_present') or not frozen.exists():
            raise ValueError('no captured submission to reverify')
        if hashlib.sha256(frozen.read_bytes()).hexdigest()!=capture.get('sha256'):
            raise ValueError('captured source no longer matches its original hash')
        task=row['payload'];prepared=json.loads((folder/'prepared.json').read_text())
        output=folder/('reverification-'+uuid.uuid4().hex);source=output/'source'/task['target_path']
        source.parent.mkdir(parents=True,exist_ok=True)
        source.write_text(reconstruct(task['source'],frozen.read_text()))
        artifacts=output/'artifacts'
        with _resources.slot(self.root, 'verifier', self.verifier_slots, timeout=180):
            for dep in prepared['dependencies']:
                rel=self.cfg['package_dir']+'/'+dep['target_path']
                data=subprocess.check_output(['git','-C',str(self.repo),'show',prepared['base_commit']+':'+rel])
                parent=output/'source'/dep['target_path'];parent.parent.mkdir(parents=True,exist_ok=True)
                parent.write_bytes(data);self._compile(
                    parent, artifacts, dep['target_path'], dep['target_name'],
                    cache_context={'recursive_dependency_hashes': prepared.get('dependency_hashes', []),
                                   'package_identity': prepared.get('package_identity')})
            verification=self._compile(source,artifacts,task['target_path'],task['target_name'])
        updated=dict(result,verification=verification,verified_source=str(source),
                     reverified_without_model=True,original_failure=result,
                     reverification_reason=reason)
        updated.pop('error',None)
        atomic_json(output/'report.json',updated)
        self.store.approve_reverification(attempt['id'],updated)
        print('REVERIFIED_FROZEN_SUBMISSION',task_id,flush=True)
        return updated

    def integrate(self, task_id: str) -> str:
        requested_unix=time.time()
        with file_lock(self.gitlock):
            lock_acquired_unix=time.time()
            row=next(t for t in self.store.list_tasks(self.project) if t['id']==task_id)
            if row['status']=='INTEGRATED':return row['integrated_commit']
            if row['status']!='VERIFIED':raise ValueError('only VERIFIED tasks enter integration')
            if git(self.repo,'branch','--show-current')!=self.cfg['integration_branch']:
                raise ValueError('integration checkout is on the wrong branch')
            if git(self.repo,'status','--porcelain'):raise ValueError('integration checkout is not clean')
            attempt=next(a for a in self.store.list_attempts(self.project) if a['id']==row['attempt_id'])
            source=Path(attempt['result']['verified_source'])
            if hashlib.sha256(source.read_bytes()).hexdigest()!=attempt['result']['verification']['sha256']:
                raise ValueError('verified source changed after verification')
            task=row['payload'];rel=self.cfg['package_dir']+'/'+task['target_path'];target=self.repo/rel
            if not target.resolve().is_relative_to(self.repo):raise ValueError('integration target escapes repository')
            if target.exists():
                if target.read_bytes()==source.read_bytes():
                    commit=git(self.repo,'rev-parse','HEAD');self.store.mark_integrated(self.project,task_id,commit)
                    return commit
                raise ValueError('target already differs; manual reconciliation required')
            target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(source.read_bytes())
            committed=False
            try:
                checkdir=self.artifacts/row['attempt_id']/'integration-artifacts'
                integration_compile_started=time.monotonic()
                base_identity = self._package_identity(git(self.repo, 'rev-parse', 'HEAD'))
                dependencies = self._dependencies(task)
                dependency_hashes=[
                    {'task_id': dep['id'], 'target_name': dep['target_name'],
                     'sha256': hashlib.sha256((self.repo/self.cfg['package_dir']/dep['target_path']).read_bytes()).hexdigest()}
                    for dep in dependencies]
                with _resources.slot(self.root, 'verifier', self.verifier_slots, timeout=180) as lease:
                    for dep in dependencies:
                        self._compile(self.repo/self.cfg['package_dir']/dep['target_path'],checkdir,
                                      dep['target_path'],dep['target_name'],
                                      cache_context={'recursive_dependency_hashes': dependency_hashes,
                                                     'package_identity': base_identity})
                    report=self._compile(target,checkdir,task['target_path'],task['target_name'])
                    verifier_wait_seconds=lease.waited_seconds
                command=self.cfg.get('integration_command')
                if command:
                    gate=checked(command,cwd=self.repo/self.cfg['package_dir'],env=self._environment(),timeout=600)
                    (checkdir/'project-gate.log').write_text(gate)
                git(self.repo,'add','--',rel)
                git(self.repo,'commit','-m','test(lean-swarm): integrate checked task '+task_id);committed=True
                commit=git(self.repo,'rev-parse','HEAD');self.store.mark_integrated(self.project,task_id,commit)
                integration_timing={'requested_unix':requested_unix,'lock_acquired_unix':lock_acquired_unix,
                                    'verifier_wait_seconds':verifier_wait_seconds,
                                    'compile_seconds':round(time.monotonic()-integration_compile_started, 6),
                                    'finished_unix':time.time()}
                atomic_json(checkdir/'integration.json',{'commit':commit,'task':task_id,'verification':report,
                    'timing':integration_timing})
                self.store.record_runtime(attempt['id'], dict(attempt['metadata'],
                    integration_timing=integration_timing))
            except Exception:
                if not committed:
                    subprocess.run(['git','-C',str(self.repo),'reset','-q','HEAD','--',rel],check=False)
                    if target.exists() and git(self.repo,'status','--porcelain','--',rel):target.unlink()
                raise
            print('INTEGRATED',task_id,commit,flush=True);return commit

    def _resource_status(self, active_workers: int = 0) -> tuple[bool, str | None]:
        """Return memory admission and a human-readable pause reason.

        A reservation is charged for every already admitted worker and for the
        worker about to be launched.  The sample is therefore not reused to
        claim an unbounded queue of tasks.  This gate only delays claims; it
        never stops an admitted task.
        """

        reserve = self.cfg.get('min_available_memory_mb', 8192)
        estimate = self.cfg.get('estimated_worker_memory_mb', 512)
        if (isinstance(reserve, bool) or not isinstance(reserve, int) or reserve < 0 or
                isinstance(estimate, bool) or not isinstance(estimate, int) or estimate <= 0):
            raise ValueError('memory admission settings are invalid')
        try:
            memory = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
            available = int(memory['MemAvailable'].split()[0]) // 1024
        except (OSError, KeyError, ValueError, IndexError):
            return True, None  # Pure tests and non-Linux hosts have no admission sample.
        required = reserve + estimate * (active_workers + 1)
        if available < required:
            return False, (f'memory admission paused: available_mb={available}, '
                           f'reserve_mb={reserve}, estimated_worker_mb={estimate}, '
                           f'admitted_workers={active_workers}')
        return True, None

    def _resource_allows_claim(self, active_workers: int = 0) -> bool:
        return self._resource_status(active_workers)[0]

    @staticmethod
    def _validate_run_number(value: object, name: str, *, zero_allowed: bool = False) -> float | int:
        if isinstance(value, bool) or not isinstance(value, (int, float)):
            raise ValueError(f'{name} must be a number')
        if isinstance(value, float) and not math.isfinite(value):
            raise ValueError(f'{name} must be finite')
        if zero_allowed:
            if value < 0:
                raise ValueError(f'{name} must be nonnegative')
        elif value <= 0:
            raise ValueError(f'{name} must be positive')
        return value

    def run(self, jobs: int = 0, integrate: bool = False, poll_hook=None,
            linger_seconds: float = 0) -> list[dict]:
        """Dispatch a finite batch, with ``jobs=0`` meaning no worker cap.

        Each admitted task owns one non-daemon thread.  This avoids a hidden
        fixed-size executor while retaining a finite positive user budget.
        Integration is one separate non-daemon thread and never prevents an
        unrelated ready task from being admitted.
        """

        if isinstance(jobs, bool) or not isinstance(jobs, int) or jobs < 0:
            raise ValueError('dispatcher jobs must be a nonnegative integer (0 means unlimited)')
        linger_seconds = self._validate_run_number(linger_seconds, 'linger_seconds', zero_allowed=True)
        attempted_integrations: set[str] = set()
        worker_threads: dict[threading.Thread, dict] = {}
        integration: dict | None = None
        integration_task: str | None = None
        dispatch_started = time.time()
        linger_deadline = time.monotonic() + float(linger_seconds) if linger_seconds else None
        poll_error: BaseException | None = None
        worker_error: BaseException | None = None
        telemetry_dir = self.root / 'telemetry'; telemetry_dir.mkdir(parents=True, exist_ok=True)
        telemetry = telemetry_dir / (self.project + '-' + uuid.uuid4().hex + '.jsonl')

        def start_thread(target, argument, label: str) -> dict:
            record = {'error': None, 'done': threading.Event(), 'label': label}

            def invoke() -> None:
                try:
                    target(argument)
                except BaseException as exc:  # retained and surfaced after own work is joined
                    record['error'] = exc
                finally:
                    record['done'].set()

            thread = threading.Thread(target=invoke, name=f'lean-swarm-{label}', daemon=False)
            record['thread'] = thread
            thread.start()
            return record

        def reap_workers() -> None:
            nonlocal worker_error
            for thread, record in list(worker_threads.items()):
                if not record['done'].is_set():
                    continue
                thread.join()
                worker_threads.pop(thread, None)
                if record['error'] is not None and worker_error is None:
                    worker_error = record['error']

        def reap_integration() -> None:
            nonlocal integration, integration_task
            if integration is None or not integration['done'].is_set():
                return
            integration['thread'].join()
            if integration['error'] is not None:
                print('INTEGRATION_BLOCKED', integration_task, str(integration['error']), flush=True)
            integration = None
            integration_task = None

        def write_telemetry(rows: list[dict], resource_ok: bool, resource_reason: str | None,
                            hook_error: BaseException | None) -> None:
            by_status: dict[str, int] = {}
            by_id = {row['id']: row for row in rows}
            ready_count = dependency_blocked = 0
            present_gates = {g['gate_id'] for g in self.store.list_acceptance_gates()}
            for row in rows:
                by_status[row['status']] = by_status.get(row['status'], 0) + 1
                if row['status'] == 'QUEUED':
                    if all(by_id.get(dep, {}).get('status') == 'INTEGRATED'
                           for dep in row['payload'].get('depends_on', [])) and all(
                               gate in present_gates for gate in row['payload'].get('integrated_gates', [])):
                        ready_count += 1
                    else:
                        dependency_blocked += 1
            record = {'unix': time.time(), 'project': self.project, 'worker_budget': jobs,
                      'worker_threads': len(worker_threads),
                      'worker_futures': len(worker_threads),
                      'integrating': integration_task if integration is not None else None,
                      'task_states': by_status, 'dependency_ready': ready_count,
                      'dependency_blocked': dependency_blocked,
                      'resource_admission': resource_ok,
                      'resource_pause_reason': resource_reason,
                      'poll_hook_error': str(hook_error) if hook_error else None,
                      'dispatch_elapsed_seconds': round(time.time() - dispatch_started, 6)}
            with telemetry.open('a') as out:
                out.write(json.dumps(record, ensure_ascii=False) + '\n')

        try:
            while True:
                reap_workers()
                reap_integration()
                if self.stop.is_set():
                    poll_allowed = False
                else:
                    poll_allowed = poll_error is None
                if poll_allowed and poll_hook is not None:
                    try:
                        poll_hook()
                    except BaseException as exc:
                        poll_error = exc
                        print('POLL_HOOK_FAILED: '+str(exc), flush=True)

                rows = self.store.list_tasks(self.project)
                if integrate and integration is None and not self.stop.is_set():
                    ready = [row for row in rows if row['status'] == 'VERIFIED' and
                             row['id'] not in attempted_integrations]
                    ready.sort(key=lambda row: (-row['payload'].get('priority', 0), row['id']))
                    if ready:
                        integration_task = ready[0]['id']
                        attempted_integrations.add(integration_task)
                        integration = start_thread(self.integrate, integration_task, 'integration')

                resource_ok, resource_reason = self._resource_status(len(worker_threads))
                while (not self.stop.is_set() and poll_error is None and
                       (jobs == 0 or len(worker_threads) < jobs) and resource_ok):
                    claim = self.store.claim(self.project, self.owner)
                    if claim is None:
                        break
                    claim['_dispatch_started_unix'] = dispatch_started
                    claim['_claimed_unix'] = time.time()
                    record = start_thread(self.execute, claim, claim['task_id'])
                    worker_threads[record['thread']] = record
                    resource_ok, resource_reason = self._resource_status(len(worker_threads))

                write_telemetry(rows, resource_ok, resource_reason, poll_error)
                pending = any(row['status'] == 'QUEUED' for row in rows)
                own_work = bool(worker_threads) or integration is not None
                now = time.monotonic()
                if self.stop.is_set():
                    if not own_work:
                        break
                elif own_work:
                    pass
                elif pending and resource_reason and linger_deadline is not None and now < linger_deadline:
                    pass
                elif linger_deadline is not None and now < linger_deadline:
                    pass
                else:
                    # A normal run is a finite batch.  Queued work blocked by
                    # dependencies, a model pause, memory, or another owner is
                    # deliberately preserved for a later dispatch.
                    break
                time.sleep(0.02)
        except BaseException:
            self.stop.set()
            raise
        finally:
            # Never abandon an own worker or integration thread.  They are
            # intentionally non-daemon and are joined before returning.
            for thread, record in list(worker_threads.items()):
                thread.join()
                if record['error'] is not None and worker_error is None:
                    worker_error = record['error']
            if integration is not None:
                integration['thread'].join()
                if integration['error'] is not None:
                    print('INTEGRATION_BLOCKED', integration_task, str(integration['error']), flush=True)
            rows = self.store.list_tasks(self.project)
            resource_ok, resource_reason = self._resource_status(0)
            write_telemetry(rows, resource_ok, resource_reason, poll_error)
        if poll_error is not None:
            raise RuntimeError('poll_hook failed; new claims were stopped') from poll_error
        if worker_error is not None:
            raise worker_error
        return self.store.list_tasks(self.project)

    def recover(self) -> list[str]:
        recovered=[]
        for attempt in self.store.list_attempts(self.project):
            if attempt['status']!='RUNNING':continue
            parts=attempt['owner'].split(':')
            if len(parts)!=3 or parts[0]!=socket.gethostname():raise ValueError('unknown owner host')
            if process_identity(int(parts[1]))==parts[2]:continue
            unit=(attempt.get('metadata') or {}).get('unit')
            containment=self._stop_unit(unit) if unit else {'service_not_started':True}
            self.store.finish(attempt['id'],'INTERRUPTED',{'reason':'dead dispatcher; worker stopped before release',
                'containment':containment});recovered.append(attempt['task_id'])
        return recovered


def job_entry(spec_path: Path) -> int:
    """Runs inside the cgroup and never connects to the user's default Grok leader."""
    spec=json.loads(spec_path.read_text())
    if spec.get('model') not in ('luna', 'grok'):
        raise ValueError("job spec model must be 'luna' or 'grok'")
    if spec.get('model') == 'luna':
        if spec.get('luna_model') != _policy_contract()[0]:
            raise ValueError('job spec contains a non-canonical Luna model')
        if spec.get('luna_reasoning_effort') not in _EFFORTS:
            raise ValueError('job spec contains an unsupported Luna reasoning effort')
    env=dict(os.environ,HOME=spec['home'],PATH=spec['path'],LEAN_PATH=spec['lean_path'],LEAN_NUM_THREADS='2')
    for key in ('OPENAI_API_KEY','XAI_API_KEY','GROK_API_KEY','CODEX_API_KEY','GH_TOKEN','GITHUB_TOKEN'):
        env.pop(key,None)
    logdir=Path(spec['logdir']);leader=None;leader_output=None
    try:
        if spec['model']=='luna':
            effort_config='model_reasoning_effort="'+spec['luna_reasoning_effort']+'"'
            cmd=[spec['codex'],'exec','--ignore-user-config','--skip-git-repo-check','--ephemeral',
                '--disable','multi_agent','-m',spec['luna_model'],'-c',effort_config,
                '-s','workspace-write','-C',spec['cwd'],'--json','-o',str(logdir/'final.txt'),'-']
            if spec.get('resource_root'):
                resource_dir = str(_resources.resource_directory(spec['resource_root']))
                cmd[cmd.index('-s'):cmd.index('-s')] = ['--add-dir', resource_dir]
            stdin=Path(spec['prompt_file']).read_bytes()
        else:
            sock='/tmp/lean-swarm-'+spec['attempt_id'].replace('-','')+'.sock'
            leader_output=(logdir/'leader.stderr').open('w')
            leader=subprocess.Popen([spec['grok'],'--leader-socket',sock,'agent','leader',
                '--no-auto-update','--relay-on-demand'],env=env,cwd=spec['cwd'],
                stdout=leader_output,stderr=subprocess.STDOUT)
            deadline=time.monotonic()+25
            while not Path(sock).exists():
                if leader.poll() is not None or time.monotonic()>deadline:raise RuntimeError('dedicated Grok leader failed')
                time.sleep(.1)
            cmd=[spec['grok'],'--leader-socket',sock,'--cwd',spec['cwd'],'--model',spec['grok_model'],
                '--no-subagents','--no-plan','--disable-web-search','--permission-mode','auto','--max-turns','40',
                '--output-format','streaming-json','--prompt-file',spec['prompt_file']]
            stdin=None
        with (logdir/'agent.jsonl').open('w') as out,(logdir/'agent.stderr').open('w') as err:
            result=subprocess.run(cmd,input=stdin,env=env,cwd=spec['cwd'],stdout=out,stderr=err)
        atomic_json(logdir/'client-result.json',{'exit_code':result.returncode,'finished_unix':time.time()})
        return result.returncode
    finally:
        if leader and leader.poll() is None:
            leader.terminate()
            try:leader.wait(timeout=5)
            except subprocess.TimeoutExpired:leader.kill();leader.wait(timeout=5)
        if leader_output:leader_output.close()


if __name__=='__main__':
    if len(sys.argv)==3 and sys.argv[1]=='_job':sys.exit(job_entry(Path(sys.argv[2])))
    raise SystemExit('Use cli.py; runtime.py only exposes internal _job mode.')
