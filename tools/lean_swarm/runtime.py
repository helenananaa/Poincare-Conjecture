"""Fixed-goal Lean workers: durable claims, frozen proofs and cgroup containment.

The controller/task cards are trusted. This is not a security proof against a
hostile agent: authenticated CLIs still need their own account state.
"""
from __future__ import annotations
import concurrent.futures, contextlib, fcntl, hashlib, json, os, re, shutil
from pathlib import Path, PurePosixPath
import signal, socket, subprocess, sys, threading, time, uuid
from state import Store

BEGIN = '/- SWARM_PROOF_BEGIN -/'
END = '/- SWARM_PROOF_END -/'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
UNIT_RE = re.compile(r'lean-swarm-[0-9a-f]{32}\.service\Z')
QUOTA = ('usage_limit_reached', 'insufficient_quota', 'usage limit reached',
         'usage limit has been reached', 'quota exceeded')


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
    if re.search(banned, proof):
        raise ValueError('placeholder or unsupported environment-changing construct')
    return expected_prefix + BEGIN + proof + END + expected_suffix


def parse_axioms(output: str, target: str) -> list[str]:
    match = re.search(r"'" + re.escape(target) + r"' depends on axioms: \[([^]]*)\]", output, re.S)
    if match:
        used = {x.strip() for x in match.group(1).split(',') if x.strip()}
    elif f"'{target}' does not depend on any axioms" in output:
        used = set()
    else:
        raise ValueError('target transitive-axiom audit missing')
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
        atomic_json(destination.with_suffix('.json'),result)
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

    def _compile(self, source: Path, artifacts: Path, relative: str, target: str | None=None) -> dict:
        seed_artifact_namespace(artifacts,relative,self.cfg['lean_path'])
        module=artifacts/Path(relative).with_suffix('.olean');module.parent.mkdir(parents=True,exist_ok=True)
        detach_object_links(module)
        cmd=[self.cfg['lean_bin']+'/lean','-j2','-DmaxHeartbeats=800000','-o',str(module),str(source)]
        output=checked(cmd,cwd=source.parent,env=self._environment(artifacts),timeout=180)
        result={'compile_passed':True,'sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
        if target:
            audit=artifacts/('Audit_'+uuid.uuid4().hex+'.lean')
            audit.write_text(source.read_text()+'\n#print axioms '+target+'\n')
            audit_output=checked([self.cfg['lean_bin']+'/lean','-j2',str(audit)],
                cwd=source.parent,env=self._environment(artifacts),timeout=180)
            result['axioms']=parse_axioms(audit_output,target);output+=audit_output
        (artifacts/(Path(relative).stem+'.log')).write_text(output)
        return result

    def _prepare(self, claim: dict, folder: Path) -> dict:
        task=claim['task'];validate_task(task);work=folder/'work'
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
        for dep in deps:self._compile(package/dep['target_path'],dep_artifacts,dep['target_path'],dep['target_name'])
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
        script=('#!/bin/bash\nset -euo pipefail\ncd "$(dirname "$0")"\nexport LEAN_PATH='+
            shlex.quote(lean_path)+'\nexec '+shlex.quote(self.cfg['lean_bin']+'/lean')+
            ' -j2 -DmaxHeartbeats=800000 '+shlex.quote(task['target_path'])+'\n')
        (package/'swarm-check.sh').write_text(script)
        logdir=work/'.swarm-runtime';logdir.mkdir()
        spec={'attempt_id':claim['attempt_id'],'model':task['model'],'cwd':str(package),
            'logdir':str(logdir),'prompt_file':str(package/'SWARM_TASK.md'),
            'codex':self.cfg['codex'],'grok':self.cfg['grok'],
            'luna_model':self.cfg.get('luna_model','gpt-5.6-luna'),
            'grok_model':self.cfg.get('grok_model','grok-4.6'),'lean_bin':self.cfg['lean_bin'],
            'lean_path':lean_path,'home':str(Path.home()),'path':self._environment()['PATH']}
        atomic_json(folder/'job.json',spec)
        return {'base_commit':base,'workspace':str(work),'package':str(package),
            'candidate':str(candidate),'dependencies':deps,'spec':spec}

    def execute(self, claim: dict) -> None:
        attempt=claim['attempt_id'];folder=self.artifacts/attempt;folder.mkdir(parents=True,exist_ok=True)
        unit='lean-swarm-'+attempt.replace('-','')+'.service'
        if not UNIT_RE.fullmatch(unit):raise ValueError('attempt ID must be a UUID')
        task=claim['task'];status='FAILED';result={'timing':{'prepare_started_unix':time.time()}};started_service=False;stopped=True
        self.store.record_runtime(attempt,{'unit':unit,'folder':str(folder),'owner':self.owner})
        try:
            prepared=self._prepare(claim,folder);atomic_json(folder/'prepared.json',prepared)
            result['timing']['prepare_finished_unix']=time.time()
            self.store.record_runtime(attempt,{'unit':unit,'folder':str(folder),
                'workspace':prepared['workspace'],'base_commit':prepared['base_commit'],'owner':self.owner})
            timeout=task.get('timeout_seconds',420)
            writable=[prepared['workspace'],str(Path.home()/'.codex'),str(Path.home()/'.grok')]
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
                for dep in prepared['dependencies']:
                    path=self.cfg['package_dir']+'/'+dep['target_path']
                    source=subprocess.check_output(['git','-C',str(self.repo),'show',prepared['base_commit']+':'+path])
                    dp=folder/'trusted-source'/dep['target_path'];dp.parent.mkdir(parents=True,exist_ok=True)
                    dp.write_bytes(source);self._compile(dp,artifacts,dep['target_path'],dep['target_name'])
                result['verification']=self._compile(verified,artifacts,task['target_path'],task['target_name'])
                result['verified_source']=str(verified);status='VERIFIED'
                result['timing']['verification_finished_unix']=time.time()
        except Exception as exc:
            result['error']=str(exc)
            if status not in ('TIMEOUT','INTERRUPTED','QUOTA'):status='FAILED'
        finally:
            if started_service and not stopped:
                try:result['containment']=self._stop_unit(unit);stopped=True
                except Exception as exc:result['containment_error']=str(exc)
            result['timing']['finished_unix']=time.time()
            atomic_json(folder/'timing.json',result['timing'])
            atomic_json(folder/'result.json',dict(result,status=status,task_id=claim['task_id']))
            if stopped:self.store.finish(attempt,status,result)
            else:
                self.stop.set();raise RuntimeError('containment uncertain; RUNNING claim retained for recovery')
        print(json.dumps({'task':claim['task_id'],'status':status,'elapsed':result.get('elapsed_seconds'),
            'error':result.get('error')},ensure_ascii=False),flush=True)

    def reverify(self, task_id: str) -> dict:
        """Recheck an immutable captured submission after an infrastructure fix.

        The original FAILED result and its event are retained. TIMEOUT candidates
        cannot be promoted with this operation. No model is called.
        """
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
        for dep in prepared['dependencies']:
            rel=self.cfg['package_dir']+'/'+dep['target_path']
            data=subprocess.check_output(['git','-C',str(self.repo),'show',prepared['base_commit']+':'+rel])
            parent=output/'source'/dep['target_path'];parent.parent.mkdir(parents=True,exist_ok=True)
            parent.write_bytes(data);self._compile(parent,artifacts,dep['target_path'],dep['target_name'])
        verification=self._compile(source,artifacts,task['target_path'],task['target_name'])
        updated=dict(result,verification=verification,verified_source=str(source),
                     reverified_without_model=True,original_failure=result,
                     reverification_reason='Trusted verifier infrastructure repair; frozen submission unchanged')
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
                for dep in self._dependencies(task):
                    self._compile(self.repo/self.cfg['package_dir']/dep['target_path'],checkdir,dep['target_path'],dep['target_name'])
                report=self._compile(target,checkdir,task['target_path'],task['target_name'])
                command=self.cfg.get('integration_command')
                if command:
                    gate=checked(command,cwd=self.repo/self.cfg['package_dir'],env=self._environment(),timeout=600)
                    (checkdir/'project-gate.log').write_text(gate)
                git(self.repo,'add','--',rel)
                git(self.repo,'commit','-m','test(lean-swarm): integrate checked task '+task_id);committed=True
                commit=git(self.repo,'rev-parse','HEAD');self.store.mark_integrated(self.project,task_id,commit)
                atomic_json(checkdir/'integration.json',{'commit':commit,'task':task_id,'verification':report,'timing':{'requested_unix':requested_unix,'lock_acquired_unix':lock_acquired_unix,'finished_unix':time.time()}})
            except Exception:
                if not committed:
                    subprocess.run(['git','-C',str(self.repo),'reset','-q','HEAD','--',rel],check=False)
                    if target.exists() and git(self.repo,'status','--porcelain','--',rel):target.unlink()
                raise
            print('INTEGRATED',task_id,commit,flush=True);return commit

    def _resource_allows_claim(self) -> bool:
        """Admission guard, not a Grok quota. Existing tasks are never killed here."""
        reserve=int(self.cfg.get('min_available_memory_mb',8192))
        try:
            memory=dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
            return int(memory['MemAvailable'].split()[0]) >= reserve*1024
        except (OSError,KeyError,ValueError):
            return True  # The tested production host is Linux; keep pure tests portable.

    def run(self, jobs: int=12, integrate: bool=False) -> list[dict]:
        """Fill ready workers while one independent thread integrates verified results.

        Integration remains single-writer and prerequisites still require INTEGRATED.
        An unrelated full-project gate no longer stops the dispatcher from launching.
        """
        if not 1<=jobs<=32:raise ValueError('dispatcher jobs must be in [1,32]')
        attempted=set();integration_future=None;integration_task=None;blocked_since=None
        telemetry_dir=self.root/'telemetry';telemetry_dir.mkdir(parents=True,exist_ok=True)
        telemetry=telemetry_dir/(self.project+'-'+uuid.uuid4().hex+'.jsonl')
        last_sample=0.0
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as pool, \
             concurrent.futures.ThreadPoolExecutor(max_workers=1) as integration_pool:
            futures=set()
            try:
                while not self.stop.is_set():
                    done={f for f in futures if f.done()};futures-=done
                    for future in done:future.result()
                    if integration_future is not None and integration_future.done():
                        try:integration_future.result()
                        except Exception as exc:
                            print('INTEGRATION_BLOCKED',integration_task,str(exc),flush=True)
                        integration_future=None
                    rows=self.store.list_tasks(self.project)
                    if integrate and integration_future is None:
                        ready=[r for r in rows if r['status']=='VERIFIED' and r['id'] not in attempted]
                        ready.sort(key=lambda r:(-r['payload'].get('priority',0),r['id']))
                        if ready:
                            integration_task=ready[0]['id'];attempted.add(integration_task)
                            integration_future=integration_pool.submit(self.integrate,integration_task)
                    resource_ok=self._resource_allows_claim()
                    while len(futures)<jobs and not self.stop.is_set() and resource_ok:
                        claim=self.store.claim(self.project,self.owner)
                        if claim is None:break
                        futures.add(pool.submit(self.execute,claim))
                        resource_ok=self._resource_allows_claim()
                    now=time.monotonic()
                    if now-last_sample>=1:
                        by_status={};by_id={r['id']:r for r in rows}
                        ready_count=0;dependency_blocked=0
                        for r in rows:
                            by_status[r['status']]=by_status.get(r['status'],0)+1
                            if r['status']=='QUEUED':
                                if all(by_id[d]['status']=='INTEGRATED' for d in r['payload']['depends_on']):ready_count+=1
                                else:dependency_blocked+=1
                        record={'unix':time.time(),'project':self.project,'worker_budget':jobs,
                            'worker_futures':len(futures),'integrating':integration_task if integration_future else None,
                            'task_states':by_status,'dependency_ready':ready_count,'dependency_blocked':dependency_blocked,
                            'resource_admission':resource_ok}
                        with telemetry.open('a') as out:out.write(json.dumps(record)+'\n')
                        last_sample=now
                    if not futures and integration_future is None:
                        pending=any(r['status']=='QUEUED' for r in rows)
                        if not resource_ok and pending:
                            if blocked_since is None:blocked_since=now
                            if now-blocked_since>=60:
                                print('RESOURCE_BLOCKED: finite batch stopped without altering queued tasks',flush=True);break
                            time.sleep(.2);continue
                        break
                    blocked_since=None
                    waiting=futures | ({integration_future} if integration_future is not None else set())
                    concurrent.futures.wait(waiting,timeout=.2,return_when=concurrent.futures.FIRST_COMPLETED)
            except BaseException:
                self.stop.set()
                raise
            finally:
                # Do not abandon live workers when the dispatcher encounters a fault.
                for future in futures:
                    try:future.result()
                    except Exception as exc:print('WORKER_FAILED_DURING_JOIN',str(exc),flush=True)
                if integration_future is not None:
                    try:integration_future.result()
                    except Exception as exc:print('INTEGRATION_BLOCKED',integration_task,str(exc),flush=True)
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
    env=dict(os.environ,HOME=spec['home'],PATH=spec['path'],LEAN_PATH=spec['lean_path'],LEAN_NUM_THREADS='2')
    for key in ('OPENAI_API_KEY','XAI_API_KEY','GROK_API_KEY','CODEX_API_KEY','GH_TOKEN','GITHUB_TOKEN'):
        env.pop(key,None)
    logdir=Path(spec['logdir']);leader=None;leader_output=None
    try:
        if spec['model']=='luna':
            cmd=[spec['codex'],'exec','--ignore-user-config','--skip-git-repo-check','--ephemeral',
                '--disable','multi_agent','-m',spec['luna_model'],'-c','model_reasoning_effort="high"',
                '-s','workspace-write','-C',spec['cwd'],'--json','-o',str(logdir/'final.txt'),'-']
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
