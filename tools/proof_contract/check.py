#!/usr/bin/env python3
"""Version-1 proof boundary guard; completion requires real Lean proof bindings.

This is change control, not a security boundary against a repository administrator.
Use a trusted git base in CI: checking only a mutable manifest is insufficient.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tempfile
from typing import Any, Callable

MANIFEST = 'docs/proof-contract/v1.lock.json'
DAG = 'docs/proof-contract/v1.dag.json'
BINDINGS = 'docs/proof-contract/v1.bindings.json'
PREFIX = 'PoincareConjecture.ProofContract.V1.'
AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")


class GuardError(ValueError):
    pass


def git(root: Path, *args: str) -> bytes:
    run = subprocess.run(['git', '-C', str(root), *args], capture_output=True)
    if run.returncode:
        raise GuardError(run.stderr.decode(errors='replace').strip())
    return run.stdout


def safe_path(path: str) -> str:
    p = PurePosixPath(path)
    if p.is_absolute() or not p.parts or '..' in p.parts or str(p) != path:
        raise GuardError('unsafe contract path: ' + path)
    return path


def reader(root: Path, ref: str | None = None) -> Callable[[str], bytes]:
    def read(path: str) -> bytes:
        safe_path(path)
        if ref:
            return git(root, 'show', (':' if ref == 'INDEX' else ref + ':') + path)
        resolved = (root / path).resolve()
        if not resolved.is_relative_to(root.resolve()):
            raise GuardError('frozen file escapes repository: ' + path)
        return resolved.read_bytes()
    return read


def json_bytes(raw: bytes) -> Any:
    # Reject duplicate keys; otherwise a scanner and consumer could disagree.
    def pairs(items: list[tuple[str, Any]]) -> dict:
        result = {}
        for key, value in items:
            if key in result:
                raise GuardError('duplicate JSON key: ' + key)
            result[key] = value
        return result
    return json.loads(raw, object_pairs_hook=pairs)


def strip_comments_strings(text: str) -> str:
    out = []; i = 0; depth = 0; quoted = False; escape = False
    while i < len(text):
        c, pair = text[i], text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/': depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if quoted:
            out.append('\n' if c == '\n' else ' ')
            if escape: escape = False
            elif c == '\\': escape = True
            elif c == '"': quoted = False
            i += 1; continue
        if pair == '/-': depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            while i < len(text) and text[i] != '\n': out.append(' '); i += 1
            continue
        if c == '"': quoted = True; out.append(' '); i += 1; continue
        out.append(c); i += 1
    if depth or quoted:
        raise GuardError('unterminated Lean comment or string')
    return ''.join(out)


def validate_dag(dag: dict) -> tuple[dict[str, dict], list[str]]:
    nodes = dag['nodes']; by_id = {n['id']: n for n in nodes}
    if len(by_id) != len(nodes): raise GuardError('duplicate DAG node')
    if dag['root'] not in by_id: raise GuardError('missing public root')
    active: set[str] = set(); done: set[str] = set()
    def visit(key: str) -> None:
        if key not in by_id: raise GuardError('missing dependency: ' + key)
        if key in active: raise GuardError('dependency cycle: ' + key)
        if key in done: return
        node = by_id[key]
        if node['kind'] not in {'goal', 'checked_assembly', 'public_target'}:
            raise GuardError('unknown node kind')
        if not NAME.fullmatch(node['declaration']): raise GuardError('unsafe declaration')
        active.add(key)
        for dep in node['depends_on']: visit(dep)
        active.remove(key); done.add(key)
    visit(dag['root'])
    if done != set(by_id): raise GuardError('orphan nodes outside public root')
    return by_id, [n['id'] for n in nodes if n['kind'] == 'goal']


def validate_bindings(data: dict, goals: list[str]) -> dict:
    if set(data) != {'schema', 'bindings'} or data['schema'] != 1:
        raise GuardError('bindings must contain only schema and actual proof bindings')
    bindings = data['bindings']
    if not isinstance(bindings, dict) or not set(bindings) <= set(goals):
        raise GuardError('binding for an unknown/non-goal node')
    for binding in bindings.values():
        if not isinstance(binding, dict) or set(binding) != {'module', 'declaration'}:
            raise GuardError('a status flag is not a proof binding')
        if not all(isinstance(v, str) and NAME.fullmatch(v) for v in binding.values()):
            raise GuardError('unsafe module/declaration in proof binding')
    return bindings


def check_snapshot(read: Callable[[str], bytes], baseline: dict | None) -> dict:
    manifest = json_bytes(read(MANIFEST))
    if manifest['schema'] != 1 or manifest['version'] != 'v1':
        raise GuardError('unsupported manifest')
    if baseline is not None and manifest != baseline:
        raise GuardError('V1 manifest changed relative to trusted baseline; add V2, preserve V1')
    trusted = baseline if baseline is not None else manifest
    for path, expected in trusted['files'].items():
        if not re.fullmatch(r'[0-9a-f]{64}', expected): raise GuardError('invalid SHA-256')
        actual = hashlib.sha256(read(path)).hexdigest()
        if actual != expected: raise GuardError('frozen file changed: ' + path)
    for path, required in trusted['required_imports'].items():
        imports = re.findall(r'^\s*import\s+([\w.]+)\s*$',
            strip_comments_strings(read(path).decode()), re.M)
        if not set(required) <= set(imports): raise GuardError('required root import removed: ' + path)
    if read('PoincareConjecture/lean-toolchain').decode().strip() != trusted['lean_toolchain']:
        raise GuardError('Lean toolchain changed')
    packages = {p['name']: p for p in json_bytes(read('PoincareConjecture/lake-manifest.json'))['packages']}
    for name, expected in trusted['dependencies'].items():
        if name not in packages or any(packages[name].get(k) != v for k, v in expected.items()):
            raise GuardError('pinned dependency changed: ' + name)
    dag = json_bytes(read(DAG)); nodes, goals = validate_dag(dag)
    bindings = validate_bindings(json_bytes(read(BINDINGS)), goals)
    return {'manifest': manifest, 'dag': dag, 'nodes': nodes, 'goals': goals,
        'bindings': bindings, 'unbound': [g for g in goals if g not in bindings]}


def parse_axioms(output: str, name: str) -> list[str]:
    reports = re.findall("'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", output, re.S)
    if not reports and "'" + name + "' does not depend on any axioms" not in output:
        raise GuardError('missing axiom report: ' + name)
    used = {a.strip() for report in reports for a in report.split(',') if a.strip()}
    if not used <= AXIOMS or 'sorryAx' in output or 'ofReduceBool' in output:
        raise GuardError('unapproved transitive axioms: ' + repr(sorted(used)))
    return sorted(used)


def run_lean(root: Path, snapshot: dict) -> dict:
    package = root / 'PoincareConjecture'
    for name, pin in snapshot['manifest']['dependencies'].items():
        dep = package / '.lake/packages' / name
        if git(dep, 'rev-parse', 'HEAD').decode().strip() != pin['rev']:
            raise GuardError('dependency checkout is not pinned: ' + name)
        if git(dep, 'status', '--porcelain', '--untracked-files=no'):
            raise GuardError('tracked dependency source is dirty: ' + name)
    sys.path.insert(0, str(root / 'tools/lean_swarm'))
    from resources import slot
    state = Path(os.environ.get('LEAN_SWARM_STATE_ROOT', '~/.local/state/lean-swarm')).expanduser()
    def run(command: list[str], resource: str, limit: int) -> str:
        with slot(state, resource, limit):
            result = subprocess.run(command, cwd=package, capture_output=True, text=True, timeout=600)
        print(result.stdout, end=''); print(result.stderr, end='', file=sys.stderr)
        if result.returncode: raise GuardError('command failed: ' + ' '.join(command))
        return result.stdout + result.stderr
    modules = ['PoincareConjecture.ProofContract'] + sorted({b['module'] for b in snapshot['bindings'].values()})
    run(['lake', '--no-cache', 'build', *modules], 'compile', 6)
    fixed = run(['lake', 'env', 'lean', '-j2', '-DmaxHeartbeats=800000',
        'tests/ProofContract/TargetAudit.lean'], 'verify', 2)
    axiom_reports = {}
    for name in snapshot['manifest']['audited_declarations']:
        axiom_reports[name] = parse_axioms(fixed, name)
    lines = ['import PoincareConjecture.ProofContract']
    lines += ['import ' + m for m in sorted({b['module'] for b in snapshot['bindings'].values()})]
    lines += ['universe u', 'namespace ProofContractBindingAudit']
    for key, binding in sorted(snapshot['bindings'].items()):
        goal = snapshot['nodes'][key]['declaration']
        lines += [f'theorem bound_{key} : {goal}.{{u}} := {binding["declaration"]}',
            f'#print axioms bound_{key}']
    complete = not snapshot['unbound']
    if complete:
        args = ' '.join('bound_' + key for key in snapshot['dag']['assembly_argument_order'])
        lines += [f'theorem completedRoot : {PREFIX}TopologicalPoincareStatement.{{u}} :=',
            f'  {PREFIX}topological_of_contracts {args}', '#print axioms completedRoot']
    lines += ['end ProofContractBindingAudit']
    with tempfile.TemporaryDirectory(prefix='proof-contract-audit-') as temporary:
        source = Path(temporary) / 'Bindings.lean'; source.write_text('\n'.join(lines) + '\n')
        output = run(['lake', 'env', 'lean', '-j2', '-DmaxHeartbeats=800000', str(source)], 'verify', 2)
    for key in snapshot['bindings']:
        name = 'ProofContractBindingAudit.bound_' + key
        axiom_reports[name] = parse_axioms(output, name)
    if complete:
        name = 'ProofContractBindingAudit.completedRoot'
        axiom_reports[name] = parse_axioms(output, name)
    return {'verified_bindings': sorted(snapshot['bindings']), 'complete': complete,
        'axioms': axiom_reports, 'scope': 'own source targets and existing pinned dependency cache; no full dependency rebuild'}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument('--base', help='trusted git revision containing the V1 lock')
    parser.add_argument('--baseline-file', type=Path, help='externally preserved V1 lock')
    parser.add_argument('--ref', help='check a commit snapshot, or INDEX for staged content')
    parser.add_argument('--bootstrap', action='store_true', help='explicit first adoption before V1 exists in git')
    parser.add_argument('--lean', action='store_true', help='compile targets and actual proof bindings')
    parser.add_argument('--require-complete', action='store_true')
    parser.add_argument('--report', type=Path)
    args = parser.parse_args(argv)
    try:
        root = args.repo.resolve(); baseline = None
        if args.ref and args.lean: raise GuardError('--lean checks the working tree only; checkout the desired ref first')
        if args.baseline_file: baseline = json_bytes(args.baseline_file.read_bytes())
        elif args.base: baseline = json_bytes(reader(root, args.base)(MANIFEST))
        else:
            exists = subprocess.run(['git', '-C', str(root), 'cat-file', '-e', 'HEAD:' + MANIFEST], capture_output=True)
            if exists.returncode == 0: baseline = json_bytes(reader(root, 'HEAD')(MANIFEST))
        if baseline is None and not args.bootstrap:
            raise GuardError('no trusted V1 baseline; first adoption requires --bootstrap')
        snapshot = check_snapshot(reader(root, args.ref), baseline)
        report = {'freeze_check': 'PASS', 'baseline_mode': 'trusted' if baseline is not None else 'BOOTSTRAP',
            'frozen_files': len(snapshot['manifest']['files']), 'goal_nodes': len(snapshot['goals']),
            'unbound_goals': snapshot['unbound'], 'bound_but_not_yet_checked': sorted(snapshot['bindings']),
            'complete': False, 'assembly_is_conditional': True}
        if args.lean:
            report.update(run_lean(root, snapshot)); report['bound_but_not_yet_checked'] = []
        # A missing binding or lack of Lean verification can never produce COMPLETE.
        if args.require_complete and not report['complete']:
            raise GuardError('proof NOT COMPLETE; unresolved or unverified obligations: ' + ', '.join(snapshot['unbound']))
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return 0
    except (GuardError, OSError, ValueError, KeyError, TypeError, subprocess.TimeoutExpired) as exc:
        print('PROOF_CONTRACT_GUARD_FAILED: ' + str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
