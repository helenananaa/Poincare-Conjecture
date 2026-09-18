#!/usr/bin/env python3
"""Validate cumulative proofs and smooth real-interval trivialization."""
import argparse
import fcntl
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time
from datetime import datetime, timezone

p = argparse.ArgumentParser()
p.add_argument('--output', type=Path)
p.add_argument('--fresh', action='store_true')
a = p.parse_args()
package = Path(__file__).resolve().parents[1]
out = (a.output or package / '.lake/integer-extension-audit').resolve()
out.mkdir(parents=True, exist_ok=True)
lock = open(package / ".lake/smooth-splice-validation.lock", "a")
fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
expected_mathlib = '520045ab14e26149ee970e2e617ca04b09bde5d6'
expected_parent = '684a8dd203bb5795415b43195e2d7889bf170a9c'
assert (package/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.1'
actual = subprocess.check_output(['git', '-C', str(package/'.lake/packages/mathlib'),
                                 'rev-parse', 'HEAD'], text=True).strip()
assert actual == expected_mathlib, actual
sources = sorted((package/'PoincareConjecture').rglob('*.lean'))
sources += sorted((package/'tests').glob('*.lean')) + [package/'PoincareConjecture.lean']
for f in sources:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', f.read_text()), str(f)
hashes_before = {str(f.relative_to(package)): hashlib.sha256(f.read_bytes()).hexdigest() for f in sources}
lock_file = open(package/'.lake/integer-extension-validation.lock', 'w')
fcntl.flock(lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
build = package/'.lake/build'
if a.fresh and build.exists():
    saved = out/('previous-build-'+str(time.time_ns()))
    build.rename(saved)
project_build_present_at_start = build.exists()
results = []
env = dict(os.environ, LEAN_NUM_THREADS='4')

def run(label, command, cwd=package):
    started = time.monotonic()
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
    (out/(label+'.log')).write_text(result.stdout)
    results.append(dict(step=label, exit_code=result.returncode,
                        seconds=round(time.monotonic()-started, 3)))
    print(label, 'exit='+str(result.returncode), flush=True)
    if result.returncode or re.search(r'warning:|sorryAx|ofReduceBool', result.stdout):
        print(result.stdout, flush=True)
        raise SystemExit('Verification failed: '+label)
    return result.stdout
version = run('toolchain', ['lake', 'env', 'lean', '--version']).strip()
assert 'version 4.32.1,' in version, version
run('build', ['lake', 'build'])
suites = [
    'FiberSaturationSanity', 'ClosedCollarSanity', 'ProductPairingSanity',
    'TorusSanity', 'TorusRegionSanity', 'BoundaryRegularitySanity',
    'SmoothEmbeddingSanity', 'PresentationSanity', 'SmoothCylinderSanity',
    'AbstractBundleCutSanity', 'ClosedRealBridgeSanity', 'AbstractBoundaryPairingSanity', 'SmoothSpliceSanity', 'PeriodicEndMatchingSanity', 'IntegerExtensionSanity',
]
for suite in suites:
    run(suite, ['lake', 'env', 'lean', 'tests/'+suite+'.lean'])
text = run('axioms', ['lake', 'env', 'lean', 'tests/FullIntegerExtensionAudit.lean'])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
closures = {}
for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text, re.S):
    used = {x.strip() for x in body.split(',') if x.strip()}
    assert used <= allowed, (name, used - allowed)
    closures[name] = sorted(used)
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    closures[name] = []
assert len(closures) == 289, (len(closures), text)
gate = package.parent/'scripts/validate-lean-changes.sh'
if gate.exists():
    run('upstream-validation', ['bash', str(gate),
        'bb91a091f0b968f8bbe8d861e025a88d82b161be'], package.parent)
    run('whitespace', ['git', 'diff', '--check'], package.parent)
hashes_after = {str(f.relative_to(package)): hashlib.sha256(f.read_bytes()).hexdigest() for f in sources}
assert hashes_before == hashes_after, 'Source changed during validation'
report = dict(
    source_hashes_stable=True,
    status='PASS', utc=datetime.now(timezone.utc).isoformat(), lean=version,
    project_build_present_at_start=project_build_present_at_start,
    mathlib_commit=actual, contribution_parent=expected_parent,
    results=results, transitive_axioms=closures,
    source_sha256={str(f.relative_to(package)): hashlib.sha256(f.read_bytes()).hexdigest()
                   for f in sources},
    configuration_sha256={n: hashlib.sha256((package/n).read_bytes()).hexdigest()
                          for n in ['lean-toolchain','lakefile.lean','lake-manifest.json']},
    scope='Global smooth real-axis extension from local smooth charts and a supplied smooth height-shifting deck diffeomorphism; all-integer equivariance and bijective local smoothness; no construction of an abstract circle-bundle smooth pullback or full Poincare proof.',
)
(out/'verification.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print('ALL_CHECKS_PASSED', out, flush=True)
