#!/usr/bin/env python3
"""Validate abstract-circle-bundle cut, seam relation, and topological mapping torus."""
import argparse, hashlib, json, os, re, subprocess, time
from datetime import datetime, timezone
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
args = parser.parse_args()
package = Path(__file__).resolve().parents[1]
repo = package.parent
out = (args.output or package/'.lake/abstract-bundle-audit').resolve()
out.mkdir(parents=True, exist_ok=True)
base = 'bb91a091f0b968f8bbe8d861e025a88d82b161be'
mathlib = '520045ab14e26149ee970e2e617ca04b09bde5d6'
assert (package/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.1'
actual = subprocess.check_output(['git', '-C', str(package/'.lake/packages/mathlib'),
                                  'rev-parse', 'HEAD'], text=True).strip()
assert actual == mathlib, actual
sources = sorted((package/'PoincareConjecture').rglob('*.lean'))
sources += sorted((package/'tests').glob('*.lean')) + [package/'PoincareConjecture.lean']
for p in sources:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', p.read_text()), str(p)
project_build_present_at_start = (package/'.lake/build').exists()
results = []
env = dict(os.environ, LEAN_NUM_THREADS='4')
def run(label, command, cwd=package):
    start = time.monotonic()
    p = subprocess.run(command, cwd=cwd, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
    (out/(label+'.log')).write_text(p.stdout)
    results.append(dict(step=label, exit_code=p.returncode,
                        seconds=round(time.monotonic()-start, 3)))
    print(label, 'exit='+str(p.returncode), flush=True)
    if p.returncode or re.search(r'warning:|sorryAx|ofReduceBool', p.stdout):
        print(p.stdout)
        raise SystemExit('Failed: '+label)
    return p.stdout

version = run('toolchain', ['lake', 'env', 'lean', '--version']).strip()
assert 'version 4.32.1,' in version, version
run('upstream-validation', ['bash', 'scripts/validate-lean-changes.sh', base], repo)
run('sanity', ['lake', 'env', 'lean', 'tests/FiberSaturationSanity.lean'])
run('closed-collar-sanity', ['lake', 'env', 'lean', 'tests/ClosedCollarSanity.lean'])
run('product-pairing-sanity', ['lake', 'env', 'lean', 'tests/ProductPairingSanity.lean'])
run('torus-sanity', ['lake', 'env', 'lean', 'tests/TorusSanity.lean'])
run('torus-region-sanity', ['lake', 'env', 'lean', 'tests/TorusRegionSanity.lean'])
run('boundary-regularity-sanity', ['lake', 'env', 'lean', 'tests/BoundaryRegularitySanity.lean'])
run('smooth-embedding-sanity', ['lake', 'env', 'lean', 'tests/SmoothEmbeddingSanity.lean'])
run('presentation-sanity', ['lake', 'env', 'lean', 'tests/PresentationSanity.lean'])
run('smooth-cylinder-sanity', ['lake', 'env', 'lean', 'tests/SmoothCylinderSanity.lean'])
run('abstract-bundle-sanity', ['lake', 'env', 'lean', 'tests/AbstractBundleCutSanity.lean'])
text = run('axioms', ['lake', 'env', 'lean', 'tests/FullAbstractBundleAudit.lean'])
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
closures = {}
for name, body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text, re.S):
    used = {x.strip() for x in body.split(',') if x.strip()}
    assert used <= allowed, (name, used - allowed)
    closures[name] = sorted(used)
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    closures[name] = []
assert len(closures) == 191, (len(closures), text)
run('whitespace', ['git', 'diff', '--check'], repo)
report = dict(status='PASS', project_build_present_at_start=project_build_present_at_start, utc=datetime.now(timezone.utc).isoformat(),
              lean=version, upstream_base=base, mathlib_commit=mathlib,
              results=results, transitive_axioms=closures,
              source_sha256={str(p.relative_to(package)):hashlib.sha256(p.read_bytes()).hexdigest()
                             for p in sources},
              contribution_parent='d15d97cf2dc9cfd73b6b5202b63539d79669e0e4',
              scope='Abstract standard FiberBundle over AddCircle to a closed-cylinder seam quotient, with derived monodromy and base-preserving homeomorphism; no smooth trivialization or continuous real-axis extension claimed')
(out/'verification.json').write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n')
print('ALL_CHECKS_PASSED', out, flush=True)
