#!/usr/bin/env python3
"""Rebuild and audit complementary-boundary selection with the pinned project."""
import argparse, fcntl, hashlib, json, os, re, subprocess, time
from datetime import datetime, timezone
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--output', type=Path)
p.add_argument('--fresh', action='store_true', help='Fresh main-package build; requires --allow-full-rebuild')
p.add_argument('--allow-full-rebuild', action='store_true',
               help='Explicit opt-in to fresh or whole-repository validation; never enable in routine agent batches')
p.add_argument('--base-ref', required=True,
               help='Explicit already-checked ancestor for incremental dependency selection; no historical default')
a = p.parse_args()
if a.fresh and not a.allow_full_rebuild:
    p.error('--fresh is disabled for routine validation; explicit --allow-full-rebuild is required')
r = Path(__file__).resolve().parents[1]
validation_base = subprocess.check_output(
    ['git','rev-parse','--verify','--end-of-options',a.base_ref+'^{commit}'],cwd=r.parent,text=True).strip()
subprocess.run(['git','merge-base','--is-ancestor',validation_base,'HEAD'],cwd=r.parent,check=True)
out = (a.output or r/'.lake/complementary-frontier-audit').resolve()
out.mkdir(parents=True, exist_ok=True)
lock = open(r/'.lake/complementary-frontier-validation.lock', 'a')
fcntl.flock(lock, fcntl.LOCK_EX)
mathlib = '520045ab14e26149ee970e2e617ca04b09bde5d6'
parent = '8dd50bcdcc5efa4d85d34a8dcfb0311797c7f3e3'
assert (r/'lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.1'
actual = subprocess.check_output(['git','-C',str(r/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip()
assert actual == mathlib
sources = sorted((r/'PoincareConjecture').rglob('*.lean'))
sources += sorted((r/'tests').glob('*.lean')) + [r/'PoincareConjecture.lean']
for f in sources:
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',f.read_text()),str(f)
def hashes():
    return {str(f.relative_to(r)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sources}
before = hashes()
build = r/'.lake/build'
if a.fresh and build.exists():
    build.rename(out/('previous-build-'+str(time.time_ns())))
fresh = not build.exists()
env = dict(os.environ, LEAN_NUM_THREADS='4')
results = []
def run(label, cmd, cwd=r):
    t = time.monotonic()
    v = subprocess.run(cmd,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT,timeout=600)
    (out/(label+'.log')).write_text(v.stdout)
    results.append(dict(step=label,exit_code=v.returncode,seconds=round(time.monotonic()-t,3)))
    print(label,'exit='+str(v.returncode),flush=True)
    if v.returncode or re.search(r'warning:|sorryAx|ofReduceBool',v.stdout):
        print(v.stdout,flush=True)
        raise SystemExit('Failed: '+label)
    return v.stdout
version = run('toolchain',['lake','env','lean','--version']).strip()
assert 'version 4.32.1,' in version
run('build',['lake','build'])
suites = sorted((r/'tests').glob('*Sanity.lean'))
for f in suites:
    run(f.stem,['lake','env','lean',str(f.relative_to(r))])
old = run('prior-axioms',['lake','env','lean','tests/FullRelativeProductAudit.lean'])
new = run('new-axioms',['lake','env','lean','tests/ComplementaryFrontierAudit.lean'])
allowed = {'propext','Classical.choice','Quot.sound'}
closures = {}
for text in [old,new]:
    for name,body in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text,re.S):
        used = {x.strip() for x in body.split(',') if x.strip()}
        assert used <= allowed,(name,used)
        closures[name] = sorted(used)
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):
        closures[name] = []
assert len(closures) == 364,len(closures)
gate = r.parent/'scripts/validate-lean-changes.sh'
if gate.exists():
    gate_args=['bash',str(gate),validation_base]
    if a.allow_full_rebuild:gate_args.append('--allow-full-rebuild')
    run('upstream-validation',gate_args,r.parent)
    run('whitespace',['git','diff','--check'],r.parent)
assert before == hashes(),'Sources changed during verification'
report = dict(status='PASS',utc=datetime.now(timezone.utc).isoformat(),lean=version,
              contribution_parent=parent,validation_base=validation_base,mathlib_commit=mathlib,source_hashes_stable=True,
              project_build_present_at_start=not fresh,sanity_suites=len(suites),results=results,
              transitive_axioms=closures,source_sha256=before,
              scope='Complementary-frontier selection from finite disjoint one-sided collars; no collar-existence, smooth-closure or complete Poincare claim.')
(out/'verification.json').write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print('ALL_CHECKS_PASSED',out,flush=True)
