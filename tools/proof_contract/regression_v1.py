#!/usr/bin/env python3
"""Run immutable V1 unit tests on their original fixture, then test live bindings.

The original test_proof_name_injection assumes only the `cover` binding. Its
fixture must not silently expand when a new mathematical leaf is completed.
This runner changes no frozen files and does not suppress original test failures.
Live Lean type/axiom verification remains a separate mandatory --lean check.
"""
from pathlib import Path
from tempfile import TemporaryDirectory
from copy import deepcopy
import json, subprocess, sys, unittest
ROOT=Path(sys.argv[1]).resolve()
REFERENCE='9d6f10c8716fbe5eeffe7c81a00da20294cb8bdb'
sys.path.insert(0,str(ROOT/'tools/proof_contract'))
import check, test_guard

def original(path):
    return subprocess.check_output(['git','-C',str(ROOT),'show',REFERENCE+':'+path])
manifest=check.json_bytes(original(check.MANIFEST))
paths=set(manifest['files']) | set(manifest['required_imports']) | {
    check.MANIFEST,check.DAG,check.BINDINGS,'PoincareConjecture/lean-toolchain','PoincareConjecture/lake-manifest.json'}
with TemporaryDirectory(prefix='poincare-v1-original-fixture-') as directory:
    fixture=Path(directory)
    for path in paths:
        p=fixture/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(original(path))
    subprocess.run(['git','init','-q',str(fixture)],check=True)
    test_guard.ROOT=fixture
    old_result=unittest.TextTestRunner(verbosity=1).run(unittest.defaultTestLoader.loadTestsFromTestCase(test_guard.FreezeGuardTests))
test_guard.ROOT=ROOT
live=check.check_snapshot(check.reader(ROOT),manifest)
class LiveBindingTests(unittest.TestCase):
    def test_current_snapshot_preserves_frozen_boundary(self):
        self.assertEqual(live['manifest'],manifest)
    def test_current_bindings_are_valid_goal_names(self):
        self.assertEqual(check.validate_bindings(check.json_bytes((ROOT/check.BINDINGS).read_bytes()),live['goals']),live['bindings'])
    def test_injected_declaration_rejected_with_full_live_goal_set(self):
        data=check.json_bytes((ROOT/check.BINDINGS).read_bytes())
        data['bindings']['cover']['declaration']='foo\naxiom hack : False'
        with self.assertRaisesRegex(check.GuardError,'unsafe'):
            check.validate_bindings(data,live['goals'])
    def test_done_flag_is_still_not_a_proof(self):
        data={'schema':1,'bindings':{'handle':{'status':'PROVED'}}}
        with self.assertRaises(check.GuardError):check.validate_bindings(data,live['goals'])
    def test_remaining_goals_not_mistaken_for_completion(self):
        self.assertIn('geometric_trace',live['unbound'])
        self.assertIn('smoothing',live['unbound'])
new_result=unittest.TextTestRunner(verbosity=1).run(unittest.defaultTestLoader.loadTestsFromTestCase(LiveBindingTests))
report={'original_frozen_fixture_reference':REFERENCE,'original_fixture_tests':old_result.testsRun,
    'original_fixture_passed':old_result.wasSuccessful(),'live_multibinding_tests':new_result.testsRun,
    'live_multibinding_passed':new_result.wasSuccessful(),'frozen_files_modified':False,
    'legacy_direct_discovery_caveat':'Original live-data test harness has a single-binding fixture assumption; use this explicit fixture runner. Remote CI workflow has not been migrated.'}
print(json.dumps(report,indent=2))
raise SystemExit(0 if old_result.wasSuccessful() and new_result.wasSuccessful() else 1)
