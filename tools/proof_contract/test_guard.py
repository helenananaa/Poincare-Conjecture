"""Pure negative tests. No model calls, Lean compilation, network or repository edits."""
from copy import deepcopy
import contextlib
import hashlib
import io
import json
from pathlib import Path
import unittest

from check import (MANIFEST, DAG, BINDINGS, GuardError, check_snapshot,
    json_bytes, main, parse_axioms, strip_comments_strings, validate_bindings, validate_dag)

ROOT = Path(__file__).resolve().parents[2]


class FreezeGuardTests(unittest.TestCase):
    def setUp(self):
        self.baseline = json_bytes((ROOT / MANIFEST).read_bytes())
        paths = set(self.baseline['files']) | set(self.baseline['required_imports']) | {
            MANIFEST, DAG, BINDINGS, 'PoincareConjecture/lean-toolchain',
            'PoincareConjecture/lake-manifest.json'}
        self.data = {p: (ROOT / p).read_bytes() for p in paths}

    def check(self):
        return check_snapshot(self.data.__getitem__, self.baseline)

    def put(self, path, data):
        self.data[path] = json.dumps(data).encode()

    def test_actual_snapshot_is_not_completion(self):
        result = self.check()
        self.assertIn('geometric_trace', result['unbound'])
        self.assertIn('cover', result['bindings'])
        self.assertNotIn('complete', result)

    def test_root_statement_tampering(self):
        path = 'PoincareConjecture/PoincareConjecture/ProofContract/V1/Root.lean'
        self.data[path] += b'\n-- altered root\n'
        with self.assertRaisesRegex(GuardError, 'frozen file'): self.check()

    def test_shared_definition_tampering(self):
        path = 'PoincareConjecture/PoincareConjecture/ProofContract/V1/Manifolds.lean'
        self.data[path] += b'\n-- altered definition\n'
        with self.assertRaisesRegex(GuardError, 'frozen file'): self.check()

    def test_rehashing_source_and_manifest_does_not_bypass_baseline(self):
        path = 'PoincareConjecture/PoincareConjecture/ProofContract/V1/Root.lean'
        self.data[path] += b'\n-- altered root\n'
        new = deepcopy(self.baseline)
        new['files'][path] = hashlib.sha256(self.data[path]).hexdigest()
        self.put(MANIFEST, new)
        with self.assertRaisesRegex(GuardError, 'trusted baseline'): self.check()

    def test_removing_frozen_file_is_not_allowed(self):
        del self.data[next(iter(self.baseline['files']))]
        with self.assertRaises(KeyError): self.check()

    def test_root_import_cannot_be_removed(self):
        self.data['PoincareConjecture/PoincareConjecture.lean'] = b'import Mathlib\n'
        with self.assertRaisesRegex(GuardError, 'root import removed'): self.check()

    def test_commented_import_is_not_an_import(self):
        self.data['PoincareConjecture/PoincareConjecture.lean'] = (
            b'/- nested /- x -/\nimport PoincareConjecture.ProofContract\n-/\n')
        with self.assertRaisesRegex(GuardError, 'root import removed'): self.check()

    def test_string_import_is_not_an_import(self):
        self.data['PoincareConjecture/PoincareConjecture.lean'] = (
            b'def decoy := "\nimport PoincareConjecture.ProofContract\n"\n')
        with self.assertRaisesRegex(GuardError, 'root import removed'): self.check()

    def test_toolchain_cannot_drift(self):
        self.data['PoincareConjecture/lean-toolchain'] = b'leanprover/lean4:nightly\n'
        with self.assertRaises(GuardError): self.check()

    def test_dependency_pin_cannot_drift(self):
        path = 'PoincareConjecture/lake-manifest.json'
        value = json_bytes(self.data[path])
        next(p for p in value['packages'] if p['name'] == 'mathlib')['rev'] = '0' * 40
        self.put(path, value)
        with self.assertRaisesRegex(GuardError, 'dependency'): self.check()

    def test_dag_cycle(self):
        dag = json_bytes(self.data[DAG]); dag['nodes'][-1]['depends_on'] = ['public_root']
        with self.assertRaisesRegex(GuardError, 'cycle'): validate_dag(dag)

    def test_dag_missing_dependency(self):
        dag = json_bytes(self.data[DAG]); dag['nodes'][0]['depends_on'] = ['missing']
        with self.assertRaisesRegex(GuardError, 'missing dependency'): validate_dag(dag)

    def test_dag_duplicate_node(self):
        dag = json_bytes(self.data[DAG]); dag['nodes'].append(dag['nodes'][0])
        with self.assertRaisesRegex(GuardError, 'duplicate'): validate_dag(dag)

    def test_dag_orphan(self):
        dag = json_bytes(self.data[DAG]); node = deepcopy(dag['nodes'][-1]); node['id'] = 'orphan'
        dag['nodes'].append(node)
        with self.assertRaisesRegex(GuardError, 'orphan'): validate_dag(dag)

    def test_done_flag_is_not_evidence(self):
        bindings = {'schema': 1, 'bindings': {'cover': {'status': 'PROVED'}}}
        with self.assertRaisesRegex(GuardError, 'not a proof'): validate_bindings(bindings, ['cover'])

    def test_unknown_goal_binding(self):
        value = json_bytes(self.data[BINDINGS]); value['bindings']['fake_goal'] = value['bindings']['cover']
        with self.assertRaisesRegex(GuardError, 'unknown'): validate_bindings(value, ['cover'])

    def test_proof_name_injection(self):
        value = json_bytes(self.data[BINDINGS]); value['bindings']['cover']['declaration'] = 'foo\naxiom hack : False'
        with self.assertRaisesRegex(GuardError, 'unsafe'): validate_bindings(value, ['cover'])

    def test_duplicate_json_keys(self):
        with self.assertRaisesRegex(GuardError, 'duplicate JSON'):
            json_bytes(b'{"complete":false,"complete":true}')

    def test_sorry_axiom_rejected_even_after_fake_success(self):
        text = "'test' does not depend on any axioms\n 'test' depends on axioms: [sorryAx]"
        with self.assertRaisesRegex(GuardError, 'unapproved'): parse_axioms(text, 'test')

    def test_unrelated_axiom_report_is_not_accepted(self):
        with self.assertRaisesRegex(GuardError, 'missing axiom'):
            parse_axioms("'other' depends on axioms: [propext]", 'test')

    def test_standard_axioms_are_accepted(self):
        self.assertEqual(parse_axioms("'test' depends on axioms: [propext, Quot.sound]", 'test'),
            ['Quot.sound', 'propext'])

    def test_unterminated_comments_are_rejected(self):
        with self.assertRaises(GuardError): strip_comments_strings('/- unclosed')

    def test_complete_gate_refuses_current_open_proof(self):
        with contextlib.redirect_stderr(io.StringIO()), contextlib.redirect_stdout(io.StringIO()):
            code = main(['--repo', str(ROOT), '--bootstrap', '--require-complete'])
        self.assertEqual(code, 1)


if __name__ == '__main__':
    unittest.main()
