"""Pure tests: no model, account, network, Lean or sudo required."""
import unittest
from runtime import BEGIN,END,reconstruct,validate_task,parse_axioms,UNIT_RE
TEMPLATE=('import Mathlib\nnamespace Demo\ntheorem target (n : Nat) : n = n :=\n'+BEGIN+'\nby\n  sorry\n'+END+'\nend Demo\n')
def task():return {'id':'test','model':'luna','depends_on':[],'source':TEMPLATE,'target_name':'Demo.target','target_path':'tests/Swarm/Target.lean'}
class FrozenProofTests(unittest.TestCase):
    def test_accepts_only_reconstructed_proof(self):
        answer=TEMPLATE.replace('  sorry','  rfl');self.assertEqual(reconstruct(TEMPLATE,answer),answer)
    def test_harmless_whitespace_restores_original_context(self):
        answer=TEMPLATE.replace('  sorry','  rfl').replace('end Demo','\nend Demo')
        self.assertEqual(reconstruct(TEMPLATE,answer),TEMPLATE.replace('  sorry','  rfl'))
    def test_statement_change_rejected(self):
        answer=TEMPLATE.replace('  sorry','  trivial').replace('n = n','True')
        with self.assertRaises(ValueError):reconstruct(TEMPLATE,answer)
    def test_placeholder_and_meta_escape_rejected(self):
        for proof in ['sorry','admit','native_decide','run_tac pure ()','unsafe']:
            with self.subTest(proof=proof),self.assertRaises(ValueError):reconstruct(TEMPLATE,TEMPLATE.replace('  sorry','  '+proof))
    def test_marker_changes_rejected(self):
        for answer in [TEMPLATE.replace(BEGIN,''),TEMPLATE+END]:
            with self.assertRaises(ValueError):reconstruct(TEMPLATE,answer)
    def test_paths_and_names(self):
        validate_task(task())
        for path in ['/tmp/out.lean','../out.lean','.git/config.lean','tests/../out.lean','out.py']:
            value=task();value['target_path']=path
            with self.subTest(path=path),self.assertRaises(ValueError):validate_task(value)
        value=task();value['target_name']='Demo.target\n#eval 1'
        with self.assertRaises(ValueError):validate_task(value)
    def test_axiom_allowlist_requires_actual_target(self):
        self.assertEqual(parse_axioms("'Demo.target' does not depend on any axioms",'Demo.target'),[])
        self.assertEqual(parse_axioms("'Demo.target' depends on axioms: [propext, Quot.sound]",'Demo.target'),['Quot.sound','propext'])
        for output in ["'Demo.target' depends on axioms: [sorryAx]","'Other.target' does not depend on any axioms",'']:
            with self.assertRaises(ValueError):parse_axioms(output,'Demo.target')
    def test_no_unrelated_unit_can_be_targeted(self):
        self.assertTrue(UNIT_RE.fullmatch('lean-swarm-'+'a'*32+'.service'))
        self.assertFalse(UNIT_RE.fullmatch('grok.service'));self.assertFalse(UNIT_RE.fullmatch('lean-swarm-*'))
if __name__=='__main__':unittest.main()

class LaunchFailureTests(unittest.TestCase):
    def test_partial_launch_failure_stops_unit_before_releasing_claim(self):
        from unittest.mock import Mock,patch
        from tempfile import TemporaryDirectory
        from pathlib import Path
        from uuid import uuid4
        from runtime import Controller
        with TemporaryDirectory() as directory:
            root=Path(directory);store=Mock()
            store.get_project.return_value={'repo':directory,'integration_branch':'integration','lean_bin':'/usr/bin','lean_path':'','package_dir':'Package'}
            controller=Controller(store,root,'test');work=root/'work';work.mkdir()
            controller._prepare=Mock(return_value={'workspace':str(work),'base_commit':'base','candidate':str(work/'candidate.lean'),'dependencies':[],'spec':{'logdir':str(work)}})
            controller._stop_unit=Mock(return_value={'cgroup_populated':False})
            claim={'attempt_id':str(uuid4()),'task_id':'job','task':task()}
            with patch('runtime.checked',side_effect=RuntimeError('launch failed after partial unit creation')),patch('runtime.Path.home',return_value=root):
                controller.execute(claim)
            controller._stop_unit.assert_called_once()
            self.assertEqual(store.finish.call_args.args[1],'FAILED')

    def test_uncertain_containment_keeps_running_claim(self):
        from unittest.mock import Mock,patch
        from tempfile import TemporaryDirectory
        from pathlib import Path
        from uuid import uuid4
        from runtime import Controller
        with TemporaryDirectory() as directory:
            root=Path(directory);store=Mock()
            store.get_project.return_value={'repo':directory,'integration_branch':'integration','lean_bin':'/usr/bin','lean_path':'','package_dir':'Package'}
            controller=Controller(store,root,'test');work=root/'work';work.mkdir()
            controller._prepare=Mock(return_value={'workspace':str(work),'base_commit':'base','candidate':str(work/'candidate.lean'),'dependencies':[],'spec':{'logdir':str(work)}})
            controller._stop_unit=Mock(side_effect=RuntimeError('processes remain'))
            claim={'attempt_id':str(uuid4()),'task_id':'job','task':task()}
            with patch('runtime.checked',side_effect=RuntimeError('launch error')),patch('runtime.Path.home',return_value=root),self.assertRaises(RuntimeError):
                controller.execute(claim)
            store.finish.assert_not_called();self.assertTrue(controller.stop.is_set())
