"""Pure tests: no model, account, network, Lean or sudo required."""
import unittest
from runtime import (BEGIN,END,reconstruct,validate_task,parse_axioms,UNIT_RE,
                     resolve_effort,validate_lean_options)
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

    def test_luna_effort_contract_and_pinned_options(self):
        base = task()
        for difficulty, expected in [('integration', 'high'), ('proof', 'xhigh'),
                                     ('foundation', 'max')]:
            value = dict(base, difficulty=difficulty)
            self.assertEqual(resolve_effort(value, {}), expected)
        self.assertEqual(resolve_effort(dict(base, reasoning_effort='max'), {}), 'max')
        self.assertEqual(resolve_effort(base, {'luna_reasoning_effort': 'high'}), 'high')
        for effort in ['low', 'medium', True, 1]:
            with self.subTest(effort=effort), self.assertRaises(ValueError):
                resolve_effort(dict(base, reasoning_effort=effort), {})
        for options in [['-DskipKernelTC=true'], ['-DtrustLevel=0'], ['--unsafe'], ['-o', 'x']]:
            with self.subTest(options=options), self.assertRaises(ValueError):
                validate_lean_options(options)
        self.assertEqual(validate_lean_options(None), ['-j2', '-DmaxHeartbeats=800000'])

    def test_job_entry_propagates_each_luna_effort_and_rejects_invalid_specs(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from unittest.mock import Mock, patch
        import json, os
        from runtime import job_entry
        with TemporaryDirectory() as directory:
            root = Path(directory); prompt = root/'prompt'; prompt.write_text('proof')
            for effort in ('high', 'xhigh', 'max'):
                logdir = root/effort; logdir.mkdir()
                spec = {'model': 'luna', 'luna_model': 'gpt-5.6-luna',
                        'luna_reasoning_effort': effort, 'codex': '/bin/false',
                        'cwd': str(root), 'logdir': str(logdir),
                        'prompt_file': str(prompt), 'home': str(root),
                        'path': os.environ.get('PATH', ''), 'lean_path': '',
                        'attempt_id': 'a'*32}
                spec_path = root/(effort+'.json'); spec_path.write_text(json.dumps(spec))
                with patch('runtime.subprocess.run', return_value=Mock(returncode=0)) as run:
                    self.assertEqual(job_entry(spec_path), 0)
                    command = run.call_args.args[0]
                    self.assertIn('model_reasoning_effort="'+effort+'"', command)
            bad = json.loads((root/'high.json').read_text()); bad['luna_reasoning_effort'] = 'low'
            bad_path = root/'bad.json'; bad_path.write_text(json.dumps(bad))
            with self.assertRaises(ValueError):
                job_entry(bad_path)

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

class ArtifactNamespaceTests(unittest.TestCase):
    def test_full_namespace_seed_and_private_output(self):
        from tempfile import TemporaryDirectory
        from pathlib import Path
        from runtime import seed_artifact_namespace,detach_object_links
        with TemporaryDirectory() as directory:
            root=Path(directory);baseline=root/'baseline';artifacts=root/'artifacts'
            old=baseline/'PoincareConjecture/Existing.olean';old.parent.mkdir(parents=True);old.write_bytes(b'pinned')
            sibling=baseline/'PoincareConjecture/Sub/Helper.olean';sibling.parent.mkdir();sibling.write_bytes(b'helper')
            seed_artifact_namespace(artifacts,'PoincareConjecture/New.lean',str(baseline))
            self.assertFalse((artifacts/'PoincareConjecture').is_symlink())
            linked=artifacts/'PoincareConjecture/Existing.olean';self.assertTrue(linked.is_symlink())
            self.assertEqual((artifacts/'PoincareConjecture/Sub/Helper.olean').read_bytes(),b'helper')
            detach_object_links(linked);linked.write_bytes(b'private replacement')
            self.assertEqual(old.read_bytes(),b'pinned')
            seed_artifact_namespace(artifacts,'PoincareConjecture/Other.lean',str(baseline))
            self.assertEqual(linked.read_bytes(),b'private replacement')
    def test_artifacts_reject_baseline_changes(self):
        from tempfile import TemporaryDirectory
        from pathlib import Path
        from runtime import seed_artifact_namespace
        with TemporaryDirectory() as directory:
            artifacts=Path(directory)/'artifacts'
            seed_artifact_namespace(artifacts,'tests/A.lean','/a')
            with self.assertRaises(ValueError):seed_artifact_namespace(artifacts,'tests/B.lean','/b')
    def test_reverification_preserves_failure_and_rejects_timeout(self):
        from tempfile import TemporaryDirectory
        from pathlib import Path
        import sqlite3,json
        from state import Store
        with TemporaryDirectory() as directory:
            db=Path(directory)/'state.sqlite3';store=Store(db);store.init_project('p',{})
            one=task();one['id']='a';two=task();two['id']='b';store.add_tasks('p',[one,two])
            first=store.claim('p','owner');store.finish(first['attempt_id'],'FAILED',{'error':'infrastructure'})
            result={'verification':{'compile_passed':True},'reverified_without_model':True}
            store.approve_reverification(first['attempt_id'],result)
            self.assertEqual(store.list_tasks('p')[0]['status'],'VERIFIED')
            with sqlite3.connect(db) as connection:
                prior=connection.execute('SELECT previous_result_json FROM reverification_events').fetchone()[0]
            self.assertEqual(json.loads(prior),{'error':'infrastructure'})
            second=store.claim('p','owner');store.finish(second['attempt_id'],'TIMEOUT',{})
            with self.assertRaises(ValueError):store.approve_reverification(second['attempt_id'],result)

if __name__=='__main__':unittest.main()
