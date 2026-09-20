import tempfile
import threading
import unittest
from pathlib import Path
from supervisor import Supervisor


class FakeStore:
    def list_tasks(self, project):
        return []
    def list_acceptance_gates(self):
        return []


class FakeController:
    def __init__(self, root):
        self.root = Path(root)
        self.project = 'test'
        self.cfg = {'verifier_slots': 2}
        self.store = FakeStore()
        self.stop = threading.Event()
        self.calls = []
    def run(self, jobs=0, integrate=False, poll_hook=None):
        self.calls.append((jobs, integrate))
        if poll_hook:
            poll_hook()
        return []


class FakeQueue:
    def __init__(self, fail=False):
        self.calls = []
        self.imports = []
        self.fail = fail
        self.rows = [{'job_id': 'r1', 'task_id': 'old-task', 'status': 'REVIEW_REQUIRED',
                      'manifest_sha256': 'a' * 64, 'effort': 'xhigh'}]
    def import_batch(self, project, path):
        self.imports.append((project, path))
    def poll(self, project):
        return {}
    def list_jobs(self, project):
        return self.rows
    def verify(self, job, targets):
        self.calls.append((job, targets))
        if self.fail:
            raise ValueError('test compiler rejection')
        return {'passed': True}


class SupervisorTests(unittest.TestCase):
    def test_successful_research_check_still_requires_review(self):
        with tempfile.TemporaryDirectory() as root:
            c, q = FakeController(root), FakeQueue()
            s = Supervisor(c, ['/tmp/old-batch'], {'r1': [{'path': 'X.lean', 'name': 'x'}]}, queue=q)
            s.run(jobs=0, integrate=True)
            self.assertEqual(len(q.calls), 1)
            self.assertEqual(q.rows[0]['status'], 'REVIEW_REQUIRED')
            self.assertEqual(c.calls, [(0, True)])

    def test_failed_check_is_not_retried_in_a_loop(self):
        with tempfile.TemporaryDirectory() as root:
            c, q = FakeController(root), FakeQueue(fail=True)
            s = Supervisor(c, verification_plan={'old-task': [{'path': 'X.lean', 'name': 'x'}]}, queue=q)
            s.run()
            s.tick()
            self.assertEqual(len(q.calls), 1)
            self.assertTrue(any('validation failed' in x for x in s.outcome.values()))

    def test_no_trusted_targets_means_no_compile_or_promotion(self):
        with tempfile.TemporaryDirectory() as root:
            c, q = FakeController(root), FakeQueue()
            Supervisor(c, queue=q).run()
            self.assertEqual(q.calls, [])
            self.assertEqual(q.rows[0]['status'], 'REVIEW_REQUIRED')

    def test_empty_target_plan_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            with self.assertRaises(ValueError):
                Supervisor(FakeController(root), verification_plan={'r1': []}, queue=FakeQueue())

    def test_poll_error_is_visible(self):
        with tempfile.TemporaryDirectory() as root:
            q = FakeQueue()
            def fail(project):
                raise RuntimeError('cannot reconcile external processes')
            q.poll = fail
            with self.assertRaises(RuntimeError):
                Supervisor(FakeController(root), queue=q).run()

if __name__ == '__main__':
    unittest.main()
