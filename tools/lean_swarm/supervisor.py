"""Local queue supervisor: dispatch proofs and collect research without restarting it.

Fixed proof cards may integrate automatically. Exploration completion only enters a
semantic-review queue; no process exit, model statement or literal-sorry scan opens a gate.
"""
from __future__ import annotations
import concurrent.futures
import hashlib
import fcntl
import json
import time
from pathlib import Path
from research_queue import ResearchQueue
from runtime import atomic_json


class Supervisor:
    def __init__(self, controller, handoff_roots=(), verification_plan=None, *, queue=None):
        self.controller = controller
        self.store = controller.store
        self.project = controller.project
        self.root = controller.root
        self.queue = queue if queue is not None else ResearchQueue(self.store, self.root)
        self.plan = verification_plan or {}
        if not isinstance(self.plan, dict):
            raise ValueError('verification plan must map research IDs to trusted target lists')
        for targets in self.plan.values():
            if not isinstance(targets, list) or not targets:
                raise ValueError('each verification plan requires a nonempty target list')
        for root in handoff_roots:
            self.queue.import_batch(self.project, Path(root))
        self.pending = {}
        self.attempted = set()
        self.outcome = {}
        self.pool = None
        self.last_snapshot = None
        self.last_write = 0.0
        safe = hashlib.sha256(self.project.encode()).hexdigest()[:20]
        self.status_path = self.root / 'telemetry' / ('supervisor-' + safe + '.json')
        self.singleton_path = self.root / 'locks' / ('supervisor-' + safe + '.lock')
        if self.status_path.is_file():
            previous = json.loads(self.status_path.read_text())
            if previous.get('project') == self.project:
                self.outcome.update(previous.get('verification_outcomes', {}))
                self.attempted.update(self.outcome)


    @staticmethod
    def _identity(row):
        return row.get('job_id', row.get('id'))

    @staticmethod
    def _manifest(row):
        value = row.get('manifest_sha256', row.get('manifest_hash'))
        if value:
            return value
        manifest = row.get('manifest', {})
        if isinstance(manifest, str):
            try:
                manifest = json.loads(manifest)
            except ValueError:
                return None
        return manifest.get('manifest_sha256', manifest.get('sha256'))

    def tick(self):
        """No model call or long compilation occurs in this dispatch-thread hook."""
        self.queue.poll(self.project)
        rows = self.queue.list_jobs(self.project)
        for future, key in list(self.pending.items()):
            if not future.done():
                continue
            try:
                result = future.result()
                if isinstance(result, dict) and result.get('status') == 'VALIDATION_FAILED':
                    self.outcome[key] = 'independent validation failed; source not accepted'
                else:
                    self.outcome[key] = 'independent-check-returned; semantic review still required'
            except Exception as exc:
                self.outcome[key] = 'validation failed: ' + str(exc)[-1500:]
            del self.pending[future]
        slots = int(self.controller.cfg.get('verifier_slots', 2))
        for row in rows:
            job_id, manifest = self._identity(row), self._manifest(row)
            targets = self.plan.get(job_id, self.plan.get(row.get('task_id')))
            if not targets or not manifest or row.get('status') != 'REVIEW_REQUIRED':
                continue
            verified = row.get('verification', {})
            if (verified.get('independent') and verified.get('manifest_sha256') == manifest
                    and verified.get('targets') == targets):
                continue
            digest = hashlib.sha256(json.dumps(targets, sort_keys=True).encode()).hexdigest()
            key = job_id + ':' + manifest + ':' + digest
            if key in self.attempted or len(self.pending) >= slots or self.pool is None:
                continue
            self.attempted.add(key)
            future = self.pool.submit(self.queue.verify, job_id, targets)
            self.pending[future] = key
        summary = [{k: r.get(k) for k in ('job_id', 'task_id', 'status', 'effort')}
                   for r in rows]
        signature = json.dumps(summary, sort_keys=True)
        now = time.monotonic()
        if signature != self.last_snapshot or now - self.last_write >= 15:
            atomic_json(self.status_path, {'updated_unix': time.time(), 'project': self.project,
                'research_jobs': summary, 'verification_active': len(self.pending),
                'verification_outcomes': self.outcome, 'automatic_semantic_approval': False})
            self.last_snapshot, self.last_write = signature, now
        return rows

    def _dispatch_signature(self):
        rows = self.store.list_tasks(self.project)
        gates = self.store.list_acceptance_gates()
        signals = {}
        if hasattr(self.store, '_connection'):
            with self.store._connection() as connection:
                signals['limits'] = [tuple(r) for r in connection.execute('SELECT model,max_active FROM limits')]
                signals['pauses'] = [tuple(r) for r in connection.execute('SELECT model,reason FROM paused_models')]
                signals['event_seq'] = connection.execute('SELECT COALESCE(MAX(seq),0) FROM scheduler_events').fetchone()[0]
        if any(r['status'] == 'QUEUED' for r in rows):
            signals['resource_retry_epoch'] = int(time.monotonic() // 10)
        return json.dumps({'signals': signals,'tasks': [(r['id'], r['status'], r.get('attempt_id'),
                                     r.get('integrated_commit')) for r in rows],
                           'gates': gates}, sort_keys=True, default=str)

    def run(self, jobs=0, integrate=False, watch=False):
        self.singleton_path.parent.mkdir(parents=True, exist_ok=True)
        with self.singleton_path.open('a') as handle:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as exc:
                raise RuntimeError('a supervisor for this project is already active') from exc
            return self._run(jobs, integrate, watch)

    def _run(self, jobs=0, integrate=False, watch=False):
        """Watch is explicit user-run software, not a hidden cross-chat callback."""
        slots = int(self.controller.cfg.get('verifier_slots', 2))
        if slots < 1:
            raise ValueError('verifier_slots must be positive')
        previous = None
        with concurrent.futures.ThreadPoolExecutor(max_workers=slots) as pool:
            self.pool = pool
            try:
                while not self.controller.stop.is_set():
                    self.tick()
                    signature = self._dispatch_signature()
                    if signature != previous:
                        self.controller.run(jobs=jobs, integrate=integrate, poll_hook=self.tick)
                        previous = self._dispatch_signature()
                    if not watch:
                        while self.pending and not self.controller.stop.is_set():
                            self.controller.stop.wait(0.1)
                            self.tick()
                        break
                    self.controller.stop.wait(1.0)
            finally:
                self.pool = None
        return self.store.list_tasks(self.project)
