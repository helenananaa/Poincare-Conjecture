"""Isolated tests for the research adoption bridge.

These tests use temporary SQLite/batch/Git directories.  They never launch a
model, invoke Lean, access a network, kill a process, or modify the scheduler
files outside the temporary fixtures.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import Mock

sys.path.insert(0, str(Path(__file__).resolve().parent))

from research_queue import ResearchQueue
from state import Store


class GateStore(Store):
    def __init__(self, db_path: Path, project: str, config: dict):
        super().__init__(db_path)
        self.init_project(project, config)
        self.gates: dict[str, dict] = {}

    def record_acceptance_gate(self, gate_id: str, gate: dict) -> None:
        prior = self.gates.get(gate_id)
        if prior is not None and prior != gate:
            raise ValueError("acceptance gate is frozen")
        self.gates[gate_id] = dict(gate)


class ResearchQueueTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.package = self.repo / "Package"
        self.package.mkdir()
        self.store = GateStore(
            self.root / "control.sqlite3",
            "project",
            {
                "repo": str(self.repo),
                "package_dir": "Package",
                "integration_branch": "integration",
                "lean_bin": "/not-used",
                "lean_path": str(self.root / "baseline"),
            },
        )
        self.batch = self.root / "batch"
        self.work = self.batch / "worker"
        self.work.mkdir(parents=True)
        (self.work / "Main.lean").write_text("theorem Main.ok : True := by trivial\n", encoding="utf-8")
        (self.work / "REPORT.md").write_text("review report\n", encoding="utf-8")
        (self.work / "FINAL.md").write_text("final report\n", encoding="utf-8")
        (self.batch / "assigned.json").write_text(json.dumps({"files": ["Main.lean"]}), encoding="utf-8")
        self._write_tasks()
        self.live = False
        self.detector_calls = 0

    def tearDown(self) -> None:
        self.temp.cleanup()

    def _write_tasks(self, **overrides: object) -> None:
        task = {
            "name": "research-one",
            "cwd": str(self.work),
            "model": "gpt-5.6-luna",
            "effort": "high",
            **overrides,
        }
        (self.batch / "tasks.json").write_text(json.dumps([task]), encoding="utf-8")

    def _detector(self, job: dict) -> dict:
        self.detector_calls += 1
        return {"live": self.live, "identity_valid": True, "descendants_stopped": not self.live}

    def _queue(self, verifier=None) -> ResearchQueue:
        return ResearchQueue(
            self.store,
            self.root / "state",
            process_detector=self._detector,
            verifier=verifier,
        )

    def _finish(self, exit_code: int = 0) -> None:
        (self.work / "process-result.json").write_text(
            json.dumps({"exit_code": exit_code, "started_at": 1, "finished_at": 2}), encoding="utf-8"
        )
        self.live = False

    def test_import_is_idempotent_and_does_not_launch(self) -> None:
        queue = self._queue()
        first = queue.import_batch("project", self.batch)
        second = queue.import_batch("project", self.batch)
        self.assertEqual([row["job_id"] for row in first], [row["job_id"] for row in second])
        self.assertEqual(len(queue.list_jobs("project")), 1)
        self.assertEqual(queue.list_jobs("project")[0]["model"], "luna")

    def test_invalid_effort_and_non_luna_model_are_rejected(self) -> None:
        queue = self._queue()
        self._write_tasks(effort="unbounded")
        with self.assertRaises(ValueError):
            queue.import_batch("project", self.batch)
        self._write_tasks(model="gpt-5.5")
        with self.assertRaises(ValueError):
            queue.import_batch("project", self.batch)

    def test_finished_success_is_review_not_solved(self) -> None:
        queue = self._queue()
        job = queue.import_batch("project", self.batch)[0]
        self._finish(0)
        report = queue.poll("project")
        row = report["jobs"][0]
        self.assertEqual(row["job_id"], job["job_id"])
        self.assertEqual(row["status"], "REVIEW_REQUIRED")
        self.assertNotEqual(row["status"], "INTEGRATED")
        self.assertTrue(row["manifest"]["frozen"])
        self.assertEqual(row["manifest"]["manifest_sha256"], row["manifest"]["manifest_sha256"])

    def test_nonzero_and_missing_completion_preserve_reviewable_candidate(self) -> None:
        queue = self._queue()
        queue.import_batch("project", self.batch)
        queue.poll("project")
        self.assertEqual(queue.list_jobs("project")[0]["status"], "INTERRUPTED")

        # A second batch has a confirmed nonzero completion and is retained as
        # FAILED, never silently converted into success.
        batch2 = self.root / "batch-two"
        worker2 = batch2 / "worker"
        worker2.mkdir(parents=True)
        (worker2 / "Two.lean").write_text("theorem Two.ok : True := by trivial\n", encoding="utf-8")
        (batch2 / "assigned.json").write_text(json.dumps({"files": ["Two.lean"]}), encoding="utf-8")
        (batch2 / "tasks.json").write_text(json.dumps([{"name": "two", "cwd": str(worker2), "model": "luna", "effort": "max"}]), encoding="utf-8")
        (worker2 / "process-result.json").write_text(json.dumps({"exit_code": 3, "finished_unix": 2}), encoding="utf-8")
        queue.import_batch("project", batch2)
        self.assertEqual([row["status"] for row in queue.poll("project")["jobs"] if row["task_id"] == "two"], ["FAILED"])

    def test_worker_mutation_after_capture_cannot_change_frozen_copy(self) -> None:
        queue = self._queue(verifier=lambda *_: {"compile_passed": True})
        job = queue.import_batch("project", self.batch)[0]
        self._finish(0)
        captured = queue.poll("project")["jobs"][0]
        before = Path(captured["manifest"]["snapshot_root"]) / "Main.lean"
        original = before.read_bytes()
        (self.work / "Main.lean").write_text("theorem Main.ok : False := by sorry\n", encoding="utf-8")
        checked = queue.verify(job["job_id"], [{"path": "Main.lean", "name": "Main.ok"}])
        self.assertTrue(checked["verification"]["compile_passed"])
        self.assertEqual(before.read_bytes(), original)

    def test_symlink_and_escape_are_rejected(self) -> None:
        outside = self.root / "outside.lean"
        outside.write_text("theorem Outside.ok : True := by trivial\n", encoding="utf-8")
        (self.batch / "assigned.json").write_text(json.dumps({"files": ["../outside.lean"]}), encoding="utf-8")
        with self.assertRaises(ValueError):
            self._queue().import_batch("project", self.batch)
        (self.batch / "assigned.json").write_text(json.dumps({"files": ["link.lean"]}), encoding="utf-8")
        (self.work / "link.lean").symlink_to(outside)
        with self.assertRaises(ValueError):
            self._queue().import_batch("project", self.batch)

    def test_exact_manifest_and_empty_targets_are_rejected(self) -> None:
        queue = self._queue(verifier=lambda *_: {"compile_passed": True})
        job = queue.import_batch("project", self.batch)[0]
        self._finish()
        queue.poll("project")
        with self.assertRaises(ValueError):
            queue.verify(job["job_id"], [])
        with self.assertRaises(ValueError):
            queue.approve(job["job_id"], "0" * 64, "reviewer", "signature and definition reviewed")

    def test_compiler_failure_does_not_approve_and_notes_must_acknowledge_changes(self) -> None:
        queue = self._queue(verifier=lambda *_: {"compile_passed": False, "error": "compiler failed"})
        job = queue.import_batch("project", self.batch)[0]
        self._finish()
        queue.poll("project")
        failed = queue.verify(job["job_id"], [{"path": "Main.lean", "name": "Main.ok"}])
        self.assertEqual(failed["status"], "VALIDATION_FAILED")
        with self.assertRaises(ValueError):
            queue.approve(job["job_id"], failed["manifest"]["manifest_sha256"], "reviewer", "looks good")

    def test_concurrent_poll_has_one_frozen_manifest(self) -> None:
        queue = self._queue()
        queue.import_batch("project", self.batch)
        self._finish()
        results: list[dict] = []
        errors: list[BaseException] = []

        def poll() -> None:
            try:
                results.append(queue.poll("project"))
            except BaseException as exc:  # pragma: no cover - diagnostic only
                errors.append(exc)

        threads = [threading.Thread(target=poll) for _ in range(2)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(10)
        self.assertFalse(errors)
        rows = queue.list_jobs("project")
        self.assertEqual(len(rows), 1)
        self.assertTrue(rows[0]["manifest"]["frozen"])

    def _git(self, *args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=self.repo, text=True).strip()

    def _prepare_commit(self) -> str:
        target = self.package / "Main.lean"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes((self.work / "Main.lean").read_bytes())
        self._git("init", "-q")
        self._git("config", "user.name", "Research Test")
        self._git("config", "user.email", "research@example.invalid")
        self._git("checkout", "-q", "-b", "integration")
        self._git("add", ".")
        subprocess.check_call(["git", "commit", "-q", "-m", "candidate"], cwd=self.repo)
        return self._git("rev-parse", "HEAD")

    @staticmethod
    def _audited_verifier(job, targets, workspace):
        return {"compile_passed": True, "transitive_axioms_checked": True,
                "target_axioms": {t["name"]: ["propext", "Classical.choice", "Quot.sound"] for t in targets},
                "compiled_sources": [x["path"] for x in job["manifest"]["files"] if x["kind"] == "source"],
                "local_proof_holes": []}

    def test_compile_only_evidence_cannot_be_approved(self):
        queue = self._queue(verifier=lambda *_: {"compile_passed": True})
        job = queue.import_batch("project", self.batch)[0]
        self._finish(); queue.poll("project")
        row = queue.verify(job["job_id"], [{"path": "Main.lean", "name": "Main.ok"}])
        with self.assertRaisesRegex(ValueError, "transitive"):
            queue.approve(job["job_id"], row["manifest"]["manifest_sha256"], "reviewer", "signature and definition checked")

    def test_max_supported_but_lower_than_high_rejected(self):
        for effort in ("minimal", "low", "medium"):
            self._write_tasks(effort=effort)
            with self.assertRaises(ValueError): self._queue().import_batch("project", self.batch)
        self._write_tasks(effort="max")
        self.assertEqual(self._queue().import_batch("project", self.batch)[0]["effort"], "max")

    def test_reviewed_matching_commit_releases_gate(self) -> None:
        queue = self._queue(verifier=self._audited_verifier)
        job = queue.import_batch("project", self.batch)[0]
        self._finish()
        queue.poll("project")
        verified = queue.verify(job["job_id"], [{"path": "Main.lean", "name": "Main.ok"}])
        notes = "Semantic review acknowledges signature/interface and definition/new-definition changes: none."
        approved = queue.approve(job["job_id"], verified["manifest"]["manifest_sha256"], "Ada", notes)
        self.assertEqual(approved["status"], "APPROVED")
        commit = self._prepare_commit()
        integrated = queue.record_integrated(job["job_id"], commit)
        self.assertEqual(integrated["status"], "INTEGRATED")
        self.assertIn("research:" + job["job_id"], self.store.gates)
        self.assertEqual(self.store.gates["research:" + job["job_id"]]["commit"], commit)
        self.assertEqual(queue.record_integrated(job["job_id"], commit)["status"], "INTEGRATED")

    def test_unknown_nonancestor_and_mismatched_commits_cannot_gate(self) -> None:
        queue = self._queue(verifier=self._audited_verifier)
        job = queue.import_batch("project", self.batch)[0]
        self._finish()
        queue.poll("project")
        verified = queue.verify(job["job_id"], [{"path": "Main.lean", "name": "Main.ok"}])
        notes = "Semantic review acknowledges signature/interface and definition/new-definition changes: none."
        queue.approve(job["job_id"], verified["manifest"]["manifest_sha256"], "Ada", notes)
        with self.assertRaises(ValueError):
            queue.record_integrated(job["job_id"], "deadbeef")
        commit = self._prepare_commit()
        (self.package / "Main.lean").write_text("theorem Main.ok : False := by sorry\n", encoding="utf-8")
        self._git("add", ".")
        subprocess.check_call(["git", "commit", "-q", "-m", "mismatch"], cwd=self.repo)
        mismatch = self._git("rev-parse", "HEAD")
        with self.assertRaises(ValueError):
            queue.record_integrated(job["job_id"], mismatch)
        self.assertNotIn("research:" + job["job_id"], self.store.gates)


if __name__ == "__main__":
    unittest.main()
