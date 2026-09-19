"""Unit tests for state.py."""

from __future__ import annotations

import multiprocessing
import tempfile
import unittest
from pathlib import Path

from state import Store


def _claim_worker(db_path: str, project_id: str, ready, result_queue) -> None:
    ready.wait()
    claim = Store(db_path).claim(project_id, f"worker-{multiprocessing.current_process().pid}")
    result_queue.put(None if claim is None else claim["attempt_id"])


def _task(task_id: str, model: str = "luna", depends_on: list[str] | None = None) -> dict:
    return {
        "id": task_id,
        "model": model,
        "depends_on": [] if depends_on is None else depends_on,
        "source": f"theorem {task_id} : True := by trivial",
        "target_name": task_id,
        "target_path": f"Main/{task_id}.lean",
    }


class StoreTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tempdir = tempfile.TemporaryDirectory()
        self.db = Path(self.tempdir.name) / "state.sqlite3"
        self.store = Store(self.db)
        self.store.init_project("p", {"root": "Main"})

    def tearDown(self) -> None:
        self.tempdir.cleanup()

    def test_project_and_restart_persistence(self) -> None:
        self.assertEqual(self.store.get_project("p"), {"root": "Main"})
        self.store.init_project("p", {"root": "Main"})
        with self.assertRaises(ValueError):
            self.store.init_project("p", {"root": "Other"})
        self.store.set_limits(luna=2, grok=3)
        restarted = Store(self.db)
        restarted.add_tasks("p", [_task("a")])
        self.assertEqual(restarted.list_tasks("p")[0]["id"], "a")

    def test_concurrent_global_cap_across_two_projects(self) -> None:
        self.store.init_project("q", {})
        self.store.set_limits(luna=2, grok=4)
        self.store.add_tasks("p", [_task(f"p{i}") for i in range(6)])
        self.store.add_tasks("q", [_task(f"q{i}") for i in range(6)])
        context = multiprocessing.get_context("spawn")
        ready = context.Event()
        result_queue = context.Queue()
        processes = [
            context.Process(
                target=_claim_worker,
                args=(str(self.db), "p" if index % 2 == 0 else "q", ready, result_queue),
            )
            for index in range(12)
        ]
        for process in processes:
            process.start()
        ready.set()
        results = [result_queue.get(timeout=30) for _ in processes]
        for process in processes:
            process.join(30)
            self.assertEqual(process.exitcode, 0)
        claimed = [attempt for attempt in results if attempt is not None]
        self.assertEqual(len(claimed), 2)
        self.assertEqual(len(set(claimed)), 2)
        self.assertEqual(sum(item["status"] == "RUNNING" for item in self.store.list_attempts()), 2)

    def test_dependencies_unlock_only_after_integration(self) -> None:
        self.store.add_tasks("p", [_task("a"), _task("b", depends_on=["a"])])
        first = self.store.claim("p", "owner-a")
        self.assertIsNotNone(first)
        self.store.finish(first["attempt_id"], "VERIFIED", {"ok": True})
        self.assertIsNone(self.store.claim("p", "owner-b"))
        self.store.mark_integrated("p", "a", "abc123")
        second = self.store.claim("p", "owner-b")
        self.assertEqual(second["task_id"], "b")

    def test_cycle_missing_dependency_and_atomic_rollback(self) -> None:
        with self.assertRaises(ValueError):
            self.store.add_tasks("p", [_task("a", depends_on=["missing"]), _task("b")])
        self.assertEqual(self.store.list_tasks("p"), [])
        with self.assertRaises(ValueError):
            self.store.add_tasks("p", [_task("a", depends_on=["b"]), _task("b", depends_on=["a"])])
        self.assertEqual(self.store.list_tasks("p"), [])

    def test_frozen_task_and_idempotent_readd(self) -> None:
        original = _task("a")
        self.store.add_tasks("p", [original])
        self.store.add_tasks("p", [dict(original)])
        changed = dict(original, source="theorem a : False := by sorry")
        with self.assertRaises(ValueError):
            self.store.add_tasks("p", [changed])
        self.assertEqual(len(self.store.list_tasks("p")), 1)

    def test_stale_heartbeat_is_not_reclaimed(self) -> None:
        self.store.add_tasks("p", [_task("a")])
        first = self.store.claim("p", "old-owner")
        self.assertIsNotNone(first)
        with self.store._connection() as connection:
            connection.execute(
                "UPDATE attempts SET heartbeat = heartbeat - 100000 WHERE id = ?",
                (first["attempt_id"],),
            )
        second = self.store.claim("p", "new-owner")
        self.assertIsNone(second)
        self.assertEqual(self.store.list_tasks("p")[0]["status"], "RUNNING")

    def test_pause_quota_retry_and_runtime(self) -> None:
        self.store.set_limits(luna=1, grok=4)
        self.store.add_tasks("p", [_task("a"), _task("b")])
        self.store.pause_model("luna", "provider quota")
        self.assertIsNone(self.store.claim("p", "owner"))
        self.store.resume_model("luna")
        first = self.store.claim("p", "owner")
        self.store.record_runtime(first["attempt_id"], {"unit": "u", "workspace": "/tmp/w"})
        self.assertEqual(self.store.list_attempts("p")[0]["metadata"]["unit"], "u")
        self.assertIsNone(self.store.claim("p", "another"))
        self.store.finish(first["attempt_id"], "QUOTA", {"error": "quota"})
        with self.assertRaises(ValueError):
            self.store.finish(first["attempt_id"], "FAILED", {})
        self.store.retry("p", "a")
        self.assertEqual(self.store.list_tasks("p")[0]["status"], "QUEUED")
        retried = self.store.claim("p", "owner-2")
        self.assertNotEqual(retried["attempt_id"], first["attempt_id"])

    def test_grok_unlimited_is_persistent_and_not_64(self) -> None:
        self.store.set_limits(luna=2, grok=0)
        self.store.add_tasks("p", [_task(f"g{i:03}", "grok") for i in range(70)])
        restarted = Store(self.db)
        claims = [restarted.claim("p", "owner") for _ in range(70)]
        self.assertTrue(all(claims))
        self.assertEqual(len({c["attempt_id"] for c in claims}), 70)
        self.assertIsNone(restarted.claim("p", "owner"))

    def test_grok_unlimited_still_obeys_pause_and_dependencies(self) -> None:
        self.store.set_limits(luna=1, grok=0)
        self.store.add_tasks("p", [_task("a", "grok"), _task("b", "grok", ["a"])])
        self.store.pause_model("grok", "subscription quota")
        self.assertIsNone(self.store.claim("p", "owner"))
        self.store.resume_model("grok")
        c = self.store.claim("p", "owner")
        self.assertEqual(c["task_id"], "a")
        self.assertIsNone(self.store.claim("p", "owner"))
        self.store.finish(c["attempt_id"], "VERIFIED", {})
        self.assertIsNone(self.store.claim("p", "owner"))
        self.store.mark_integrated("p", "a", "base")
        self.assertEqual(self.store.claim("p", "owner")["task_id"], "b")

    def test_grok_default_and_luna_guard(self) -> None:
        task = _task("implicit")
        del task["model"]
        self.store.add_tasks("p", [task])
        self.assertEqual(self.store.list_tasks("p")[0]["model"], "grok")
        for invalid in (0, 9, True, -1):
            with self.assertRaises(ValueError):
                self.store.set_limits(luna=invalid, grok=0)
        with self.assertRaises(ValueError):
            self.store.set_limits(luna=4, grok=-1)
        self.store.set_limits(luna=8, grok=0)

    def test_invalid_transitions(self) -> None:
        self.store.add_tasks("p", [_task("a")])
        with self.assertRaises(ValueError):
            self.store.mark_integrated("p", "a", "commit")
        with self.assertRaises(ValueError):
            self.store.retry("p", "a")
        attempt = self.store.claim("p", "owner")
        with self.assertRaises(ValueError):
            self.store.finish(attempt["attempt_id"], "INTEGRATED", {})


if __name__ == "__main__":
    unittest.main()
