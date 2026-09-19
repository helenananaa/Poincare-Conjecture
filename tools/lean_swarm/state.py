"""Persistent state for a small, multi-process Lean proof-agent scheduler.

The scheduler deliberately does not reclaim leases based on wall-clock time.
An attempt remains RUNNING until its owner (or an explicitly supervising
caller) establishes that the worker has stopped and calls :meth:`Store.finish`.
"""

from __future__ import annotations

import contextlib
import json
import math
import re
import sqlite3
import time
import uuid
from pathlib import Path
from typing import Any, Iterator


_TASK_ID = re.compile(r"[A-Za-z0-9_-]+\Z")
_MODELS = frozenset(("luna", "grok"))
_TASK_STATES = frozenset(
    ("QUEUED", "RUNNING", "VERIFIED", "FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED", "INTEGRATED")
)
_ATTEMPT_STATES = frozenset(("RUNNING", "VERIFIED", "FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED"))
_FINISH_STATES = frozenset(("VERIFIED", "FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED"))


def _json(value: Any, what: str) -> str:
    """Serialize JSON and turn low-level errors into useful API errors."""

    try:
        return json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False
        )
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{what} must be JSON serializable") from exc


def _object(text: str, what: str) -> dict[str, Any]:
    try:
        value = json.loads(text)
    except json.JSONDecodeError as exc:  # pragma: no cover - only corrupt on-disk state
        raise ValueError(f"stored {what} is not valid JSON") from exc
    if not isinstance(value, dict):  # pragma: no cover - protected by the API
        raise ValueError(f"stored {what} is not a JSON object")
    return value


class Store:
    """A SQLite-backed scheduler store.

    Every public operation opens and closes its own SQLite connection.  This
    makes a Store safe to use from different threads and processes, provided
    they point at the same database path.
    """

    def __init__(self, db_path: str | Path):
        self.db_path = str(db_path)
        self._initialize_schema()

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.db_path, timeout=30.0, isolation_level=None)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA busy_timeout = 30000")
        connection.execute("PRAGMA foreign_keys = ON")
        connection.execute("PRAGMA journal_mode = WAL")
        return connection

    @contextlib.contextmanager
    def _connection(self) -> Iterator[sqlite3.Connection]:
        connection = self._connect()
        try:
            yield connection
        finally:
            connection.close()

    @contextlib.contextmanager
    def _transaction(self) -> Iterator[sqlite3.Connection]:
        with self._connection() as connection:
            connection.execute("BEGIN IMMEDIATE")
            try:
                yield connection
            except BaseException:
                connection.rollback()
                raise
            else:
                connection.commit()

    def _initialize_schema(self) -> None:
        with self._transaction() as connection:
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS projects (
                    project_id TEXT PRIMARY KEY,
                    config_json TEXT NOT NULL
                )
                """
            )
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS tasks (
                    project_id TEXT NOT NULL,
                    task_id TEXT NOT NULL,
                    model TEXT NOT NULL CHECK (model IN ('luna', 'grok')),
                    payload_json TEXT NOT NULL,
                    status TEXT NOT NULL CHECK (
                        status IN ('QUEUED', 'RUNNING', 'VERIFIED', 'FAILED',
                                   'TIMEOUT', 'QUOTA', 'INTERRUPTED', 'INTEGRATED')
                    ),
                    integrated_commit TEXT,
                    PRIMARY KEY (project_id, task_id),
                    FOREIGN KEY (project_id) REFERENCES projects(project_id)
                )
                """
            )
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS attempts (
                    id TEXT PRIMARY KEY,
                    project_id TEXT NOT NULL,
                    task_id TEXT NOT NULL,
                    status TEXT NOT NULL CHECK (
                        status IN ('RUNNING', 'VERIFIED', 'FAILED', 'TIMEOUT',
                                   'QUOTA', 'INTERRUPTED')
                    ),
                    owner TEXT NOT NULL,
                    started_at REAL NOT NULL,
                    heartbeat REAL NOT NULL,
                    metadata_json TEXT NOT NULL DEFAULT '{}',
                    result_json TEXT NOT NULL DEFAULT '{}',
                    FOREIGN KEY (project_id, task_id)
                        REFERENCES tasks(project_id, task_id)
                )
                """
            )
            connection.execute(
                """
                CREATE UNIQUE INDEX IF NOT EXISTS one_running_attempt_per_task
                ON attempts(project_id, task_id) WHERE status = 'RUNNING'
                """
            )
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS limits (
                    model TEXT PRIMARY KEY CHECK (model IN ('luna', 'grok')),
                    max_active INTEGER NOT NULL
                )
                """
            )
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS paused_models (
                    model TEXT PRIMARY KEY CHECK (model IN ('luna', 'grok')),
                    reason TEXT NOT NULL
                )
                """
            )
            connection.execute("INSERT OR IGNORE INTO limits(model, max_active) VALUES ('luna', 4)")
            connection.execute("INSERT OR IGNORE INTO limits(model, max_active) VALUES ('grok', 4)")

    @staticmethod
    def _project_id(project_id: str) -> str:
        if not isinstance(project_id, str) or not project_id:
            raise ValueError("project_id must be a non-empty string")
        return project_id

    @staticmethod
    def _model(model: str) -> str:
        if not isinstance(model, str) or model not in _MODELS:
            raise ValueError("model must be 'luna' or 'grok'")
        return model

    @staticmethod
    def _task(task: dict[str, Any]) -> dict[str, Any]:
        if not isinstance(task, dict):
            raise ValueError("each task must be a dict")
        required = ("id", "model", "depends_on", "source", "target_name", "target_path")
        missing = [key for key in required if key not in task]
        if missing:
            raise ValueError(f"task is missing required field(s): {', '.join(missing)}")
        task_id = task["id"]
        if not isinstance(task_id, str) or not _TASK_ID.fullmatch(task_id):
            raise ValueError("task id must match [A-Za-z0-9_-]+")
        Store._model(task["model"])
        dependencies = task["depends_on"]
        if not isinstance(dependencies, list) or any(
            not isinstance(dependency, str) for dependency in dependencies
        ):
            raise ValueError(f"task {task_id!r} depends_on must be a list of strings")
        for field in ("source", "target_name", "target_path"):
            if not isinstance(task[field], str):
                raise ValueError(f"task {task_id!r} {field} must be a string")
        if "hint" in task and not isinstance(task["hint"], str):
            raise ValueError(f"task {task_id!r} hint must be a string")
        if "timeout_seconds" in task:
            timeout = task["timeout_seconds"]
            if isinstance(timeout, bool) or not isinstance(timeout, (int, float)):
                raise ValueError(f"task {task_id!r} timeout_seconds must be a positive number")
            if not math.isfinite(float(timeout)) or timeout <= 0:
                raise ValueError(f"task {task_id!r} timeout_seconds must be a positive number")
        _json(task, f"task {task_id!r}")
        return dict(task)

    @staticmethod
    def _owner(owner: str) -> str:
        if not isinstance(owner, str) or not owner:
            raise ValueError("owner must be a non-empty string")
        return owner

    def init_project(self, project_id: str, config: dict[str, Any]) -> None:
        """Create a project, or verify the configuration of an existing one."""

        project_id = self._project_id(project_id)
        if not isinstance(config, dict):
            raise ValueError("config must be a dict")
        encoded = _json(config, "config")
        with self._transaction() as connection:
            row = connection.execute(
                "SELECT config_json FROM projects WHERE project_id = ?", (project_id,)
            ).fetchone()
            if row is None:
                connection.execute(
                    "INSERT INTO projects(project_id, config_json) VALUES (?, ?)",
                    (project_id, encoded),
                )
            elif row["config_json"] != encoded:
                raise ValueError(f"project {project_id!r} already exists with different config")

    def get_project(self, project_id: str) -> dict[str, Any]:
        """Return a project's configuration."""

        project_id = self._project_id(project_id)
        with self._connection() as connection:
            row = connection.execute(
                "SELECT config_json FROM projects WHERE project_id = ?", (project_id,)
            ).fetchone()
        if row is None:
            raise KeyError(f"unknown project {project_id!r}")
        return _object(row["config_json"], "project configuration")

    @staticmethod
    def _limit_value(model: str, value: int) -> int:
        Store._model(model)
        maximum = 8 if model == "luna" else 64
        if isinstance(value, bool) or not isinstance(value, int) or not 1 <= value <= maximum:
            raise ValueError(f"{model} limit must be an integer from 1 through {maximum}")
        return value

    def set_limits(self, luna: int = 4, grok: int = 4) -> None:
        """Set persistent global concurrency limits for both models."""

        luna = self._limit_value("luna", luna)
        grok = self._limit_value("grok", grok)
        requested = {"luna": luna, "grok": grok}
        with self._transaction() as connection:
            current = {
                row["model"]: row["max_active"]
                for row in connection.execute("SELECT model, max_active FROM limits")
            }
            if current != requested:
                running = connection.execute(
                    "SELECT COUNT(*) FROM attempts WHERE status = 'RUNNING'"
                ).fetchone()[0]
                if running:
                    raise ValueError("cannot change limits while attempts are RUNNING")
            connection.executemany(
                "UPDATE limits SET max_active = ? WHERE model = ?",
                ((luna, "luna"), (grok, "grok")),
            )

    def add_tasks(self, project_id: str, tasks: list[dict[str, Any]]) -> None:
        """Atomically add validated tasks, preserving frozen task definitions."""

        project_id = self._project_id(project_id)
        if not isinstance(tasks, list):
            raise ValueError("tasks must be a list")
        validated = [self._task(task) for task in tasks]
        ids = [task["id"] for task in validated]
        if len(ids) != len(set(ids)):
            raise ValueError("tasks contains duplicate task ids")
        with self._transaction() as connection:
            if connection.execute(
                "SELECT 1 FROM projects WHERE project_id = ?", (project_id,)
            ).fetchone() is None:
                raise KeyError(f"unknown project {project_id!r}")

            existing_rows = connection.execute(
                "SELECT task_id, model, payload_json FROM tasks WHERE project_id = ?", (project_id,)
            ).fetchall()
            existing = {row["task_id"]: row for row in existing_rows}
            all_ids = set(existing)
            all_ids.update(ids)
            for task in validated:
                for dependency in task["depends_on"]:
                    if dependency not in all_ids:
                        raise ValueError(
                            f"task {task['id']!r} depends on missing task {dependency!r}"
                        )

            graph: dict[str, list[str]] = {
                row["task_id"]: _object(row["payload_json"], "task payload")["depends_on"]
                for row in existing_rows
            }
            graph.update({task["id"]: task["depends_on"] for task in validated})
            visiting: set[str] = set()
            visited: set[str] = set()

            def visit(task_id: str) -> None:
                if task_id in visiting:
                    raise ValueError(f"dependency cycle involving task {task_id!r}")
                if task_id in visited:
                    return
                visiting.add(task_id)
                for dependency in graph.get(task_id, []):
                    visit(dependency)
                visiting.remove(task_id)
                visited.add(task_id)

            for task_id in graph:
                visit(task_id)

            for task in validated:
                row = existing.get(task["id"])
                payload = _json(task, f"task {task['id']!r}")
                if row is not None:
                    if row["model"] != task["model"] or row["payload_json"] != payload:
                        raise ValueError(f"task {task['id']!r} is frozen and cannot be changed")
                    continue
                connection.execute(
                    """
                    INSERT INTO tasks(project_id, task_id, model, payload_json, status)
                    VALUES (?, ?, ?, ?, 'QUEUED')
                    """,
                    (project_id, task["id"], task["model"], payload),
                )

    def claim(self, project_id: str, owner: str) -> dict[str, Any] | None:
        """Atomically claim one eligible task, or return ``None``."""

        project_id = self._project_id(project_id)
        owner = self._owner(owner)
        with self._transaction() as connection:
            if connection.execute(
                "SELECT 1 FROM projects WHERE project_id = ?", (project_id,)
            ).fetchone() is None:
                raise KeyError(f"unknown project {project_id!r}")
            limits = {
                row["model"]: row["max_active"]
                for row in connection.execute("SELECT model, max_active FROM limits")
            }
            paused = {
                row["model"]
                for row in connection.execute("SELECT model FROM paused_models")
            }
            active = {
                row["model"]: row["count"]
                for row in connection.execute(
                    """
                    SELECT t.model, COUNT(*) AS count
                    FROM attempts AS a
                    JOIN tasks AS t ON t.project_id = a.project_id AND t.task_id = a.task_id
                    WHERE a.status = 'RUNNING'
                    GROUP BY t.model
                    """
                )
            }
            candidates = connection.execute(
                """
                SELECT task_id, model, payload_json
                FROM tasks
                WHERE project_id = ? AND status = 'QUEUED'
                ORDER BY task_id
                """,
                (project_id,),
            ).fetchall()
            selected: sqlite3.Row | None = None
            task_payload: dict[str, Any] | None = None
            for candidate in candidates:
                model = candidate["model"]
                if model in paused or active.get(model, 0) >= limits[model]:
                    continue
                payload = _object(candidate["payload_json"], "task payload")
                dependency_ids = payload.get("depends_on", [])
                dependencies_ready = True
                for dependency in dependency_ids:
                    dependency_row = connection.execute(
                        """
                        SELECT status FROM tasks
                        WHERE project_id = ? AND task_id = ?
                        """,
                        (project_id, dependency),
                    ).fetchone()
                    if dependency_row is None or dependency_row["status"] != "INTEGRATED":
                        dependencies_ready = False
                        break
                if not dependencies_ready:
                    continue
                selected = candidate
                task_payload = payload
                break
            if selected is None or task_payload is None:
                return None

            attempt_id = str(uuid.uuid4())
            now = time.time()
            connection.execute(
                """
                INSERT INTO attempts(
                    id, project_id, task_id, status, owner, started_at, heartbeat,
                    metadata_json, result_json
                ) VALUES (?, ?, ?, 'RUNNING', ?, ?, ?, '{}', '{}')
                """,
                (attempt_id, project_id, selected["task_id"], owner, now, now),
            )
            updated = connection.execute(
                """
                UPDATE tasks SET status = 'RUNNING'
                WHERE project_id = ? AND task_id = ? AND status = 'QUEUED'
                """,
                (project_id, selected["task_id"]),
            ).rowcount
            if updated != 1:  # pragma: no cover - BEGIN IMMEDIATE prevents this race
                raise RuntimeError("task changed while it was being claimed")
            active[selected["model"]] = active.get(selected["model"], 0) + 1
            return {
                "project_id": project_id,
                "task_id": selected["task_id"],
                "attempt_id": attempt_id,
                "task": task_payload,
            }

    @staticmethod
    def _attempt_id(attempt_id: str) -> str:
        if not isinstance(attempt_id, str) or not attempt_id:
            raise ValueError("attempt_id must be a non-empty string")
        return attempt_id

    def record_runtime(self, attempt_id: str, metadata: dict[str, Any]) -> None:
        """Replace an attempt's arbitrary runtime metadata without changing its task."""

        attempt_id = self._attempt_id(attempt_id)
        if not isinstance(metadata, dict):
            raise ValueError("metadata must be a dict")
        encoded = _json(metadata, "metadata")
        with self._transaction() as connection:
            updated = connection.execute(
                "UPDATE attempts SET metadata_json = ? WHERE id = ?", (encoded, attempt_id)
            ).rowcount
            if updated != 1:
                raise KeyError(f"unknown attempt {attempt_id!r}")

    def heartbeat(self, attempt_id: str) -> None:
        """Refresh a heartbeat only for an attempt that is still RUNNING."""

        attempt_id = self._attempt_id(attempt_id)
        with self._transaction() as connection:
            row = connection.execute("SELECT status FROM attempts WHERE id = ?", (attempt_id,)).fetchone()
            if row is None:
                raise KeyError(f"unknown attempt {attempt_id!r}")
            if row["status"] != "RUNNING":
                raise ValueError(f"attempt {attempt_id!r} is not RUNNING")
            connection.execute(
                "UPDATE attempts SET heartbeat = ? WHERE id = ?", (time.time(), attempt_id)
            )

    def finish(self, attempt_id: str, status: str, result: dict[str, Any]) -> None:
        """Finish a RUNNING attempt after its worker process is contained and stopped."""

        attempt_id = self._attempt_id(attempt_id)
        if status not in _FINISH_STATES:
            raise ValueError("invalid finish status")
        if not isinstance(result, dict):
            raise ValueError("result must be a dict")
        encoded = _json(result, "result")
        with self._transaction() as connection:
            row = connection.execute(
                "SELECT project_id, task_id, status FROM attempts WHERE id = ?", (attempt_id,)
            ).fetchone()
            if row is None:
                raise KeyError(f"unknown attempt {attempt_id!r}")
            if row["status"] != "RUNNING":
                raise ValueError(f"attempt {attempt_id!r} is already {row['status']}")
            task = connection.execute(
                "SELECT status FROM tasks WHERE project_id = ? AND task_id = ?",
                (row["project_id"], row["task_id"]),
            ).fetchone()
            if task is None or task["status"] != "RUNNING":
                raise ValueError("attempt's task is not RUNNING")
            connection.execute(
                "UPDATE attempts SET status = ?, result_json = ? WHERE id = ?",
                (status, encoded, attempt_id),
            )
            connection.execute(
                "UPDATE tasks SET status = ? WHERE project_id = ? AND task_id = ?",
                (status, row["project_id"], row["task_id"]),
            )

    def pause_model(self, model: str, reason: str) -> None:
        """Pause new claims for a model globally, retaining the reason."""

        self._model(model)
        if not isinstance(reason, str) or not reason:
            raise ValueError("reason must be a non-empty string")
        with self._transaction() as connection:
            connection.execute(
                """
                INSERT INTO paused_models(model, reason) VALUES (?, ?)
                ON CONFLICT(model) DO UPDATE SET reason = excluded.reason
                """,
                (model, reason),
            )

    def resume_model(self, model: str) -> None:
        """Allow new claims for a model globally."""

        self._model(model)
        with self._transaction() as connection:
            connection.execute("DELETE FROM paused_models WHERE model = ?", (model,))

    def list_tasks(self, project_id: str) -> list[dict[str, Any]]:
        """List task state and the id of the most recently created attempt."""

        project_id = self._project_id(project_id)
        with self._connection() as connection:
            rows = connection.execute(
                """
                SELECT t.task_id, t.status, t.model, t.payload_json, t.integrated_commit,
                       (SELECT a.id FROM attempts AS a
                        WHERE a.project_id = t.project_id AND a.task_id = t.task_id
                        ORDER BY a.started_at DESC, a.rowid DESC LIMIT 1) AS attempt_id
                FROM tasks AS t
                WHERE t.project_id = ?
                ORDER BY t.task_id
                """,
                (project_id,),
            ).fetchall()
        return [
            {
                "id": row["task_id"],
                "status": row["status"],
                "model": row["model"],
                "payload": _object(row["payload_json"], "task payload"),
                "integrated_commit": row["integrated_commit"],
                "attempt_id": row["attempt_id"],
            }
            for row in rows
        ]

    def list_attempts(self, project_id: str | None = None) -> list[dict[str, Any]]:
        """List attempts, optionally limited to one project."""

        if project_id is not None:
            project_id = self._project_id(project_id)
        with self._connection() as connection:
            if project_id is None:
                rows = connection.execute(
                    """
                    SELECT id, project_id, task_id, status, owner, started_at, heartbeat,
                           metadata_json, result_json
                    FROM attempts ORDER BY started_at, rowid
                    """
                ).fetchall()
            else:
                rows = connection.execute(
                    """
                    SELECT id, project_id, task_id, status, owner, started_at, heartbeat,
                           metadata_json, result_json
                    FROM attempts WHERE project_id = ? ORDER BY started_at, rowid
                    """,
                    (project_id,),
                ).fetchall()
        return [
            {
                "id": row["id"],
                "project_id": row["project_id"],
                "task_id": row["task_id"],
                "status": row["status"],
                "owner": row["owner"],
                "started_at": row["started_at"],
                "heartbeat": row["heartbeat"],
                "metadata": _object(row["metadata_json"], "attempt metadata"),
                "result": _object(row["result_json"], "attempt result"),
            }
            for row in rows
        ]

    def mark_integrated(self, project_id: str, task_id: str, commit: str) -> None:
        """Move a VERIFIED task to INTEGRATED and record its commit."""

        project_id = self._project_id(project_id)
        if not isinstance(task_id, str) or not _TASK_ID.fullmatch(task_id):
            raise ValueError("task id must match [A-Za-z0-9_-]+")
        if not isinstance(commit, str) or not commit:
            raise ValueError("commit must be a non-empty string")
        with self._transaction() as connection:
            row = connection.execute(
                "SELECT status FROM tasks WHERE project_id = ? AND task_id = ?",
                (project_id, task_id),
            ).fetchone()
            if row is None:
                raise KeyError(f"unknown task {task_id!r}")
            if row["status"] != "VERIFIED":
                raise ValueError(f"task {task_id!r} is not VERIFIED")
            connection.execute(
                """
                UPDATE tasks SET status = 'INTEGRATED', integrated_commit = ?
                WHERE project_id = ? AND task_id = ?
                """,
                (commit, project_id, task_id),
            )

    def retry(self, project_id: str, task_id: str) -> None:
        """Queue a terminally failed task again while retaining its attempts."""

        project_id = self._project_id(project_id)
        if not isinstance(task_id, str) or not _TASK_ID.fullmatch(task_id):
            raise ValueError("task id must match [A-Za-z0-9_-]+")
        with self._transaction() as connection:
            row = connection.execute(
                "SELECT status FROM tasks WHERE project_id = ? AND task_id = ?",
                (project_id, task_id),
            ).fetchone()
            if row is None:
                raise KeyError(f"unknown task {task_id!r}")
            if row["status"] not in ("FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED"):
                raise ValueError(f"task {task_id!r} cannot be retried from {row['status']}")
            connection.execute(
                """
                UPDATE tasks SET status = 'QUEUED', integrated_commit = NULL
                WHERE project_id = ? AND task_id = ?
                """,
                (project_id, task_id),
            )
