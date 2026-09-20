"""Persistent state for the multi-process Lean proof-agent scheduler.

The store deliberately does not reclaim leases based on wall-clock time.  An
attempt remains RUNNING until its owner (or an explicitly supervising caller)
establishes that the worker has stopped and calls :meth:`Store.finish`.
"""

from __future__ import annotations

import contextlib
import json
import math
import posixpath
import re
import sqlite3
import time
import uuid
from pathlib import Path
from typing import Any, Iterator

try:  # The test runner imports modules directly from tools/lean_swarm.
    from policy import LUNA_MODEL, SQLITE_MAX_INTEGER, resolve_effort
except ImportError:  # pragma: no cover - also supports package imports.
    from .policy import LUNA_MODEL, SQLITE_MAX_INTEGER, resolve_effort


_TASK_ID = re.compile(r"[A-Za-z0-9_-]+\Z")
_MODELS = frozenset(("luna", "grok"))
_TASK_STATES = frozenset(
    ("QUEUED", "RUNNING", "VERIFIED", "FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED", "INTEGRATED")
)
_ATTEMPT_STATES = frozenset(("RUNNING", "VERIFIED", "FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED"))
_FINISH_STATES = frozenset(("VERIFIED", "FAILED", "TIMEOUT", "QUOTA", "INTERRUPTED"))
_MANIFEST_SHA256 = re.compile(r"[0-9a-fA-F]{64}\Z")


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


def _relative_path(value: Any, what: str) -> str:
    """Validate a scheduler path without allowing parent traversal."""

    if not isinstance(value, str) or not value:
        raise ValueError(f"{what} must be a non-empty relative path")
    normalized_separators = value.replace("\\", "/")
    if normalized_separators.startswith("/") or re.match(r"^[A-Za-z]:", normalized_separators):
        raise ValueError(f"{what} must be relative")
    if any(part == ".." for part in normalized_separators.split("/")):
        raise ValueError(f"{what} must not contain '..'")
    normalized = posixpath.normpath(normalized_separators)
    if normalized in ("", ".", "..") or normalized.startswith("../"):
        raise ValueError(f"{what} must be a non-empty relative path")
    return normalized


def _path_overlap(left: str, right: str) -> bool:
    return left == right or left.startswith(right + "/") or right.startswith(left + "/")


def _project_identity(project_id: str, config: dict[str, Any]) -> tuple[str, str] | None:
    """Return the resolved repo/package pair used for output admission."""

    repo = config.get("repo")
    if not isinstance(repo, str) or not repo:
        return None
    repo_path = Path(repo).expanduser().resolve()
    package = config.get("package_dir", config.get("package"))
    if package is None or package == "":
        package_path = repo_path
    elif not isinstance(package, str):
        return None
    else:
        package_path = (Path(package).expanduser() if Path(package).is_absolute() else repo_path / package).resolve()
    return str(repo_path), str(package_path)


def _task_paths(payload: dict[str, Any]) -> list[str]:
    values = payload["write_paths"] if "write_paths" in payload else [payload["target_path"]]
    return [_relative_path(value, "write_paths entry") for value in values]


def _resource_lock_entries(payload: dict[str, Any]) -> list[tuple[str, str]]:
    entries: list[tuple[str, str]] = []
    for lock in payload.get("resource_locks", []):
        if isinstance(lock, str):
            entries.append(("project", lock))
            continue
        name = lock.get("name", lock.get("id", lock.get("lock")))
        entries.append((lock.get("scope", "project"), name))
    return entries


def _effective_estimate(payload: dict[str, Any]) -> float:
    value = payload.get("estimated_seconds", payload.get("timeout_seconds", 420))
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        return 420.0
    try:
        numeric = float(value)
    except (OverflowError, ValueError):
        return 420.0
    if not math.isfinite(numeric) or value <= 0:
        return 420.0
    return numeric


def _validate_positive_finite(value: Any, what: str) -> None:
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{what} must be a positive number")
    try:
        numeric = float(value)
    except (OverflowError, ValueError) as exc:
        raise ValueError(f"{what} must be a positive number") from exc
    if not math.isfinite(numeric) or value <= 0:
        raise ValueError(f"{what} must be a positive number")


class Store:
    """A SQLite-backed scheduler store."""

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
            # INSERT OR IGNORE intentionally preserves configured values in an
            # existing database.  Only an explicit set_limits call changes them.
            connection.execute("INSERT OR IGNORE INTO limits(model, max_active) VALUES ('luna', 0)")
            connection.execute("INSERT OR IGNORE INTO limits(model, max_active) VALUES ('grok', 0)")
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS acceptance_gates (
                    gate_id TEXT PRIMARY KEY,
                    evidence_json TEXT NOT NULL,
                    recorded_at REAL NOT NULL
                )
                """
            )
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS scheduler_events (
                    seq INTEGER PRIMARY KEY,
                    recorded_at REAL NOT NULL,
                    project_id TEXT,
                    task_id TEXT,
                    attempt_id TEXT,
                    kind TEXT NOT NULL,
                    details_json TEXT NOT NULL
                )
                """
            )

    @staticmethod
    def _event(
        connection: sqlite3.Connection,
        kind: str,
        details: dict[str, Any],
        project_id: str | None = None,
        task_id: str | None = None,
        attempt_id: str | None = None,
    ) -> None:
        connection.execute(
            """
            INSERT INTO scheduler_events(
                recorded_at, project_id, task_id, attempt_id, kind, details_json
            ) VALUES (?, ?, ?, ?, ?, ?)
            """,
            (time.time(), project_id, task_id, attempt_id, kind, _json(details, "event details")),
        )

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
        task = dict(task)
        task.setdefault("model", "luna")
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
        _relative_path(task["target_path"], f"task {task_id!r} target_path")
        if "hint" in task and not isinstance(task["hint"], str):
            raise ValueError(f"task {task_id!r} hint must be a string")
        if "difficulty" in task and not isinstance(task["difficulty"], str):
            raise ValueError(f"task {task_id!r} difficulty must be a string")
        if "timeout_seconds" in task:
            timeout = task["timeout_seconds"]
            _validate_positive_finite(timeout, f"task {task_id!r} timeout_seconds")
        if "estimated_seconds" in task:
            estimate = task["estimated_seconds"]
            _validate_positive_finite(estimate, f"task {task_id!r} estimated_seconds")
        if "priority" in task:
            priority = task["priority"]
            if isinstance(priority, bool) or not isinstance(priority, int) or not -1000 <= priority <= 1000:
                raise ValueError("priority must be an integer from -1000 through 1000")
        if "write_paths" in task:
            write_paths = task["write_paths"]
            if not isinstance(write_paths, list) or not write_paths:
                raise ValueError(f"task {task_id!r} write_paths must be a non-empty list")
            for index, path in enumerate(write_paths):
                _relative_path(path, f"task {task_id!r} write_paths[{index}]")
        if "resource_locks" in task:
            locks = task["resource_locks"]
            if not isinstance(locks, list):
                raise ValueError(f"task {task_id!r} resource_locks must be a list")
            for lock in locks:
                if isinstance(lock, str):
                    if not lock:
                        raise ValueError(f"task {task_id!r} resource lock name must be non-empty")
                elif isinstance(lock, dict):
                    name = lock.get("name", lock.get("id", lock.get("lock")))
                    if not isinstance(name, str) or not name:
                        raise ValueError(f"task {task_id!r} resource lock name must be non-empty")
                    if lock.get("scope", "project") not in {"project", "repo"}:
                        raise ValueError(f"task {task_id!r} resource lock scope must be project or repo")
                else:
                    raise ValueError(f"task {task_id!r} resource_locks entries must be strings or dicts")
        if "integrated_gates" in task:
            gates = task["integrated_gates"]
            if not isinstance(gates, list) or any(not isinstance(gate, str) or not gate for gate in gates):
                raise ValueError(f"task {task_id!r} integrated_gates must be a list of string ids")
        if task["model"] == "luna":
            # Validate explicit effort, but do not insert a default effort into
            # this frozen task payload.
            resolve_effort(task)
        _json(task, f"task {task_id!r}")
        return dict(task)

    @staticmethod
    def _owner(owner: str) -> str:
        if not isinstance(owner, str) or not owner:
            raise ValueError("owner must be a non-empty string")
        return owner

    @staticmethod
    def _limit_value(model: str, value: int) -> int:
        Store._model(model)
        if isinstance(value, bool) or not isinstance(value, int):
            raise ValueError("model limit must be an integer")
        if not 0 <= value <= SQLITE_MAX_INTEGER:
            raise ValueError("model limit must be a SQLite-safe nonnegative integer")
        return value

    @staticmethod
    def _attempt_id(attempt_id: str) -> str:
        if not isinstance(attempt_id, str) or not attempt_id:
            raise ValueError("attempt_id must be a non-empty string")
        return attempt_id

    @staticmethod
    def _research_model(value: Any) -> str | None:
        if not isinstance(value, str):
            return None
        normalized = value.lower()
        if normalized in {"luna", LUNA_MODEL.lower()}:
            return "luna"
        if normalized == "grok" or normalized.startswith("grok-"):
            return "grok"
        return None

    @staticmethod
    def _research_counts(connection: sqlite3.Connection) -> dict[str, int]:
        table = connection.execute(
            "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = 'research_jobs'"
        ).fetchone()
        if table is None:
            return {}
        columns = {row["name"] for row in connection.execute("PRAGMA table_info(research_jobs)")}
        if not {"model", "status"}.issubset(columns):
            return {}
        counts = {"luna": 0, "grok": 0}
        for row in connection.execute(
            """
            SELECT model, COUNT(*) AS count
            FROM research_jobs
            WHERE status IN ('RUNNING', 'PREPARING')
            GROUP BY model
            """
        ):
            model = Store._research_model(row["model"])
            if model is not None:
                counts[model] += row["count"]
        return counts

    @staticmethod
    def _active_counts(connection: sqlite3.Connection) -> dict[str, int]:
        counts = {"luna": 0, "grok": 0}
        for row in connection.execute(
            """
            SELECT t.model, COUNT(*) AS count
            FROM attempts AS a
            JOIN tasks AS t ON t.project_id = a.project_id AND t.task_id = a.task_id
            WHERE a.status = 'RUNNING'
            GROUP BY t.model
            """
        ):
            counts[row["model"]] = row["count"]
        imported = Store._research_counts(connection)
        for model in _MODELS:
            counts[model] += imported.get(model, 0)
        return counts

    def set_limits(self, luna: int = 0, grok: int = 0) -> None:
        """Set persistent global concurrency limits for both models."""

        luna = self._limit_value("luna", luna)
        grok = self._limit_value("grok", grok)
        requested = {"luna": luna, "grok": grok}
        with self._transaction() as connection:
            current = {
                row["model"]: row["max_active"]
                for row in connection.execute("SELECT model, max_active FROM limits")
            }
            active = self._active_counts(connection)
            for model, limit in requested.items():
                if limit != 0 and active.get(model, 0) > limit:
                    raise ValueError(f"{model} limit cannot be below current active work")
            if current != requested:
                connection.executemany(
                    "UPDATE limits SET max_active = ? WHERE model = ?",
                    ((luna, "luna"), (grok, "grok")),
                )
                self._event(connection, "limits", {"old": current, "new": requested})

    def init_project(self, project_id: str, config: dict[str, Any]) -> None:
        """Create a project, or verify the configuration of an existing one."""

        project_id = self._project_id(project_id)
        if not isinstance(config, dict):
            raise ValueError("config must be a dict")
        resolve_effort({}, config)
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
            project_row = connection.execute(
                "SELECT config_json FROM projects WHERE project_id = ?", (project_id,)
            ).fetchone()
            if project_row is None:
                raise KeyError(f"unknown project {project_id!r}")
            config = _object(project_row["config_json"], "project configuration")
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
                if task["model"] == "luna":
                    resolve_effort(task, config)
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
                self._event(
                    connection,
                    "enqueue",
                    {"model": task["model"]},
                    project_id=project_id,
                    task_id=task["id"],
                )

    def claim(self, project_id: str, owner: str) -> dict[str, Any] | None:
        """Atomically claim one eligible task, or return ``None``."""

        project_id = self._project_id(project_id)
        owner = self._owner(owner)
        with self._transaction() as connection:
            project_rows = connection.execute("SELECT project_id, config_json FROM projects").fetchall()
            projects = {
                row["project_id"]: _object(row["config_json"], "project configuration")
                for row in project_rows
            }
            if project_id not in projects:
                raise KeyError(f"unknown project {project_id!r}")
            project_config = projects[project_id]
            limits = {
                row["model"]: row["max_active"]
                for row in connection.execute("SELECT model, max_active FROM limits")
            }
            paused = {
                row["model"]
                for row in connection.execute("SELECT model FROM paused_models")
            }
            active = self._active_counts(connection)
            all_rows = connection.execute(
                "SELECT project_id, task_id, model, payload_json, status FROM tasks"
            ).fetchall()
            all_tasks = {
                (row["project_id"], row["task_id"]): _object(row["payload_json"], "task payload")
                for row in all_rows
            }
            local_tasks = {
                row["task_id"]: all_tasks[(project_id, row["task_id"])]
                for row in all_rows
                if row["project_id"] == project_id
            }
            local_statuses = {
                row["task_id"]: row["status"] for row in all_rows if row["project_id"] == project_id
            }

            # Build the DAG once for this transaction.  Both metrics are
            # memoized, so a claim does not repeatedly walk every descendant.
            children: dict[str, set[str]] = {task_id: set() for task_id in local_tasks}
            for task_id, payload in local_tasks.items():
                for dependency in payload.get("depends_on", []):
                    if dependency in children:
                        children[dependency].add(task_id)

            critical_memo: dict[str, float] = {}

            def critical_path_score(task_id: str) -> float:
                if task_id in critical_memo:
                    return critical_memo[task_id]
                if local_statuses.get(task_id) == "INTEGRATED":
                    critical_memo[task_id] = 0.0
                    return 0.0
                own = _effective_estimate(local_tasks[task_id])
                score = own
                for child in children[task_id]:
                    if local_statuses.get(child) != "INTEGRATED":
                        score = max(score, own + critical_path_score(child))
                critical_memo[task_id] = score
                return score

            descendants_memo: dict[str, frozenset[str]] = {}

            def unfinished_descendants(task_id: str) -> frozenset[str]:
                if task_id in descendants_memo:
                    return descendants_memo[task_id]
                found: set[str] = set()
                for child in children[task_id]:
                    if local_statuses.get(child) != "INTEGRATED":
                        found.add(child)
                        found.update(unfinished_descendants(child))
                result = frozenset(found)
                descendants_memo[task_id] = result
                return result

            candidates = connection.execute(
                """
                SELECT task_id, model, payload_json
                FROM tasks
                WHERE project_id = ? AND status = 'QUEUED'
                """,
                (project_id,),
            ).fetchall()
            candidates = sorted(
                candidates,
                key=lambda row: (
                    -int(local_tasks[row["task_id"]].get("priority", 0)),
                    -critical_path_score(row["task_id"]),
                    -len(unfinished_descendants(row["task_id"])),
                    row["task_id"],
                ),
            )

            running = connection.execute(
                """
                SELECT a.project_id, t.task_id, t.payload_json
                FROM attempts AS a
                JOIN tasks AS t ON t.project_id = a.project_id AND t.task_id = a.task_id
                WHERE a.status = 'RUNNING'
                """
            ).fetchall()
            running_outputs: list[tuple[tuple[str, str] | None, list[str], set[tuple[Any, ...]]]] = []
            for row in running:
                payload = _object(row["payload_json"], "task payload")
                try:
                    paths = _task_paths(payload)
                except (KeyError, ValueError):  # Historical cards are never rewritten.
                    paths = []
                identity = _project_identity(row["project_id"], projects[row["project_id"]])
                lock_keys: set[tuple[Any, ...]] = set()
                for scope, name in _resource_lock_entries(payload):
                    if scope == "repo" and identity is not None:
                        lock_keys.add(("repo", identity, name))
                    elif scope == "project":
                        lock_keys.add(("project", row["project_id"], name))
                running_outputs.append((identity, paths, lock_keys))

            gate_rows = {
                row["gate_id"] for row in connection.execute("SELECT gate_id FROM acceptance_gates")
            }
            selected: sqlite3.Row | None = None
            task_payload: dict[str, Any] | None = None
            selected_identity = _project_identity(project_id, project_config)
            for candidate in candidates:
                task_id = candidate["task_id"]
                model = candidate["model"]
                if model in paused or (limits[model] != 0 and active.get(model, 0) >= limits[model]):
                    continue
                payload = _object(candidate["payload_json"], "task payload")
                if any(local_statuses.get(dependency) != "INTEGRATED" for dependency in payload.get("depends_on", [])):
                    continue
                if any(gate not in gate_rows for gate in payload.get("integrated_gates", [])):
                    continue
                if model == "luna":
                    resolve_effort(payload, project_config)
                try:
                    candidate_paths = _task_paths(payload)
                except (KeyError, ValueError):
                    continue
                candidate_locks: set[tuple[Any, ...]] = set()
                for scope, name in _resource_lock_entries(payload):
                    if scope == "repo" and selected_identity is not None:
                        candidate_locks.add(("repo", selected_identity, name))
                    elif scope == "project":
                        candidate_locks.add(("project", project_id, name))
                blocked = False
                for identity, paths, lock_keys in running_outputs:
                    if selected_identity is not None and identity == selected_identity:
                        if any(_path_overlap(left, right) for left in candidate_paths for right in paths):
                            blocked = True
                            break
                    if candidate_locks.intersection(lock_keys):
                        blocked = True
                        break
                if blocked:
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
            self._event(
                connection,
                "claim",
                {"model": selected["model"], "owner": owner},
                project_id=project_id,
                task_id=selected["task_id"],
                attempt_id=attempt_id,
            )
            return {
                "project_id": project_id,
                "task_id": selected["task_id"],
                "attempt_id": attempt_id,
                "task": task_payload,
            }

    def record_runtime(self, attempt_id: str, metadata: dict[str, Any]) -> None:
        """Replace arbitrary runtime metadata without changing the task."""

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
            connection.execute("UPDATE attempts SET heartbeat = ? WHERE id = ?", (time.time(), attempt_id))

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
                "SELECT status, model FROM tasks WHERE project_id = ? AND task_id = ?",
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
            self._event(
                connection,
                "finish",
                {"status": status, "model": task["model"]},
                project_id=row["project_id"],
                task_id=row["task_id"],
                attempt_id=attempt_id,
            )
            if status == "QUOTA":
                self._event(
                    connection,
                    "quota",
                    {"status": status, "model": task["model"]},
                    project_id=row["project_id"],
                    task_id=row["task_id"],
                    attempt_id=attempt_id,
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
            self._event(connection, "quota", {"model": model, "paused": True, "reason": reason})

    def resume_model(self, model: str) -> None:
        """Allow new claims for a model globally."""

        self._model(model)
        with self._transaction() as connection:
            deleted = connection.execute("DELETE FROM paused_models WHERE model = ?", (model,)).rowcount
            if deleted:
                self._event(connection, "quota", {"model": model, "paused": False})

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
            self._event(
                connection,
                "integrate",
                {"commit": commit},
                project_id=project_id,
                task_id=task_id,
            )

    def retry(self, project_id: str, task_id: str) -> None:
        """Queue a terminally failed task again while retaining its attempts."""

        project_id = self._project_id(project_id)
        if not isinstance(task_id, str) or not _TASK_ID.fullmatch(task_id):
            raise ValueError("task id must match [A-Za-z0-9_-]+")
        with self._transaction() as connection:
            row = connection.execute(
                "SELECT status, model FROM tasks WHERE project_id = ? AND task_id = ?",
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
            self._event(
                connection,
                "enqueue",
                {"model": row["model"], "retry": True},
                project_id=project_id,
                task_id=task_id,
            )

    @staticmethod
    def _gate_evidence(evidence: dict[str, Any]) -> str:
        if not isinstance(evidence, dict):
            raise ValueError("evidence must be a dict")
        commit = evidence.get("commit")
        manifest = evidence.get("manifest_sha256")
        audited = evidence.get("audited_targets")
        reviewer = evidence.get("reviewer")
        if not isinstance(commit, str) or not commit:
            raise ValueError("evidence commit must be non-empty")
        if not isinstance(manifest, str) or not _MANIFEST_SHA256.fullmatch(manifest):
            raise ValueError("evidence manifest_sha256 must be 64 hexadecimal characters")
        if not isinstance(audited, list) or not audited:
            raise ValueError("evidence audited_targets must be a non-empty list")
        if not isinstance(reviewer, str) or not reviewer:
            raise ValueError("evidence reviewer must be non-empty")
        return _json(evidence, "acceptance evidence")

    @staticmethod
    def _gate_id(gate_id: str) -> str:
        if not isinstance(gate_id, str) or not gate_id:
            raise ValueError("gate_id must be a non-empty string")
        return gate_id

    def record_acceptance_gate(self, gate_id: str, evidence: dict[str, Any]) -> None:
        """Record trusted external acceptance evidence idempotently."""

        gate_id = self._gate_id(gate_id)
        encoded = self._gate_evidence(evidence)
        with self._transaction() as connection:
            row = connection.execute(
                "SELECT evidence_json FROM acceptance_gates WHERE gate_id = ?", (gate_id,)
            ).fetchone()
            if row is not None:
                if row["evidence_json"] != encoded:
                    raise ValueError(f"acceptance gate {gate_id!r} already has different evidence")
                return
            connection.execute(
                "INSERT INTO acceptance_gates(gate_id, evidence_json, recorded_at) VALUES (?, ?, ?)",
                (gate_id, encoded, time.time()),
            )
            self._event(connection, "gate", {"gate_id": gate_id})

    def get_acceptance_gate(self, gate_id: str) -> dict[str, Any] | None:
        gate_id = self._gate_id(gate_id)
        with self._connection() as connection:
            row = connection.execute(
                "SELECT gate_id, evidence_json, recorded_at FROM acceptance_gates WHERE gate_id = ?",
                (gate_id,),
            ).fetchone()
        if row is None:
            return None
        return {
            "gate_id": row["gate_id"],
            "evidence": _object(row["evidence_json"], "acceptance evidence"),
            "recorded_at": row["recorded_at"],
        }

    def list_acceptance_gates(self) -> list[dict[str, Any]]:
        with self._connection() as connection:
            rows = connection.execute(
                "SELECT gate_id, evidence_json, recorded_at FROM acceptance_gates ORDER BY gate_id"
            ).fetchall()
        return [
            {
                "gate_id": row["gate_id"],
                "evidence": _object(row["evidence_json"], "acceptance evidence"),
                "recorded_at": row["recorded_at"],
            }
            for row in rows
        ]

    def list_events(self, after: int = 0, project_id: str | None = None) -> list[dict[str, Any]]:
        if isinstance(after, bool) or not isinstance(after, int) or after < 0:
            raise ValueError("after must be a nonnegative integer")
        if project_id is not None:
            project_id = self._project_id(project_id)
        with self._connection() as connection:
            if project_id is None:
                rows = connection.execute(
                    """
                    SELECT seq, recorded_at, project_id, task_id, attempt_id, kind, details_json
                    FROM scheduler_events WHERE seq > ? ORDER BY seq
                    """,
                    (after,),
                ).fetchall()
            else:
                rows = connection.execute(
                    """
                    SELECT seq, recorded_at, project_id, task_id, attempt_id, kind, details_json
                    FROM scheduler_events WHERE seq > ? AND project_id = ? ORDER BY seq
                    """,
                    (after, project_id),
                ).fetchall()
        return [
            {
                "seq": row["seq"],
                "recorded_at": row["recorded_at"],
                "project_id": row["project_id"],
                "task_id": row["task_id"],
                "attempt_id": row["attempt_id"],
                "kind": row["kind"],
                "details": _object(row["details_json"], "event details"),
            }
            for row in rows
        ]

    def approve_reverification(self, attempt_id: str, result: dict[str, Any]) -> None:
        """Record a trusted successful recheck while preserving failed history."""

        self._attempt_id(attempt_id)
        verification = result.get("verification") if isinstance(result, dict) else None
        if not isinstance(verification, dict) or not verification.get("compile_passed"):
            raise ValueError("successful trusted compilation is required")
        if not result.get("reverified_without_model"):
            raise ValueError("reverification provenance is required")
        encoded = _json(result, "reverification result")
        with self._transaction() as connection:
            row = connection.execute("SELECT * FROM attempts WHERE id = ?", (attempt_id,)).fetchone()
            if row is None:
                raise KeyError(attempt_id)
            latest = connection.execute(
                """
                SELECT id FROM attempts
                WHERE project_id = ? AND task_id = ?
                ORDER BY started_at DESC, rowid DESC LIMIT 1
                """,
                (row["project_id"], row["task_id"]),
            ).fetchone()
            task = connection.execute(
                "SELECT status FROM tasks WHERE project_id = ? AND task_id = ?",
                (row["project_id"], row["task_id"]),
            ).fetchone()
            if row["status"] != "FAILED" or task["status"] != "FAILED" or latest["id"] != attempt_id:
                raise ValueError("only the latest FAILED attempt may be reverified")
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS reverification_events (
                    event_id TEXT PRIMARY KEY, attempt_id TEXT NOT NULL, recorded_at REAL NOT NULL,
                    previous_result_json TEXT NOT NULL, result_json TEXT NOT NULL,
                    FOREIGN KEY (attempt_id) REFERENCES attempts(id)
                )
                """
            )
            connection.execute(
                "INSERT INTO reverification_events VALUES (?,?,?,?,?)",
                (str(uuid.uuid4()), attempt_id, time.time(), row["result_json"], encoded),
            )
            connection.execute("UPDATE attempts SET status = 'VERIFIED', result_json = ? WHERE id = ?", (encoded, attempt_id))
            connection.execute(
                "UPDATE tasks SET status = 'VERIFIED' WHERE project_id = ? AND task_id = ?",
                (row["project_id"], row["task_id"]),
            )
            self._event(
                connection,
                "finish",
                {"status": "VERIFIED", "reverified_without_model": True},
                project_id=row["project_id"],
                task_id=row["task_id"],
                attempt_id=attempt_id,
            )
