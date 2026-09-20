"""A read-only adoption and review bridge for existing research batches.

This module deliberately does not launch workers.  :class:`ResearchQueue`
adopts work which already exists in a batch directory, observes its owner,
freezes a candidate after the owner has stopped, and places the frozen
candidate in an independent verification/review flow.

Public API
==========

``ResearchQueue(store, state_root, *, process_detector=None, verifier=None)``
    ``store`` is the scheduler store (or a compatible object exposing a
    ``db_path`` and, at integration time, ``record_acceptance_gate``).
    ``state_root`` is a persistent state directory.  Snapshots are copied
    below ``state_root/research`` and never below a worker directory.

``import_batch(project_id, batch_root, depends_on=None) -> list[dict]``
    Adopt the records in ``batch_root/tasks.json``.  The accepted model
    spellings are ``luna``/``grok`` and ``gpt-5.6-luna``/``grok-4.6``;
    the latter are normalized to the former.  Effort must be one of
    ``high``, ``xhigh``, or ``max``.  Re-importing
    the same ``(batch_root, task_id)`` returns the frozen existing row and
    never launches or restarts anything.

``poll(project_id) -> dict``
    Cheaply observe adopted jobs, update process/result evidence, and copy
    stopped candidates.  It does not run Lean.  A successful worker becomes
    ``REVIEW_REQUIRED`` after capture; it never becomes verified or
    integrated merely because it exited zero.

``list_jobs(project_id) -> list[dict]``
    Return decoded job rows, including evidence, frozen manifest, review,
    dependencies, and a ``stale_base`` value of ``CURRENT``, ``STALE``, or
    ``UNKNOWN``.

``verify(job_id, targets) -> dict``
    Independently compile a frozen candidate.  ``targets`` must be a
    non-empty list of trusted ``{'path': relative_lean_path, 'name':
    fully.qualified.name}`` dictionaries.  The default verifier uses a
    fresh output directory, production baseline paths, and only fresh
    outputs for owned files.  Tests may inject ``verifier(job, targets,
    workspace)`` (two- and one-argument callables are also accepted).

``approve(job_id, manifest_sha256, reviewer, notes) -> dict``
    Record a semantic review only after successful independent verification,
    with an exact frozen manifest hash and notes explicitly addressing
    signatures/interfaces and definitions/new definitions.  Approval does
    not integrate code.

``record_integrated(job_id, commit) -> dict``
    Validate a real hexadecimal Git commit, ancestry to the configured
    integration branch, and byte-for-byte equality of every frozen owned
    source with that commit.  It then calls
    ``store.record_acceptance_gate('research:' + job_id, gate)`` and only
    after that succeeds records ``INTEGRATED``.  This method performs no
    Git writes and is idempotent for the same commit.

The process detector is an optional callback ``detector(job)`` returning a
mapping.  ``{'live': True, 'identity_valid': True, 'descendants_stopped':
False}`` is the smallest useful live result; ``{'live': False,
'descendants_stopped': True}`` denotes a stopped owner.  The built-in
detector validates ``/proc`` PID start time, command line, and working
directory, including adopted child processes.  No detector result ever
causes a kill operation.

This is an evidence-preserving bridge, not a perfect malicious-agent
sandbox.  In particular, semantic review and the later core acceptance
gate remain mandatory.
"""

from __future__ import annotations

import contextlib
import hashlib
import inspect
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import sqlite3
import subprocess
import tempfile
import time
import uuid
from typing import Any, Callable, Iterator


STATUSES = frozenset(
    {
        "PREPARING",
        "RUNNING",
        "CAPTURE_PENDING",
        "REVIEW_REQUIRED",
        "VALIDATION_FAILED",
        "APPROVED",
        "INTEGRATED",
        "FAILED",
        "INTERRUPTED",
    }
)
MODELS = frozenset({"luna", "grok"})
EFFORTS = frozenset({"high", "xhigh", "max"})
_MODEL_ALIASES = {
    "luna": "luna",
    "gpt-5.6-luna": "luna",
    "grok": "grok",
    "grok-4.6": "grok",
}
_TASK_ID = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,191}\Z")
_LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*\Z")
_HEX_COMMIT = re.compile(r"[0-9a-fA-F]{7,64}\Z")
_PATH_MAX = 512
_FILE_MAX = 2_000_000
_TOTAL_MAX = 20_000_000
_FILE_MAX_COUNT = 256
_UNSAFE_PARTS = frozenset(
    {
        ".git",
        ".lake",
        "build",
        "cache",
        "caches",
        "auth",
        "state",
        "logs",
        "log",
        "node_modules",
        "__pycache__",
    }
)
_UNSAFE_SUFFIXES = frozenset(
    {
        ".olean",
        ".ilean",
        ".c",
        ".o",
        ".a",
        ".so",
        ".dylib",
        ".dll",
        ".pyc",
        ".tmp",
        ".log",
    }
)


def _json(value: Any, label: str) -> str:
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False, allow_nan=False)
    except (TypeError, ValueError) as exc:
        raise ValueError(f"{label} must be JSON serializable") from exc


def _decode(text: str, label: str) -> Any:
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValueError(f"stored {label} is not valid JSON") from exc


def _now() -> float:
    return time.time()


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _relative(path: str, label: str = "path") -> str:
    if not isinstance(path, str) or not path or len(path) > _PATH_MAX:
        raise ValueError(f"{label} must be a non-empty short relative path")
    pure = PurePosixPath(path.replace("\\", "/"))
    if pure.is_absolute() or not pure.parts or ".." in pure.parts or "." in pure.parts:
        raise ValueError(f"{label} must not be absolute or escape its root")
    if any(not part or part.startswith(".") for part in pure.parts):
        raise ValueError(f"{label} contains a hidden or empty path component")
    return pure.as_posix()


def _safe_job_id(job_id: str) -> str:
    if not isinstance(job_id, str) or not re.fullmatch(r"[0-9a-f]{32}", job_id):
        raise ValueError("job_id is not a queue job id")
    return job_id


def _safe_project(project_id: str) -> str:
    if not isinstance(project_id, str) or not project_id or len(project_id) > 191:
        raise ValueError("project_id must be a non-empty short string")
    return project_id


def _is_under(path: Path, root: Path) -> bool:
    try:
        path.relative_to(root)
    except ValueError:
        return False
    return True


def _has_symlink_component(path: Path) -> bool:
    current = path
    while True:
        if current.is_symlink():
            return True
        if current.parent == current:
            return False
        current = current.parent


def _canonical_module(path: str, package_dir: str) -> str:
    value = path[:-5] if path.endswith(".lean") else path
    package = package_dir.strip("/").replace("\\", "/")
    if package and (value == package or value.startswith(package + "/")):
        value = value[len(package) :].lstrip("/")
    return value.replace("/", ".")


class ResearchQueue:
    """Persistent adoption, capture, verification, and review queue.

    Construction creates only ``research_jobs`` and ``research_events`` in
    the store database.  It does not alter scheduler tasks, task files, or
    worker processes.
    """

    def __init__(
        self,
        store: Any,
        state_root: str | Path,
        *,
        process_detector: Callable[[dict[str, Any]], Any] | None = None,
        verifier: Callable[..., Any] | None = None,
        command_runner: Callable[..., Any] | None = None,
        clock: Callable[[], float] = _now,
    ) -> None:
        self.store = store
        self.state_root = Path(state_root).resolve()
        self.state_root.mkdir(parents=True, exist_ok=True)
        db_path = getattr(store, "db_path", None)
        if db_path is None:
            raise ValueError("store must expose the shared SQLite db_path")
        self.db_path = str(db_path)
        self.process_detector = process_detector
        self.verifier = verifier
        self.command_runner = command_runner or subprocess.run
        self.clock = clock
        self._initialize_schema()

    def _connect(self) -> sqlite3.Connection:
        connection = sqlite3.connect(self.db_path, timeout=30.0, isolation_level=None)
        connection.row_factory = sqlite3.Row
        connection.execute("PRAGMA busy_timeout = 30000")
        connection.execute("PRAGMA foreign_keys = ON")
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
                CREATE TABLE IF NOT EXISTS research_jobs (
                    job_id TEXT PRIMARY KEY,
                    project_id TEXT NOT NULL,
                    batch_root TEXT NOT NULL,
                    task_id TEXT NOT NULL,
                    model TEXT NOT NULL CHECK (model IN ('luna', 'grok')),
                    effort TEXT NOT NULL,
                    status TEXT NOT NULL CHECK (status IN (
                        'PREPARING', 'RUNNING', 'CAPTURE_PENDING',
                        'REVIEW_REQUIRED', 'VALIDATION_FAILED', 'APPROVED',
                        'INTEGRATED', 'FAILED', 'INTERRUPTED')),
                    payload_json TEXT NOT NULL,
                    runtime_json TEXT NOT NULL,
                    manifest_json TEXT NOT NULL DEFAULT '{}',
                    verification_json TEXT NOT NULL DEFAULT '{}',
                    review_json TEXT NOT NULL DEFAULT '{}',
                    integrated_commit TEXT,
                    updated_at REAL NOT NULL,
                    depends_on_json TEXT NOT NULL DEFAULT '[]',
                    UNIQUE(batch_root, task_id)
                )
                """
            )
            connection.execute(
                """
                CREATE TABLE IF NOT EXISTS research_events (
                    event_id TEXT PRIMARY KEY,
                    job_id TEXT NOT NULL,
                    project_id TEXT NOT NULL,
                    event_type TEXT NOT NULL,
                    evidence_json TEXT NOT NULL,
                    recorded_at REAL NOT NULL
                )
                """
            )
            connection.execute(
                "CREATE INDEX IF NOT EXISTS research_jobs_project_status "
                "ON research_jobs(project_id, status)"
            )
            connection.execute(
                "CREATE INDEX IF NOT EXISTS research_events_job_time "
                "ON research_events(job_id, recorded_at)"
            )
            connection.execute(
                """
                CREATE TRIGGER IF NOT EXISTS research_events_append_only_update
                BEFORE UPDATE ON research_events
                BEGIN
                    SELECT RAISE(ABORT, 'research_events is append-only');
                END
                """
            )
            connection.execute(
                """
                CREATE TRIGGER IF NOT EXISTS research_events_append_only_delete
                BEFORE DELETE ON research_events
                BEGIN
                    SELECT RAISE(ABORT, 'research_events is append-only');
                END
                """
            )

    @staticmethod
    def _model(value: Any) -> str:
        if not isinstance(value, str) or value not in _MODEL_ALIASES:
            raise ValueError("research model must be luna/grok or gpt-5.6-luna/grok-4.6")
        return _MODEL_ALIASES[value]

    @staticmethod
    def _effort(value: Any) -> str:
        if not isinstance(value, str) or value not in EFFORTS:
            raise ValueError("effort must be one of high, xhigh, max")
        return value

    @staticmethod
    def _task_id(value: Any) -> str:
        if not isinstance(value, str) or not _TASK_ID.fullmatch(value):
            raise ValueError("task name must be a short stable task id")
        return value

    def _event(
        self,
        connection: sqlite3.Connection,
        job_id: str,
        project_id: str,
        event_type: str,
        evidence: dict[str, Any],
    ) -> None:
        connection.execute(
            "INSERT INTO research_events(event_id, job_id, project_id, event_type, evidence_json, recorded_at) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (str(uuid.uuid4()), job_id, project_id, event_type, _json(evidence, "event evidence"), self.clock()),
        )

    def _store_project(self, project_id: str) -> dict[str, Any]:
        getter = getattr(self.store, "get_project", None)
        if getter is None:
            return {}
        try:
            result = getter(project_id)
        except (KeyError, AttributeError):
            return {}
        if not isinstance(result, dict):
            return {}
        return result

    @staticmethod
    def _read_json(path: Path) -> Any:
        if path.is_symlink() or not path.is_file() or path.stat().st_size > _FILE_MAX:
            raise ValueError(f"unsafe metadata file: {path}")
        try:
            return json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise ValueError(f"invalid metadata file: {path}") from exc

    @staticmethod
    def _walk_strings(value: Any, key: str = "") -> Iterator[str]:
        if isinstance(value, dict):
            for name, child in value.items():
                yield from ResearchQueue._walk_strings(child, str(name).lower())
                if isinstance(name, str) and (name.endswith(".lean") or name in {"REPORT.md", "FINAL.md"}):
                    yield name
        elif isinstance(value, list):
            for child in value:
                yield from ResearchQueue._walk_strings(child, key)
        elif isinstance(value, str):
            normalized = value.replace("\\", "/")
            if (
                normalized.endswith(".lean")
                or normalized.endswith("/REPORT.md")
                or normalized.endswith("/FINAL.md")
                or normalized in {"REPORT.md", "FINAL.md"}
                or key in {"path", "file", "files", "source", "sources", "source_file", "source_files", "assigned", "editable"}
            ):
                yield value

    @staticmethod
    def _metadata_candidates(batch_root: Path, workdir: Path, name: str) -> list[Path]:
        result: list[Path] = []
        for path in (batch_root / name, workdir / name):
            if path not in result and path.exists():
                result.append(path)
        return result

    @staticmethod
    def _unsafe_file(rel: str) -> bool:
        pure = PurePosixPath(rel)
        return any(part in _UNSAFE_PARTS for part in pure.parts) or any(
            pure.name.endswith(suffix) for suffix in _UNSAFE_SUFFIXES
        )

    def _owned_file(self, raw: str, workdir: Path, batch_root: Path) -> tuple[str, Path]:
        if not isinstance(raw, str) or not raw:
            raise ValueError("owned file path must be a string")
        raw_path = Path(raw)
        candidates = [raw_path] if raw_path.is_absolute() else [workdir / raw_path, batch_root / raw_path]
        chosen: Path | None = None
        for candidate in candidates:
            # Check the spelling supplied by the batch before resolving it;
            # checking only the resolved path would silently follow a link in
            # a parent directory.
            current_spelling = candidate
            while True:
                if current_spelling.is_symlink():
                    raise ValueError(f"owned source may not traverse a symlink: {raw}")
                if current_spelling == workdir or current_spelling == batch_root or current_spelling.parent == current_spelling:
                    break
                current_spelling = current_spelling.parent
            try:
                resolved = candidate.resolve(strict=True)
            except OSError:
                continue
            if resolved.is_file() and _is_under(resolved, workdir.resolve()):
                chosen = resolved
                break
        if chosen is None:
            raise ValueError(f"owned source is missing or escapes workdir: {raw}")
        current = chosen
        while True:
            if current.is_symlink():
                raise ValueError(f"owned source may not be a symlink: {raw}")
            if current == workdir.resolve():
                break
            if current.parent == current:
                raise ValueError(f"owned source escapes workdir: {raw}")
            current = current.parent
        rel = chosen.relative_to(workdir.resolve()).as_posix()
        rel = _relative(rel, "owned source")
        if not rel.endswith(".lean") or self._unsafe_file(rel):
            raise ValueError("owned source must be a non-generated .lean file")
        if chosen.stat().st_size > _FILE_MAX:
            raise ValueError("owned source exceeds size limit")
        return rel, chosen

    def _ownership(self, batch_root: Path, workdir: Path, record: dict[str, Any]) -> list[dict[str, str]]:
        raw_paths: list[str] = []
        for key in ("assigned", "editable", "assigned_files", "editable_files", "source_files", "files"):
            value = record.get(key)
            if value is not None:
                raw_paths.extend(self._walk_strings(value, key))
        for metadata_name in ("editable.json", "assigned.json"):
            for metadata in self._metadata_candidates(batch_root, workdir, metadata_name):
                raw_paths.extend(self._walk_strings(self._read_json(metadata)))
        dedup: dict[str, Path] = {}
        for raw in raw_paths:
            normalized = raw.replace("\\", "/") if isinstance(raw, str) else ""
            if not (
                normalized.endswith(".lean")
                or normalized.endswith("/REPORT.md")
                or normalized.endswith("/FINAL.md")
                or normalized in {"REPORT.md", "FINAL.md"}
            ):
                # Ownership files may also describe logs, caches, or result
                # payloads.  Those are deliberately not candidate sources.
                continue
            if normalized in {"REPORT.md", "FINAL.md"}:
                continue  # Root reports are captured separately, never compiled.
            rel, path = self._owned_file(raw, workdir, batch_root)
            dedup[rel] = path

        # Reports are evidence, not source.  Only a worker-root report is
        # admitted; this prevents a batch-level report from becoming a source
        # outside the captured workdir.
        for name in ("REPORT.md", "FINAL.md"):
            report = workdir / name
            if report.exists():
                if report.is_symlink() or not report.is_file():
                    raise ValueError(f"{name} must be a regular worker file")
                if report.stat().st_size > _FILE_MAX:
                    raise ValueError(f"{name} exceeds size limit")
                dedup[name] = report.resolve()
        entries = []
        for rel in sorted(dedup):
            entries.append({"path": rel, "kind": "report" if rel in {"REPORT.md", "FINAL.md"} else "source"})
        if len(entries) > _FILE_MAX_COUNT:
            raise ValueError("candidate has too many assigned files")
        return entries

    def _repository_path(self, workdir: Path, rel: str, config: dict[str, Any]) -> str:
        package_dir = str(config.get("package_dir", "")).strip("/\\").replace("\\", "/")
        repo_value = config.get("repo")
        if repo_value:
            try:
                repo = Path(str(repo_value)).resolve()
                work = workdir.resolve()
                if _is_under(work, repo):
                    base = work.relative_to(repo).as_posix()
                    if base:
                        candidate = f"{base}/{rel}"
                    else:
                        candidate = rel
                else:
                    candidate = f"{package_dir}/{rel}" if package_dir else rel
            except OSError:
                candidate = f"{package_dir}/{rel}" if package_dir else rel
        else:
            candidate = f"{package_dir}/{rel}" if package_dir else rel
        candidate = candidate.strip("/")
        return _relative(candidate, "repository path")

    @staticmethod
    def _find_client_pid(record: dict[str, Any], batch_root: Path, workdir: Path) -> int | None:
        values: list[Any] = []

        def visit(value: Any, key: str = "") -> None:
            if isinstance(value, dict):
                for name, child in value.items():
                    if str(name).lower() in {"client_pid", "pid", "process_id"}:
                        values.append(child)
                    visit(child, str(name).lower())
            elif isinstance(value, list):
                for child in value:
                    visit(child, key)

        visit(record)
        for name in ("active.json", "metadata.json"):
            for path in ResearchQueue._metadata_candidates(batch_root, workdir, name):
                try:
                    visit(ResearchQueue._read_json(path))
                except ValueError:
                    continue
        for value in values:
            if isinstance(value, int) and not isinstance(value, bool) and value > 0:
                return value
            if isinstance(value, str) and value.isdigit() and int(value) > 0:
                return int(value)
        return None

    @staticmethod
    def _find_result_path(batch_root: Path, workdir: Path) -> Path | None:
        for path in (workdir / "process-result.json", batch_root / "process-result.json"):
            if path.exists():
                return path
        return None

    @staticmethod
    def _commits(record: dict[str, Any]) -> list[str]:
        result: list[str] = []
        for key in ("base_commit", "baseline_commit", "seed_commit", "source_baseline_commit"):
            value = record.get(key)
            if isinstance(value, str) and value and value not in result:
                result.append(value)
        return result

    def _initial_identity(self, pid: int | None) -> dict[str, Any] | None:
        if pid is None:
            return None
        return self._proc_record(pid)

    def _initial_children(self, pid: int | None) -> list[dict[str, Any]]:
        """Capture child identities at adoption for PID-reuse-safe polling."""

        if pid is None:
            return []
        records: dict[int, dict[str, Any]] = {}
        try:
            entries = list(Path("/proc").iterdir())
        except OSError:
            entries = []
        for entry in entries:
            if not entry.name.isdigit():
                continue
            record = self._proc_record(int(entry.name))
            if record is not None:
                records[record["pid"]] = record
        children: list[dict[str, Any]] = []
        frontier = [pid]
        seen = {pid}
        while frontier:
            parent = frontier.pop()
            for record in records.values():
                child = record["pid"]
                if child in seen or record.get("ppid") != parent:
                    continue
                seen.add(child)
                frontier.append(child)
                children.append(record)
        return children

    def import_batch(
        self,
        project_id: str,
        batch_root: str | Path,
        depends_on: list[str] | dict[str, Any] | None = None,
    ) -> list[dict[str, Any]]:
        """Adopt existing ``tasks.json`` records without launching them."""

        project_id = _safe_project(project_id)
        root = Path(batch_root).resolve()
        if not root.is_dir() or root.is_symlink():
            raise ValueError("batch_root must be a real directory")
        tasks_path = root / "tasks.json"
        raw_tasks = self._read_json(tasks_path)
        if isinstance(raw_tasks, dict) and isinstance(raw_tasks.get("tasks"), list):
            records = raw_tasks["tasks"]
        elif isinstance(raw_tasks, list):
            records = raw_tasks
        elif isinstance(raw_tasks, dict):
            records = []
            for name, value in raw_tasks.items():
                if isinstance(value, dict):
                    records.append(dict(value, name=value.get("name", name)))
        else:
            raise ValueError("tasks.json must contain a task list")
        if not records:
            return []
        dependency_value: list[str] | dict[str, Any]
        if depends_on is None:
            dependency_value = []
        elif isinstance(depends_on, list) and all(isinstance(value, str) and value for value in depends_on):
            dependency_value = list(depends_on)
        elif isinstance(depends_on, dict):
            dependency_value = dict(depends_on)
        else:
            raise ValueError("depends_on must be a list of IDs/gates or a mapping")
        config = self._store_project(project_id)
        prepared: list[dict[str, Any]] = []
        seen: set[str] = set()
        for record in records:
            if not isinstance(record, dict):
                raise ValueError("each tasks.json record must be an object")
            task_id = self._task_id(record.get("name"))
            if task_id in seen:
                raise ValueError(f"duplicate task name: {task_id}")
            seen.add(task_id)
            model = self._model(record.get("model"))
            effort = self._effort(record.get("effort"))
            cwd_value = record.get("cwd")
            if not isinstance(cwd_value, str) or not cwd_value:
                raise ValueError(f"task {task_id!r} has no cwd")
            workdir = Path(cwd_value)
            if not workdir.is_absolute():
                workdir = root / workdir
            if _has_symlink_component(workdir):
                raise ValueError(f"task {task_id!r} cwd traverses a symlink")
            workdir = workdir.resolve()
            if not workdir.is_dir() or workdir.is_symlink():
                raise ValueError(f"task {task_id!r} cwd is not a real directory")
            owned = self._ownership(root, workdir, record)
            for entry in owned:
                entry["repository_path"] = self._repository_path(workdir, entry["path"], config)
            pid = self._find_client_pid(record, root, workdir)
            result_path = self._find_result_path(root, workdir)
            sanitized_record = {
                key: record[key]
                for key in ("name", "cwd", "model", "effort", "base_commit", "baseline_commit", "seed_commit", "source_baseline_commit")
                if key in record
            }
            payload = {
                "project_id": project_id,
                "task": sanitized_record,
                "workdir": str(workdir),
                "owned_files": owned,
                "baseline_commits": self._commits(record),
                "depends_on": dependency_value,
                "result_path": str(result_path) if result_path else None,
            }
            runtime = {
                "client_pid": pid,
                "initial_identity": self._initial_identity(pid),
                "initial_children": self._initial_children(pid),
                "result_path": str(result_path) if result_path else None,
                "adopted_at": self.clock(),
            }
            prepared.append(
                {
                    "job_id": uuid.uuid4().hex,
                    "project_id": project_id,
                    "batch_root": str(root),
                    "task_id": task_id,
                    "model": model,
                    "effort": effort,
                    "payload": payload,
                    "runtime": runtime,
                    "depends_on": dependency_value,
                }
            )

        result: list[str] = []
        with self._transaction() as connection:
            for item in prepared:
                existing = connection.execute(
                    "SELECT job_id FROM research_jobs WHERE batch_root = ? AND task_id = ?",
                    (item["batch_root"], item["task_id"]),
                ).fetchone()
                if existing is not None:
                    result.append(existing["job_id"])
                    continue
                encoded_dep = _json(item["depends_on"], "depends_on")
                connection.execute(
                    """
                    INSERT INTO research_jobs(
                        job_id, project_id, batch_root, task_id, model, effort, status,
                        payload_json, runtime_json, manifest_json, verification_json,
                        review_json, integrated_commit, updated_at, depends_on_json
                    ) VALUES (?, ?, ?, ?, ?, ?, 'PREPARING', ?, ?, '{}', '{}', '{}', NULL, ?, ?)
                    """,
                    (
                        item["job_id"],
                        item["project_id"],
                        item["batch_root"],
                        item["task_id"],
                        item["model"],
                        item["effort"],
                        _json(item["payload"], "task payload"),
                        _json(item["runtime"], "runtime evidence"),
                        self.clock(),
                        encoded_dep,
                    ),
                )
                self._event(connection, item["job_id"], project_id, "IMPORTED", {"status": "PREPARING"})
                result.append(item["job_id"])
        return [self._job_by_id(job_id) for job_id in result]

    def _job_by_id(self, job_id: str) -> dict[str, Any]:
        _safe_job_id(job_id)
        with self._connection() as connection:
            row = connection.execute("SELECT * FROM research_jobs WHERE job_id = ?", (job_id,)).fetchone()
        if row is None:
            raise KeyError(f"unknown research job {job_id!r}")
        return self._public_row(row)

    def _public_row(self, row: sqlite3.Row | dict[str, Any]) -> dict[str, Any]:
        get = row.__getitem__
        payload = _decode(get("payload_json"), "payload")
        runtime = _decode(get("runtime_json"), "runtime")
        manifest = _decode(get("manifest_json"), "manifest")
        verification = _decode(get("verification_json"), "verification")
        review = _decode(get("review_json"), "review")
        return {
            "job_id": get("job_id"),
            "project_id": get("project_id"),
            "batch_root": get("batch_root"),
            "task_id": get("task_id"),
            "model": get("model"),
            "effort": get("effort"),
            "status": get("status"),
            "payload": payload,
            "runtime": runtime,
            "manifest": manifest,
            "verification": verification,
            "review": review,
            "integrated_commit": get("integrated_commit"),
            "depends_on": _decode(get("depends_on_json"), "depends_on"),
            "updated_at": get("updated_at"),
            "stale_base": self._stale_base(payload),
        }

    def list_jobs(self, project_id: str) -> list[dict[str, Any]]:
        """List all adopted jobs for a project without running verification."""

        project_id = _safe_project(project_id)
        with self._connection() as connection:
            rows = connection.execute(
                "SELECT * FROM research_jobs WHERE project_id = ? ORDER BY updated_at, task_id",
                (project_id,),
            ).fetchall()
        return [self._public_row(row) for row in rows]

    def _proc_record(self, pid: int) -> dict[str, Any] | None:
        proc = Path("/proc") / str(pid)
        try:
            stat_text = (proc / "stat").read_text()
            after_name = stat_text.rsplit(") ", 1)[1].split()
            starttime = after_name[19]
            ppid = int(after_name[1])
            cwd = os.readlink(proc / "cwd")
            command = (proc / "cmdline").read_bytes().replace(b"\0", b" ").decode("utf-8", "replace").strip()
            if not command:
                command = (proc / "comm").read_text().strip()
            return {"pid": pid, "ppid": ppid, "starttime": starttime, "cwd": cwd, "command": command}
        except (OSError, IndexError, ValueError, UnicodeError):
            return None

    def _default_process_detector(self, job: dict[str, Any]) -> dict[str, Any]:
        runtime = job["runtime"]
        payload = job["payload"]
        pid = runtime.get("client_pid")
        initial = runtime.get("initial_identity")
        workdir = Path(payload["workdir"]).resolve()
        records: dict[int, dict[str, Any]] = {}
        if isinstance(pid, int) and pid > 0:
            current = self._proc_record(pid)
            if current is not None:
                records[pid] = current
        try:
            proc_entries = list(Path("/proc").iterdir())
        except OSError:
            proc_entries = []
        for entry in proc_entries:
            if entry.name.isdigit() and int(entry.name) not in records:
                record = self._proc_record(int(entry.name))
                if record is not None:
                    records[record["pid"]] = record

        client = records.get(pid) if isinstance(pid, int) else None
        client_valid = False
        if client is not None:
            client_valid = _is_under(Path(client["cwd"]).resolve(), workdir)
            if initial:
                client_valid = client_valid and all(client.get(key) == initial.get(key) for key in ("starttime", "cwd", "command"))
            else:
                client_valid = client_valid and bool(client.get("command"))

        expected_children = {
            int(item.get("pid")): item
            for item in runtime.get("initial_children", [])
            if isinstance(item, dict) and str(item.get("pid", "")).isdigit()
        }
        live_child = False
        for candidate in records.values():
            if candidate["pid"] == pid:
                continue
            if not _is_under(Path(candidate["cwd"]).resolve(), workdir):
                continue
            expected = expected_children.get(candidate["pid"])
            if expected and not all(candidate.get(key) == expected.get(key) for key in ("starttime", "cwd", "command")):
                continue
            # A process which was not present at adoption is only considered
            # while the exact adopted client is still alive and owns it.
            if expected or client_valid:
                live_child = True
                break
        return {
            "live": bool(client_valid or live_child),
            "identity_valid": bool(client_valid or live_child),
            "descendants_stopped": not live_child,
            "pid": pid,
            "observed": {str(key): value for key, value in records.items() if key == pid or value.get("cwd") == str(workdir)},
        }

    def _detect(self, job: dict[str, Any]) -> dict[str, Any]:
        if self.process_detector is None:
            return self._default_process_detector(job)
        value = self.process_detector(job)
        if isinstance(value, bool):
            return {"live": value, "identity_valid": value, "descendants_stopped": not value}
        if isinstance(value, list):
            live = bool(value)
            return {"live": live, "identity_valid": live, "descendants_stopped": not live, "observed": value}
        if not isinstance(value, dict):
            raise ValueError("process_detector must return a bool, list, or mapping")
        result = dict(value)
        result.setdefault("identity_valid", result.get("live", False))
        result.setdefault("descendants_stopped", not bool(result.get("live", False)))
        result["live"] = bool(result.get("live", False)) and bool(result.get("identity_valid", False))
        return result

    @staticmethod
    def _result_info(path_value: Any) -> dict[str, Any]:
        if not path_value:
            return {"known": False, "reason": "process-result.json is missing"}
        path = Path(str(path_value))
        if path.is_symlink() or not path.is_file() or path.stat().st_size > _FILE_MAX:
            return {"known": False, "reason": "process-result.json is unsafe or missing"}
        try:
            value = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            return {"known": False, "reason": "process-result.json is invalid"}
        if not isinstance(value, dict):
            return {"known": False, "reason": "process-result.json is not an object"}
        exit_value: Any = None
        for key in ("exit_code", "returncode", "exit", "code"):
            if key in value:
                exit_value = value[key]
                break
        if exit_value is None and isinstance(value.get("result"), dict):
            for key in ("exit_code", "returncode", "exit", "code"):
                if key in value["result"]:
                    exit_value = value["result"][key]
                    break
        try:
            exit_code = int(exit_value)
        except (TypeError, ValueError):
            return {"known": False, "reason": "completion exit code is missing"}
        timestamp_keys = ("ended", "finished_at", "finished_unix", "ended_at", "ended_unix", "completed_at", "completed_unix")
        if not any(key in value for key in timestamp_keys):
            return {"known": False, "reason": "completion timestamp is missing"}
        return {
            "known": True,
            "exit_code": exit_code,
            "successful": exit_code == 0,
            "evidence_path": str(path),
            "timestamps": {
                key: value
                for key, value in value.items()
                if key in {"started", "ended", "started_at", "started_unix", "finished_at", "finished_unix", "ended_at", "ended_unix", "completed_at", "completed_unix"}
            },
            "raw_keys": sorted(str(key) for key in value),
        }

    def _set_status(
        self,
        job_id: str,
        status: str,
        *,
        evidence: dict[str, Any] | None = None,
        allowed: tuple[str, ...] | None = None,
    ) -> bool:
        if status not in STATUSES:
            raise ValueError(f"invalid research status: {status}")
        with self._transaction() as connection:
            row = connection.execute("SELECT project_id, status FROM research_jobs WHERE job_id = ?", (job_id,)).fetchone()
            if row is None:
                raise KeyError(job_id)
            if allowed is not None and row["status"] not in allowed:
                return False
            if row["status"] == status:
                return True
            connection.execute(
                "UPDATE research_jobs SET status = ?, updated_at = ? WHERE job_id = ?",
                (status, self.clock(), job_id),
            )
            self._event(connection, job_id, row["project_id"], "STATUS", {"from": row["status"], "to": status, **(evidence or {})})
            return True

    def _capture(self, job: dict[str, Any], result_info: dict[str, Any]) -> None:
        manifest = job["manifest"]
        if manifest:
            return
        payload = job["payload"]
        workdir = Path(payload["workdir"]).resolve()
        artifact_root = self.state_root / "research" / job["job_id"]
        snapshot = artifact_root / "snapshot"
        staging = artifact_root / (".capture-" + uuid.uuid4().hex)
        staging.mkdir(parents=True, exist_ok=False)
        total = 0
        files: list[dict[str, Any]] = []
        try:
            for entry in sorted(payload.get("owned_files", []), key=lambda item: item["path"]):
                rel = _relative(entry["path"], "owned file")
                source = workdir / rel
                if source.is_symlink() or not source.is_file():
                    raise ValueError(f"worker file is missing or symlinked: {rel}")
                resolved = source.resolve(strict=True)
                if not _is_under(resolved, workdir) or resolved != source:
                    raise ValueError(f"worker file escapes workdir: {rel}")
                size = source.stat().st_size
                if size > _FILE_MAX:
                    raise ValueError(f"worker file exceeds size limit: {rel}")
                total += size
                if total > _TOTAL_MAX:
                    raise ValueError("candidate exceeds total capture size limit")
                destination = staging / rel
                destination.parent.mkdir(parents=True, exist_ok=True)
                data = source.read_bytes()
                if len(data) != size:
                    raise ValueError(f"worker file changed during capture: {rel}")
                destination.write_bytes(data)
                files.append(
                    {
                        "path": rel,
                        "kind": entry["kind"],
                        "size": len(data),
                        "sha256": _sha(data),
                        "repository_path": entry.get("repository_path"),
                    }
                )
            files.sort(key=lambda item: item["path"])
            digest_input = {"files": files}
            manifest_hash = _sha(_json(digest_input, "manifest").encode("utf-8"))
            capture_manifest = {
                "version": 1,
                "frozen": True,
                "snapshot_root": str(snapshot),
                "captured_at": self.clock(),
                "files": files,
                "manifest_sha256": manifest_hash,
                "result": result_info,
            }
            if snapshot.exists():
                shutil.rmtree(staging)
                return
            try:
                staging.rename(snapshot)
            except FileExistsError:
                # Another poller won the immutable-capture race.
                if staging.exists():
                    shutil.rmtree(staging)
                return
            with self._transaction() as connection:
                row = connection.execute("SELECT project_id, status, manifest_json FROM research_jobs WHERE job_id = ?", (job["job_id"],)).fetchone()
                if row is None:
                    raise KeyError(job["job_id"])
                if _decode(row["manifest_json"], "manifest"):
                    return
                final_status = "REVIEW_REQUIRED" if result_info.get("known") and result_info.get("successful") else (
                    "FAILED" if result_info.get("known") and not result_info.get("successful") else "INTERRUPTED"
                )
                connection.execute(
                    "UPDATE research_jobs SET status = ?, manifest_json = ?, runtime_json = ?, updated_at = ? WHERE job_id = ?",
                    (
                        final_status,
                        _json(capture_manifest, "manifest"),
                        _json({**job["runtime"], "completion": result_info}, "runtime evidence"),
                        self.clock(),
                        job["job_id"],
                    ),
                )
                self._event(
                    connection,
                    job["job_id"],
                    row["project_id"],
                    "CAPTURED",
                    {"status": final_status, "manifest_sha256": manifest_hash, "exit_code": result_info.get("exit_code")},
                )
        except BaseException:
            if staging.exists():
                shutil.rmtree(staging)
            raise

    def poll(self, project_id: str) -> dict[str, Any]:
        """Observe jobs and capture stopped candidates; never run Lean."""

        project_id = _safe_project(project_id)
        jobs = self.list_jobs(project_id)
        for job in jobs:
            if job["status"] not in {"PREPARING", "RUNNING", "CAPTURE_PENDING"}:
                continue
            if job["status"] == "CAPTURE_PENDING" and job["manifest"]:
                continue
            try:
                observation = self._detect(job)
            except Exception as exc:
                self._set_status(job["job_id"], "INTERRUPTED", evidence={"reason": f"process detection failed: {exc}"}, allowed=("PREPARING", "RUNNING", "CAPTURE_PENDING"))
                continue
            live = bool(observation.get("live"))
            stopped = bool(observation.get("descendants_stopped", not live))
            if live or not stopped:
                self._set_status(job["job_id"], "RUNNING", evidence={"process": observation}, allowed=("PREPARING", "RUNNING", "CAPTURE_PENDING"))
                continue
            result_path = job["runtime"].get("result_path") or job["payload"].get("result_path")
            if not result_path:
                # The result is commonly written by the worker after the
                # batch is imported.  Resolve the fixed expected location;
                # never search arbitrary files or accept a claimed path.
                result_path = str(Path(job["payload"]["workdir"]) / "process-result.json")
            result_info = self._result_info(result_path)
            self._set_status(job["job_id"], "CAPTURE_PENDING", evidence={"process": observation, "completion": result_info}, allowed=("PREPARING", "RUNNING", "CAPTURE_PENDING"))
            refreshed = self._job_by_id(job["job_id"])
            try:
                self._capture(refreshed, result_info)
            except Exception as exc:
                failure_status = "FAILED" if result_info.get("known") and not result_info.get("successful") else "INTERRUPTED"
                with self._transaction() as connection:
                    row = connection.execute("SELECT project_id, status, manifest_json, runtime_json FROM research_jobs WHERE job_id = ?", (job["job_id"],)).fetchone()
                    if row is not None and not _decode(row["manifest_json"], "manifest"):
                        runtime = _decode(row["runtime_json"], "runtime")
                        runtime["capture_error"] = str(exc)
                        connection.execute("UPDATE research_jobs SET status = ?, runtime_json = ?, updated_at = ? WHERE job_id = ?", (failure_status, _json(runtime, "runtime"), self.clock(), job["job_id"]))
                        self._event(connection, job["job_id"], row["project_id"], "CAPTURE_FAILED", {"status": failure_status, "error": str(exc)})
        final_jobs = self.list_jobs(project_id)
        counts = {status: sum(job["status"] == status for job in final_jobs) for status in sorted(STATUSES)}
        return {"project_id": project_id, "jobs": final_jobs, "counts": counts}

    def _manifest_files(self, job: dict[str, Any]) -> list[dict[str, Any]]:
        manifest = job["manifest"]
        if not isinstance(manifest, dict) or not manifest.get("frozen"):
            raise ValueError("job has no frozen capture")
        files = manifest.get("files")
        if not isinstance(files, list) or len(files) > _FILE_MAX_COUNT:
            raise ValueError("frozen manifest is invalid")
        snapshot = Path(str(manifest.get("snapshot_root", ""))).resolve()
        if not _is_under(snapshot, self.state_root / "research"):
            raise ValueError("frozen snapshot is outside state_root")
        seen: set[str] = set()
        total = 0
        actual_files: list[dict[str, Any]] = []
        for entry in files:
            if not isinstance(entry, dict):
                raise ValueError("frozen manifest entry is invalid")
            rel = _relative(entry.get("path"), "manifest path")
            if rel in seen:
                raise ValueError("frozen manifest contains duplicate paths")
            seen.add(rel)
            target = snapshot / rel
            if target.is_symlink() or not target.is_file() or target.resolve() != target:
                raise ValueError("frozen snapshot contains an unsafe path")
            data = target.read_bytes()
            if len(data) > _FILE_MAX or len(data) != entry.get("size") or _sha(data) != entry.get("sha256"):
                raise ValueError("frozen snapshot bytes do not match its manifest")
            total += len(data)
            if total > _TOTAL_MAX:
                raise ValueError("frozen snapshot exceeds size limit")
            actual_files.append(dict(entry))
        canonical = {"files": sorted(actual_files, key=lambda item: item["path"])}
        if _sha(_json(canonical, "manifest").encode("utf-8")) != manifest.get("manifest_sha256"):
            raise ValueError("frozen manifest hash does not match its files")
        return actual_files

    @staticmethod
    def _targets(targets: Any) -> list[dict[str, str]]:
        if not isinstance(targets, list) or not targets:
            raise ValueError("at least one trusted verification target is required")
        result: list[dict[str, str]] = []
        seen: set[tuple[str, str]] = set()
        for target in targets:
            if not isinstance(target, dict):
                raise ValueError("each verification target must be an object")
            path = _relative(target.get("path"), "target path")
            if not path.endswith(".lean") or path.endswith(".olean"):
                raise ValueError("target path must be a relative .lean source")
            name = target.get("name")
            if not isinstance(name, str) or not _LEAN_NAME.fullmatch(name):
                raise ValueError("target name must be a fully qualified Lean name")
            key = (path, name)
            if key in seen:
                raise ValueError("duplicate verification target")
            seen.add(key)
            result.append({"path": path, "name": name})
        return result

    def _verification_workspace(self, job: dict[str, Any], files: list[dict[str, Any]]) -> tempfile.TemporaryDirectory[str]:
        verification_root = self.state_root / "research" / "verification"
        verification_root.mkdir(parents=True, exist_ok=True)
        temporary = tempfile.TemporaryDirectory(prefix=job["job_id"] + "-", dir=verification_root)
        source_root = Path(temporary.name) / "source"
        source_root.mkdir()
        snapshot = Path(job["manifest"]["snapshot_root"])
        for entry in files:
            if entry["kind"] != "source":
                continue
            destination = source_root / entry["path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(snapshot / entry["path"], destination)
        return temporary

    def _invoke_verifier(self, job: dict[str, Any], targets: list[dict[str, str]], workspace: Path) -> dict[str, Any]:
        if self.verifier is None:
            return self._real_verify(job, targets, workspace)
        callback = self.verifier
        try:
            signature = inspect.signature(callback)
            parameters = list(signature.parameters.values())
            positional = [parameter for parameter in parameters if parameter.kind in (parameter.POSITIONAL_ONLY, parameter.POSITIONAL_OR_KEYWORD)]
            if any(parameter.kind == parameter.VAR_POSITIONAL for parameter in parameters) or len(positional) >= 3:
                value = callback(job, targets, workspace)
            elif len(positional) == 2:
                value = callback(job, targets)
            else:
                value = callback(job)
        except (TypeError, ValueError):
            value = callback(job, targets, workspace)
        if isinstance(value, bool):
            return {"compile_passed": value}
        if not isinstance(value, dict):
            return {"compile_passed": False, "error": "verifier returned no structured result"}
        result = dict(value)
        result["compile_passed"] = result.get("compile_passed") is True
        return result

    def _real_verify(self, job, targets, workspace):
        from research_verifier import verify_snapshot
        try:
            return verify_snapshot(self, job, targets, workspace)
        except Exception as exc:
            return {"compile_passed": False, "transitive_axioms_checked": False,
                    "error": str(exc)[-10000:]}

    def verify(self, job_id: str, targets: list[dict[str, Any]]) -> dict[str, Any]:
        """Queue one independent verification attempt for trusted targets."""

        _safe_job_id(job_id)
        checked_targets = self._targets(targets)
        job = self._job_by_id(job_id)
        if job["status"] in {"INTEGRATED", "APPROVED"}:
            prior_targets = job["verification"].get("targets", []) if isinstance(job["verification"], dict) else []
            if prior_targets != checked_targets:
                raise ValueError("verified or approved job has frozen different targets")
            return job
        if job["status"] not in {"REVIEW_REQUIRED", "FAILED", "INTERRUPTED", "VALIDATION_FAILED"}:
            raise ValueError(f"job is not ready for independent verification: {job['status']}")
        files = self._manifest_files(job)
        source_paths = {entry["path"] for entry in files if entry["kind"] == "source"}
        if any(target["path"] not in source_paths for target in checked_targets):
            raise ValueError("verification target must name a frozen assigned source")
        temporary = self._verification_workspace(job, files)
        try:
            outcome = self._invoke_verifier(job, checked_targets, Path(temporary.name))
        finally:
            temporary.cleanup()
        outcome["targets"] = checked_targets
        outcome["manifest_sha256"] = job["manifest"]["manifest_sha256"]
        outcome["verified_at"] = self.clock()
        outcome["independent"] = True
        status = "REVIEW_REQUIRED" if outcome.get("compile_passed") is True else "VALIDATION_FAILED"
        with self._transaction() as connection:
            row = connection.execute("SELECT project_id, status, manifest_json FROM research_jobs WHERE job_id = ?", (job_id,)).fetchone()
            if row is None:
                raise KeyError(job_id)
            current_manifest = _decode(row["manifest_json"], "manifest")
            if current_manifest.get("manifest_sha256") != job["manifest"].get("manifest_sha256"):
                raise ValueError("frozen manifest changed during verification")
            connection.execute(
                "UPDATE research_jobs SET status = ?, verification_json = ?, updated_at = ? WHERE job_id = ?",
                (status, _json(outcome, "verification result"), self.clock(), job_id),
            )
            self._event(connection, job_id, row["project_id"], "VERIFIED" if outcome.get("compile_passed") is True else "VALIDATION_FAILED", {"status": status, "manifest_sha256": outcome["manifest_sha256"]})
        return self._job_by_id(job_id)

    @staticmethod
    def _review_notes(notes: Any) -> str:
        if not isinstance(notes, str) or not notes.strip():
            raise ValueError("semantic review notes are required")
        lowered = notes.lower()
        signature_ack = any(word in lowered for word in ("signature", "interface", "api"))
        definition_ack = any(word in lowered for word in ("definition", "new-definition", "new definition"))
        if not signature_ack or not definition_ack:
            raise ValueError("review notes must acknowledge signatures/interfaces and definitions/new definitions")
        return notes.strip()

    def approve(self, job_id: str, manifest_sha256: str, reviewer: str, notes: str) -> dict[str, Any]:
        """Record explicit semantic approval without integrating the files."""

        _safe_job_id(job_id)
        if not isinstance(manifest_sha256, str) or not re.fullmatch(r"[0-9a-f]{64}", manifest_sha256):
            raise ValueError("manifest_sha256 must be a SHA-256 hex digest")
        if not isinstance(reviewer, str) or not reviewer.strip():
            raise ValueError("reviewer must be non-empty")
        notes = self._review_notes(notes)
        job = self._job_by_id(job_id)
        if job["manifest"].get("manifest_sha256") != manifest_sha256:
            raise ValueError("manifest hash does not match frozen capture")
        verification = job["verification"]
        if verification.get("compile_passed") is not True or not verification.get("independent"):
            raise ValueError("successful independent verification is required before approval")
        if verification.get("transitive_axioms_checked") is not True:
            raise ValueError("transitive target-axiom verification is mandatory")
        targets = verification.get("targets", [])
        axioms = verification.get("target_axioms", {})
        allowed = {"propext", "Classical.choice", "Quot.sound"}
        if not targets or not isinstance(axioms, dict):
            raise ValueError("named target axiom evidence is missing")
        for target in targets:
            used = axioms.get(target["name"])
            if not isinstance(used, list) or not set(used) <= allowed:
                raise ValueError("unaccepted target axiom dependency")
        declared_sources = {entry["path"] for entry in job["manifest"].get("files", []) if entry.get("kind") == "source"}
        if set(verification.get("compiled_sources", [])) != declared_sources:
            raise ValueError("all captured source files must compile independently")
        if verification.get("local_proof_holes"):
            raise ValueError("whole-job approval cannot hide remaining owned-source proof holes")
        if job["status"] == "INTEGRATED":
            return job
        if job["status"] == "APPROVED":
            if job["review"].get("manifest_sha256") != manifest_sha256:
                raise ValueError("approved review is frozen")
            return job
        if job["status"] not in {"REVIEW_REQUIRED", "FAILED", "INTERRUPTED"}:
            raise ValueError(f"job cannot be approved from {job['status']}")
        review = {
            "manifest_sha256": manifest_sha256,
            "reviewer": reviewer.strip(),
            "notes": notes,
            "audited_targets": verification.get("targets", []),
            "reviewed_at": self.clock(),
        }
        with self._transaction() as connection:
            row = connection.execute("SELECT project_id, status, review_json FROM research_jobs WHERE job_id = ?", (job_id,)).fetchone()
            if row is None:
                raise KeyError(job_id)
            if row["status"] == "INTEGRATED":
                return self._job_by_id(job_id)
            connection.execute("UPDATE research_jobs SET status = 'APPROVED', review_json = ?, updated_at = ? WHERE job_id = ?", (_json(review, "review"), self.clock(), job_id))
            self._event(connection, job_id, row["project_id"], "APPROVED", {"manifest_sha256": manifest_sha256, "reviewer": reviewer.strip()})
        return self._job_by_id(job_id)

    def _git(self, repo: Path, args: list[str], *, text: bool = True) -> subprocess.CompletedProcess[Any]:
        return self.command_runner(
            ["git", "-C", str(repo), *args],
            text=text,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30,
        )

    def _commit_and_branch(self, job: dict[str, Any], commit: str) -> tuple[Path, str, str]:
        if not _HEX_COMMIT.fullmatch(commit):
            raise ValueError("commit must be a real hexadecimal Git object name")
        config = self._store_project(job["project_id"])
        repo_value = config.get("repo")
        branch = config.get("integration_branch")
        if not repo_value or not isinstance(branch, str) or not branch:
            raise ValueError("project repo and integration_branch are required for integration")
        repo = Path(str(repo_value)).resolve()
        resolved = self._git(repo, ["rev-parse", "--verify", f"{commit}^{{commit}}"])
        if resolved.returncode != 0:
            raise ValueError("unknown Git commit")
        resolved_hash = (resolved.stdout.decode() if isinstance(resolved.stdout, bytes) else str(resolved.stdout)).strip()
        if not re.fullmatch(r"[0-9a-fA-F]{40}", resolved_hash):
            raise ValueError("Git did not resolve a commit")
        branch_result = self._git(repo, ["rev-parse", "--verify", f"{branch}^{{commit}}"])
        if branch_result.returncode != 0:
            raise ValueError("unknown integration branch")
        ancestor = self._git(repo, ["merge-base", "--is-ancestor", resolved_hash, branch])
        if ancestor.returncode != 0:
            raise ValueError("commit is not an ancestor of the integration branch")
        return repo, resolved_hash.lower(), str(config.get("package_dir", "")).strip("/\\")

    def record_integrated(self, job_id: str, commit: str) -> dict[str, Any]:
        """Release the core acceptance gate only for a byte-matching reviewed commit."""

        _safe_job_id(job_id)
        job = self._job_by_id(job_id)
        if job["status"] == "INTEGRATED":
            if job["integrated_commit"] != commit:
                raise ValueError("integrated job is frozen to a different commit")
            return job
        if job["status"] != "APPROVED":
            raise ValueError("semantic approval is required before integration")
        if (job["verification"].get("compile_passed") is not True
                or job["verification"].get("transitive_axioms_checked") is not True
                or job["verification"].get("local_proof_holes")
                or not job["review"].get("reviewer")):
            raise ValueError("successful verification and semantic review are required")
        if job["review"].get("manifest_sha256") != job["manifest"].get("manifest_sha256"):
            raise ValueError("review is not for the frozen manifest")
        repo, resolved_commit, package_dir = self._commit_and_branch(job, commit)
        manifest_files = self._manifest_files(job)
        for entry in manifest_files:
            if entry.get("kind") != "source":
                continue
            repository_path = entry.get("repository_path")
            if not isinstance(repository_path, str) or not repository_path:
                repository_path = f"{package_dir}/{entry['path']}" if package_dir else entry["path"]
            repository_path = _relative(repository_path, "repository path")
            shown = self._git(repo, ["show", f"{resolved_commit}:{repository_path}"], text=False)
            if shown.returncode != 0:
                raise ValueError(f"frozen source is missing at commit: {repository_path}")
            data = shown.stdout if isinstance(shown.stdout, bytes) else bytes(shown.stdout)
            snapshot_data = (Path(job["manifest"]["snapshot_root"]) / entry["path"]).read_bytes()
            if data != snapshot_data:
                raise ValueError(f"frozen source does not match commit: {repository_path}")
        audited_names = [target.get("name") for target in job["verification"].get("targets", []) if isinstance(target, dict)]
        gate = {
            "commit": resolved_commit,
            "manifest_sha256": job["manifest"]["manifest_sha256"],
            "audited_targets": audited_names,
            "reviewer": job["review"].get("reviewer"),
            "notes": job["review"].get("notes"),
            "job_id": job_id,
            "source_paths": [entry["path"] for entry in manifest_files if entry.get("kind") == "source"],
        }
        recorder = getattr(self.store, "record_acceptance_gate", None)
        if recorder is None:
            raise RuntimeError("Store.record_acceptance_gate is required before research integration")
        recorder("research:" + job_id, gate)
        with self._transaction() as connection:
            row = connection.execute("SELECT project_id, status, integrated_commit FROM research_jobs WHERE job_id = ?", (job_id,)).fetchone()
            if row is None:
                raise KeyError(job_id)
            if row["status"] == "INTEGRATED":
                if row["integrated_commit"] != resolved_commit:
                    raise ValueError("integration commit changed concurrently")
            elif row["status"] != "APPROVED":
                raise ValueError("job changed while recording acceptance gate")
            else:
                connection.execute("UPDATE research_jobs SET status = 'INTEGRATED', integrated_commit = ?, updated_at = ? WHERE job_id = ?", (resolved_commit, self.clock(), job_id))
                self._event(connection, job_id, row["project_id"], "INTEGRATED", {"commit": resolved_commit, "manifest_sha256": gate["manifest_sha256"]})
        return self._job_by_id(job_id)

    def _stale_base(self, payload: dict[str, Any]) -> str:
        bases = payload.get("baseline_commits")
        if not isinstance(bases, list) or not bases:
            return "UNKNOWN"
        config = self._store_project(payload.get("project_id", "")) if payload.get("project_id") else {}
        repo_value = config.get("repo")
        branch = config.get("integration_branch")
        if not repo_value or not branch:
            return "UNKNOWN"
        try:
            repo = Path(str(repo_value)).resolve()
            current = self._git(repo, ["rev-parse", "--verify", f"{branch}^{{commit}}"])
            if current.returncode != 0:
                return "UNKNOWN"
            current_hash = str(current.stdout).strip()
            for base in bases:
                if not isinstance(base, str) or not _HEX_COMMIT.fullmatch(base):
                    continue
                resolved = self._git(repo, ["rev-parse", "--verify", f"{base}^{{commit}}"])
                if resolved.returncode != 0:
                    continue
                base_hash = str(resolved.stdout).strip()
                if base_hash == current_hash:
                    return "CURRENT"
                return "STALE"
        except Exception:
            return "UNKNOWN"
        return "UNKNOWN"
