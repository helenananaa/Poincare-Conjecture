"""Small process-shared resource semaphores for the Lean scheduler.

The scheduler has several independently running processes (controllers,
workers, and legacy handoff commands).  A lock per slot makes the resource
limit visible to all of them without a broker or a database.  ``flock`` also
releases a slot if a process is killed, which is important for compiler
capacity: a stale PID must not permanently consume a slot.
"""
from __future__ import annotations

import argparse
import contextlib
import errno
import fcntl
import math
import os
from dataclasses import dataclass
from pathlib import Path
import subprocess
import time
from typing import Iterator, Sequence
import re


_SAFE_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*\Z")
_POLL_SECONDS = 0.02


def _validate_name(name: str) -> str:
    if not isinstance(name, str) or not _SAFE_NAME.fullmatch(name):
        raise ValueError("resource name must contain only letters, digits, '.', '_' or '-'")
    return name


def _validate_limit(limit: int) -> int:
    if isinstance(limit, bool) or not isinstance(limit, int) or limit <= 0:
        raise ValueError("resource limit must be a positive integer")
    return limit


def _validate_timeout(timeout: float | None) -> float | None:
    if timeout is None:
        return None
    if isinstance(timeout, bool) or not isinstance(timeout, (int, float)):
        raise ValueError("resource timeout must be a nonnegative number or None")
    timeout = float(timeout)
    if not math.isfinite(timeout) or timeout < 0:
        raise ValueError("resource timeout must be a nonnegative number or None")
    return timeout


def resource_directory(root: str | Path) -> Path:
    """Return and create the directory containing the slot lock files."""

    directory = Path(root).expanduser().resolve() / "locks" / "resources"
    directory.mkdir(parents=True, exist_ok=True)
    return directory


@dataclass
class Lease:
    """Information about the slot acquired by :func:`slot`."""

    resource: str
    index: int
    waited_seconds: float
    acquired_unix: float


@contextlib.contextmanager
def slot(root: str | Path, resource: str, limit: int,
         timeout: float | None = None) -> Iterator[Lease]:
    """Acquire one process-shared slot for ``resource``.

    ``root`` is the scheduler state root.  Consequently the default
    installation uses ``~/.local/state/lean-swarm/locks/resources`` when the
    controller's state root is the standard one.  Each contender tries every
    slot lock non-blockingly, sleeping only briefly between attempts.  The
    opened descriptor remains alive for the whole context and is closed on
    exit, releasing the flock even when the body raises.
    """

    name = _validate_name(resource)
    count = _validate_limit(limit)
    wait_limit = _validate_timeout(timeout)
    directory = resource_directory(root)
    started = time.monotonic()
    acquired: tuple[int, object] | None = None
    while acquired is None:
        for index in range(count):
            path = directory / f"{name}.{index}.lock"
            stream = path.open("a+")
            try:
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                if exc.errno not in (errno.EACCES, errno.EAGAIN):
                    stream.close()
                    raise
                stream.close()
                continue
            acquired = (index, stream)
            break
        if acquired is not None:
            break
        elapsed = time.monotonic() - started
        if wait_limit is not None and elapsed >= wait_limit:
            raise TimeoutError(f"timed out waiting for {name!r} resource slot")
        remaining = _POLL_SECONDS
        if wait_limit is not None:
            remaining = min(remaining, max(0.0, wait_limit - elapsed))
        time.sleep(remaining)

    index, stream = acquired
    lease = Lease(name, index, time.monotonic() - started, time.time())
    try:
        yield lease
    finally:
        fcntl.flock(stream.fileno(), fcntl.LOCK_UN)
        stream.close()


def run_locked(root: str | Path, resource: str, limit: int,
               command: Sequence[str], timeout: float | None = None) -> int:
    """Run an executable while holding a shared resource slot."""

    if not command:
        raise ValueError("locked command must not be empty")
    with slot(root, resource, limit, timeout=timeout):
        return subprocess.run(list(command), check=False).returncode


def _main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="run one command under a Lean scheduler resource slot")
    parser.add_argument("--root", required=True)
    parser.add_argument("--resource", required=True)
    parser.add_argument("--limit", required=True, type=int)
    parser.add_argument("--timeout", type=float, default=None)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(argv)
    command = list(args.command)
    if command[:1] == ["--"]:
        command = command[1:]
    return run_locked(args.root, args.resource, args.limit, command, timeout=args.timeout)


if __name__ == "__main__":  # pragma: no cover - exercised by generated worker scripts
    raise SystemExit(_main())
