"""Small, dependency-free policy helpers for the proof scheduler."""

from __future__ import annotations

import re
from typing import Any


LUNA_MODEL = "gpt-5.6-luna"
ALLOWED_EFFORTS = frozenset(("high", "xhigh", "max"))
SQLITE_MAX_INTEGER = 2**63 - 1


def parse_limit(value: Any) -> int:
    """Parse a model limit; zero is the scheduler's unlimited sentinel."""

    if isinstance(value, bool):
        raise ValueError("limit must be a nonnegative integer")
    if value is None:
        return 0
    if isinstance(value, str):
        normalized = value.strip().lower()
        if normalized in {"unlimited", "none", "0"}:
            return 0
        if not re.fullmatch(r"[0-9]+", normalized):
            raise ValueError("limit must be a nonnegative integer")
        value = int(normalized, 10)
    elif not isinstance(value, int):
        raise ValueError("limit must be a nonnegative integer")
    if value < 0 or value > SQLITE_MAX_INTEGER:
        raise ValueError("limit must be a SQLite-safe nonnegative integer")
    return value


def resolve_effort(task: dict[str, Any], config: dict[str, Any] | None = None) -> str:
    """Resolve the Luna reasoning effort without silently weakening a request."""

    if not isinstance(task, dict):
        raise ValueError("task must be a dict")
    if config is None:
        config = {}
    if not isinstance(config, dict):
        raise ValueError("config must be a dict")
    if "luna_model" in config and config["luna_model"] != LUNA_MODEL:
        raise ValueError(f"config luna_model must be exactly {LUNA_MODEL!r}")

    if "reasoning_effort" in task:
        effort = task["reasoning_effort"]
        if not isinstance(effort, str) or effort not in ALLOWED_EFFORTS:
            raise ValueError("reasoning_effort must be one of high, xhigh, max")
        return effort

    difficulty = task.get("difficulty")
    defaults = {"integration": "high", "proof": "xhigh", "foundation": "max"}
    if isinstance(difficulty, str) and difficulty in defaults:
        return defaults[difficulty]

    if "luna_reasoning_effort" in config:
        effort = config["luna_reasoning_effort"]
        if not isinstance(effort, str) or effort not in ALLOWED_EFFORTS:
            raise ValueError("config luna_reasoning_effort must be one of high, xhigh, max")
        return effort
    return "high"
