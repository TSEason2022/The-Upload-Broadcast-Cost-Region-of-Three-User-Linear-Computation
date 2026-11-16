"""Canonical original-representation fingerprints, not digital signatures."""
from __future__ import annotations

import hashlib
import json

from .task import Task


def task_fingerprint(task: Task) -> str:
    """SHA-256 of field representation, width and original rows in original order.

    Redundant rows and row order matter; JSON whitespace and key order do not.
    For authenticity, compare against a separately trusted fingerprint. A digest
    stored alongside an untrusted task can be recomputed by an attacker.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    value = {"schema": "three-user-task-v1", "field": task.field.to_dict(), "n": task.n,
             "side": [m.to_list() for m in task.original_side],
             "demand": [m.to_list() for m in task.original_demand]}
    raw = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False)
    return hashlib.sha256(raw.encode("ascii")).hexdigest()
