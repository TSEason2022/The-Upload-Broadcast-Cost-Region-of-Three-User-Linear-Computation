"""Compile-local cooperative checkpoints, isolated across nested calls/threads."""
from __future__ import annotations

from contextvars import ContextVar
from typing import Callable

_checker: ContextVar[Callable[[], None] | None] = ContextVar("three_user_codes_checker", default=None)


def checkpoint() -> None:
    check = _checker.get()
    if check is not None:
        check()
