"""Compile progress and cooperative resource control; no global mutable budget."""
from __future__ import annotations

from dataclasses import dataclass, field
from math import isfinite
from time import monotonic
from typing import Callable, Protocol

from .errors import CompilationCancelled, SearchBudgetExceeded


class CancellationToken(Protocol):
    """Implemented by threading.Event, multiprocessing.Event and equivalents."""
    def is_set(self) -> bool: ...


@dataclass(frozen=True)
class ProgressEvent:
    """An immutable snapshot, delivered synchronously in the compiling thread."""
    stage: str
    search_states: int
    elapsed_seconds: float

    def to_dict(self) -> dict:
        return {"stage": self.stage, "search_states": self.search_states,
                "elapsed_seconds": self.elapsed_seconds}


@dataclass
class SearchBudget:
    max_states: int | None = 100_000
    max_seconds: float | None = 60.0
    cancel_event: CancellationToken | None = None
    progress: Callable[[ProgressEvent], None] | None = None
    progress_interval: float = 0.25
    states: int = field(default=0, init=False)
    start: float = field(default_factory=monotonic, init=False)
    stage: str = field(default="starting", init=False)
    timings: dict[str, float] = field(default_factory=dict, init=False)
    counters: dict[str, int] = field(default_factory=dict, init=False)
    _last_progress: float = field(default=0.0, init=False)
    _stage_start: float = field(default_factory=monotonic, init=False)
    _in_callback: bool = field(default=False, init=False)

    def __post_init__(self):
        if self.max_states is not None and (isinstance(self.max_states, bool) or
                not isinstance(self.max_states, int) or self.max_states < 1):
            raise ValueError("max_states must be a positive integer or None")
        if self.max_seconds is not None and (isinstance(self.max_seconds, bool) or
                not isinstance(self.max_seconds, (int, float)) or
                not isfinite(self.max_seconds) or self.max_seconds <= 0):
            raise ValueError("max_seconds must be finite and positive or None")
        if (isinstance(self.progress_interval, bool) or
                not isinstance(self.progress_interval, (int, float)) or
                not isfinite(self.progress_interval) or self.progress_interval < 0):
            raise ValueError("progress_interval must be finite and nonnegative")
        if self.progress is not None and not callable(self.progress):
            raise TypeError("progress must be callable or None")
        if self.cancel_event is not None and not callable(getattr(self.cancel_event, "is_set", None)):
            raise TypeError("cancel_event must implement is_set()")

    def snapshot(self, now: float | None = None) -> dict:
        now = monotonic() if now is None else now
        return {"states": self.states, "elapsed_seconds": now - self.start,
                "stage": self.stage, **self.counters}

    def check(self, *, force_progress: bool = False) -> None:
        now = monotonic()
        if self.cancel_event is not None and self.cancel_event.is_set():
            raise CompilationCancelled("Compilation cancelled by caller; no infeasibility conclusion.", self.snapshot(now))
        if ((self.max_states is not None and self.states > self.max_states) or
                (self.max_seconds is not None and now - self.start > self.max_seconds)):
            raise SearchBudgetExceeded(
                "Search budget exhausted; increase it to continue. This is not an infeasibility result.",
                self.snapshot(now))
        if (self.progress is not None and not self._in_callback and
                (force_progress or now - self._last_progress >= self.progress_interval)):
            self._last_progress, self._in_callback = now, True
            try:
                self.progress(ProgressEvent(self.stage, self.states, now - self.start))
            finally:
                self._in_callback = False
            # A callback may set the token or take substantial time. Check it
            # again without recursively delivering progress callbacks.
            if self.cancel_event is not None and self.cancel_event.is_set():
                raise CompilationCancelled("Compilation cancelled by caller; no infeasibility conclusion.", self.snapshot())
            if self.max_seconds is not None and monotonic() - self.start > self.max_seconds:
                raise SearchBudgetExceeded("Time budget exhausted in progress callback; no infeasibility conclusion.", self.snapshot())

    def tick(self, amount: int = 1) -> None:
        if isinstance(amount, bool) or not isinstance(amount, int) or amount < 0:
            raise ValueError("tick amount must be a nonnegative integer")
        self.states += amount
        self.check()

    def set_stage(self, stage: str) -> None:
        now = monotonic()
        self.timings[self.stage] = self.timings.get(self.stage, 0.0) + now - self._stage_start
        self.stage, self._stage_start = stage, now
        self.check(force_progress=True)

    def count(self, key: str, amount: int = 1) -> None:
        self.counters[key] = self.counters.get(key, 0) + amount
