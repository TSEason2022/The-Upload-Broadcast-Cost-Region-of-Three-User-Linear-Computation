"""Stable, catchable library exceptions (also subclasses of familiar builtins)."""
from __future__ import annotations

from typing import Any, Mapping


class CodingError(Exception):
    """Base class for library-specific operational errors."""


class VerificationError(CodingError, ValueError):
    """A certificate, claimed cost or task binding failed exact verification."""


class InputFormatError(CodingError, ValueError):
    """Malformed, oversized or unsupported interchange data."""


class BlocklengthError(CodingError, ValueError):
    """The requested original-field blocklength does not admit the requested code."""


class ConstructionError(CodingError, RuntimeError):
    """An internal construction/theorem consistency invariant failed."""


class SearchBudgetExceeded(CodingError, RuntimeError):
    """A resource stop, NEVER a claim that the task is infeasible."""

    def __init__(self, message: str, stats: Mapping[str, Any]):
        super().__init__(message)
        self.stats = dict(stats)


class CompilationCancelled(CodingError, RuntimeError):
    """The caller's cooperative cancellation signal was set."""

    def __init__(self, message: str, stats: Mapping[str, Any]):
        super().__init__(message)
        self.stats = dict(stats)
