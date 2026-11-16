"""Bounded, strict JSON interchange with verified original-row provenance.

New writers use compiled-code v2. Legacy v1 readers remain available explicitly
for migration. Embedded SHA-256 detects representation changes, not malicious
re-signing: pass a separately trusted expected_fingerprint to pin an input.
"""
from __future__ import annotations

import json
from math import isfinite
import os
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

from .certificate import CodeCertificate, VerificationReport
from .compiler import CompileResult
from .errors import InputFormatError, VerificationError
from .field import Field
from .linalg import Matrix, lift
from .profile import broadcast_profile
from .provenance import task_fingerprint
from .task import Task
from .upload_bound import upload_cost


@dataclass(frozen=True)
class ReadLimits:
    """Conservative deserialization bounds, overridable for trusted large inputs.

    These limit stored matrix cells and the expanded certificate matrices used
    during verification, not the complexity of subsequent algebra. For compiled
    code, max_cells applies to the input task and certificate together.
    Do not expose unrestricted compilation directly to untrusted clients.
    """
    max_bytes: int = 32 * 1024 * 1024
    max_cells: int = 4_000_000
    max_rows: int = 100_000
    max_columns: int = 100_000
    max_blocklength: int = 4096

    def __post_init__(self):
        for name in ("max_bytes", "max_cells", "max_rows", "max_columns", "max_blocklength"):
            value = getattr(self, name)
            if isinstance(value, bool) or not isinstance(value, int) or value < 1:
                raise ValueError(f"{name} must be a positive integer")


DEFAULT_LIMITS = ReadLimits()


def fraction_dict(value: Fraction | int) -> dict[str, int]:
    value = Fraction(value)
    return {"numerator": value.numerator, "denominator": value.denominator}


def _fraction(value):
    if not isinstance(value, dict):
        raise InputFormatError("cost must be an exact numerator/denominator object")
    a, b = value.get("numerator"), value.get("denominator")
    if any(not isinstance(v, int) or isinstance(v, bool) for v in (a, b)) or b <= 0:
        raise InputFormatError("cost requires integer numerator and positive integer denominator")
    return Fraction(a, b)


def _nonnegative(value, label, upper):
    if isinstance(value, bool) or not isinstance(value, int) or not 0 <= value <= upper:
        raise InputFormatError(f"{label} must be an integer in [0, {upper}]")
    return value


def _rows(value, width, limits, label):
    if not isinstance(value, (list, tuple)) or len(value) > limits.max_rows:
        raise InputFormatError(f"{label} must be a row array within max_rows")
    if len(value) * width > limits.max_cells:
        raise InputFormatError(f"{label} exceeds max_cells")
    for row in value:
        if not isinstance(row, (list, tuple)) or len(row) != width:
            raise InputFormatError(f"{label} has an invalid row or row width")
    return len(value) * width


def _triplet(value, label):
    if not isinstance(value, (list, tuple)) or len(value) != 3:
        raise InputFormatError(f"{label} must contain exactly three matrices")
    return value


def task_to_dict(task: Task) -> dict[str, Any]:
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    return {"schema": "three-user-task-v1", "field": task.field.to_dict(), "n": task.n,
            "side": [m.to_list() for m in task.original_side],
            "demand": [m.to_list() for m in task.original_demand]}


def task_from_dict(data: dict, *, limits: ReadLimits = DEFAULT_LIMITS) -> Task:
    try:
        if not isinstance(data, dict):
            raise InputFormatError("task JSON must be an object")
        if data.get("schema", "three-user-task-v1") != "three-user-task-v1":
            raise InputFormatError("unsupported task schema")
        n = _nonnegative(data["n"], "n", limits.max_columns)
        if "q" in data and "field" in data:
            raise InputFormatError("provide q or field, not both")
        side = _triplet(data["side"], "side")
        demand = _triplet(data["demand"], "demand")
        total = sum(_rows(rows, n, limits, "task matrix") for rows in (*side, *demand))
        if total > limits.max_cells:
            raise InputFormatError("task exceeds total max_cells")
        field = Field.from_dict(data["field"]) if "field" in data else Field(data["q"])
        return Task(field, tuple(Matrix(field, r, ncols=n) for r in side),
                    tuple(Matrix(field, r, ncols=n) for r in demand))
    except (KeyError, TypeError, ValueError, AttributeError, OverflowError) as exc:
        if isinstance(exc, InputFormatError):
            raise
        raise InputFormatError(f"invalid task: {exc}") from exc


def verify_result(result: CompileResult, original_task: Task) -> VerificationReport:
    """Verify original representation, identities AND the two cost formulas.

    Feasibility is established by exact identities. Global optimality still
    relies on the manuscript's theorem, not on a formal proof checker.
    Legacy in-memory results without a fingerprint bind only rowspace semantics.
    """
    if not isinstance(result, CompileResult) or not isinstance(original_task, Task):
        raise TypeError("verify_result requires a CompileResult and a Task")
    c = result.certificate
    if not isinstance(c, CodeCertificate):
        raise VerificationError("result must contain a CodeCertificate")
    if result.input_fingerprint is not None and result.input_fingerprint != task_fingerprint(original_task):
        raise VerificationError("original task representation fingerprint does not match")
    if c.task.field != original_task.field or c.base_field != original_task.field:
        raise VerificationError("certificate field does not match the original task")
    # Check metadata BEFORE expansion. Canonical rows suffice for binding and
    # avoid allocating redundant original measurement rows during verification.
    if c.task.n != original_task.n * c.blocklength:
        raise VerificationError("certificate source dimension does not match blocklength")
    side = tuple(lift(a, c.blocklength) for a in original_task.side)
    demand = tuple(lift(w, c.blocklength) for w in original_task.demand)
    if c.task.side != side or c.task.demand != demand:
        raise VerificationError("certificate does not represent the supplied original task")
    U = upload_cost(original_task)
    D = broadcast_profile(original_task.side, original_task.augmented).cost
    if U != result.upload_optimum or D != result.broadcast_optimum:
        raise VerificationError("claimed optimal costs do not match the recomputed formulas")
    u, d = U*c.blocklength, D*c.blocklength
    if u.denominator != 1 or d.denominator != 1:
        raise VerificationError("claimed blocklength does not clear rate denominators")
    return c.verify(int(u), int(d))


def result_to_dict(result: CompileResult, original_task: Task) -> dict[str, Any]:
    report = verify_result(result, original_task)
    return {"schema": "three-user-compiled-code-v2", "input_task": task_to_dict(original_task),
            "input_fingerprint": task_fingerprint(original_task),
            "upload_optimum": fraction_dict(result.upload_optimum),
            "broadcast_optimum": fraction_dict(result.broadcast_optimum),
            "strategy": result.strategy, "stats": dict(result.stats),
            "verification": report.to_dict(), "certificate": result.certificate.to_dict()}


def _certificate_limits(data, original, limits):
    if not isinstance(data, dict):
        raise InputFormatError("certificate must be an object")
    if data.get("schema") != "three-user-linear-code-v1":
        raise VerificationError("unsupported certificate schema")
    if (Field.from_dict(data["field"]) != original.field
            or Field.from_dict(data["base_field"]) != original.field):
        raise VerificationError("certificate field does not match the original task")
    length = _nonnegative(data["blocklength"], "blocklength", limits.max_blocklength)
    if length == 0:
        raise InputFormatError("blocklength must be positive")
    # Count the complete interchange object, rather than permitting each part
    # independently to consume the full input budget.
    total = sum(m.nrows * m.ncols for m in original.original_side + original.original_demand)
    shapes = {}
    for name in ("side", "demand", "uploads", "local_maps", "decoders", "side_decoders"):
        shapes[name] = []
        for value in _triplet(data[name], name):
            if not isinstance(value, dict):
                raise InputFormatError(f"{name} entry must be a matrix object")
            width = _nonnegative(value["ncols"], "ncols", limits.max_columns)
            total += _rows(value["rows"], width, limits, name)
            shapes[name].append((len(value["rows"]), width))
    value = data["broadcast"]
    if not isinstance(value, dict):
        raise InputFormatError("broadcast must be a matrix object")
    width = _nonnegative(value["ncols"], "broadcast ncols", limits.max_columns)
    total += _rows(value["rows"], width, limits, "broadcast")
    if total > limits.max_cells:
        raise InputFormatError("compiled code exceeds total max_cells")
    source_width = original.n * length
    upload_rows = sum(rows for rows, _ in shapes["uploads"])
    broadcast_rows = len(value["rows"])
    if source_width > limits.max_columns or upload_rows > limits.max_rows:
        raise InputFormatError("expanded certificate exceeds dimension limits")
    # B and E may both be small while their product is enormous: for example
    # B has shape (r, 1) and E has shape (1, n). Bound the materialized signal
    # before CodeCertificate.from_dict invokes its exact identity verifier.
    if upload_rows * source_width > limits.max_cells or broadcast_rows * source_width > limits.max_cells:
        raise InputFormatError("expanded certificate signal exceeds max_cells")
    expanded_cells = 0
    for matrix in original.side + original.demand:
        expanded_cells += matrix.nrows * matrix.ncols * length * length
        if matrix.nrows * length > limits.max_rows:
            raise InputFormatError("expanded original task exceeds read limits")
    if expanded_cells > limits.max_cells:
        raise InputFormatError("expanded original task exceeds total max_cells")
    # Bind dimensions before allocating lifted tasks or doing matrix products.
    # Writers serialize canonical task bases, so their row counts are known.
    def require_shape(actual, expected, label):
        if actual != expected:
            raise VerificationError(f"{label} has shape {actual}, expected {expected}")
    require_shape((broadcast_rows, width), (broadcast_rows, upload_rows), "broadcast")
    for i in range(3):
        side_rows = original.side[i].nrows * length
        demand_rows = original.demand[i].nrows * length
        local_rows = shapes["uploads"][i][0]
        for name, expected in (
                ("side", (side_rows, source_width)),
                ("demand", (demand_rows, source_width)),
                ("uploads", (local_rows, source_width)),
                ("local_maps", (local_rows, side_rows)),
                ("decoders", (demand_rows, broadcast_rows)),
                ("side_decoders", (demand_rows, side_rows))):
            require_shape(shapes[name][i], expected, f"{name}[{i}]")


def result_from_dict(data: dict, *, allow_legacy: bool = True,
                     expected_fingerprint: str | None = None,
                     limits: ReadLimits = DEFAULT_LIMITS) -> tuple[CompileResult, Task]:
    try:
        if not isinstance(data, dict):
            raise InputFormatError("compiled-code JSON must be an object")
        schema = data.get("schema")
        if schema not in ("three-user-compiled-code-v1", "three-user-compiled-code-v2"):
            raise InputFormatError("unsupported compiled-code schema")
        if schema.endswith("v1") and not allow_legacy:
            raise InputFormatError("legacy v1 code is disabled; migrate to v2")
        original = task_from_dict(data["input_task"], limits=limits)
        digest = task_fingerprint(original)
        fingerprint = None
        if schema.endswith("v2"):
            fingerprint = data.get("input_fingerprint")
            if not isinstance(fingerprint, str) or fingerprint != digest:
                raise VerificationError("original task representation fingerprint does not match")
        if expected_fingerprint is not None and expected_fingerprint != digest:
            raise VerificationError("input does not match the separately trusted fingerprint")
        _certificate_limits(data["certificate"], original, limits)
        if not isinstance(data.get("stats", {}), dict) or not isinstance(data.get("strategy", "imported"), str):
            raise InputFormatError("stats must be an object and strategy must be text")
        result = CompileResult(CodeCertificate.from_dict(data["certificate"]),
                               _fraction(data["upload_optimum"]), _fraction(data["broadcast_optimum"]),
                               data.get("strategy", "imported"), dict(data.get("stats", {})), fingerprint)
        # Stored verification summaries are advisory, never trusted.
        verify_result(result, original)
        return result, original
    except (KeyError, TypeError, ValueError, AttributeError, IndexError, OverflowError) as exc:
        if isinstance(exc, (InputFormatError, VerificationError)):
            raise
        raise InputFormatError(f"invalid compiled code: {exc}") from exc


def _unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise InputFormatError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_constant(value):
    raise InputFormatError(f"invalid JSON number: {value}")


def _finite_float(value):
    result = float(value)
    if not isfinite(result):
        raise InputFormatError(f"nonfinite JSON number: {value}")
    return result


def loads_json(text: str | bytes, *, limits: ReadLimits = DEFAULT_LIMITS):
    """Strict, duplicate-key-rejecting, finite-number-only bounded JSON parser."""
    if not isinstance(text, (str, bytes)):
        raise TypeError("JSON input must be str or bytes")
    try:
        if len(text) > limits.max_bytes or (isinstance(text, str) and len(text.encode("utf-8")) > limits.max_bytes):
            raise InputFormatError("JSON input exceeds max_bytes")
        return json.loads(text, object_pairs_hook=_unique_object, parse_constant=_reject_constant, parse_float=_finite_float)
    except (ValueError, RecursionError) as exc:
        if isinstance(exc, InputFormatError):
            raise
        raise InputFormatError(f"invalid JSON: {exc}") from exc


def read_json(path: str | os.PathLike, *, limits: ReadLimits = DEFAULT_LIMITS):
    with open(path, "rb") as stream:
        text = stream.read(limits.max_bytes + 1)
    return loads_json(text, limits=limits)


def write_json(path: str | os.PathLike, data) -> None:
    """Atomic same-directory replacement; old file survives serialization failure.

    The file is flushed/fsynced before rename. Atomic visibility is not a claim
    of full power-loss durability on every filesystem or operating system.
    """
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix="."+path.name+".", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as stream:
            json.dump(data, stream, ensure_ascii=False, indent=2, allow_nan=False)
            stream.write("\n")
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def load_task(path: str | os.PathLike, *, limits: ReadLimits = DEFAULT_LIMITS) -> Task:
    return task_from_dict(read_json(path, limits=limits), limits=limits)


def save_task(task: Task, path: str | os.PathLike) -> None:
    write_json(path, task_to_dict(task))


def load_code(path: str | os.PathLike, *, expected_fingerprint: str | None = None,
              allow_legacy: bool = True, limits: ReadLimits = DEFAULT_LIMITS) -> tuple[CompileResult, Task]:
    return result_from_dict(read_json(path, limits=limits), expected_fingerprint=expected_fingerprint,
                            allow_legacy=allow_legacy, limits=limits)


def save_code(result: CompileResult, task: Task, path: str | os.PathLike) -> None:
    write_json(path, result_to_dict(result, task))
