"""Exact, independently checkable encoder/decoder matrix certificates.

Conventions: x is a source column; A_i and W_i are row matrices. Upload
E_i x is locally computable iff E_i=T_i A_i. With E stacked from the E_i,
the relay broadcasts B E x. Decoding is the exact identity
W_i=C_i B E+H_i A_i. No sampled source vectors or floating-point ranks are
used by the verifier.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
from functools import cached_property

from .field import Field
from .linalg import Matrix, coordinates, rank, vstack
from .task import Task


from .errors import VerificationError


@dataclass(frozen=True)
class VerificationReport:
    field_order: int
    source_dimension: int
    upload_count: int
    upload_rank: int
    broadcast_count: int
    broadcast_rank: int
    local_identities: tuple[bool, bool, bool]
    decoder_identities: tuple[bool, bool, bool]

    def to_dict(self):
        return asdict(self)


def _triplet(value, name):
    if not isinstance(value, (list, tuple)) or len(value) != 3:
        raise VerificationError(f"{name} must contain exactly three matrices")
    if any(not isinstance(m, Matrix) for m in value):
        raise VerificationError(f"{name} must contain Matrix objects")


def _matrix_shape(matrix, field, rows, columns, name):
    if not isinstance(matrix, Matrix):
        raise VerificationError(f"{name} is not a Matrix")
    if matrix.field != field or matrix.shape != (rows, columns):
        raise VerificationError(f"{name} must have shape {(rows, columns)} over {field!r}")


def _count(value, name):
    if value is not None and (not isinstance(value, int) or isinstance(value, bool) or value < 0):
        raise VerificationError(f"{name} must be a nonnegative integer")


def verify_certificate(task, uploads, B, decoderC, decoderH, localT,
                       expected_upload_count=None, expected_broadcast_count=None):
    """Verify every encoding and decoding identity, raising on any mismatch.

    If an expected cost is supplied, both the literal transmitted row count
    and the resulting signal rank must equal it. Without expected costs,
    valid but redundant transmissions are accepted and reported accurately.
    A verified feasible code alone does not establish global optimality;
    expected costs must come from separately justified bounds.
    """
    if not isinstance(task, Task):
        raise VerificationError("task must be a Task")
    for value, name in ((uploads, "uploads"), (decoderC, "decoderC"),
                        (decoderH, "decoderH"), (localT, "localT")):
        _triplet(value, name)
    _count(expected_upload_count, "expected_upload_count")
    _count(expected_broadcast_count, "expected_broadcast_count")
    field = task.field
    for i in range(3):
        _matrix_shape(uploads[i], field, uploads[i].nrows, task.n, f"E_{i}")
        _matrix_shape(localT[i], field, uploads[i].nrows, task.side[i].nrows, f"T_{i}")
        if localT[i] @ task.side[i] != uploads[i]:
            raise VerificationError(f"local generation identity E_{i}=T_{i} A_{i} failed")
    stacked = vstack(*uploads)
    if not isinstance(B, Matrix):
        raise VerificationError("B must be a Matrix")
    _matrix_shape(B, field, B.nrows, stacked.nrows, "B")
    broadcast = B @ stacked
    for i in range(3):
        _matrix_shape(decoderC[i], field, task.demand[i].nrows, B.nrows, f"C_{i}")
        _matrix_shape(decoderH[i], field, task.demand[i].nrows, task.side[i].nrows, f"H_{i}")
        if decoderC[i] @ broadcast + decoderH[i] @ task.side[i] != task.demand[i]:
            raise VerificationError(f"zero-error decoding identity failed for user {i}")
    upload_rank, broadcast_rank = rank(stacked), rank(broadcast)
    if expected_upload_count is not None:
        if stacked.nrows != expected_upload_count:
            raise VerificationError(f"upload row count is {stacked.nrows}, expected {expected_upload_count}")
        if upload_rank != expected_upload_count:
            raise VerificationError(f"upload rank is {upload_rank}, expected {expected_upload_count}")
    if expected_broadcast_count is not None:
        if B.nrows != expected_broadcast_count:
            raise VerificationError(f"broadcast row count is {B.nrows}, expected {expected_broadcast_count}")
        if broadcast_rank != expected_broadcast_count:
            raise VerificationError(f"broadcast rank is {broadcast_rank}, expected {expected_broadcast_count}")
    return VerificationReport(field.q, task.n, stacked.nrows, upload_rank,
                              B.nrows, broadcast_rank, (True, True, True), (True, True, True))


@dataclass(frozen=True)
class CodeCertificate:
    task: Task
    uploads: tuple[Matrix, Matrix, Matrix]
    broadcast: Matrix
    local_maps: tuple[Matrix, Matrix, Matrix]
    decoders: tuple[Matrix, Matrix, Matrix]
    side_decoders: tuple[Matrix, Matrix, Matrix]
    blocklength: int = 1
    base_field: Field | None = None

    def __post_init__(self):
        if not isinstance(self.blocklength, int) or isinstance(self.blocklength, bool) or self.blocklength < 1:
            raise VerificationError("blocklength must be a positive integer")
        if self.base_field is None:
            object.__setattr__(self, "base_field", self.task.field)
        if not isinstance(self.base_field, Field):
            raise VerificationError("base_field must be a Field")
        if self.base_field.p != self.task.field.p:
            raise VerificationError("base_field and code field must have the same characteristic")
        # Freeze outer collections too; Matrix itself is immutable.
        for name in ("uploads", "local_maps", "decoders", "side_decoders"):
            object.__setattr__(self, name, tuple(getattr(self, name)))

    @property
    def B(self):
        return self.broadcast

    @cached_property
    def stacked_upload(self):
        return vstack(*self.uploads)

    @cached_property
    def signal(self):
        return self.broadcast @ self.stacked_upload

    def verify(self, expected_upload_count=None, expected_broadcast_count=None):
        return verify_certificate(self.task, self.uploads, self.broadcast, self.decoders,
                                  self.side_decoders, self.local_maps,
                                  expected_upload_count, expected_broadcast_count)

    def to_dict(self):
        self.verify()
        def matrix(m):
            return {"rows": m.to_list(), "ncols": m.ncols}
        return {
            "schema": "three-user-linear-code-v1",
            "field": self.task.field.to_dict(),
            "base_field": self.base_field.to_dict(),
            "blocklength": self.blocklength,
            "side": [matrix(m) for m in self.task.side],
            "demand": [matrix(m) for m in self.task.demand],
            "uploads": [matrix(m) for m in self.uploads],
            "broadcast": matrix(self.broadcast),
            "local_maps": [matrix(m) for m in self.local_maps],
            "decoders": [matrix(m) for m in self.decoders],
            "side_decoders": [matrix(m) for m in self.side_decoders],
        }

    @classmethod
    def from_dict(cls, data):
        if not isinstance(data, dict) or data.get("schema") != "three-user-linear-code-v1":
            raise VerificationError("unsupported certificate schema")
        try:
            field = Field.from_dict(data["field"])
            def matrix(value):
                return Matrix(field, value["rows"], ncols=value["ncols"])
            def matrices(name):
                return tuple(matrix(value) for value in data[name])
            task = Task(field, matrices("side"), matrices("demand"))
            certificate = cls(task, matrices("uploads"), matrix(data["broadcast"]),
                              matrices("local_maps"), matrices("decoders"),
                              matrices("side_decoders"), data["blocklength"],
                              Field.from_dict(data["base_field"]))
            certificate.verify()
            return certificate
        except (KeyError, TypeError, ValueError, IndexError) as exc:
            if isinstance(exc, VerificationError):
                raise
            raise VerificationError(f"invalid certificate: {exc}") from exc


def make_certificate(task, uploads, B, *, blocklength=1, base_field=None,
                     expected_upload_count=None, expected_broadcast_count=None):
    """Solve for local/decoder maps and return a fully verified certificate.

    ``task`` is the already lifted task.  Blocklength and base_field are
    provenance metadata, not a request to lift its matrices automatically.
    Decoder solving handles redundant row representations exactly.
    """
    _triplet(uploads, "uploads")
    if not isinstance(task, Task):
        raise VerificationError("task must be a Task")
    field = task.field
    for i, upload in enumerate(uploads):
        _matrix_shape(upload, field, upload.nrows, task.n, f"E_{i}")
    stacked = vstack(*uploads)
    if not isinstance(B, Matrix):
        raise VerificationError("B must be a Matrix")
    _matrix_shape(B, field, B.nrows, stacked.nrows, "B")
    signal = B @ stacked
    local, decoders, side_decoders = [], [], []
    for i in range(3):
        try:
            local.append(coordinates(uploads[i], task.side[i]))
            coefficients = coordinates(task.demand[i], vstack(signal, task.side[i]))
        except ValueError as exc:
            raise VerificationError(f"cannot construct local or decoding map for user {i}: {exc}") from exc
        # Slices of an exact, validated solution contain field elements already.
        decoders.append(Matrix._from_validated(
            field, (row[:B.nrows] for row in coefficients.rows), B.nrows))
        side_decoders.append(Matrix._from_validated(
            field, (row[B.nrows:] for row in coefficients.rows), task.side[i].nrows))
    certificate = CodeCertificate(task, tuple(uploads), B, tuple(local), tuple(decoders),
                                  tuple(side_decoders), blocklength, base_field)
    certificate.verify(expected_upload_count, expected_broadcast_count)
    return certificate


def restrict_matrix_to_prime(matrix):
    """Expand every coefficient into its multiplication matrix over GF(p).

    Ordering is [coordinate 0..k-1 of element 0, then element 1, ...].
    Each block's j-th column is the polynomial-basis expansion of a*p**j.
    This is field multiplication, never reduction modulo the field order.
    """
    field, degree = matrix.field, matrix.field.degree
    prime = Field(field.p)
    cache = {}
    for value in set(value for row in matrix.rows for value in row):
        columns = []
        for j in range(degree):
            element = field.mul(value, field.p ** j)
            digits = []
            for _ in range(degree):
                digits.append(element % field.p)
                element //= field.p
            columns.append(digits)
        cache[value] = [[columns[j][i] for j in range(degree)] for i in range(degree)]
    rows = []
    for row in matrix.rows:
        for i in range(degree):
            rows.append([entry for value in row for entry in cache[value][i]])
    return Matrix(prime, rows, ncols=matrix.ncols * degree)


def restrict_certificate_to_prime(certificate):
    """Restrict a code over GF(p**k) to GF(p), multiplying blocklength by k.

    The input's blocklength must be measured over its coefficient field:
    base_field == task.field. Returned matrices use element-major source
    coordinates; convert explicitly if a consumer uses instance-major order.
    Exact maps are reconstructed for the canonical row bases of the new Task.
    """
    if not isinstance(certificate, CodeCertificate):
        raise TypeError("certificate must be a CodeCertificate")
    certificate.verify()
    if certificate.base_field != certificate.task.field:
        raise VerificationError("restriction requires blocklength metadata measured over the coefficient field")
    degree, prime = certificate.task.field.degree, Field(certificate.task.field.p)
    task = Task(prime, tuple(restrict_matrix_to_prime(m) for m in certificate.task.side),
                tuple(restrict_matrix_to_prime(m) for m in certificate.task.demand))
    return make_certificate(task, tuple(restrict_matrix_to_prime(m) for m in certificate.uploads),
                            restrict_matrix_to_prime(certificate.broadcast),
                            blocklength=certificate.blocklength * degree, base_field=prime)
