"""Distributed execution using the user's original measurement conventions.

Certificates use canonical row bases; actual sensors/applications may present
redundant measurements and demand output rows in a particular order. This
adapter restores those conventions exactly, without the source being available
to an encoder or the relay.
"""
from __future__ import annotations

from dataclasses import dataclass, field as dataclass_field
from typing import Iterable, Iterator, Sequence

from .certificate import CodeCertificate, VerificationError
from .linalg import Matrix, contains, coordinates, lift, vstack
from .task import Task


@dataclass(frozen=True)
class OperatingCode:
    """A code executing on original observations and delivering original rows.

    ``certificate`` must already use the original task's field and the source
    order (instance 0 source coordinates, instance 1 source coordinates, ...).
    For L instances, user i supplies L*original_side[i].nrows observation rows,
    in the same instance-major order. Each Matrix column is an independent
    complete block; thus one call can process one or many source blocks.

    Construction re-solves exact identities against the original, potentially
    redundant row matrices. It does not modify or resynthesize the code.
    """
    certificate: CodeCertificate
    original_task: Task
    original_side: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False)
    original_demand: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False)
    original_local_maps: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False)
    original_decoders: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False)
    original_side_decoders: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False)

    def __post_init__(self):
        if not isinstance(self.certificate, CodeCertificate) or not isinstance(self.original_task, Task):
            raise TypeError("OperatingCode requires a CodeCertificate and a Task")
        self.certificate.verify()
        cert, task = self.certificate, self.original_task
        if cert.task.field != task.field or cert.base_field != task.field:
            raise VerificationError("runtime requires a certificate already represented over the original task field")
        if cert.task.n != task.n * cert.blocklength:
            raise VerificationError("certificate source dimension does not match original task times blocklength")
        side = tuple(lift(a, cert.blocklength) for a in task.original_side)
        demand = tuple(lift(w, cert.blocklength) for w in task.original_demand)
        for i in range(3):
            for original, canonical, name in ((side[i], cert.task.side[i], "side"),
                                               (demand[i], cert.task.demand[i], "demand")):
                if not contains(original, canonical) or not contains(canonical, original):
                    raise VerificationError(f"original {name} subspace for user {i} differs from the certificate")
        local, decoders, retained = [], [], []
        signal, B = cert.signal, cert.broadcast
        for i in range(3):
            if side[i] == cert.task.side[i] and demand[i] == cert.task.demand[i]:
                local.append(cert.local_maps[i])
                decoders.append(cert.decoders[i])
                retained.append(cert.side_decoders[i])
                continue
            try:
                local.append(coordinates(cert.uploads[i], side[i]))
                coefficients = coordinates(demand[i], vstack(signal, side[i]))
            except ValueError as exc:
                raise VerificationError(f"cannot recover original user {i} conventions: {exc}") from exc
            decoders.append(Matrix._from_validated(
                task.field, (row[:B.nrows] for row in coefficients.rows), B.nrows))
            retained.append(Matrix._from_validated(
                task.field, (row[B.nrows:] for row in coefficients.rows), side[i].nrows))
        for name, value in (("original_side", side), ("original_demand", demand),
                            ("original_local_maps", tuple(local)),
                            ("original_decoders", tuple(decoders)),
                            ("original_side_decoders", tuple(retained))):
            object.__setattr__(self, name, value)
        # The immutable certificate was fully verified before adapting its maps.
        self._verify_original_identities()

    def verify(self):
        """Verify identities in the original measurement and output row order."""
        self.certificate.verify()
        return self._verify_original_identities()

    def _verify_original_identities(self):
        signal = self.certificate.signal
        for i in range(3):
            if self.original_local_maps[i] @ self.original_side[i] != self.certificate.uploads[i]:
                raise VerificationError(f"original local generation identity failed for user {i}")
            if (self.original_decoders[i] @ signal
                    + self.original_side_decoders[i] @ self.original_side[i]
                    != self.original_demand[i]):
                raise VerificationError(f"original demand decoding identity failed for user {i}")
        return True

    @staticmethod
    def _user(user):
        if not isinstance(user, int) or isinstance(user, bool) or user not in range(3):
            raise ValueError("user index must be 0, 1 or 2")

    def _values(self, value, rows, label):
        if not isinstance(value, Matrix):
            raise TypeError(f"{label} must be a Matrix with source blocks as columns")
        if value.field != self.original_task.field:
            raise ValueError(f"{label} uses a different finite field")
        if value.nrows != rows:
            raise ValueError(f"{label} has {value.nrows} rows, expected {rows}")

    def encode_upload(self, user: int, observations: Matrix) -> Matrix:
        """A single user encodes from its own observations only."""
        self._user(user)
        self._values(observations, self.original_side[user].nrows, f"user {user} observations")
        return self.original_local_maps[user] @ observations

    def encode_uploads(self, observations: Sequence[Matrix]) -> tuple[Matrix, Matrix, Matrix]:
        """Convenience batch of three independent local-encoder calls."""
        if not isinstance(observations, (list, tuple)) or len(observations) != 3:
            raise ValueError("observations must contain three Matrix objects")
        outputs = tuple(self.encode_upload(i, observations[i]) for i in range(3))
        if len({values.ncols for values in outputs}) != 1:
            raise ValueError("the three observations must contain the same number of source blocks")
        return outputs

    def broadcast(self, uploads: Sequence[Matrix]) -> Matrix:
        """The relay uses uploaded values only; returns its common message."""
        if not isinstance(uploads, (list, tuple)) or len(uploads) != 3:
            raise ValueError("uploads must contain three Matrix objects")
        for i in range(3):
            self._values(uploads[i], self.certificate.uploads[i].nrows, f"user {i} upload")
        if len({values.ncols for values in uploads}) != 1:
            raise ValueError("the three uploads must contain the same number of source blocks")
        return self.certificate.broadcast @ vstack(*uploads)

    def decode(self, user: int, side_values: Matrix, broadcast_values: Matrix) -> Matrix:
        """Recover original demand rows from local and broadcast values only."""
        self._user(user)
        self._values(side_values, self.original_side[user].nrows, f"user {user} observations")
        self._values(broadcast_values, self.certificate.broadcast.nrows, "broadcast")
        if side_values.ncols != broadcast_values.ncols:
            raise ValueError("local observations and broadcast must contain the same number of source blocks")
        return (self.original_decoders[user] @ broadcast_values
                + self.original_side_decoders[user] @ side_values)


    def decode_all(self, observations: Sequence[Matrix], signal: Matrix) -> tuple[Matrix, Matrix, Matrix]:
        """Decode three users without introducing any access to the source."""
        if not isinstance(observations, (list, tuple)) or len(observations) != 3:
            raise ValueError("observations must contain three Matrix objects")
        return tuple(self.decode(i, observations[i], signal) for i in range(3))

    def execute(self, observations: Sequence[Matrix]) -> ExecutionResult:
        """Run one batch from local observations only, retaining intermediate messages."""
        uploads = self.encode_uploads(observations)
        signal = self.broadcast(uploads)
        return ExecutionResult(uploads, signal, self.decode_all(observations, signal))

    def iter_execute(self, batches: Iterable[Sequence[Matrix]]) -> Iterator[ExecutionResult]:
        """Lazy execution: consume and return one observation batch at a time.

        No source samples are synthesized, no input sequence is materialized,
        and the adapter does not retain previously yielded batches.
        """
        for observations in batches:
            yield self.execute(observations)


@dataclass(frozen=True)
class ExecutionResult:
    uploads: tuple[Matrix, Matrix, Matrix]
    broadcast: Matrix
    decoded: tuple[Matrix, Matrix, Matrix]
