"""Deterministic exact linear algebra over :class:`~.field.Field`.

Subspaces are represented by row bases; ``nullspace(A)`` returns a *row*
basis N satisfying A @ N.T = 0. Zero-dimensional matrices retain their
ambient width. Gaussian elimination uses exact field pivots, never numerical
tolerances or floating point arithmetic.
"""
from __future__ import annotations

from dataclasses import dataclass, field as dataclass_field
from typing import Iterable, Iterator

from .field import Field, _integer
from ._kernels import Echelon, pack_binary, unpack_binary, reciprocal, row_operations
from ._resources import checkpoint


def _size(n: int, name: str) -> int:
    n = _integer(n, name)
    if n < 0:
        raise ValueError(f"{name} must be nonnegative")
    return n


@dataclass(frozen=True, slots=True, init=False)
class Matrix:
    field: Field
    rows: tuple[tuple[int, ...], ...]
    ncols: int
    _rref_data: object = dataclass_field(default=None, repr=False, compare=False)
    _rank_data: int | None = dataclass_field(default=None, repr=False, compare=False)
    _binary_data: tuple[int, ...] | None = dataclass_field(default=None, repr=False, compare=False)
    _coordinate_data: object = dataclass_field(default=None, repr=False, compare=False)

    def __init__(self, field: Field, rows: Iterable[Iterable[int]], ncols: int | None = None):
        if not isinstance(field, Field):
            raise TypeError("field must be a Field")
        rows = tuple(tuple(field.validate(v) for v in row) for row in rows)
        if ncols is None:
            ncols = len(rows[0]) if rows else 0
        ncols = _size(ncols, "ncols")
        if any(len(row) != ncols for row in rows):
            raise ValueError("matrix rows have inconsistent widths")
        object.__setattr__(self, "field", field)
        object.__setattr__(self, "rows", rows)
        object.__setattr__(self, "ncols", ncols)
        object.__setattr__(self, "_rref_data", None)
        object.__setattr__(self, "_rank_data", None)
        object.__setattr__(self, "_binary_data", None)
        object.__setattr__(self, "_coordinate_data", None)

    @classmethod
    def _from_validated(cls, field: Field, rows, ncols: int) -> Matrix:
        """Private constructor for proven-valid kernel output, never JSON input."""
        result = object.__new__(cls)
        object.__setattr__(result, "field", field)
        object.__setattr__(result, "rows", tuple(tuple(row) for row in rows))
        object.__setattr__(result, "ncols", ncols)
        object.__setattr__(result, "_rref_data", None)
        object.__setattr__(result, "_rank_data", None)
        object.__setattr__(result, "_binary_data", None)
        object.__setattr__(result, "_coordinate_data", None)
        return result

    def _binary_rows(self) -> tuple[int, ...]:
        cached = self._binary_data
        if cached is None:
            cached = tuple(pack_binary(row) for row in self.rows)
            object.__setattr__(self, "_binary_data", cached)
        return cached

    @property
    def nrows(self) -> int:
        return len(self.rows)

    @property
    def shape(self) -> tuple[int, int]:
        return self.nrows, self.ncols

    def __len__(self) -> int:
        return self.nrows

    def __iter__(self) -> Iterator[tuple[int, ...]]:
        return iter(self.rows)

    def __getitem__(self, index):
        return self.rows[index]

    @property
    def T(self) -> Matrix:
        return Matrix._from_validated(self.field, zip(*self.rows) if self.nrows else (() for _ in range(self.ncols)), self.nrows)

    def __matmul__(self, other: Matrix) -> Matrix:
        _same_field(self, other)
        if self.ncols != other.nrows:
            raise ValueError(f"incompatible product shapes {self.shape} and {other.shape}")
        f, width = self.field, other.ncols
        output = []
        if f.q == 2:
            packed = other._binary_rows()
            for i, row in enumerate(self.rows):
                if i % 16 == 0:
                    checkpoint()
                bits = 0
                for a, b in zip(row, packed):
                    if a:
                        bits ^= b
                output.append(unpack_binary(bits, width))
        else:
            # Reuse sparsity once per product instead of testing every zero in
            # every output row. Prime-field reductions can be delayed safely:
            # Python integers do not overflow, including near-64-bit primes.
            sparse = tuple(tuple((j, b) for j, b in enumerate(row) if b) for row in other.rows)
            for i, row in enumerate(self.rows):
                if i % 16 == 0:
                    checkpoint()
                result = [0] * width
                if f.degree == 1:
                    for a, entries in zip(row, sparse):
                        if a:
                            for j, b in entries:
                                result[j] += a * b
                    result = [v % f.p for v in result]
                elif f._muls is not None:
                    adds, muls = f._adds, f._muls
                    for a, entries in zip(row, sparse):
                        if a:
                            products = muls[a]
                            if f.p == 2:
                                for j, b in entries:
                                    result[j] ^= products[b]
                            else:
                                for j, b in entries:
                                    result[j] = adds[result[j]][products[b]]
                else:
                    add, mul = f._add, f._multiplication()
                    for a, entries in zip(row, sparse):
                        if a:
                            for j, b in entries:
                                result[j] = add(result[j], mul(a, b))
                output.append(result)
        return Matrix._from_validated(f, output, width)

    def __add__(self, other: Matrix) -> Matrix:
        _same_shape(self, other)
        f = self.field
        if f.p == 2:
            rows = (tuple(a ^ b for a, b in zip(x, y)) for x, y in zip(self, other))
        elif f.degree == 1:
            rows = (tuple((a + b) % f.p for a, b in zip(x, y)) for x, y in zip(self, other))
        else:
            add = (lambda a, b: f._adds[a][b]) if f._adds is not None else f._add
            rows = (tuple(add(a, b) for a, b in zip(x, y)) for x, y in zip(self, other))
        return Matrix._from_validated(f, rows, self.ncols)

    def __sub__(self, other: Matrix) -> Matrix:
        _same_shape(self, other)
        f = self.field
        if f.p == 2:
            return self + other
        if f.degree == 1:
            rows = (tuple((a - b) % f.p for a, b in zip(x, y)) for x, y in zip(self, other))
        else:
            sub = ((lambda a, b: f._subs[a][b]) if f._subs is not None
                   else (lambda a, b: f._add(a, f._neg(b))))
            rows = (tuple(sub(a, b) for a, b in zip(x, y)) for x, y in zip(self, other))
        return Matrix._from_validated(f, rows, self.ncols)

    def to_list(self) -> list[list[int]]:
        return [list(row) for row in self.rows]

    def to_dict(self) -> dict:
        return {"field": self.field.to_dict(), "ncols": self.ncols, "rows": self.to_list()}

    @classmethod
    def from_dict(cls, data: dict) -> Matrix:
        return cls(Field.from_dict(data["field"]), data["rows"], ncols=data["ncols"])


def _same_field(*matrices: Matrix) -> Field:
    if not matrices:
        raise ValueError("at least one matrix is required")
    if not all(isinstance(m, Matrix) for m in matrices):
        raise TypeError("arguments must be Matrix objects")
    f = matrices[0].field
    if any(m.field != f for m in matrices[1:]):
        raise ValueError("matrices use different field representations")
    return f


def _same_shape(a: Matrix, b: Matrix) -> None:
    _same_field(a, b)
    if a.shape != b.shape:
        raise ValueError("matrix shapes differ")


def zeros(field: Field, nrows: int, ncols: int) -> Matrix:
    nrows, ncols = _size(nrows, "nrows"), _size(ncols, "ncols")
    if not isinstance(field, Field):
        raise TypeError("field must be a Field")
    return Matrix._from_validated(field, ((0,) * ncols for _ in range(nrows)), ncols)


def eye(field: Field, n: int) -> Matrix:
    n = _size(n, "n")
    if not isinstance(field, Field):
        raise TypeError("field must be a Field")
    return Matrix._from_validated(field, (tuple(int(i == j) for j in range(n)) for i in range(n)), n)


def from_columns(field: Field, columns: Iterable[Iterable[int]], nrows: int | None = None) -> Matrix:
    columns = tuple(tuple(c) for c in columns)
    if nrows is None:
        nrows = len(columns[0]) if columns else 0
    return Matrix(field, columns, ncols=_size(nrows, "nrows")).T


def hstack(*matrices: Matrix) -> Matrix:
    f = _same_field(*matrices)
    r = matrices[0].nrows
    if any(m.nrows != r for m in matrices):
        raise ValueError("hstack row counts differ")
    return Matrix._from_validated(f, (tuple(v for m in matrices for v in m[i]) for i in range(r)), sum(m.ncols for m in matrices))


def vstack(*matrices: Matrix) -> Matrix:
    f = _same_field(*matrices)
    c = matrices[0].ncols
    if any(m.ncols != c for m in matrices):
        raise ValueError("vstack column counts differ")
    return Matrix._from_validated(f, (row for m in matrices for row in m), c)


def block_diag(*matrices: Matrix) -> Matrix:
    f = _same_field(*matrices)
    total = sum(m.ncols for m in matrices)
    output, offset = [], 0
    for m in matrices:
        output.extend((0,) * offset + row + (0,) * (total - offset - m.ncols) for row in m)
        offset += m.ncols
    return Matrix._from_validated(f, output, total)


def lift(matrix: Matrix, length: int) -> Matrix:
    """I_length tensor matrix, using instance-major coordinate order."""
    length = _size(length, "length")
    if not length:
        return zeros(matrix.field, 0, 0)
    if not matrix.nrows:
        return zeros(matrix.field, 0, matrix.ncols * length)
    return block_diag(*(matrix for _ in range(length)))


def scalar_mul(matrix: Matrix, scalar: int) -> Matrix:
    matrix.field.validate(scalar)
    scale, _ = row_operations(matrix.field)
    return Matrix._from_validated(matrix.field, (scale(list(row), scalar) for row in matrix), matrix.ncols)


def rref(matrix: Matrix) -> tuple[Matrix, tuple[int, ...]]:
    """Canonical exact RREF, with a per-immutable-matrix bounded-lifetime cache."""
    if not isinstance(matrix, Matrix):
        raise TypeError("matrix must be a Matrix")
    checkpoint()
    data = matrix._rref_data
    if data is None:
        f, pivots, r = matrix.field, [], 0
        if f.q == 2:
            packed = list(matrix._binary_rows())
            for c in range(matrix.ncols):
                if c % 16 == 0:
                    checkpoint()
                bit = 1 << c
                pivot = next((i for i in range(r, matrix.nrows) if packed[i] & bit), None)
                if pivot is None:
                    continue
                packed[r], packed[pivot] = packed[pivot], packed[r]
                row = packed[r]
                for i in range(matrix.nrows):
                    if i != r and packed[i] & bit:
                        packed[i] ^= row
                pivots.append(c)
                r += 1
                if r == matrix.nrows:
                    break
            rows = tuple(unpack_binary(bits, matrix.ncols) for bits in packed)
        else:
            a = matrix.to_list()
            scale, subtract = row_operations(f)
            for c in range(matrix.ncols):
                if c % 16 == 0:
                    checkpoint()
                pivot = next((i for i in range(r, matrix.nrows) if a[i][c]), None)
                if pivot is None:
                    continue
                a[r], a[pivot] = a[pivot], a[r]
                if a[r][c] != 1:
                    a[r][c:] = scale(a[r][c:], reciprocal(f, a[r][c]))
                for i in range(matrix.nrows):
                    if i != r and a[i][c]:
                        factor = a[i][c]
                        a[i][c] = 0
                        subtract(a[i], a[r], factor, c + 1)
                pivots.append(c)
                r += 1
                if r == matrix.nrows:
                    break
            rows = tuple(tuple(row) for row in a)
        data = rows, tuple(pivots)
        # Publish immutable data only; duplicate computation in racing readers
        # is harmless. Caches are excluded from equality and hashing.
        object.__setattr__(matrix, "_rref_data", data)
        object.__setattr__(matrix, "_rank_data", len(pivots))
    rows, pivots = data
    if rows == matrix.rows:
        return matrix, pivots
    result = Matrix._from_validated(matrix.field, rows, matrix.ncols)
    object.__setattr__(result, "_rref_data", data)
    object.__setattr__(result, "_rank_data", len(pivots))
    return result, pivots


def row_basis(matrix: Matrix) -> Matrix:
    reduced, pivots = rref(matrix)
    if reduced.nrows == len(pivots):
        return reduced
    result = Matrix._from_validated(matrix.field, reduced.rows[:len(pivots)], matrix.ncols)
    object.__setattr__(result, "_rref_data", (result.rows, pivots))
    object.__setattr__(result, "_rank_data", len(pivots))
    return result


def rank(matrix: Matrix) -> int:
    """Rank by forward/incremental elimination; never materialize an RREF."""
    if not isinstance(matrix, Matrix):
        raise TypeError("matrix must be a Matrix")
    checkpoint()
    result = matrix._rank_data
    if result is None:
        echelon = _echelon(matrix)
        result = len(echelon.pivots)
        object.__setattr__(matrix, "_rank_data", result)
    return result


def nullspace(matrix: Matrix) -> Matrix:
    reduced, pivots = rref(matrix)
    pivot_set = set(pivots)
    output = []
    for free in range(matrix.ncols):
        if free % 16 == 0:
            checkpoint()
        if free in pivot_set:
            continue
        row = [0] * matrix.ncols
        row[free] = 1
        for i, pivot in enumerate(pivots):
            row[pivot] = matrix.field._neg(reduced[i][free])
        output.append(row)
    result = Matrix._from_validated(matrix.field, output, matrix.ncols)
    object.__setattr__(result, "_rank_data", len(output))
    return result


def row_sum(*matrices: Matrix) -> Matrix:
    return row_basis(vstack(*matrices))


def intersection(a: Matrix, b: Matrix) -> Matrix:
    _same_field(a, b)
    if a.ncols != b.ncols:
        raise ValueError("subspaces have different ambient dimensions")
    if not a.nrows or not b.nrows:
        return zeros(a.field, 0, a.ncols)
    if a == b:
        return row_basis(a)
    # For dense spaces the annihilator identity (A intersect B)^perp =
    # A^perp + B^perp replaces a large relation system with smaller kernels.
    a, b = row_basis(a), row_basis(b)
    if a.nrows == a.ncols:
        return b
    if b.nrows == b.ncols:
        return a
    if a.nrows + b.nrows >= a.ncols + (a.ncols + 1) // 2:
        return row_basis(nullspace(vstack(nullspace(a), nullspace(b))))
    relation = hstack(a.T, scalar_mul(b.T, b.field._neg(1)))
    kernel = nullspace(relation)
    left = Matrix._from_validated(a.field, (row[:a.nrows] for row in kernel), a.nrows)
    return row_basis(left @ a)


def contains(a: Matrix, b: Matrix) -> bool:
    """Whether rowspace(a) contains rowspace(b)."""
    _same_field(a, b)
    if a.ncols != b.ncols:
        raise ValueError("subspaces have different ambient dimensions")
    checkpoint()
    if not b.nrows or a == b:
        return True
    echelon = _echelon(a)
    if len(echelon.pivots) == a.ncols:
        return True
    if a.field.q == 2:
        return not any(echelon.insert_binary(row, add=False) for row in b._binary_rows())
    return not any(echelon.insert(row, add=False) for row in b.rows)


def solve(a: Matrix, b: Matrix) -> Matrix:
    """Solve a @ x = b exactly; set all free coordinates of x to zero.

    Supports multiple right-hand sides, rank-deficient a, and zero sizes.
    Raises ValueError if any right-hand side is inconsistent.
    """
    _same_field(a, b)
    if a.nrows != b.nrows:
        raise ValueError("right-hand side row count differs")
    reduced, pivots = rref(hstack(a, b))
    if any(p >= a.ncols for p in pivots):
        raise ValueError("linear system is inconsistent")
    output = [[0] * b.ncols for _ in range(a.ncols)]
    for i, p in enumerate(pivots):
        output[p] = list(reduced[i][a.ncols:])
    return Matrix._from_validated(a.field, output, b.ncols)


def coordinates(vectors: Matrix, basis: Matrix) -> Matrix:
    """Return x satisfying x @ basis = vectors, even for dependent basis rows."""
    _same_field(vectors, basis)
    if vectors.ncols != basis.ncols:
        raise ValueError("coordinate matrices have different ambient dimensions")
    if not vectors.nrows:
        return zeros(basis.field, 0, basis.nrows)
    data = basis._rref_data
    if data is not None and data[0] == basis.rows and len(data[1]) == basis.nrows:
        # A canonical RREF basis has identity columns at its pivots. Coordinates
        # are those entries of each vector; the product checks membership.
        result = Matrix._from_validated(basis.field,
            (tuple(row[p] for p in data[1]) for row in vectors.rows), basis.nrows)
        if result @ basis != vectors:
            raise ValueError("linear system is inconsistent")
        return result
    # Solve repeatedly against a fixed independent row basis by factoring a
    # square pivot-column minor once. For a dependent input basis, choose the
    # pivot columns of basis.T: these are exactly the variables selected by
    # solve(basis.T, vectors.T), so all the same free coefficients stay zero.
    # Store only immutable data on this basis; no global cache retains tasks.
    factor = basis._coordinate_data
    if factor is None:
        if basis.nrows == basis.ncols and basis._rank_data == basis.nrows:
            # Normal-form construction already certifies square bases. Their
            # pivot minor is the entire matrix; do not eliminate it twice to
            # rediscover that fact before computing its inverse.
            columns = indices = tuple(range(basis.nrows))
        else:
            reduced, columns = rref(basis)
            if len(columns) == basis.nrows:
                if reduced.rows == basis.rows:
                    result = Matrix._from_validated(basis.field,
                        (tuple(row[j] for j in columns) for row in vectors.rows), basis.nrows)
                    if result @ basis != vectors:
                        raise ValueError("linear system is inconsistent")
                    return result
                indices = tuple(range(basis.nrows))
            else:
                _, indices = rref(basis.T)
        independent = Matrix._from_validated(basis.field,
                                             (basis.rows[i] for i in indices),
                                             basis.ncols)
        minor = Matrix._from_validated(basis.field,
            (tuple(row[j] for j in columns) for row in independent.rows), len(columns))
        factor = indices, columns, inverse(minor), independent
        object.__setattr__(basis, "_coordinate_data", factor)
    indices, columns, inverse_minor, independent = factor
    selected = Matrix._from_validated(basis.field,
        (tuple(row[j] for j in columns) for row in vectors.rows), len(columns))
    coefficients = selected @ inverse_minor
    if coefficients @ independent != vectors:
        raise ValueError("linear system is inconsistent")
    if len(indices) == basis.nrows:
        # Pivot indices for a full-row-rank input are 0,...,nrows-1.
        return coefficients
    rows = []
    for row in coefficients.rows:
        result = [0] * basis.nrows
        for i, value in zip(indices, row):
            result[i] = value
        rows.append(result)
    return Matrix._from_validated(basis.field, rows, basis.nrows)


def coordinates_many(vectors: Iterable[Matrix], basis: Matrix) -> tuple[Matrix, ...]:
    """Batch coordinate right-hand sides sharing one exact coefficient basis.

    The output has the same order and row partitions as ``vectors``. All
    membership and field checks, including empty inputs, match coordinates.
    """
    vectors = tuple(vectors)
    _same_field(basis, *vectors)
    if any(v.ncols != basis.ncols for v in vectors):
        raise ValueError("coordinate matrices have different ambient dimensions")
    if not vectors:
        return ()
    combined = Matrix._from_validated(basis.field,
        (row for matrix in vectors for row in matrix.rows), basis.ncols)
    coefficients = coordinates(combined, basis)
    output, offset = [], 0
    for matrix in vectors:
        output.append(Matrix._from_validated(basis.field,
            coefficients.rows[offset:offset + matrix.nrows], basis.nrows))
        offset += matrix.nrows
    return tuple(output)


def inverse(matrix: Matrix) -> Matrix:
    if matrix.nrows != matrix.ncols:
        raise ValueError("inverse requires a square matrix")
    try:
        return solve(matrix, eye(matrix.field, matrix.nrows))
    except ValueError as exc:
        raise ValueError("matrix is singular") from exc


def determinant(matrix: Matrix) -> int:
    if matrix.nrows != matrix.ncols:
        raise ValueError("determinant requires a square matrix")
    if matrix.field.q == 2:
        return int(rank(matrix) == matrix.nrows)
    f, a, result = matrix.field, matrix.to_list(), 1
    _, subtract = row_operations(f)
    mul = f._multiplication()
    for c in range(matrix.ncols):
        if c % 16 == 0:
            checkpoint()
        pivot = next((r for r in range(c, matrix.nrows) if a[r][c]), None)
        if pivot is None:
            return 0
        if pivot != c:
            a[c], a[pivot] = a[pivot], a[c]
            result = f._neg(result)
        value = a[c][c]
        result = mul(result, value)
        inv = reciprocal(f, value)
        for r in range(c + 1, matrix.nrows):
            if a[r][c]:
                factor = mul(a[r][c], inv)
                a[r][c] = 0
                subtract(a[r], a[c], factor, c + 1)
    return result


def extend_basis(base: Matrix, candidates: Matrix, target_dim: int | None = None) -> Matrix:
    """Select original rows, preserving their order, until target dimension.

    First select an independent subset of ``base``; then append independent
    rows from ``candidates``. No row combinations are returned. With no target,
    return a basis of their sum; otherwise failure to reach target raises.
    """
    f = _same_field(base, candidates)
    if base.ncols != candidates.ncols:
        raise ValueError("basis extension ambient dimensions differ")
    if target_dim is not None:
        target_dim = _size(target_dim, "target_dim")
        if target_dim > base.ncols:
            raise ValueError("target dimension exceeds ambient dimension")
    echelon = Echelon(f, base.ncols)
    selected = []

    def insert(original: tuple[int, ...]) -> bool:
        if not echelon.insert(original):
            return False
        selected.append(original)
        return True

    for row in base:
        insert(row)
    if target_dim is not None and len(selected) > target_dim:
        raise ValueError("target dimension is smaller than rank(base)")
    for row in candidates:
        if target_dim is not None and len(selected) == target_dim:
            break
        insert(row)
    if target_dim is not None and len(selected) != target_dim:
        raise ValueError("candidate rows cannot reach target dimension")
    return Matrix._from_validated(f, selected, base.ncols)


def quotient_rank(vectors: Matrix, base: Matrix) -> int:
    """Dimension added by vectors modulo base, with one incremental factorization."""
    _same_field(vectors, base)
    if vectors.ncols != base.ncols:
        raise ValueError("subspaces have different ambient dimensions")
    checkpoint()
    echelon = _echelon(base)
    before = len(echelon.pivots)
    if before == base.ncols:
        return 0
    if base.field.q == 2:
        echelon.load_binary(vectors._binary_rows())
    else:
        echelon.load(vectors.rows)
    return len(echelon.pivots) - before


def _echelon(matrix: Matrix) -> Echelon:
    """Build a private mutable basis, reusing known exact RREF factorizations.

    Rank profiles repeatedly reduce against the same canonical spaces. Their
    normalized pivots can be copied directly, without eliminating them again.
    The mutable dictionaries/lists are never shared with a Matrix or caller.
    """
    echelon = Echelon(matrix.field, matrix.ncols)
    data = matrix._rref_data
    if data is not None:
        rows, pivots = data
        echelon.pivots = list(pivots)
        if matrix.field.q == 2:
            packed = (matrix._binary_rows() if rows == matrix.rows
                      else tuple(pack_binary(row) for row in rows[:len(pivots)]))
            echelon.bits = dict(zip(pivots, packed))
        else:
            echelon.rows = dict(zip(pivots, rows))
    elif matrix.field.q == 2:
        echelon.load_binary(matrix._binary_rows())
    else:
        echelon.load(matrix.rows)
    return echelon
