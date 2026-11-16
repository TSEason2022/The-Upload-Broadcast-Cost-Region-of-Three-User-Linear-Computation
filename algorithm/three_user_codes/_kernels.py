"""Private exact kernels for already validated field elements.

Only immutable Matrix/Field inputs reach these routines. Public constructors
and scalar arithmetic still reject booleans, floats and out-of-range values.
No fixed-width integer multiplication, numerical rank or random pivots occur.
"""
from __future__ import annotations

from bisect import insort
from functools import lru_cache
from typing import Callable

from .field import Field
from ._resources import checkpoint

Scale = Callable[[list[int], int], list[int]]
Subtract = Callable[[list[int], list[int] | tuple[int, ...], int, int], None]


@lru_cache(maxsize=32)
def row_operations(f: Field) -> tuple[Scale, Subtract]:
    """Select arithmetic once per representation, rather than once per entry."""
    if f.degree == 1:
        p = f.p
        def scale(row, a):
            return [(a * x) % p for x in row]
        def subtract(row, other, a, start=0):
            for j in range(start, len(row)):
                row[j] = (row[j] - a * other[j]) % p
    elif f._muls is not None:
        muls, subs = f._muls, f._subs
        def scale(row, a):
            table = muls[a]
            return [table[x] for x in row]
        if f.p == 2:
            def subtract(row, other, a, start=0):
                table = muls[a]
                for j in range(start, len(row)):
                    row[j] ^= table[other[j]]
        else:
            def subtract(row, other, a, start=0):
                table = muls[a]
                for j in range(start, len(row)):
                    row[j] = subs[row[j]][table[other[j]]]
    else:
        mul, add, neg = f._multiplication(), f._add, f._neg
        def scale(row, a):
            return [mul(a, x) for x in row]
        if f.p == 2:
            def subtract(row, other, a, start=0):
                for j in range(start, len(row)):
                    row[j] ^= mul(a, other[j])
        else:
            def subtract(row, other, a, start=0):
                for j in range(start, len(row)):
                    row[j] = add(row[j], neg(mul(a, other[j])))
    return scale, subtract


def reciprocal(f: Field, value: int) -> int:
    # Callers have already proved value != 0 and value belongs to f.
    return f._invs[value] if f._invs is not None else f.inv(value)


_BINARY_ASCII = bytes.maketrans(b"\x00\x01", b"01")
_ASCII_BINARY = bytes.maketrans(b"01", b"\x00\x01")


def pack_binary(row) -> int:
    """Pack trusted 0/1 coefficients using exact C-level binary conversion.

    Coordinates are least significant first. Byte translation avoids a Python
    shift for every coefficient; base 2 has no decimal integer digit limit.
    """
    digits = bytes(row)
    return int(digits.translate(_BINARY_ASCII)[::-1], 2) if digits else 0


def unpack_binary(bits: int, width: int) -> tuple[int, ...]:
    """Unpack trusted 0 <= bits < 2**width, preserving leading zero columns."""
    if not width:
        return ()
    return tuple(format(bits, f"0{width}b").encode().translate(_ASCII_BINARY)[::-1])


class Echelon:
    """Incremental exact row basis. Insert never changes existing input rows.

    The internal basis need only be echelon, not reduced echelon. Sorted
    pivots ensure deterministic reduction even when pivots arrive out of order.
    Binary rows are entire Python integers and eliminate by one XOR.
    """
    __slots__ = ("field", "width", "pivots", "rows", "bits", "scale", "subtract", "insertions")

    def __init__(self, field: Field, width: int):
        self.field, self.width = field, width
        self.pivots: list[int] = []
        self.rows: dict[int, tuple[int, ...]] = {}
        self.bits: dict[int, int] = {}
        self.scale, self.subtract = row_operations(field)
        self.insertions = 0

    def insert_binary(self, work: int, *, add: bool = True) -> bool:
        """Insert an already packed GF(2) row without packing it again.

        Only visit nonzero leading coordinates. Stopping at the first absent
        pivot is sufficient for independence, even when pivots arrive out of
        order; an echelon basis need not clear the pivots to its right.
        """
        self.insertions += 1
        if self.insertions % 32 == 0:
            checkpoint()
        while work:
            pivot = (work & -work).bit_length() - 1
            existing = self.bits.get(pivot)
            if existing is None:
                if add:
                    self.bits[pivot] = work
                    insort(self.pivots, pivot)
                return True
            work ^= existing
        return False

    def insert(self, original, *, add: bool = True) -> bool:
        """Return whether original is independent; optionally add the residual."""
        if self.field.q == 2:
            return self.insert_binary(pack_binary(original), add=add)
        self.insertions += 1
        if self.insertions % 32 == 0:
            checkpoint()
        work = list(original)
        for p in self.pivots:
            if work[p]:
                # The pivot is normalized to one; avoid multiplying its entry.
                factor = work[p]
                work[p] = 0
                self.subtract(work, self.rows[p], factor, p + 1)
        pivot = next((j for j, value in enumerate(work) if value), None)
        if pivot is None:
            return False
        if add:
            if work[pivot] != 1:
                work[pivot:] = self.scale(work[pivot:], reciprocal(self.field, work[pivot]))
            self.rows[pivot] = tuple(work)
            insort(self.pivots, pivot)
        return True

    def load(self, rows) -> None:
        for row in rows:
            self.insert(row)
            if len(self.pivots) == self.width:
                break

    def load_binary(self, rows) -> None:
        for row in rows:
            self.insert_binary(row)
            if len(self.pivots) == self.width:
                break
