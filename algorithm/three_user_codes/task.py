"""Validated three-user linear computation tasks (row-vector convention)."""
from __future__ import annotations

from dataclasses import dataclass, field as dataclass_field
from functools import cached_property

from .field import Field
from .linalg import Matrix, contains, lift, row_basis, row_sum


@dataclass(frozen=True)
class Task:
    """A user observes ``side[i] @ x`` and requests ``demand[i] @ x``.

    Matrices store linear functions in their *rows*. Redundant rows are
    removed deterministically. The original inputs remain available as
    ``original_side`` and ``original_demand`` so callers can recover their
    original measurement/output conventions by a further coordinate solve.
    A task is rejected if a demand cannot be determined from the union of
    all three observations; an initially uninformed relay cannot solve it.
    """

    field: Field
    side: tuple[Matrix, Matrix, Matrix]
    demand: tuple[Matrix, Matrix, Matrix]
    original_side: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False, repr=False, compare=False)
    original_demand: tuple[Matrix, Matrix, Matrix] = dataclass_field(init=False, repr=False, compare=False)

    def __post_init__(self):
        if len(self.side) != 3 or len(self.demand) != 3:
            raise ValueError("exactly three side and three demand matrices are required")
        matrices = tuple(self.side) + tuple(self.demand)
        if not all(isinstance(a, Matrix) for a in matrices):
            raise TypeError("side and demand entries must be Matrix objects")
        if any(a.field != self.field for a in matrices):
            raise ValueError("all task matrices must use the task field")
        if len({a.ncols for a in matrices}) != 1:
            raise ValueError("all task matrices must have the same number of source columns")
        original_side, original_demand = tuple(self.side), tuple(self.demand)
        side = tuple(row_basis(a) for a in original_side)
        demand = tuple(row_basis(w) for w in original_demand)
        available = row_sum(*side)
        for i, w in enumerate(demand):
            if not contains(available, w):
                raise ValueError(f"user {i + 1} requests information outside the joint side-information span")
        object.__setattr__(self, "original_side", original_side)
        object.__setattr__(self, "original_demand", original_demand)
        object.__setattr__(self, "side", side)
        object.__setattr__(self, "demand", demand)

    @property
    def n(self) -> int:
        return self.side[0].ncols

    @cached_property
    def augmented(self) -> tuple[Matrix, Matrix, Matrix]:
        return tuple(row_sum(a, w) for a, w in zip(self.side, self.demand))

    @cached_property
    def deficits(self) -> tuple[int, int, int]:
        return tuple(u.nrows - a.nrows for a, u in zip(self.side, self.augmented))

    def lift(self, blocklength: int) -> "Task":
        """Independent instances, ordered by instance then source coordinate."""
        if isinstance(blocklength, bool) or not isinstance(blocklength, int) or blocklength < 1:
            raise ValueError("blocklength must be a positive integer")
        return Task(self.field,
                    tuple(lift(a, blocklength) for a in self.original_side),
                    tuple(lift(w, blocklength) for w in self.original_demand))


    @classmethod
    def from_rows(cls, field: Field | int, side, demand, *, n: int | None = None) -> Task:
        """Construct a task from three row collections without Matrix boilerplate.

        Supply n for all-empty inputs. Rows are still strictly validated as
        Python integers in the field encoding, not coerced from floats/bools.
        """
        field = Field(field) if isinstance(field, int) else field
        if not isinstance(field, Field):
            raise TypeError("field must be a Field or a prime-power integer")
        side, demand = tuple(side), tuple(demand)
        if len(side) != 3 or len(demand) != 3:
            raise ValueError("exactly three side and three demand row collections are required")
        rows = tuple(tuple(tuple(row) for row in matrix) for matrix in side + demand)
        if n is None:
            n = next((len(row) for matrix in rows for row in matrix), None)
            if n is None:
                raise ValueError("n is required when every matrix has zero rows")
        matrices = tuple(Matrix(field, matrix, ncols=n) for matrix in rows)
        return cls(field, matrices[:3], matrices[3:])
