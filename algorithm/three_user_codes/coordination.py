"""Exact deterministic coordination of homogeneous decoder columns.

All arithmetic is in a finite field. No floating-point determinants, random
search, symbolic expansion, or numerical tolerances are used. Each parameter
group supplies at most one column of any decoder, as required by the theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ._kernels import reciprocal, row_operations
from ._resources import checkpoint
from .linalg import Matrix, eye, inverse, nullspace, solve


@dataclass(frozen=True)
class ColumnSpec:
    """A homogeneous decoder column: ``column = linear_map @ theta[group]``."""
    group: int
    column: int
    linear_map: Matrix


@dataclass(frozen=True)
class DecoderTemplate:
    """Square fixed matrix with selected columns replaced by parameter groups."""
    fixed: Matrix
    slots: tuple[ColumnSpec, ...]

    def evaluate(self, assignment: Sequence[Sequence[int]]) -> Matrix:
        f = self.fixed.field
        rows = [list(row) for row in self.fixed.rows]
        for spec in self.slots:
            x = assignment[spec.group]
            if len(x) != spec.linear_map.ncols:
                raise ValueError("parameter group has the wrong width")
            for value in x:
                f.validate(value)
            column = spec.linear_map @ Matrix._from_validated(f, ((v,) for v in x), 1)
            for j, row in enumerate(column.rows):
                rows[j][spec.column] = row[0]
        return Matrix(f, rows, ncols=self.fixed.ncols)


@dataclass(frozen=True)
class CoordinationResult:
    assignment: tuple[tuple[int, ...], ...]
    matrices: tuple[Matrix, ...]
    groups_processed: int
    inverse_updates: int
    candidate_evaluations: int


def _avoid_with_count(forms: Matrix) -> tuple[tuple[int, ...], int]:
    """Avoid t nonzero linear forms using at most t+1 projective candidates."""
    f, t, r = forms.field, forms.nrows, forms.ncols
    if t == 0:
        return (0,) * r, 0
    if any(not any(row) for row in forms.rows):
        raise ValueError("a zero form cannot be avoided")
    if f.q < t:
        if f.q == 2:
            # Over GF(2), nonzero is exactly one. Unlike a union bound, this
            # linear system is necessary and sufficient for any form count.
            x = solve(forms, Matrix(f, [[1] for _ in range(t)], ncols=1))
            return tuple(row[0] for row in x.rows), t
        # Repeated/scaled constraints exclude the same hyperplane. Removing
        # them can restore the projective guarantee without any search.
        mul = f._multiplication()
        unique = {}
        for row in forms.rows:
            normalization = reciprocal(f, next(a for a in row if a))
            unique[tuple(mul(value, normalization) for value in row)] = None
        if len(unique) == t or len(unique) > f.q:
            raise ValueError("the guaranteed construction requires field order >= number of distinct kernels")
        forms = Matrix._from_validated(f, unique, r)
        t = forms.nrows
    x = [0] * r
    x[next(j for j, a in enumerate(forms.rows[0]) if a)] = 1
    evaluations = 1
    for k in range(1, t):
        new = forms.rows[k]
        evaluations += 1
        if f.dot(new, x):
            continue
        y = [0] * r
        y[next(j for j, a in enumerate(new) if a)] = 1
        # x and y are independent: the new form vanishes only on x.
        # Every current kernel excludes at most one of these projective points.
        candidates = [tuple(x), tuple(y)]
        candidates += [tuple(f.add(a, f.mul(alpha, b)) for a, b in zip(x, y))
                       for alpha in range(1, k + 1)]
        chosen = None
        for candidate in candidates:
            evaluations += k + 1
            if all(f.dot(row, candidate) for row in forms.rows[:k + 1]):
                chosen = candidate
                break
        if chosen is None:
            raise ArithmeticError("projective avoidance invariant failed")
        x = list(chosen)
    return tuple(x), evaluations


def avoid_linear_forms(forms: Matrix) -> tuple[int, ...]:
    """Return x with every row of ``forms`` nonzero on x, deterministically.

    The guarantee requires at most ``field.q`` distinct kernels. Over GF(2)
    the exact linear system ``forms @ x = 1`` also handles larger lists.
    Zero constraints return the zero vector. A zero row is rejected.
    """
    return _avoid_with_count(forms)[0]


def avoid_subspaces(subspaces: Sequence[Matrix], *, field=None, dimension=None) -> tuple[int, ...]:
    """Avoid proper subspaces supplied by row generators.

    Each subspace is enlarged to one exact annihilating hyperplane. The number
    of distinct selected hyperplanes must not exceed the field order, except
    when an exact binary solve succeeds. With no spaces, supply field/dimension.
    """
    if not subspaces:
        if field is None or dimension is None or dimension < 0:
            raise ValueError("empty input requires field and nonnegative dimension")
        return (0,) * dimension
    f, r = subspaces[0].field, subspaces[0].ncols
    forms = []
    for space in subspaces:
        if space.field != f or space.ncols != r:
            raise ValueError("subspaces must have the same ambient space and field")
        annihilator = nullspace(space)
        if not annihilator.nrows:
            raise ValueError("excluded subspace is not proper")
        forms.append(annihilator.rows[0])
    return avoid_linear_forms(Matrix(f, forms, ncols=r))


def coordinate_columns(templates: Sequence[DecoderTemplate],
                       witnesses: Sequence[Sequence[Sequence[int]]],
                       group_widths: Sequence[int] | None = None) -> CoordinationResult:
    """Coordinate individually invertible assignments into one common assignment.

    ``witnesses[i]`` is a complete assignment making ``templates[i]`` invertible.
    Groups are nonempty vectors and supply at most one column in each decoder.
    The projective guarantee depends on the number of decoders affected by
    each group, not the total decoder count. Binary groups use an exact linear
    system if needed; incompatible groups raise ValueError.
    Inverses are updated by exact Sherman--Morrison column updates; the final
    matrices/inverses are checked by exact multiplication before returning.
    """
    if not templates or len(templates) != len(witnesses):
        raise ValueError("one nonempty decoder list and one witness per decoder are required")
    f = templates[0].fixed.field
    inferred: dict[int, int] = {}
    slots_by_group = []
    for template in templates:
        base = template.fixed
        if base.field != f or base.nrows != base.ncols:
            raise ValueError("decoder matrices must be square over one field")
        groups, columns, mapping = set(), set(), {}
        for spec in template.slots:
            if (spec.group < 0 or spec.group in groups or spec.column in columns or
                    not 0 <= spec.column < base.ncols):
                raise ValueError("each group and decoder column may occur at most once")
            L = spec.linear_map
            if L.field != f or L.nrows != base.nrows or L.ncols < 1:
                raise ValueError("invalid homogeneous column map")
            if spec.group in inferred and inferred[spec.group] != L.ncols:
                raise ValueError("inconsistent parameter group widths")
            inferred[spec.group] = L.ncols
            groups.add(spec.group); columns.add(spec.column); mapping[spec.group] = spec
        slots_by_group.append(mapping)
    G = len(witnesses[0])
    if any(len(w) != G for w in witnesses):
        raise ValueError("all witnesses must assign every group")
    widths = tuple(group_widths) if group_widths is not None else tuple(
        inferred.get(g, len(witnesses[0][g])) for g in range(G))
    if len(widths) != G or any(r < 1 for r in widths) or any(g >= G for g in inferred):
        raise ValueError("invalid group widths")
    if any(widths[g] != r for g, r in inferred.items()):
        raise ValueError("supplied widths disagree with decoder maps")
    current = []
    for w in witnesses:
        if any(len(x) != widths[g] for g, x in enumerate(w)):
            raise ValueError("witness group has the wrong width")
        for x in w:
            for value in x:
                f.validate(value)
        current.append([tuple(x) for x in w])
    matrices = [t.evaluate(w) for t, w in zip(templates, current)]
    try:
        inverses = [inverse(C) for C in matrices]
    except ValueError as exc:
        raise ValueError("each supplied witness must make its own decoder invertible") from exc
    updates = evaluations = 0
    _, subtract_row = row_operations(f)
    mul = f._multiplication()
    for g in range(G):
        checkpoint()
        forms = []
        for i, mapping in enumerate(slots_by_group):
            if g in mapping:
                spec = mapping[g]
                cofactor = Matrix._from_validated(f, [inverses[i].rows[spec.column]],
                                                  inverses[i].ncols)
                forms.append((cofactor @ spec.linear_map).rows[0])
        x, count = _avoid_with_count(Matrix(f, forms, ncols=widths[g]))
        evaluations += count
        parameter_column = Matrix._from_validated(f, ((value,) for value in x), 1)
        for i, mapping in enumerate(slots_by_group):
            current[i][g] = x
            if g not in mapping:
                continue
            spec = mapping[g]
            c, C, R = spec.column, matrices[i], inverses[i]
            v = tuple(row[0] for row in (spec.linear_map @ parameter_column).rows)
            delta = tuple(f.sub(v[j], C.rows[j][c]) for j in range(C.nrows))
            updates += 1
            if not any(delta):
                # This is an identity column update; retain the cached matrix
                # and inverse rather than rebuilding their quadratic storage.
                continue
            z_column = R @ Matrix._from_validated(f, ((value,) for value in delta), 1)
            z = tuple(row[0] for row in z_column.rows)
            denominator = f.add(1, z[c])
            if denominator == 0:
                raise ArithmeticError("coordinated column unexpectedly singular")
            scale = reciprocal(f, denominator)
            rr = R.rows[c]
            inverse_rows = []
            for a, row in enumerate(R.rows):
                if z[a]:
                    row = list(row)
                    subtract_row(row, rr, mul(z[a], scale), 0)
                inverse_rows.append(row)
            inverses[i] = Matrix._from_validated(f, inverse_rows, C.ncols)
            newrows = [list(row) for row in C.rows]
            for a in range(C.nrows):
                newrows[a][c] = v[a]
            matrices[i] = Matrix._from_validated(f, newrows, C.ncols)
    assignment = tuple(current[0])
    if any(tuple(w) != assignment for w in current):
        raise ArithmeticError("witnesses were not fully coordinated")
    for t, C, R in zip(templates, matrices, inverses):
        if t.evaluate(assignment) != C or C @ R != eye(f, C.nrows):
            raise ArithmeticError("exact decoder inverse verification failed")
    return CoordinationResult(assignment, tuple(matrices), G, updates, evaluations)


def choose_outside_kernels(forms, dimension: int, field) -> list[int]:
    """Convenience API for relay-normal selection from row linear forms."""
    matrix = forms if isinstance(forms, Matrix) else Matrix(field, forms, ncols=dimension)
    if matrix.field != field or matrix.ncols != dimension:
        raise ValueError("form dimensions/field do not match")
    return list(avoid_linear_forms(matrix))
