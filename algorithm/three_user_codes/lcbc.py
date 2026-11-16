"""Deterministic optimal broadcast for arbitrary three-user linear tasks.

The inputs A[i], W[i] contain row generators for side information and desired
linear functions. For q >= 3 and an integer LCBC optimum, ``build_lcbc`` gives
a scalar optimal code on that same field. Binary tasks with separated side
spaces spanning the source also have this guarantee (Proposition 25). Use
``lift`` externally to clear a half-integral optimum; no hidden field extension
or further block lift occurs here. Selection uses exact linear algebra, not
coefficient enumeration.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from typing import Sequence

from .coordination import (ColumnSpec, CoordinationResult, DecoderTemplate,
                           coordinate_columns)
from ._kernels import row_operations, unpack_binary
from ._resources import checkpoint
from .linalg import (Matrix, eye, extend_basis, intersection, inverse, nullspace, rank,
                     row_basis, row_sum, rref, scalar_mul, solve, vstack, zeros)


class BinaryScalarRealizationUnavailable(ValueError):
    """The polynomial binary construction did not find a scalar realization.

    This is not a proof of infeasibility. It is never raised on the separated,
    source-spanning tasks covered by Proposition 25.
    """


@dataclass(frozen=True)
class LCBCParameters:
    m: tuple[int, int, int]
    common: int
    b: tuple[int, int, int]
    pair_ranks: tuple[int, int, int]  # (r12, r13, r23)
    p: tuple[int, int, int]
    h_star: Fraction
    cost: Fraction


@dataclass(frozen=True)
class LCBCCode:
    broadcast: Matrix
    # W_i = C_i @ broadcast + H_i @ A_i, with original input row counts.
    decoders: tuple[tuple[Matrix, Matrix], ...]
    cost: Fraction
    allocation: dict[str, int | tuple[int, int, int]]
    stats: dict[str, int]

    def verify(self, A: Sequence[Matrix], W: Sequence[Matrix]) -> bool:
        """Check all-source exact identities (not sampled messages)."""
        return (len(A) == len(W) == len(self.decoders) == 3 and
                self.broadcast.nrows == self.cost and
                all(C @ self.broadcast + H @ a == w
                    for (C, H), a, w in zip(self.decoders, A, W)))


def _validate(A, W):
    if len(A) != 3 or len(W) != 3:
        raise ValueError("exactly three side matrices and three demand matrices are required")
    f, d = A[0].field, A[0].ncols
    if any(M.field != f or M.ncols != d for M in tuple(A) + tuple(W)):
        raise ValueError("all task matrices must have the same field and number of columns")
    return f, d


def _spaces(A, W):
    sides = tuple(row_basis(a) for a in A)
    U = tuple(row_sum(a, w) for a, w in zip(sides, W))
    pair = {(i, j): intersection(U[i], U[j]) for i, j in combinations(range(3), 2)}
    common = intersection(pair[0, 1], U[2])
    coupled = tuple(intersection(U[i], row_sum(*(U[j] for j in range(3) if j != i)))
                    for i in range(3))
    return sides, U, pair, common, coupled


def _parameters(sides, U, pair, common, coupled):
    def cr(space, side):
        return rank(vstack(space, side)) - side.nrows
    m = tuple(u.nrows - a.nrows for u, a in zip(U, sides))
    a = min(cr(common, side) for side in sides)
    b = tuple(cr(coupled[i], sides[i]) for i in range(3))
    rij = {ij: min(cr(V, sides[i]) for i in ij) for ij, V in pair.items()}
    p = tuple(cr(row_sum(*(V for ij, V in pair.items() if i in ij)), sides[i])
              for i in range(3))
    # (h-b_j)_+ +(h-b_k)_+ <= p_i-a is equivalent to three linear bounds.
    bounds = []
    for i in range(3):
        j, k = [x for x in range(3) if x != i]
        bounds.extend([Fraction(b[i] + rij[j, k] - a),
                       Fraction(p[i] - a + b[j]),
                       Fraction(p[i] - a + b[k]),
                       Fraction(p[i] - a + b[j] + b[k], 2)])
    h = min(bounds)
    return LCBCParameters(m, a, b, tuple(rij[ij] for ij in sorted(rij)), p,
                          h, Fraction(sum(m) - a) - h)


def lcbc_parameters(A: Sequence[Matrix], W: Sequence[Matrix]) -> LCBCParameters:
    """Compute the exact rational optimum using ranks and closed-form water filling."""
    _validate(A, W)
    return _parameters(*_spaces(A, W))


def _extra(base: Matrix, candidates: Matrix, count: int) -> Matrix:
    """Choose actual rows using incremental exact echelon reduction.

    The basis is factored once, then each candidate needs O(d * rank) field
    operations. Selected rows retain their original coefficients and ordering.
    """
    if count < 0:
        raise ArithmeticError("negative basis quota")
    f, d = base.field, base.ncols
    if count == 0:
        return zeros(f, 0, d)
    independent = row_basis(base)
    try:
        extended = extend_basis(independent, candidates, independent.nrows + count)
    except ValueError as exc:
        raise ArithmeticError("rank inequalities do not support the requested basis quota") from exc
    return Matrix._from_validated(f, extended.rows[independent.nrows:], ncols=d)


def _columns(matrix: Matrix, columns: tuple[int, ...]) -> Matrix:
    """Select proven-valid coordinates without revalidating field entries."""
    return Matrix._from_validated(matrix.field,
                                  (tuple(row[j] for j in columns) for row in matrix),
                                  len(columns))


@dataclass(frozen=True)
class _QuotientProjection:
    """A quotient map stored as pivot indices and an at-most dim(A)-by-m block."""

    pivots: tuple[int, ...]
    columns: tuple[int, ...]
    coefficients: Matrix

    def apply(self, matrix: Matrix) -> Matrix:
        if not self.columns:
            return zeros(matrix.field, matrix.nrows, 0)
        if not self.pivots:
            return _columns(matrix, self.columns)
        return (_columns(matrix, self.columns) -
                _columns(matrix, self.pivots) @ self.coefficients)


def _quotient_projection(side: Matrix, selected: Matrix) -> _QuotientProjection:
    """Build an isomorphism on span(side, selected)/side without an annihilator.

    For an RREF side basis A with pivot set I, reduction is
    R(x) = x - x_I A, whose kernel is exactly row(A). If the m rows of S
    complement A, R(S) has rank m. Its pivot columns J therefore give an
    invertible restriction on that quotient: phi(x) = x_J - x_I A[:, J].
    The restricted map's kernel on the full ambient space can be larger than
    A; only its restriction to span(A, S) is used by the decoder templates.

    Construction stores an m-by-d residual and then an at-most dim(A)-by-m
    coefficient block, instead of a (d-dim(A))-by-d annihilator. Empty
    conditional demand needs neither a factorization nor a residual.
    """
    if not selected.nrows:
        return _QuotientProjection((), (), zeros(side.field, 0, 0))
    basis = row_basis(side)
    _, pivots = rref(basis)
    # Reduce only nonzero pivot coefficients. A generic matrix product would
    # scan every entry of A even for a single sparse selected row.
    residual_rows = []
    if side.field.q == 2:
        packed_basis = basis._binary_rows()
        for index, (bits, row) in enumerate(zip(selected._binary_rows(), selected.rows)):
            if index % 16 == 0:
                checkpoint()
            for pivot, other in zip(pivots, packed_basis):
                if row[pivot]:
                    bits ^= other
            residual_rows.append(unpack_binary(bits, side.ncols))
    else:
        _, subtract = row_operations(side.field)
        for index, row in enumerate(selected.rows):
            if index % 16 == 0:
                checkpoint()
            work = list(row)
            for pivot, other in zip(pivots, basis.rows):
                if work[pivot]:
                    factor, work[pivot] = work[pivot], 0
                    subtract(work, other, factor, pivot + 1)
            residual_rows.append(work)
    residual = Matrix._from_validated(side.field, residual_rows, side.ncols)
    _, columns = rref(residual)
    if len(columns) != selected.nrows:
        raise ArithmeticError("conditional-demand quotient lost rank")
    # Pivot coordinates whose coefficient rows vanish never affect phi. This
    # makes coordinate-side quotients a gather operation, with no matrix product.
    coefficients = _columns(basis, columns)
    relevant = [(pivot, row) for pivot, row in zip(pivots, coefficients.rows) if any(row)]
    return _QuotientProjection(
        tuple(pivot for pivot, _ in relevant), columns,
        Matrix._from_validated(side.field, (row for _, row in relevant), len(columns)))


def _pair_basis(base: Matrix, first: Matrix, second: Matrix,
                n1: int, n2: int) -> tuple[Matrix, Matrix]:
    """Select two basis quotas without repeated dependency deletion.

    Choose first-space directions outside ``base + second`` first. Only the
    remaining first-space quota can consume second-space rank. The individual
    and union rank inequalities then guarantee enough room for the second.
    """
    if n1 < 0 or n2 < 0:
        raise ArithmeticError("negative pairwise basis quota")
    base = row_basis(base)
    with_first, with_second = row_sum(base, first), row_sum(base, second)
    union = row_sum(with_first, second)
    r0 = base.nrows
    if (n1 > with_first.nrows - r0 or n2 > with_second.nrows - r0 or
            n1 + n2 > union.nrows - r0):
        raise ArithmeticError("infeasible pairwise basis quotas")
    essential_count = min(n1, union.nrows - with_second.nrows)
    essential = _extra(with_second, first, essential_count)
    filler = _extra(vstack(base, essential), first, n1 - essential_count)
    selected_first = vstack(essential, filler)
    selected_second = _extra(vstack(base, selected_first), second, n2)
    return selected_first, selected_second


def _aligned_bases(U, pair, coupled):
    """Construct B1+B2=B3, complements to pair intersections inside coupled Ui.

    Choose B3 modulo U13+U23, then decompose B3 in U1+U2 by a linear solve.
    Any such decomposition gives compatible complements for users 1 and 2.
    """
    f, d = U[0].field, U[0].ncols
    base3 = row_sum(pair[0, 2], pair[1, 2])
    B3 = _extra(base3, coupled[2], coupled[2].nrows - base3.nrows)
    if not B3.nrows:
        Z = zeros(f, 0, d)
        return Z, Z, Z
    co = solve(vstack(U[0], U[1]).T, B3.T).T
    C1 = Matrix._from_validated(f, [row[:U[0].nrows] for row in co.rows], ncols=U[0].nrows)
    C2 = Matrix._from_validated(f, [row[U[0].nrows:] for row in co.rows], ncols=U[1].nrows)
    B1, B2 = C1 @ U[0], C2 @ U[1]
    if B1 + B2 != B3:
        raise ArithmeticError("alignment identity failed")
    for i, B in enumerate((B1, B2, B3)):
        pairbase = row_sum(*(V for ij, V in pair.items() if i in ij))
        if rank(vstack(pairbase, B)) != coupled[i].nrows or B.nrows != coupled[i].nrows - pairbase.nrows:
            raise ArithmeticError("aligned complement rank verification failed")
    return B1, B2, B3


def _disjoint_common(common: Matrix, sides: Sequence[Matrix], separated: int) -> Matrix:
    """Lemma 24: a maximum common block independent modulo every side.

    Build a map from the common space to K^m injective on each intersection
    with a side. Its kernel is the requested block. All coordinates are on the
    original field; even over GF(2), no candidates need be enumerated.
    """
    f, d = common.field, common.ncols
    order = (separated,) + tuple(i for i in range(3) if i != separated)
    T1, T2, T3 = (intersection(common, sides[i]) for i in order)
    T23 = intersection(T2, T3)
    E2 = _extra(T23, T2, T2.nrows - T23.nrows)
    E3 = _extra(T23, T3, T3.nrows - T23.nrows)
    partial = vstack(T1, T23, E2, E3)
    R = _extra(partial, common, common.nrows - partial.nrows)
    basis = vstack(partial, R)
    m, c = max(T1.nrows, T2.nrows, T3.nrows), T23.nrows
    unit = eye(f, m).rows
    mapping = Matrix._from_validated(f, list(unit[:T1.nrows]) + list(unit[:c]) +
                     list(unit[c:c + E2.nrows]) + list(unit[c:c + E3.nrows]) +
                     [(0,) * m] * R.nrows, ncols=m)
    block = nullspace(mapping.T) @ basis
    if (block.nrows != common.nrows - m or
            any(rank(vstack(side, block)) != side.nrows + block.nrows for side in sides)):
        raise ArithmeticError("maximum disjoint common-block invariant failed")
    return block


def _coordinate_binary(templates, witnesses, widths) -> CoordinationResult:
    """Coordinate binary columns by linear solves, with exact inverse updates.

    The fixed common block removes the three-form common-column obstruction.
    Pair groups constrain at most two decoders. For aligned groups, the full
    relation space and spanning side spaces rule out an odd row dependency.
    These are precisely the hypotheses used in Proposition 25.
    """
    f = templates[0].fixed.field
    matrices = [t.evaluate(w) for t, w in zip(templates, witnesses)]
    inverses = [inverse(C) for C in matrices]
    mappings = [{spec.group: spec for spec in t.slots} for t in templates]
    assignment, updates, evaluations = [], 0, 0
    for g, width in enumerate(widths):
        checkpoint()
        forms = []
        for i, mapping in enumerate(mappings):
            if g in mapping:
                spec = mapping[g]
                row = inverses[i].rows[spec.column]
                forms.append(tuple(f.dot(row, col) for col in spec.linear_map.T.rows))
        try:
            x = solve(Matrix._from_validated(f, forms, ncols=width),
                      Matrix._from_validated(f, [[1] for _ in forms], ncols=1)).T.rows[0]
        except ValueError as exc:
            raise BinaryScalarRealizationUnavailable(
                "binary scalar column conditions are incompatible; this construction "
                "does not establish infeasibility and never extends the field") from exc
        assignment.append(x)
        evaluations += len(forms)
        for i, mapping in enumerate(mappings):
            if g not in mapping:
                continue
            spec = mapping[g]
            c, C, inv = spec.column, matrices[i], inverses[i]
            new_column = tuple(f.dot(row, x) for row in spec.linear_map.rows)
            delta = tuple(new_column[j] ^ C.rows[j][c] for j in range(C.nrows))
            z = tuple(f.dot(row, delta) for row in inv.rows)
            if z[c]:
                raise ArithmeticError("binary coordinated column unexpectedly singular")
            cofactor = inv.rows[c]
            inverses[i] = Matrix._from_validated(f, [
                tuple(value ^ other for value, other in zip(row, cofactor)) if z[a] else row
                for a, row in enumerate(inv.rows)], ncols=C.ncols)
            new_rows = [list(row) for row in C.rows]
            for a, value in enumerate(new_column):
                new_rows[a][c] = value
            matrices[i] = Matrix._from_validated(f, new_rows, ncols=C.ncols)
            updates += 1
    result = tuple(assignment)
    for t, C, inv in zip(templates, matrices, inverses):
        if t.evaluate(result) != C or C @ inv != eye(f, C.nrows):
            raise ArithmeticError("binary exact inverse verification failed")
    return CoordinationResult(result, tuple(matrices), len(widths), updates, evaluations)


def build_lcbc(A: Sequence[Matrix], W: Sequence[Matrix], *,
               round_up: bool = False) -> LCBCCode:
    """Build an original-field scalar code at an integer LCBC optimum.

    For q>=3 the construction covers arbitrary three-user LCBC tasks. For
    q=2 it is guaranteed when the sides span the source and some side has
    zero intersection with the sum of the other two (Proposition 25). Other
    binary tasks are attempted and may raise BinaryScalarRealizationUnavailable;
    that exception is not an infeasibility certificate.

    Redundant and empty rows are accepted. Decoders use the original input
    rows. By default, half-integral costs require an explicit two-instance lift
    by the caller. With ``round_up=True``, the integer allocation in Lemma 26
    of ``TIT_version.pdf`` instead attains ``ceil(D*)`` with one instance. The
    returned ``cost`` is this realized integer length; ``lcbc_parameters``
    continues to return the exact rational optimum. This function never
    changes fields or blocklengths.

    Coefficient coordination takes place separately in each quotient U_i/A_i,
    so its inverse matrices have orders m_i, not the ambient source dimension.
    """
    checkpoint()
    if not isinstance(round_up, bool):
        raise TypeError("round_up must be a bool")
    f, d = _validate(A, W)
    sides, U, pair, common, coupled = _spaces(A, W)
    params = _parameters(sides, U, pair, common, coupled)
    if params.cost.denominator != 1 and not round_up:
        raise ValueError("half-integral LCBC optimum: lift the task to two instances first")
    # Flooring h* is the integer-allocation argument, not rate rounding after
    # constructing an incompatible fractional allocation.
    h = params.h_star.numerator // params.h_star.denominator
    realized_cost = Fraction(sum(params.m) - params.common - h)
    a, b, m = params.common, params.b, params.m
    w = tuple(max(0, h - b[i]) for i in range(3))
    pair_count = {tuple(j for j in range(3) if j != i): w[i] for i in range(3)}
    lam = min(b[i] - sum(w[j] for j in range(3) if j != i) for i in range(3)) - a
    private_counts = tuple(m[i] - a - sum(w[j] for j in range(3) if j != i) - lam
                           for i in range(3))
    if min(a, lam, *private_counts, *w) < 0:
        raise ArithmeticError("water-filling produced a negative allocation")
    fixed_common = None
    binary_guaranteed = False
    if f.q == 2:
        separated = next((i for i in range(3) if intersection(
            sides[i], row_sum(*(sides[j] for j in range(3) if j != i))).nrows == 0), None)
        if separated is not None:
            fixed_common = _disjoint_common(common, sides, separated)
            binary_guaranteed = row_sum(*sides).nrows == d
    align_maps = None
    if lam:
        B = _aligned_bases(U, pair, coupled)
        I12, I13 = pair[0, 1], pair[0, 2]
        # Two incident pair blocks already span all common relations. Removing
        # the common part from I23 gives a basis of the full relation space,
        # reducing every aligned parameter group by dim(U123) coordinates.
        I23 = _extra(common, pair[1, 2], pair[1, 2].nrows - common.nrows)
        align_maps = (
            vstack(I12, I13, zeros(f, I23.nrows, d), B[0]),
            vstack(scalar_mul(I12, f.neg(1)), zeros(f, I13.nrows, d), I23, B[1]),
            vstack(zeros(f, I12.nrows, d), I13, I23, B[2]),
        )
    # A group carries one row of the broadcast (two rows for an aligned group).
    groups = []  # (kind, pair-label-or-None, per-user maps as row generators)
    if fixed_common is None:
        for _ in range(a):
            groups.append(("common", None, (common, common, common)))
    for ij in sorted(pair):
        maps = tuple(pair[ij] if i in ij else None for i in range(3))
        for _ in range(pair_count[ij]):
            groups.append(("pair", ij, maps))
    for _ in range(lam):
        groups.append(("aligned", None, align_maps))
    widths = tuple(next(V.nrows for V in maps if V is not None) for _, _, maps in groups)
    if any(width == 0 for width in widths):
        raise ArithmeticError("positive allocation in an empty parameter space")
    templates, witnesses, private_blocks = [], [], []
    for i in range(3):
        checkpoint()
        selected_common = fixed_common if fixed_common is not None else _extra(sides[i], common, a)
        base = vstack(sides[i], selected_common)
        incident = [ij for ij in sorted(pair) if i in ij]
        selected_pair = _pair_basis(base, pair[incident[0]], pair[incident[1]],
                                    pair_count[incident[0]], pair_count[incident[1]])
        base = vstack(base, *selected_pair)
        selected_align = _extra(base, coupled[i], lam)
        base = vstack(base, selected_align)
        private = _extra(base, U[i], private_counts[i])
        base = vstack(base, private)
        # All selected rows and group images lie in U_i. Reduce just the m_i
        # selected rows modulo A_i, then keep independent residual coordinates.
        # Applying this sparse quotient map never materializes an annihilator
        # or a dense d-by-m_i projection, including when m_i is zero.
        selected = Matrix._from_validated(f, base.rows[sides[i].nrows:], ncols=d)
        projection = _quotient_projection(sides[i], selected)
        selected_by_type = {("common", None): selected_common,
                            ("aligned", None): selected_align}
        selected_by_type.update({("pair", ij): V
                                for ij, V in zip(incident, selected_pair)})
        # Solve each homogeneous map once with all selected columns as RHS.
        # Repeated scalar solves refactored the same matrix once per column.
        coefficients, quotient_maps = {}, {}
        for kind, label, maps in groups:
            key, V = (kind, label), maps[i]
            if V is not None and key not in coefficients:
                coefficients[key] = iter(solve(V.T, selected_by_type[key].T).T.rows)
                quotient_maps[key] = projection.apply(V).T
        witness = [(0,) * r for r in widths]
        fixed_rows, slots = [], []
        if fixed_common is not None:
            fixed_rows.extend(projection.apply(fixed_common).rows)
        for g, (kind, label, maps) in enumerate(groups):
            V = maps[i]
            if V is None:
                continue
            witness[g] = next(coefficients[kind, label])
            slots.append(ColumnSpec(g, len(fixed_rows), quotient_maps[kind, label]))
            fixed_rows.append((0,) * m[i])
        fixed_rows.extend(projection.apply(private).rows)
        templates.append(DecoderTemplate(Matrix._from_validated(f, fixed_rows, ncols=m[i]).T, tuple(slots)))
        witnesses.append(witness)
        private_blocks.append(private)
    try:
        coordinated = (_coordinate_binary(templates, witnesses, widths) if f.q == 2 else
                       coordinate_columns(templates, witnesses, widths))
    except BinaryScalarRealizationUnavailable as exc:
        if binary_guaranteed:
            raise ArithmeticError("separated binary LCBC construction invariant failed") from exc
        raise
    broadcast_rows = list(fixed_common.rows) if fixed_common is not None else []
    for x, (kind, _, maps) in zip(coordinated.assignment, groups):
        if kind == "aligned":
            selected_maps = (maps[0], maps[1])
        else:
            selected_maps = (next(V for V in maps if V is not None),)
        for V in selected_maps:
            broadcast_rows.append((Matrix._from_validated(f, [x], ncols=V.nrows) @ V).rows[0])
    for private in private_blocks:
        broadcast_rows.extend(private.rows)
    broadcast = Matrix._from_validated(f, broadcast_rows, ncols=d)
    if broadcast.nrows != realized_cost:
        raise ArithmeticError("constructed broadcast length differs from exact optimum")
    decoders = []
    for a_original, demand in zip(A, W):
        co = solve(vstack(broadcast, a_original).T, demand.T).T
        C = Matrix._from_validated(f, [row[:broadcast.nrows] for row in co.rows], ncols=broadcast.nrows)
        H = Matrix._from_validated(f, [row[broadcast.nrows:] for row in co.rows], ncols=a_original.nrows)
        decoders.append((C, H))
    code = LCBCCode(broadcast, tuple(decoders), realized_cost,
                    {"common": a, "pair12": pair_count[0, 1], "pair13": pair_count[0, 2],
                     "pair23": pair_count[1, 2], "aligned": lam, "private": private_counts},
                    {"groups": coordinated.groups_processed,
                     "inverse_updates": coordinated.inverse_updates,
                     "candidate_evaluations": coordinated.candidate_evaluations,
                     "ambient_dimension": d,
                     "max_decoder_dimension": max(m),
                     "decoder_inverse_cells": sum(mi * mi for mi in m),
                     "rounded_scalar_cost": int(params.cost != realized_cost),
                     "original_field_order": f.q,
                     "binary_separation_guarantee": int(binary_guaranteed),
                     "fixed_common_columns": fixed_common.nrows if fixed_common is not None else 0})
    if not code.verify(A, W):
        raise ArithmeticError("all-source decoder identity verification failed")
    return code
