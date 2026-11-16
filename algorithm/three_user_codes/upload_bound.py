"""Compute the manuscript's exact upload optimum from arbitrary matrices.

The implementation does not require a quiver decomposition or an extension
field: the three side spaces have an elementary simultaneous normal form.
It computes the graph-relation rank before deleting passive coordinates.
Every operation is exact in the supplied finite field.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction

from .linalg import Matrix, contains, coordinates, extend_basis, intersection, nullspace, rank, row_basis, row_sum, vstack
from .task import Task


def _empty(field, n):
    return Matrix._from_validated(field, (), n)


def _select_columns(a: Matrix, indices) -> Matrix:
    indices = tuple(indices)
    return Matrix._from_validated(a.field, (tuple(r[j] for j in indices) for r in a.rows), len(indices))


def _additions(base: Matrix, candidates: Matrix) -> Matrix:
    """Preserve original candidate vectors while selecting a complement.

    An incremental echelon table avoids recomputing ranks for every row.
    The returned vectors complement ``base`` in ``base + candidates``.
    """
    independent = row_basis(base)
    extended = extend_basis(independent, candidates)
    return Matrix._from_validated(base.field, extended.rows[independent.nrows:], base.ncols)


@dataclass(frozen=True)
class SideNormalForm:
    """A basis of the joint side span and exact normal-form component bases.

    Basis order is common, K1,K2,K3, P1,P2,P3, tripod_v, tripod_r.
    Ki is known to the two users other than i. On a tripod row the three
    side directions are v, r, r-v. ``slices`` records basis-row indices.
    """
    basis: Matrix
    common: Matrix
    pair: tuple[Matrix, Matrix, Matrix]
    private: tuple[Matrix, Matrix, Matrix]
    tripod_v: Matrix
    tripod_r: Matrix
    slices: dict[str, tuple[int, ...]]


def side_normal_form(side) -> SideNormalForm:
    """Elementary deterministic three-subspace decomposition over the base field."""
    if len(side) != 3:
        raise ValueError("three side spaces are required")
    a = tuple(row_basis(x) for x in side)
    f, n = a[0].field, a[0].ncols
    if any(x.field != f or x.ncols != n for x in a):
        raise ValueError("side spaces must share field and ambient dimension")
    common = intersection(intersection(a[0], a[1]), a[2])
    pairs = []
    for i in range(3):
        j, k = (h for h in range(3) if h != i)
        pairs.append(_additions(common, intersection(a[j], a[k])))
    pairs = tuple(pairs)
    # v is independent modulo the pair components visible to user 1.
    shared_1 = row_sum(common, pairs[1], pairs[2])
    v = _additions(shared_1, intersection(a[0], row_sum(a[1], a[2])))
    # Express v = r + (v-r) using an actual basis from A2 followed by A3.
    a3_extra = _additions(a[1], a[2])
    sum23_basis = vstack(a[1], a3_extra)
    split = coordinates(v, sum23_basis)
    r = _select_columns(split, range(a[1].nrows)) @ a[1]
    marked = (v, r, r - v)
    private = []
    for i in range(3):
        j, k = (h for h in range(3) if h != i)
        private.append(_additions(row_sum(common, pairs[j], pairs[k], marked[i]), a[i]))
    private = tuple(private)
    blocks = (("common", common), *((f"K{i}", pairs[i]) for i in range(3)),
              *((f"P{i}", private[i]) for i in range(3)), ("v", v), ("r", r))
    slices = {}
    pos = 0
    for name, block in blocks:
        slices[name] = tuple(range(pos, pos + block.nrows))
        pos += block.nrows
    basis = vstack(*(block for _, block in blocks))
    # These are semantic checks of a nontrivial decomposition, not float tolerances.
    if rank(basis) != basis.nrows or not contains(basis, row_sum(*a)):
        raise ArithmeticError("internal side-space decomposition failed to produce a basis")
    for i in range(3):
        j, k = (h for h in range(3) if h != i)
        rebuilt = row_sum(common, pairs[j], pairs[k], private[i], marked[i])
        if rebuilt != a[i]:
            # Row-sum returns a canonical row basis; explicit containment makes
            # this robust to alternate canonicalization choices in a backend.
            if not contains(rebuilt, a[i]) or not contains(a[i], rebuilt):
                raise ArithmeticError("internal side-space decomposition changed an observation")
    return SideNormalForm(basis, common, pairs, private, v, r, slices)


def _task_normal_form(task) -> SideNormalForm:
    """Share a normal form only within an immutable Task's lifetime.

    Legacy task-like callers still work but are not cached: their side spaces
    might be mutable. Coordinate changes produce a fresh Task and cache.
    """
    if isinstance(task, Task):
        cached = getattr(task, "_side_normal_form_data", None)
        if cached is not None:
            return cached
    normal = side_normal_form(task.side)
    if isinstance(task, Task):
        object.__setattr__(task, "_side_normal_form_data", normal)
    return normal


@dataclass(frozen=True)
class UploadParameters:
    rho: int
    r0: int
    b: int
    c: int
    tau: tuple[int, int, int]

    @property
    def omega(self) -> Fraction:
        return max(*(Fraction(self.c + t) for t in self.tau),
                   Fraction(3 * self.c + sum(self.tau), 2))

    @property
    def cost(self) -> Fraction:
        return Fraction(self.rho + self.r0 + self.b) + self.omega


def upload_parameters(task) -> UploadParameters:
    """Compute rho,r0,b,c,tau of the manuscript's upload formula.

    Pair-demand graphs are removed by projection onto private/tripod
    coordinates. Pure tripod demands Di are retained, and graph lifts are
    used only modulo D1+D2+D3. Consequently arbitrary choices of lifts do
    not affect ``b``. In row convention B and G have domain basis vectors
    as rows, so ker(B) is computed as ``nullspace(B.T)``.
    """
    if isinstance(task, Task):
        cached = getattr(task, "_upload_parameters_data", None)
        if cached is not None:
            return cached
    f, n = task.field, task.n
    normal = _task_normal_form(task)
    sides, augmented = task.side, task.augmented
    t = normal.tripod_v.nrows
    pdims = tuple(x.nrows for x in normal.private)
    ptotal = sum(pdims)
    poffsets = (0, pdims[0], pdims[0] + pdims[1], ptotal)
    pindices = sum((normal.slices[f"P{i}"] for i in range(3)), ())
    tau = []
    for i in range(3):
        j, k = (h for h in range(3) if h != i)
        tau.append(rank(intersection(augmented[i], intersection(sides[j], sides[k]))) - normal.common.nrows)
    # All three coordinate systems share the same normal-form basis. Solve
    # their right-hand sides together, so its coefficient matrix is factored
    # only once, also when the joint side span has passive ambient columns.
    all_coeff = coordinates(vstack(*augmented), normal.basis)
    ds, ls, gs = [], [], []
    coeff_offset = 0
    for i in range(3):
        coeff = Matrix._from_validated(f,
            all_coeff.rows[coeff_offset:coeff_offset + augmented[i].nrows],
            all_coeff.ncols)
        coeff_offset += augmented[i].nrows
        pp = _select_columns(coeff, pindices)
        # Quotient by the user's own private space.
        prows = [list(row) for row in pp.rows]
        for row in prows:
            row[poffsets[i]:poffsets[i + 1]] = [0] * pdims[i]
        pp = Matrix._from_validated(f, prows, ptotal)
        cv = _select_columns(coeff, normal.slices["v"])
        cr = _select_columns(coeff, normal.slices["r"])
        tt = cr if i == 0 else cv if i == 1 else cv + cr
        q = row_basis(Matrix._from_validated(f, (tuple(x) + tuple(y) for x, y in zip(pp.rows, tt.rows)), ptotal + t))
        qp = _select_columns(q, range(ptotal))
        qt = _select_columns(q, range(ptotal, ptotal + t))
        d = row_basis(nullspace(qp.T) @ qt)
        # Independent projection rows retain the same row's tripod lift.
        chosen_p = _additions(_empty(f, ptotal), qp)
        lifts = []
        selected_rows = list(chosen_p.rows)
        # Duplicate projection rows cannot both be selected. A first occurrence
        # is a valid lift; differing choices are absorbed into Di.
        for row in selected_rows:
            index = qp.rows.index(row)
            lifts.append(qt.rows[index])
        g = Matrix._from_validated(f, lifts, t)
        ds.append(d)
        ls.append(chosen_p)
        gs.append(g)
    rho = sum(rank(row_sum(*(_select_columns(ls[i], range(poffsets[j], poffsets[j + 1]))
                              for i in range(3) if i != j))) for j in range(3))
    dsum = row_sum(*ds)
    c = rank(intersection(intersection(ds[0], ds[1]), ds[2]))
    r0 = dsum.nrows - c
    brows = []
    for i, li in enumerate(ls):
        for row in li.rows:
            out = list(row)
            # B=(x21+x31, x12+x32, x13-x23).
            if i == 1:
                for j in range(poffsets[2], poffsets[3]):
                    out[j] = f.neg(out[j])
            brows.append(out)
    bm = Matrix._from_validated(f, brows, ptotal)
    gm = vstack(*gs)
    relations = nullspace(bm.T) @ gm
    b = rank(row_sum(dsum, relations)) - dsum.nrows
    result = UploadParameters(rho, r0, b, c, tuple(tau))
    if isinstance(task, Task):
        object.__setattr__(task, "_upload_parameters_data", result)
    return result


def upload_cost(task) -> Fraction:
    """Exact regularized optimum, including half-integral omniscience cost."""
    return upload_parameters(task).cost
