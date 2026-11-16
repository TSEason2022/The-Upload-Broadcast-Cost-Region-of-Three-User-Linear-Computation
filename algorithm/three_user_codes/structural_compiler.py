"""Certified repeated-resonant construction over the supplied finite field.

This bounded accelerator discovers direct summands from the six input flags;
it never uses generator labels.  It supports resonant R_n summands, arbitrary
private-demand edges, and a zero-excess remainder after active reduction.
Other families and unsuccessful algebra probes retain the compiler's complete
search fallback.  This is not a complete affine-quiver decomposition.
"""
from __future__ import annotations

from dataclasses import dataclass
from random import Random

from .linalg import (Matrix, contains, coordinates, eye, intersection, lift,
                     nullspace, rank, row_basis, row_sum, vstack)
from .profile import broadcast_profile
from .task import Task
from .upload_bound import _task_normal_form


_MAX_ALGEBRA_VARIABLES = 384
_MAX_STRUCTURAL_DIMENSION = 80


@dataclass(frozen=True)
class FlagComponent:
    """A compact task and its injective map into the original source rows."""
    task: Task
    embedding: Matrix


@dataclass(frozen=True)
class FlagSplit:
    """Two invariant images with independently checkable projector witnesses."""
    components: tuple[FlagComponent, FlagComponent]
    projectors: tuple[Matrix, Matrix]

    def verify(self, task):
        identity = eye(task.field, task.n)
        p, q = self.projectors
        if p + q != identity or p @ p != p or q @ q != q:
            raise ArithmeticError("flag splitting maps are not complementary projectors")
        if rank(row_sum(*(c.embedding for c in self.components))) != task.n:
            raise ArithmeticError("flag splitting images do not span the source")
        for component, projector in zip(self.components, self.projectors):
            if row_basis(projector) != row_basis(component.embedding):
                raise ArithmeticError("flag projector has the wrong image")
            for original, compact in zip(task.side + task.augmented,
                                         component.task.side + component.task.augmented):
                if not contains(original, original @ projector):
                    raise ArithmeticError("flag projector does not preserve a task subspace")
                if row_basis(original @ projector) != row_basis(compact @ component.embedding):
                    raise ArithmeticError("flag component reconstruction failed")
        return True


def _compact(task, embedding):
    """Restrict all six flags to an invariant summand and use its own basis."""
    return Task(task.field,
                tuple(coordinates(intersection(a, embedding), embedding) for a in task.side),
                tuple(coordinates(intersection(u, embedding), embedding) for u in task.augmented))


def _side_homomorphisms(reference, task, budget):
    """Preserving the sides is built in; solve only the augmented constraints.

    On pairwise-disjoint spanning sides, the side normal form consists of
    private blocks and a common tripod multiplicity space.  Endomorphisms
    have independent private maps, private-to-own-tripod maps, and the same
    map on both tripod arms.  This avoids a dense n^2-variable ambient Hom
    system.  This applies both to End(task) and to recognition Hom(reference,
    task).  Returned matrices use the tasks' compact source coordinates.
    """
    if task.n > _MAX_STRUCTURAL_DIMENSION or reference.n != task.n:
        budget.count("structural_algebra_size_skips")
        return ()
    normal = _task_normal_form(task)
    source_normal = normal if reference is task else _task_normal_form(reference)
    if (normal.common.nrows or any(k.nrows for k in normal.pair)
            or source_normal.common.nrows or any(k.nrows for k in source_normal.pair)):
        return ()
    f, n = task.field, task.n
    if (normal.basis.nrows != n or source_normal.basis.nrows != n
            or normal.slices != source_normal.slices):
        return ()
    private = [normal.slices[f"P{i}"] for i in range(3)]
    v, r = normal.slices["v"], normal.slices["r"]
    variables = sum(len(p) ** 2 + len(p) * len(v) for p in private) + len(v) ** 2
    if variables > _MAX_ALGEBRA_VARIABLES:
        budget.count("structural_algebra_size_skips")
        return ()
    minus_one = f.neg(1)
    # Each free variable is represented by its sparse matrix entries.
    terms = []
    for user, indices in enumerate(private):
        for source in indices:
            for target in indices:
                terms.append(((source, target, 1),))
            for j in range(len(v)):
                if user == 0:
                    terms.append(((source, v[j], 1),))
                elif user == 1:
                    terms.append(((source, r[j], 1),))
                else:
                    terms.append(((source, r[j], 1), (source, v[j], minus_one)))
    for i in range(len(v)):
        for j in range(len(v)):
            terms.append(((v[i], v[j], 1), (r[i], r[j], 1)))
    source_signals = tuple(coordinates(u, source_normal.basis) for u in reference.augmented)
    signals = (source_signals if reference is task else
               tuple(coordinates(u, normal.basis) for u in task.augmented))
    equations = []
    add, mul = f.add, f.mul
    for source_signal, signal in zip(source_signals, signals):
        annihilator = nullspace(signal)
        for x in source_signal.rows:
            budget.check()
            for y in annihilator.rows:
                equation = []
                for entries in terms:
                    value = 0
                    for i, j, coefficient in entries:
                        if x[i] and y[j]:
                            value = add(value, mul(mul(x[i], y[j]), coefficient))
                    equation.append(value)
                if any(equation):
                    equations.append(equation)
    budget.count("structural_hom_variables", len(terms))
    hom = nullspace(Matrix(f, equations, ncols=len(terms)))
    inverse_basis = coordinates(eye(f, n), source_normal.basis)
    result = []
    for coefficients in hom.rows:
        rows = [[0] * n for _ in range(n)]
        for coefficient, entries in zip(coefficients, terms):
            if coefficient:
                for i, j, sign in entries:
                    rows[i][j] = add(rows[i][j], mul(coefficient, sign))
        result.append(inverse_basis @ Matrix(f, rows, n) @ normal.basis)
    budget.count("structural_endomorphism_dimension" if reference is task else
                 "structural_isomorphism_dimension", len(result))
    return tuple(result)


def _endomorphisms(task, budget):
    return _side_homomorphisms(task, task, budget)


def _fitting_split(task, operator, budget):
    """Stable kernel/image split of an endomorphism; nilpotents do not split."""
    f, n = task.field, task.n
    power = operator
    old_rank = rank(power)
    if old_rank in (0, n):
        return None
    for _ in range(n.bit_length() + 1):
        budget.check()
        squared = power @ power
        new_rank = rank(squared)
        if new_rank == old_rank:
            left, right = row_basis(power), nullspace(power.T)
            if left.nrows + right.nrows != n:
                return None
            basis = vstack(left, right)
            if rank(basis) != n:
                return None
            inverse_basis = coordinates(eye(f, n), basis)
            diagonal = Matrix(f, [tuple(int(i == j and i < left.nrows) for j in range(n))
                                 for i in range(n)], n)
            p = inverse_basis @ diagonal @ basis
            q = eye(f, n) - p
            components = (FlagComponent(_compact(task, left), left),
                          FlagComponent(_compact(task, right), right))
            split = FlagSplit(components, (p, q))
            split.verify(task)
            budget.count("structural_verified_splits")
            return split
        if new_rank == 0:
            return None
        power, old_rank = squared, new_rank
    return None


def _discover_split(task, budget):
    hom = _endomorphisms(task, budget)
    if len(hom) <= 1:
        return None
    f, n = task.field, task.n
    identity = eye(f, n)
    rng = Random(0xE6A110C)
    seen = set()

    def candidates():
        yield from hom
        for _ in range(16):
            coefficients = [rng.randrange(f.q) for _ in hom]
            rows = [[0] * n for _ in range(n)]
            for c, h in zip(coefficients, hom):
                if c:
                    for i, row in enumerate(h.rows):
                        for j, value in enumerate(row):
                            if value:
                                rows[i][j] = f.add(rows[i][j], f.mul(c, value))
            yield Matrix(f, rows, n)

    scalars = tuple(range(min(f.q, 16)))
    for endomorphism in candidates():
        if endomorphism.rows in seen:
            continue
        seen.add(endomorphism.rows)
        budget.tick()
        budget.count("structural_endomorphisms_probed")
        for scalar in scalars:
            shifted = (endomorphism if not scalar else
                       endomorphism - Matrix(f, [tuple(f.mul(scalar, x) for x in row)
                                                  for row in identity.rows], n))
            answer = _fitting_split(task, shifted, budget)
            if answer is not None:
                return answer
    return None


def _resonant_embedding(task, budget):
    from .compiler import resonant_task
    n, remainder = divmod(task.n - 2, 3)
    if (remainder or n < 1 or any(a.nrows != n + 1 for a in task.side)
            or any(u.nrows != 2 * n + 1 for u in task.augmented)):
        return None
    reference = resonant_task(task.field, n)
    if reference.side == task.side and reference.augmented == task.augmented:
        transform = eye(task.field, task.n)
    else:
        transform = None
        # R_n is absolutely indecomposable.  If the two representations are
        # isomorphic, non-isomorphisms form a proper linear subspace of Hom;
        # therefore some member of every Hom basis is invertible.  This rule
        # is deliberately restricted to the certified R_n reference.
        for candidate in _side_homomorphisms(reference, task, budget):
            budget.tick()
            if rank(candidate) == task.n:
                transform = candidate
                break
    if transform is None:
        return None
    if any(row_basis(a @ transform) != b for a, b in
           zip(reference.side + reference.augmented, task.side + task.augmented)):
        raise ArithmeticError("resonant model does not reconstruct all six flags")
    budget.count("structural_resonant_components")
    return n, transform


def _resonant_components(task, budget):
    """Return certified R_n models and a profile-preserving zero-excess part."""
    resonant, zero_excess = [], []

    def visit(compact, embedding):
        budget.check()
        if compact.n > _MAX_STRUCTURAL_DIMENSION:
            budget.count("structural_algebra_size_skips")
            return False
        excess = sum(a.nrows for a in compact.side) - compact.n
        if excess == 0:
            zero_excess.append(embedding)
            return True
        if excess == 1:
            model = _resonant_embedding(compact, budget)
            if model is not None:
                size, transform = model
                resonant.append((size, transform @ embedding))
                return True
        split = _discover_split(compact, budget)
        if split is None:
            return False
        for component in split.components:
            if not visit(component.task, component.embedding @ embedding):
                return False
        return True

    if not visit(task, eye(task.field, task.n)):
        return None
    return resonant, zero_excess


def _instance_rows(matrix, instance, length):
    if length == 1:
        return matrix
    before = (0,) * (instance * matrix.ncols)
    after = (0,) * ((length - instance - 1) * matrix.ncols)
    return Matrix(matrix.field, [before + row + after for row in matrix.rows],
                  length * matrix.ncols)


def _construct(task, blocklength, upload_count, broadcast_count, budget):
    from .active_reduction import active_reduce
    from .mixing import extract_private_edges
    from .structure import omniscience_relay
    from .compiler import _feasible, _relay_profile, locally_generated_uploads

    reduction = active_reduce(task)
    om, res = reduction.omniscience, reduction.residual
    if not res.task.n:
        return None
    budget.set_stage("structural-decomposition")
    remainder, private_edges = extract_private_edges(res.task, budget)
    remaining_basis = row_sum(*remainder.side)
    if not remaining_basis.nrows:
        return None
    compact = Task(task.field,
                   tuple(coordinates(a, remaining_basis) for a in remainder.side),
                   tuple(coordinates(u, remaining_basis) for u in remainder.augmented))
    decomposition = _resonant_components(compact, budget)
    if decomposition is None:
        budget.count("structural_unrecognized_remainders")
        return None
    models, zero_excess = decomposition
    if not models:
        return None
    full_embedding = remaining_basis @ res.embedding
    models = [(size, model @ full_embedding) for size, model in models]
    zero_excess = [space @ full_embedding for space in zero_excess]
    original_edges = {edge: space @ res.embedding for edge, space in private_edges.items()}
    L, f, d = blocklength, task.field, task.n * blocklength
    lifted_models = [(size, _instance_rows(model, instance, L))
                     for instance in range(L) for size, model in models]
    edges = {edge: [row for instance in range(L)
                   for row in _instance_rows(space, instance, L).rows]
             for edge, space in original_edges.items()}
    fixed = []
    if om.task.n:
        om_task = om.task if L == 1 else om.task.lift(L)
        om_relay = omniscience_relay(om_task)
        if om_relay is None:
            return None
        fixed.extend((om_relay @ (om.embedding if L == 1 else lift(om.embedding, L))).rows)
    for instance in range(L):
        for space in zero_excess:
            fixed.extend(_instance_rows(space, instance, L).rows)

    full_profile = broadcast_profile(task.side, task.augmented)
    slack = [broadcast_count - L * value for value in full_profile.first]
    if min(slack) < 0 or any(L * value > broadcast_count for value in full_profile.second):
        return None
    plus, minus = (0, 3, 4), (1, 2, 5)
    count = len(lifted_models)
    plus_deficit = max(0, count - sum(slack[i] for i in plus))
    minus_deficit = max(0, count - sum(slack[i] for i in minus))
    if plus_deficit and minus_deficit:
        return None
    budget.set_stage("structural-cycle-allocation")
    omitted = {edge: set() for edge in edges}
    repair_count = plus_deficit or minus_deficit
    if repair_count:
        positive = bool(plus_deficit)
        cycle = ((0, 2), (1, 0), (2, 1)) if positive else ((0, 1), (1, 2), (2, 0))
        if any(len(edges[e]) < repair_count for e in cycle):
            return None
        changed_edge = (0, 2) if positive else (1, 2)
        coordinate = 1 if positive else 3
        if slack[coordinate] < repair_count:
            return None
        slack[coordinate] -= repair_count
        for index, (size, model) in enumerate(lifted_models[:repair_count]):
            budget.tick()
            x = list(model.rows[:3 * size])
            v, r = model.rows[3 * size:]
            edge_row = edges[changed_edge][index]
            subtracted = v if positive else r
            mixed = tuple(f.sub(a, b) for a, b in zip(edge_row, subtracted))
            fixed.extend(x + [r if positive else v, mixed])
            omitted[changed_edge].add(index)
        budget.count("structural_positive_cycle_repairs" if positive else
                     "structural_negative_cycle_repairs", repair_count)
    for edge, rows in edges.items():
        fixed.extend(row for index, row in enumerate(rows) if index not in omitted[edge])
    remaining = lifted_models[repair_count:]
    # Appendix D-A: disjoint capacity pairs for PT, PR, and PV.
    capacities = [min(slack[a], slack[b]) for a, b in ((0, 2), (1, 4), (3, 5))]
    if sum(capacities) < len(remaining):
        return None
    offset = 0
    for choice, capacity in enumerate(capacities):
        number = min(capacity, len(remaining) - offset)
        for size, model in remaining[offset:offset + number]:
            budget.tick()
            x = list(model.rows[:3 * size])
            v, r = model.rows[3 * size:]
            if choice == 0:
                x[size - 1] = tuple(f.add(a, b) for a, b in zip(x[size - 1], v))
                tripod = tuple(f.sub(a, b) for a, b in zip(r, v))
            elif choice == 1:
                tripod = r
            else:
                tripod = v
            fixed.extend(x + [tripod])
        offset += number
    if offset != len(remaining):
        return None
    relay = row_basis(Matrix(f, fixed, d))
    lifted_task = task if L == 1 else task.lift(L)
    if (relay.nrows != upload_count or not _feasible(lifted_task, relay)
            or locally_generated_uploads(lifted_task, relay) is None
            or _relay_profile(lifted_task, relay).cost > broadcast_count):
        raise ArithmeticError("certified structural construction failed relay validation")
    budget.count("structural_relay_candidates")
    return relay


def structural_relay_candidates(task, blocklength, upload_count, broadcast_count, budget):
    """Yield a verified lifted relay; caller must construct the joint broadcast.

    Failed recognition and the local 512-probe allowance yield no candidates.
    Global time/state limits and cancellation still propagate to the caller.
    The complete compiler fallback remains responsible for unsupported tasks.
    """
    from .compiler import _RelayProbeBudget, _RelayProbeStopped
    probe = _RelayProbeBudget(budget, 512)
    budget.count("structural_constructor_attempts")
    try:
        result = _construct(task, blocklength, upload_count, broadcast_count, probe)
    except _RelayProbeStopped:
        budget.count("structural_probe_stops")
        return
    if result is not None:
        yield result
