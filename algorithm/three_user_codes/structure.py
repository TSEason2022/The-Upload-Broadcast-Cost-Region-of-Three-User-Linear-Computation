"""Safe structural reductions and deterministic relay warm starts.

These helpers return exact subspaces in the caller's source coordinates.
They never add the broadcast optima of independent components: the fifteen
broadcast-profile branches must be combined before taking their maximum.
Failure to recognize a structure is represented by ``None`` or a single
component, and is never reported as mathematical infeasibility.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from functools import cached_property
from itertools import product

from ._resources import checkpoint
from .linalg import (Matrix, contains, coordinates, extend_basis, eye, intersection,
                     nullspace, rank, row_basis, row_sum, scalar_mul, solve, vstack, zeros)
from .task import Task


def independent_observation_relay(task: Task) -> Matrix | None:
    """An upload-optimal relay for observations independent modulo common data.

    Recognizes ``A_i = C + P_i`` with ``C = intersection_i A_i`` and
    ``C + P_0 + P_1 + P_2`` a direct sum, in arbitrary source coordinates.
    For each owner, upload exactly the projection of the other users'
    demands onto its private space. Common data and private directions
    irrelevant to remote demands require no upload. This is the inactive
    private-coordinate reduction followed by the independent-observation
    construction; no enumeration of subspaces or field elements is needed.

    The zero relay is also returned whenever every demand is already known,
    irrespective of the side-space structure. Callers still validate costs,
    locality and the global broadcast profile before accepting a code.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    checkpoint()
    if not any(task.deficits):
        return zeros(task.field, 0, task.n)
    common = intersection(intersection(task.side[0], task.side[1]), task.side[2])
    private = []
    for side in task.side:
        extended = extend_basis(common, side)
        private.append(Matrix(task.field, extended.rows[common.nrows:], ncols=task.n))
    basis = vstack(common, *private)
    if rank(basis) != basis.nrows:
        return None
    coefficients = tuple(coordinates(w, basis) for w in task.demand)
    uploads = []
    offset = common.nrows
    for owner, local in enumerate(private):
        checkpoint()
        end = offset + local.nrows
        projected = Matrix(task.field,
                           (row[offset:end] for user, w in enumerate(coefficients)
                            if user != owner for row in w.rows),
                           ncols=local.nrows)
        uploads.append(row_basis(projected) @ local)
        offset = end
    return row_basis(vstack(*uploads))


@dataclass(frozen=True)
class CoordinateComponent:
    """One coordinate-supported direct summand and its exact source embedding.

    ``P @ component.embedding`` maps any local relay basis ``P`` back to
    the source coordinates of the input task. Embeddings are materialized
    lazily so inspection of a sparse partition does not allocate an ambient
    square matrix. The component task has the same field as the input.
    """
    task: Task
    columns: tuple[int, ...]
    ambient_dimension: int

    @cached_property
    def embedding(self) -> Matrix:
        return Matrix(self.task.field,
                      (tuple(int(j == column) for j in range(self.ambient_dimension))
                       for column in self.columns),
                      ncols=self.ambient_dimension)


def coordinate_components(task: Task) -> tuple[CoordinateComponent, ...]:
    """Split disconnected coordinate supports of the six canonical flags.

    A union-find pass joins the nonzero columns of every row in ``A_i``
    and ``U_i = A_i + W_i``. Thus every one of the six spaces is a direct
    sum over the returned blocks. Canonical row bases make the partition
    insensitive to redundant rows and measurement order. All-zero ambient
    columns are omitted; an entirely empty task returns an empty tuple.

    This is a conservative, coordinate-dependent decomposition, not a
    general quiver decomposition. A connected input returns one component.
    Neither upload nor broadcast optimal costs may simply be summed here;
    the compiler validates each proposed combined relay globally.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    parent = list(range(task.n))
    sizes = [1] * task.n
    active = set()

    def root(column):
        while parent[column] != column:
            parent[column] = parent[parent[column]]
            column = parent[column]
        return column

    for space in task.side + task.augmented:
        for row in space.rows:
            checkpoint()
            support = tuple(i for i, value in enumerate(row) if value)
            active.update(support)
            if not support:
                continue
            first = root(support[0])
            for column in support[1:]:
                second = root(column)
                if first == second:
                    continue
                if sizes[first] < sizes[second]:
                    first, second = second, first
                parent[second] = first
                sizes[first] += sizes[second]
    groups = {}
    for column in sorted(active):
        groups.setdefault(root(column), []).append(column)
    output = []
    for columns_list in sorted(groups.values(), key=lambda values: values[0]):
        checkpoint()
        columns = tuple(columns_list)

        def restrict(space):
            return Matrix(task.field,
                          (tuple(row[j] for j in columns) for row in space.rows),
                          ncols=len(columns))

        local = Task(task.field, tuple(map(restrict, task.side)),
                     tuple(map(restrict, task.demand)))
        output.append(CoordinateComponent(local, columns, task.n))
    return tuple(output)


def binary_corank_one_candidates(task: Task) -> tuple[Matrix, ...]:
    """At most twelve feasible, locally generated binary corank-one relays.

    When the side spaces generate the ambient space with one relation,
    seek a hyperplane containing one user's augmented space. Nonvanishing
    on a remote relation projection guarantees that its local intersections
    span it. Instead of applying a three-hyperplane avoidance guarantee
    (which fails over GF(2)), solve every signature of at most three relevant
    forms. This costs at most four linear solves per arm, irrespective of
    ambient dimension. Every returned candidate is checked exactly.

    This finite warm start is deliberately incomplete: one representative
    per signature need not preserve every broadcast-profile branch. Global
    profile acceptance is the compiler's responsibility, and no candidate
    must not be interpreted as infeasibility. Other fields or side-relation
    dimensions return an empty tuple.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    if task.field.q != 2 or sum(a.nrows for a in task.side) != task.n + 1:
        return ()
    stacked = vstack(*task.side)
    if rank(stacked) != task.n:
        return ()
    relations = nullspace(stacked.T)
    if relations.nrows != 1:
        return ()
    projections = []
    start = 0
    for side in task.side:
        end = start + side.nrows
        coefficients = Matrix(task.field, [relations.rows[0][start:end]], side.nrows)
        projections.append(coefficients @ side)
        start = end
    candidates = []
    seen = set()
    for arm in range(3):
        checkpoint()
        j, k = (i for i in range(3) if i != arm)
        normal_basis = nullspace(task.augmented[arm])
        if not normal_basis.nrows:
            continue

        def nonzero_form(space):
            values = normal_basis @ space.T
            for column in range(values.ncols):
                form = tuple(row[column] for row in values.rows)
                if any(form):
                    return form
            return None

        first = nonzero_form(projections[j])
        if first is None:
            continue
        forms = [first]
        remote = (intersection(task.side[j], task.augmented[k]),
                  intersection(task.side[k], task.augmented[j]))
        active = tuple(space for space in remote if space.nrows)
        if not active:
            active = (intersection(task.augmented[j], task.augmented[k]),)
        for space in active:
            form = nonzero_form(space)
            if form is not None and form not in forms:
                forms.append(form)
        equations = Matrix(task.field, forms, normal_basis.nrows)
        # Prefer the simultaneous nonvanishing signature before allowing
        # any of the optional profile forms to vanish.
        for suffix in product((1, 0), repeat=len(forms) - 1):
            checkpoint()
            right = Matrix(task.field, [(value,) for value in (1,) + suffix], 1)
            try:
                coefficients = solve(equations, right).T
            except ValueError:
                continue  # This binary signature is inconsistent.
            relay = row_basis(nullspace(coefficients @ normal_basis))
            if relay.rows in seen:
                continue
            if relay.nrows != task.n - 1:
                continue
            if any(not contains(row_sum(a, relay), u)
                   for a, u in zip(task.side, task.augmented)):
                continue
            if row_sum(*(intersection(a, relay) for a in task.side)) != relay:
                continue
            seen.add(relay.rows)
            candidates.append(relay)
    return tuple(candidates)


def omniscience_relay(task: Task) -> Matrix | None:
    """Construct an optimal integral omniscience upload over the input field.

    Recognizes tasks with ``A_i + W_i = sum_j A_j`` for all three users.
    Common observations need no communication, and private directions are
    uploaded by their unique owner. The remaining pair and tripod spaces
    use the original-field construction of the manuscript's omniscience
    lemma: three pairwise disjoint kernels, followed by independent column
    completions. Every operation is a finite-field linear solve or rank
    computation, without searching field elements or local subspaces.

    A fractional optimum returns ``None``. Calling this helper on
    ``task.lift(2)`` always clears that denominator, including over GF(2),
    without extending the field. The returned row basis uses exactly the
    source coordinate order of the supplied task. As for every structural
    candidate, the compiler still checks the global upload and broadcast
    targets before accepting it.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    available = row_sum(*task.side)
    if any(u != available for u in task.augmented):
        return None
    from .upload_bound import side_normal_form
    normal = side_normal_form(task.side)
    f, n = task.field, task.n
    c = normal.tripod_v.nrows
    tau = tuple(space.nrows for space in normal.pair)
    eta = tuple(c + dimension for dimension in tau)
    total = sum(eta)
    optimum = max(*(Fraction(value) for value in eta), Fraction(total, 2))
    if optimum.denominator != 1:
        return None
    if 2 * max(eta) <= total:
        rates = tuple(total // 2 - value for value in eta)
    else:
        dominant = max(range(3), key=eta.__getitem__)
        j, k = (user for user in range(3) if user != dominant)
        rates_list = [0, 0, 0]
        rates_list[j] = eta[k]
        rates_list[k] = eta[dominant] - eta[k]
        rates = tuple(rates_list)
    # N_0, N_1 and N_2 are pairwise disjoint, including characteristic two.
    kernel_dimensions = tuple(max(c - value, 0) for value in rates)
    order = sorted(range(3), key=lambda user: (-kernel_dimensions[user], user))
    first, second, third = (kernel_dimensions[user] for user in order)
    identity = eye(f, c)
    kernels = (Matrix(f, identity.rows[:first], c),
               Matrix(f, identity.rows[first:first + second], c),
               Matrix(f, [tuple(f.add(x, y) for x, y in
                                zip(identity.rows[a], identity.rows[first + a]))
                          for a in range(third)], c))
    views = (normal.tripod_v, normal.tripod_r, normal.tripod_r - normal.tripod_v)
    matrices = [None, None, None]
    for user, kernel in zip(order, kernels):
        complement = nullspace(kernel)
        matrices[user] = vstack(complement, zeros(f, rates[user] - complement.nrows, c))
    uploads = [matrices[user] @ views[user] for user in range(3)]
    for missing_user in range(3):
        checkpoint()
        j, k = (user for user in range(3) if user != missing_user)
        # At user 1 (zero-based), knowing r leaves -v in the third view.
        right = scalar_mul(matrices[k], f.neg(1)) if missing_user == 1 else matrices[k]
        missing_tripod = vstack(matrices[j], right)
        extended = extend_basis(missing_tripod.T, eye(f, rates[j] + rates[k]),
                                c + tau[missing_user])
        added_columns = Matrix(f, extended.rows[c:], rates[j] + rates[k]).T
        for owner, rows in ((j, added_columns.rows[:rates[j]]),
                            (k, added_columns.rows[rates[j]:])):
            coefficients = Matrix(f, rows, tau[missing_user])
            uploads[owner] = uploads[owner] + coefficients @ normal.pair[missing_user]
    uploads = tuple(vstack(normal.private[user], uploads[user]) for user in range(3))
    relay = row_basis(vstack(*uploads))
    expected = sum(space.nrows for space in normal.private) + int(optimum)
    if relay.nrows != expected:
        raise ArithmeticError("omniscience construction produced an incorrect upload dimension")
    if any(not contains(a, uploaded) for a, uploaded in zip(task.side, uploads)):
        raise ArithmeticError("omniscience construction produced a nonlocal upload")
    if any(not contains(row_sum(a, relay), available) for a in task.side):
        raise ArithmeticError("omniscience construction failed an exact decoding-span check")
    return relay


def pure_tripod_relay(task: Task) -> Matrix | None:
    """An integral optimal upload candidate for functional pure-tripod tasks.

    Recognizes side spaces ``V, R, R - V`` with no common, pair or private
    summands, under an arbitrary invertible change of source coordinates.
    Decompose the three missing-view row spaces once more. On a row demanded
    by a proper subset of users, upload the view of a user outside that
    subset. A two-dimensional demand tripod with rows ``a, b, b-a`` uses
    ``V_b`` and ``R_a``. Rows common to all three demands use the original-
    field omniscience construction. This is the manuscript's residual
    row-wise upload construction in the absence of private graph terms.

    A half-integral target returns ``None``; lifting the task twice clears
    it. The returned candidate has checked locality and demand feasibility;
    the compiler must check its global broadcast profile and construct the
    broadcast before accepting it. Other side-space structures are skipped.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    from .upload_bound import side_normal_form
    normal = side_normal_form(task.side)
    if (normal.common.nrows or any(space.nrows for space in normal.pair)
            or any(space.nrows for space in normal.private)):
        return None
    f, n = task.field, task.n
    t = normal.tripod_v.nrows
    basis = vstack(normal.tripod_v, normal.tripod_r)
    missing = []
    for user, demand in enumerate(task.demand):
        coefficients = coordinates(demand, basis)
        cv = Matrix(f, [row[:t] for row in coefficients.rows], t)
        cr = Matrix(f, [row[t:] for row in coefficients.rows], t)
        missing.append(row_basis(cr if user == 0 else cv if user == 1 else cv + cr))
    demands = side_normal_form(tuple(missing))
    if demands.common.nrows % 2:
        return None
    views = (normal.tripod_v, normal.tripod_r, normal.tripod_r - normal.tripod_v)
    uploads = [zeros(f, 0, n) for _ in range(3)]
    for user in range(3):
        # Pair rows are demanded by the other two users, whereas a private
        # demand row is required by this user alone.
        uploads[user] = vstack(uploads[user], demands.pair[user] @ views[user])
        owner = (user + 1) % 3
        uploads[owner] = vstack(uploads[owner], demands.private[user] @ views[owner])
    uploads[0] = vstack(uploads[0], demands.tripod_r @ views[0])
    uploads[1] = vstack(uploads[1], demands.tripod_v @ views[1])
    common_views = tuple(demands.common @ view for view in views)
    common_available = row_sum(*common_views)
    common_task = Task(f, common_views, (common_available,) * 3)
    common_relay = omniscience_relay(common_task)
    if common_relay is None:
        raise ArithmeticError("an integral demand tripod unexpectedly required another instance")
    relay = row_sum(*uploads, common_relay)
    expected = demands.basis.nrows + demands.common.nrows // 2
    if relay.nrows != expected:
        raise ArithmeticError("pure-tripod construction produced an incorrect upload dimension")
    if any(not contains(row_sum(a, relay), w) for a, w in zip(task.side, task.demand)):
        raise ArithmeticError("pure-tripod construction failed an exact demand-span check")
    if row_sum(*(intersection(a, relay) for a in task.side)) != relay:
        raise ArithmeticError("pure-tripod construction produced a nonlocal relay")
    return relay
