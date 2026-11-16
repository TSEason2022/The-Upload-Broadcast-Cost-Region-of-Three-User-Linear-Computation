"""Construct relays in active coordinates and broadcast jointly.

Omniscience uploads preserve every broadcast-profile branch.  Their relay
can therefore be fixed while searching the residual component.  Scalar
residual menus on two instances are only a sufficient warm start; complete
search on the lifted residual still permits cross-instance mixing.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import chain

from .errors import ConstructionError
from .linalg import block_diag, eye, lift, row_basis, row_sum, zeros
from .profile import broadcast_profile
from .structure import omniscience_relay, pure_tripod_relay


def active_relay_uploads(task, blocklength, upload_count, broadcast_count,
                         budget, max_cache_entries, accept):
    """Try a certified active decomposition before ambient exact search.

    Returned uploads use ``task.lift(blocklength)`` source coordinates.
    ``accept`` must construct and verify the joint broadcast.  A ``None``
    result leaves the caller's complete ambient fallback available.
    """
    from .active_reduction import active_reduce
    from .compiler import (_accept, _exact_relay_search, _feasible,
                           _relay_profile, _scalar_choices,
                           enumerate_subspaces, gaussian_binomial,
                           locally_generated_uploads)

    budget.set_stage("active-reduction")
    reduction = active_reduce(task)
    om, res = reduction.omniscience, reduction.residual
    if res.task.n == task.n:
        budget.count("active_reduction_no_smaller_residual")
        return None
    budget.count("active_reductions")
    budget.count("active_original_dimension", task.n)
    budget.count("active_omniscience_dimension", om.task.n)
    budget.count("active_residual_dimension", res.task.n)
    budget.count("active_passive_dimension", reduction.passive.task.n)
    L = blocklength
    lifted = task if L == 1 else task.lift(L)
    om_task = om.task if L == 1 else om.task.lift(L)
    res_task = res.task if L == 1 else res.task.lift(L)
    om_map = om.embedding if L == 1 else lift(om.embedding, L)
    res_map = res.embedding if L == 1 else lift(res.embedding, L)
    r_res = reduction.parameters.rho + reduction.parameters.r0 + reduction.parameters.b
    r_om = upload_count - L * r_res
    budget.set_stage("active-omniscience")
    om_relay = (zeros(task.field, 0, 0) if not om.task.n
                else omniscience_relay(om_task))
    if om_relay is None or om_relay.nrows != r_om:
        raise ConstructionError("active omniscience upload dimension disagrees with the exact bound")
    embedded_om = om_relay @ om_map
    om_profile = broadcast_profile(om_task.side, om_task.augmented).doubled
    ceilings = tuple(2 * broadcast_count - value for value in om_profile)

    def try_relay(P, profile=None):
        budget.check()
        profile = _relay_profile(res_task, P).doubled if profile is None else profile
        if any(value > ceiling for value, ceiling in zip(profile, ceilings)):
            budget.count("active_pruned_profile")
            return None
        joint = row_sum(embedded_om, P @ res_map)
        candidate = _accept(lifted, joint, upload_count, broadcast_count)
        if candidate is not None and accept(candidate):
            budget.count("active_joint_broadcasts")
            return candidate
        return None

    # The component construction is inexpensive, but its profile can be
    # unsuitable globally.  Every warm start still passes joint acceptance.
    budget.set_stage("active-residual-candidates")
    warm = _scalar_choices(res.task, Fraction(r_res), budget)
    if all(2 * A.nrows == res.task.n for A in res.task.side):
        tripod = pure_tripod_relay(res.task)
        if tripod is not None:
            warm = chain((tripod,), warm)
    seen = set()
    menu = []

    def add_scalar(P):
        P = row_basis(P)
        if P.rows in seen:
            return None
        seen.add(P.rows)
        if (P.nrows != r_res or not _feasible(res.task, P)
                or locally_generated_uploads(res.task, P) is None):
            return None
        profile = _relay_profile(res.task, P).doubled
        budget.count("active_scalar_residual_relays")
        if L == 1:
            return try_relay(P, profile)
        # Keep actual spaces even for equal profiles.  In particular, a
        # binary realization must not be inferred from a profile signature.
        menu.append((P, profile))
        for Q, other in menu:
            total = tuple(a + b for a, b in zip(profile, other))
            if any(a > b for a, b in zip(total, ceilings)):
                budget.count("active_pruned_profile_pairs")
                continue
            pairs = ((P, Q),) if P.rows == Q.rows else ((P, Q), (Q, P))
            for first, second in pairs:
                budget.tick()
                budget.count("active_scalar_pairs")
                candidate = try_relay(block_diag(first, second), total)
                if candidate is not None:
                    return candidate
        return None

    for P in warm:
        candidate = add_scalar(P)
        if candidate is not None:
            return candidate

    # Complete only modest scalar menus.  Larger scalar spaces go directly
    # to the adaptive lifted-residual search, without claiming this menu is
    # an exhaustive parameterization of two-instance relays.
    scalar_count = gaussian_binomial(res.task.n, r_res, task.field.q)
    if scalar_count <= 2048:
        budget.set_stage("active-residual-menu")
        for P in enumerate_subspaces(eye(task.field, res.task.n), r_res, budget):
            budget.count("active_scalar_spaces")
            candidate = add_scalar(P)
            if candidate is not None:
                return candidate

    budget.set_stage("active-residual-exact-search")
    answer = None

    def accept_residual(uploads):
        nonlocal answer
        answer = try_relay(row_sum(*uploads))
        return answer is not None

    # The residual profile alone is bounded above by the full budget; the
    # callback applies the sharper fifteen component-specific ceilings.
    # This search allows all local spaces on L instances, not just scalar
    # direct sums.  Binary broadcast insufficiency still leaves the outer
    # complete joint relay/broadcast pass available.
    _exact_relay_search(res_task, L * r_res, broadcast_count, budget,
                        max_cache_entries, accept_residual)
    return answer
