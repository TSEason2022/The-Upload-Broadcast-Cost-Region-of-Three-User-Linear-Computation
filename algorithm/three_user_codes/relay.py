"""Deterministic small-field normals for the manuscript's residual relays.

These routines consume a component already satisfying the stated maximal-rank
hypotheses.  They are not a quiver-decomposition or arbitrary-task compiler.
All intersections, restrictions and profile comparisons are exact.  Input
hypotheses are checked before selection, and the complete resulting profile is
checked afterwards.  Arms are numbered 0, 1, 2 throughout this Python package.
"""
from __future__ import annotations

from itertools import combinations, permutations

from .linalg import Matrix, contains, intersection, nullspace, rank, row_basis, vstack
from .coordination import choose_outside_kernels
from .profile import broadcast_profile


class RelaySelectionError(ValueError):
    """A component fails a required relay-selection hypothesis or identity."""


def normal_relay_spaces(side, augmented, normal):
    """Return exact intersections with ``ker(normal)`` for a feasible relay.

    Unlike the component selectors below, this reduction works over every
    finite field and imposes no maximal-rank hypotheses.  If the relay has
    codimension ``c``, feasibility is checked in only ``c`` coordinates:
    ``U_i <= A_i + ker(N)`` iff ``image(U_i N.T) <= image(A_i N.T)``.
    Local intersections are then ``ker((A_i N.T).T) A_i``.  This avoids
    constructing and eliminating ambient joins for rejected dual candidates.

    Inputs are row bases over a common field.  ``None`` means precisely that
    feasibility or local generation fails; otherwise the result is
    ``(relay, local_intersections, augmented_intersections)``.
    """
    image_side = tuple(a @ normal.T for a in side)
    image_augmented = tuple(u @ normal.T for u in augmented)
    if any(not contains(a, u) for a, u in zip(image_side, image_augmented)):
        return None
    local = tuple(nullspace(image.T) @ a
                  for a, image in zip(side, image_side))
    relay = row_basis(vstack(*local))
    if relay.nrows != normal.ncols - rank(normal):
        return None
    induced = tuple(nullspace(image.T) @ u
                    for u, image in zip(augmented, image_augmented))
    return relay, local, induced


def _join(*spaces):
    return row_basis(vstack(*spaces))


def _conditioned_rank(space, side):
    return rank(vstack(space, side)) - rank(side)


def _check_maximal(side, augmented, dimension):
    m = [u.nrows - a.nrows for a, u in zip(side, augmented)]
    for i, j in combinations(range(3), 2):
        if rank(vstack(augmented[i], augmented[j])) != dimension:
            raise RelaySelectionError(f"U_{i}+U_{j} does not span the component")
        common = intersection(augmented[i], augmented[j])
        for k in (i, j):
            if _conditioned_rank(common, side[k]) != min(m[k], common.nrows):
                raise RelaySelectionError(f"pair ({i},{j}) fails maximal conditional rank at user {k}")
    common01 = intersection(augmented[0], augmented[1])
    if rank(vstack(common01, augmented[2])) != dimension:
        raise RelaySelectionError("(U_0 intersect U_1)+U_2 does not span the component")
    triple = intersection(common01, augmented[2])
    if triple.nrows > min(m):
        raise RelaySelectionError("triple intersection exceeds a demand quotient dimension")
    for i in range(3):
        if _conditioned_rank(triple, side[i]) != triple.nrows:
            raise RelaySelectionError(f"triple intersection is not transverse to A_{i}")


def _prepare(side, augmented, expected_defect):
    if len(side) != 3 or len(augmented) != 3:
        raise RelaySelectionError("exactly three side and augmented spaces are required")
    if any(not isinstance(m, Matrix) for m in (*side, *augmented)):
        raise TypeError("side and augmented spaces must be Matrix objects")
    field, dimension = side[0].field, side[0].ncols
    if field.q < 3:
        raise RelaySelectionError("the three-subspace guarantee requires field order at least 3")
    if any(m.field != field or m.ncols != dimension for m in (*side, *augmented)):
        raise RelaySelectionError("all component spaces must share a field and ambient dimension")
    side, augmented = tuple(map(row_basis, side)), tuple(map(row_basis, augmented))
    for i in range(3):
        if not contains(augmented[i], side[i]):
            raise RelaySelectionError(f"A_{i} is not contained in U_{i}")
    stacked = vstack(*side)
    if rank(stacked) != dimension:
        raise RelaySelectionError("the side spaces do not generate the full ambient component")
    relations = nullspace(stacked.T)
    if relations.nrows != expected_defect:
        raise RelaySelectionError(f"expected side-relation dimension {expected_defect}, got {relations.nrows}")
    _check_maximal(side, augmented, dimension)
    projections, start = [], 0
    for a in side:
        coeff = Matrix(field, [row[start:start+a.nrows] for row in relations.rows], ncols=a.nrows)
        projections.append(coeff @ a)
        start += a.nrows
    return side, augmented, tuple(projections)


def _nonzero_column(values):
    for column in range(values.ncols):
        form = tuple(row[column] for row in values.rows)
        if any(form):
            return form
    raise RelaySelectionError("a required nonvanishing map is identically zero over the input field")


def _nonzero_form(normal_basis, space):
    """A hyperplane containing the forbidden annihilator of ``space``."""
    return _nonzero_column(normal_basis @ space.T)


def _linear_combination(coefficients, basis):
    return Matrix(basis.field, [coefficients], ncols=basis.nrows) @ basis


def _verify_result(side, augmented, relay, corank):
    dimension = side[0].ncols
    if relay.nrows != dimension - corank:
        raise RelaySelectionError("constructed relay has incorrect codimension")
    local = tuple(intersection(a, relay) for a in side)
    induced = tuple(intersection(u, relay) for u in augmented)
    if rank(vstack(*local)) != relay.nrows:
        raise RelaySelectionError("constructed relay is not locally generated")
    for i in range(3):
        if not contains(_join(side[i], relay), augmented[i]):
            raise RelaySelectionError(f"constructed relay cannot serve user {i}'s demand")
        if induced[i].nrows - local[i].nrows != augmented[i].nrows - side[i].nrows:
            raise RelaySelectionError(f"demand quotient dimension changed for user {i}")
    _check_maximal(local, induced, relay.nrows)
    original = broadcast_profile(side, augmented)
    selected = broadcast_profile(local, induced)
    expected_first = tuple(
        max(induced[i].nrows - local[i].nrows,
            relay.nrows - local[i].nrows - local[j].nrows)
        for i, j, _ in permutations(range(3))
    )
    if tuple(selected.first) != expected_first:
        raise RelaySelectionError("one or more of the six induced first-family branches is incorrect")
    if tuple(selected.second) != tuple(original.second):
        raise RelaySelectionError("one or more of the nine second-family branches was not preserved")


def corank_one(side, augmented, arm=0):
    """Return a row basis for P=ker(ell), with ell vanishing on U_arm.

    Requires generated sides, a one-dimensional relation space, the full
    maximal-rank conditions, and proper nonvanishing conditions.  A bad arm is
    rejected explicitly; no extension or randomized retry is performed.
    """
    if not isinstance(arm, int) or isinstance(arm, bool) or arm not in range(3):
        raise RelaySelectionError("arm must be 0, 1 or 2")
    side, augmented, projections = _prepare(side, augmented, 1)
    j, k = [i for i in range(3) if i != arm]
    normal_basis = nullspace(augmented[arm])
    forms = [_nonzero_form(normal_basis, projections[j])]
    remote = (intersection(side[j], augmented[k]), intersection(side[k], augmented[j]))
    nonempty = [space for space in remote if space.nrows]
    if nonempty:
        forms.extend(_nonzero_form(normal_basis, space) for space in nonempty)
    else:
        forms.append(_nonzero_form(normal_basis, intersection(augmented[j], augmented[k])))
    coefficients = choose_outside_kernels(forms, normal_basis.nrows, normal_basis.field)
    relay = nullspace(_linear_combination(coefficients, normal_basis))
    _verify_result(side, augmented, relay, 1)
    return relay


def corank_two(side, augmented, arms=(0, 1)):
    """Return a row basis for the codimension-two R_2+n*delta relay.

    This verifies the R_2 dimension vector for n>=1. The two selected arms
    receive their own annihilating normal; all other conditions are derived
    from the side-relation kernel, not supplied as opaque witness data.
    """
    if len(arms) != 2 or any(not isinstance(i, int) or isinstance(i, bool) or i not in range(3) for i in arms) or arms[0] == arms[1]:
        raise RelaySelectionError("arms must contain two distinct indices from 0, 1, 2")
    side, augmented, projections = _prepare(side, augmented, 2)
    first, second = arms
    third = next(i for i in range(3) if i not in arms)
    n, remainder = divmod(side[0].ncols - 1, 3)
    if remainder or n < 1 or any(a.nrows != n+1 for a in side) or any(u.nrows != 2*n+1 for u in augmented):
        raise RelaySelectionError("corank_two requires the R_2+n*delta dimension vector with n>=1")
    h1, h2 = nullspace(augmented[first]), nullspace(augmented[second])
    remote1 = (intersection(side[second], augmented[third]), intersection(side[third], augmented[second]))
    remote2 = (intersection(side[first], augmented[third]), intersection(side[third], augmented[first]))
    if any(space.nrows != 1 for space in (*remote1, *remote2)):
        raise RelaySelectionError("the four designated remote intersections must be lines")
    forms1 = [_nonzero_form(h1, space) for space in remote1]
    forms2 = [_nonzero_form(h2, space) for space in remote2]
    b1, b2 = h1 @ projections[second].T, h2 @ projections[first].T
    field = h1.field
    wedge = Matrix(field, [[field.sub(field.mul(r[0], s[1]), field.mul(r[1], s[0]))
                            for s in b2.rows] for r in b1.rows], ncols=h2.nrows)
    # Choosing a single nonzero column enlarges the left radical to a proper
    # hyperplane, preserving the constant-three-exclusions guarantee.
    forms1.append(_nonzero_column(wedge))
    x1 = choose_outside_kernels(forms1, h1.nrows, field)
    second_wedge = _linear_combination(x1, wedge)
    forms2.append(tuple(second_wedge.rows[0]))
    x2 = choose_outside_kernels(forms2, h2.nrows, field)
    relay = nullspace(vstack(_linear_combination(x1, h1), _linear_combination(x2, h2)))
    _verify_result(side, augmented, relay, 2)
    return relay
