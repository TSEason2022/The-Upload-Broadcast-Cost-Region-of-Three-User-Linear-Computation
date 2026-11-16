"""Certified end-to-end synthesis with constructive fast paths and exact search.

The fallback enumerates canonical local subspaces, not source samples or
floating-point approximations. It is complete when run without a search budget,
but exponential in the worst case. A budget stop never means infeasibility.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import prod
from typing import Callable
from time import monotonic

from .field import Field
from .linalg import (Matrix, zeros, eye, vstack, block_diag, lift, row_basis,
                     row_sum, rank, nullspace, intersection, contains,
                     coordinates, extend_basis, quotient_rank)
from .task import Task
from .profile import broadcast_profile
from .upload_bound import upload_cost
from .lcbc import build_lcbc
from .certificate import CodeCertificate, VerificationReport, make_certificate
from .relay import corank_one, corank_two, normal_relay_spaces, RelaySelectionError
from .errors import SearchBudgetExceeded, BlocklengthError, ConstructionError
from .progress import SearchBudget, ProgressEvent, CancellationToken
from .provenance import task_fingerprint
from ._resources import _checker
from ._kernels import pack_binary, unpack_binary, reciprocal, row_operations

from .runtime import OperatingCode


@dataclass
class CompileResult:
    certificate: CodeCertificate
    upload_optimum: Fraction
    broadcast_optimum: Fraction
    strategy: str
    stats: dict
    input_fingerprint: str | None = None

    def verify(self, original_task: Task) -> VerificationReport:
        """Recheck original-input binding, exact identities and cost formulas."""
        from .io import verify_result
        return verify_result(self, original_task)

    def operating_code(self, original_task: Task) -> OperatingCode:
        """Build an adapter preserving the caller's observation/output order."""
        self.verify(original_task)
        return OperatingCode(self.certificate, original_task)


def gaussian_binomial(n, k, q):
    if k < 0 or k > n:
        return 0
    k = min(k, n-k)
    return prod(q**(n-i)-1 for i in range(k)) // prod(q**(k-i)-1 for i in range(k))


def enumerate_subspaces(basis, dimension, budget):
    """Every dimension-k subspace once, via unique RREF coefficient matrices."""
    f = basis.field
    basis = row_basis(basis)
    n = basis.nrows
    if not 0 <= dimension <= n:
        return
    for pivots in combinations(range(n), dimension):
        free = [c for c in range(n) if c not in pivots]
        cells = [(i, c) for i, p in enumerate(pivots) for c in free if c > p]
        # itertools.product(range(q), ...) eagerly stores all q elements.
        # A mixed-radix counter keeps memory O(number of free entries), even
        # for prime fields close to 2**64.
        for encoded in range(f.q ** len(cells)):
            budget.tick()
            values = [0] * len(cells)
            for j in range(len(cells)-1, -1, -1):
                encoded, values[j] = divmod(encoded, f.q)
            rows = [[0]*n for _ in pivots]
            for i, p in enumerate(pivots):
                rows[i][p] = 1
            for (i, c), value in zip(cells, values):
                rows[i][c] = value
            yield Matrix(f, rows, ncols=n) @ basis


def locally_generated_uploads(task, P):
    """Choose an independent basis of P from the actual local intersections."""
    return _uploads_from_local(tuple(intersection(A, P) for A in task.side), P)


def _uploads_from_local(local_spaces, P):
    """Select a distributed basis from already computed local intersections."""
    f, n = P.field, P.ncols
    chosen = zeros(f, 0, n)
    uploads = []
    for local in local_spaces:
        extended = extend_basis(chosen, local)
        uploads.append(Matrix(f, extended.rows[chosen.nrows:], ncols=n))
        chosen = extended
    if chosen.nrows != P.nrows:
        return None
    return tuple(uploads)


def _feasible(task, P):
    return all(contains(row_sum(A, P), W) for A, W in zip(task.side, task.demand))


def _relay_profile(task, P):
    return broadcast_profile(tuple(intersection(A, P) for A in task.side),
                             tuple(intersection(U, P) for U in task.augmented))


def _accept(task, P, upload_count, broadcast_count):
    P = row_basis(P)
    if P.nrows != upload_count or not _feasible(task, P):
        return None
    uploads = locally_generated_uploads(task, P)
    if uploads is None or _relay_profile(task, P).cost > broadcast_count:
        return None
    return uploads


def resonant_task(field, n):
    """The manuscript's R_n, in [X1,X2,X3,V,R] coefficient coordinates."""
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError('resonant n must be positive')
    d = 3*n+2
    e = eye(field, d).rows
    add = lambda x, y: tuple(field.add(a,b) for a,b in zip(x,y))
    neg = lambda x: tuple(field.neg(a) for a in x)
    side = (Matrix(field, list(e[:n])+[e[3*n]], d),
            Matrix(field, list(e[n:2*n])+[e[3*n+1]], d),
            Matrix(field, list(e[2*n:3*n])+[add(e[3*n+1],neg(e[3*n]))], d))
    w1 = [add(e[n+j],e[2*n+j]) for j in range(n)]
    w2 = [add(e[j],e[2*n+j]) for j in range(n)]
    w3 = []
    for j in range(n):
        r = add(e[j], e[n+j])
        if j+1<n: r=add(r,e[n+j+1])
        if j==n-1: r=add(r,e[3*n])
        w3.append(r)
    return Task(field, side, tuple(Matrix(field,w,d) for w in (w1,w2,w3)))


def _flag_isomorphism(reference, task, budget):
    """Find an invertible Hom basis member for an absolutely indecomposable reference.

    For isomorphic absolutely indecomposable finite-field representations,
    non-isomorphisms form the radical, a proper linear subspace of Hom.
    Therefore at least one member of any Hom basis is invertible.
    """
    f, d = task.field, task.n
    if reference.n != d:
        return None
    equations = []
    for B, A in zip(reference.side+reference.augmented, task.side+task.augmented):
        if B.nrows != A.nrows: return None
        for v in B.rows:
            for w in nullspace(A).rows:
                budget.check()
                row = [0] * (d*d)
                for i, x in enumerate(v):
                    if x:
                        for j, y in enumerate(w):
                            if y:
                                row[i*d+j] = f._muls[x][y] if f._muls is not None else f._mul(x,y)
                equations.append(row)
    hom = nullspace(Matrix(f,equations,ncols=d*d))
    for coefficients in hom.rows:
        budget.tick()
        H = Matrix(f,[coefficients[i*d:(i+1)*d] for i in range(d)],d)
        if rank(H)==d:
            return H
    return None


def _resonant_choices(task, budget):
    if task.n < 5 or (task.n-2)%3:
        return []
    n=(task.n-2)//3
    if any(A.nrows!=n+1 for A in task.side) or any(U.nrows!=2*n+1 for U in task.augmented):
        return []
    ref=resonant_task(task.field,n)
    if all(contains(A,B) and contains(B,A) for A,B in
           zip(ref.side+ref.augmented,task.side+task.augmented)):
        H=eye(task.field,task.n)
    else:
        H=_flag_isomorphism(ref,task,budget)
    if H is None: return []
    f,d=task.field,task.n
    e=eye(f,d).rows
    pv=Matrix(f,list(e[:3*n])+[e[3*n]],d)
    pr=Matrix(f,list(e[:3*n])+[e[3*n+1]],d)
    rows=list(e[:3*n])
    rows[n-1]=tuple(f.add(a,b) for a,b in zip(rows[n-1],e[3*n]))
    rows.append(tuple(f.sub(a,b) for a,b in zip(e[3*n+1],e[3*n])))
    pt=Matrix(f,rows,d)
    return [row_basis(P@H) for P in (pv,pr,pt)]


def _scalar_choices(task, scalar_upload, budget):
    """Stream distinct sufficient relays, doing expensive recognition on demand.

    The caller tests each relay before requesting the next.  This iterator is
    deliberately incomplete; exhaustion never substitutes for exact search.
    """
    if scalar_upload.denominator != 1: return
    u=int(scalar_upload)
    f,n=task.field,task.n
    seen=set()
    def checked(P):
        budget.check()
        P=row_basis(P)
        if P.nrows==u and _feasible(task,P) and locally_generated_uploads(task,P) is not None:
            key=P.rows
            if key not in seen:
                seen.add(key)
                budget.count("scalar_candidates_yielded")
                return P
        return None
    if u==n:
        P=checked(eye(f,n))
        if P is not None: yield P
        return
    if u==0:
        P=checked(zeros(f,0,n))
        if P is not None: yield P
        return
    from .structure import independent_observation_relay, binary_corank_one_candidates
    private_relay=independent_observation_relay(task)
    if private_relay is not None:
        P=checked(private_relay)
        # This construction preserves all broadcast branches: omitted source
        # coordinates are common or unused by every remote demand.
        if P is not None:
            yield P
            return
    chi=sum(A.nrows for A in task.side)-n
    if f.q==2 and chi==1:
        for P in binary_corank_one_candidates(task):
            budget.tick()
            candidate=checked(P)
            if candidate is not None: yield candidate
    if chi==1 and f.q!=2:
        for arm in range(3):
            try: candidate=checked(corank_one(task.side,task.augmented,arm))
            except RelaySelectionError:pass
            else:
                if candidate is not None: yield candidate
    elif chi==2:
        for arms in combinations(range(3),2):
            try: candidate=checked(corank_two(task.side,task.augmented,arms=arms))
            except RelaySelectionError:pass
            else:
                if candidate is not None: yield candidate
    # Reached only after earlier relays failed joint broadcast acceptance.
    # A nonempty binary menu does not suppress all later recognition forever.
    for P in _resonant_choices(task,budget):
        candidate=checked(P)
        if candidate is not None: yield candidate
    # Coordinate candidates are inexpensive deterministic warm starts.
    # They are accepted only after exact locality and feasibility checks.
    if 0<=u<=n and (n-u<=2 or u<=2):
        identity=eye(f,n)
        for index,pivots in enumerate(combinations(range(n),u)):
            if index>=512:break
            budget.tick()
            candidate=checked(Matrix(f,[identity.rows[i] for i in pivots],n))
            if candidate is not None: yield candidate


def _cuts(task):
    """All proper user-subset upload cuts, valid for arbitrary encoders."""
    result=[]
    for mask in range(1,7):
        inside=[i for i in range(3) if mask>>i&1]
        outside=[i for i in range(3) if not mask>>i&1]
        A=row_sum(*(task.side[i] for i in outside))
        W=row_sum(*(task.demand[i] for i in outside))
        result.append((inside,rank(row_sum(A,W))-A.nrows))
    return result


def _residual_cut_data(task):
    """Coalition observations/demands reused across allocations and nodes."""
    return tuple((mask,
                  row_sum(*(task.side[i] for i in range(3) if not mask >> i & 1)),
                  row_sum(*(task.demand[i] for i in range(3) if not mask >> i & 1)))
                 for mask in range(1, 7))


class _LocalSpaces(dict):
    """Allowed uploads and forced group spans from the same exact rank pass."""
    def __init__(self, spaces, tight_groups=()):
        super().__init__(spaces)
        self.tight_groups = tuple(tight_groups)


def _local_capacity_groups(P, users, rates, allowed, budget):
    """Hall/Rado capacities modulo P; None means no independent quota split.

    If a subset is tight, every quota-respecting completion has the same
    combined span for that subset.  Store that span for exact contraction.
    """
    tight = []
    for size in range(1, len(users) + 1):
        for ids in combinations(users, size):
            budget.check()
            target = row_sum(P, *(allowed[i] for i in ids))
            capacity = target.nrows - P.nrows
            required = sum(rates[i] for i in ids)
            budget.count("local_capacity_checks")
            if capacity < required:
                budget.count("pruned_contracted_capacity" if size == 1
                             else "pruned_group_capacity")
                return None
            if capacity == required:
                tight.append((ids, target))
    return tuple(reversed(tight))


def _forced_group_uploads(P, users, rates, allowed, budget):
    """Construct one independent quota split of a forced group span.

    A finite colored basis of each C_i suffices for this independence-only
    subproblem.  Choose a vector only when all remaining Hall capacities
    survive.  The Rado condition guarantees one such basis vector exists.
    This is NOT a replacement for general demand-aware subspace search.
    """
    remaining = {i: rates[i] for i in users}
    chosen = {i: [] for i in users}
    current = P
    for i in users:
        while remaining[i]:
            remaining[i] -= 1
            rest = tuple(j for j in users if remaining[j])
            for row in allowed[i].rows:
                budget.check()
                vector = Matrix._from_validated(P.field, (row,), P.ncols)
                extended = row_sum(current, vector)
                if extended.nrows != current.nrows + 1:
                    continue
                if _local_capacity_groups(extended, rest, remaining,
                                          allowed, budget) is None:
                    continue
                chosen[i].append(row)
                current = extended
                budget.count("forced_group_basis_vectors")
                break
            else:
                raise ConstructionError("Hall-feasible forced group has no quota basis extension")
    return {i: Matrix._from_validated(P.field, chosen[i], P.ncols)
            for i in users}


def _residual_upload_spaces(task, P, users, rates, budget, cut_data=None):
    """Exact residual cuts and forced local spaces; None proves no completion.

    Give the already uploaded P to each outside coalition as a genie. For
    S among the remaining users, its uploads must cover outside demands
    modulo B=P+sum(A_i, i outside S). If that deficit equals sum(r_i, i in S),
    their image is *exactly* the missing-demand space. Consequently every
    remaining upload of user j in S belongs to A_j intersect (B+W_outside).
    Only upload choices are restricted: original receiver side information
    is never changed.
    """
    allowed = {i: task.side[i] for i in users}
    remaining_mask = sum(1 << i for i in users)
    data = _residual_cut_data(task) if cut_data is None else cut_data
    for mask, outside_side, outside_demand in data:
        if mask & ~remaining_mask:
            continue
        budget.check()
        ids = tuple(i for i in users if mask >> i & 1)
        capacity = sum(rates[i] for i in ids)
        base = row_sum(P, outside_side)
        deficit = quotient_rank(outside_demand, base)
        budget.count("residual_cut_checks")
        if deficit > capacity:
            budget.count("pruned_residual_cut")
            return None
        if deficit == capacity and capacity:
            target = row_sum(base, outside_demand)
            for i in ids:
                if not rates[i]:
                    continue
                contracted = intersection(allowed[i], target)
                if contracted.nrows < allowed[i].nrows:
                    budget.count("tight_cut_contractions")
                    budget.count("tight_cut_dimensions_removed",
                                 allowed[i].nrows - contracted.nrows)
                    allowed[i] = contracted
    # Individual capacities do not detect conflicting pair allocations.
    # There are at most seven subsets, including the complete remaining set.
    tight = _local_capacity_groups(P, users, rates, allowed, budget)
    return None if tight is None else _LocalSpaces(allowed, tight)


class _SubspacePool:
    """Lazy, compile-local cache; hits still count as visited search states.

    Reservations cap BOTH entry count and coefficient cells. Enumeration is
    never eagerly exhausted, so a first successful candidate stays cheap.
    """
    def __init__(self, task, budget, max_entries):
        self.task, self.budget = task, budget
        self.remaining_entries = max_entries
        self.remaining_cells = 1_000_000
        self.entries = {}

    def iterate(self, user, dimension):
        key = user, dimension
        if key not in self.entries:
            basis = self.task.side[user]
            size = gaussian_binomial(basis.nrows, dimension, basis.field.q)
            cells = size * max(1, dimension * basis.ncols)
            if size > self.remaining_entries or cells > self.remaining_cells:
                yield from enumerate_subspaces(basis, dimension, self.budget)
                return
            self.remaining_entries -= size
            self.remaining_cells -= cells
            self.entries[key] = [[], enumerate_subspaces(basis, dimension, self.budget), False]
        entry = self.entries[key]
        index = 0
        while True:
            if index < len(entry[0]):
                self.budget.tick()
                self.budget.count("subspace_cache_hits")
                local = entry[0][index]
            elif entry[2]:
                return
            else:
                try:
                    local = next(entry[1])
                except StopIteration:
                    entry[2] = True
                    return
                entry[0].append(local)
                self.budget.count("cached_subspaces")
            index += 1
            yield local


def _upload_allocations(task, upload_count, budget):
    """Cut-feasible upload allocations ordered by exact enumeration count."""
    f=task.field
    dims=[A.nrows for A in task.side]
    cuts=_cuts(task)
    allocations=[]
    for r0 in range(min(dims[0],upload_count)+1):
        budget.check()
        for r1 in range(min(dims[1],upload_count-r0)+1):
            rates=(r0,r1,upload_count-r0-r1)
            if not 0<=rates[2]<=dims[2]:continue
            if any(sum(rates[i] for i in ids)<bound for ids,bound in cuts):continue
            count=prod(gaussian_binomial(a,r,f.q) for a,r in zip(dims,rates))
            allocations.append((count,rates))
    allocations.sort()
    return allocations


def _normal_prefixes(field, n, codimension, budget, viable):
    """Canonical RREF normals, pruning only completed independent-row prefixes.

    The leaf order is identical to enumerate_subspaces(eye(...), ...). Each
    visited prefix is a budgeted state, including every unpruned leaf. No
    field-sized product pool is allocated.
    """
    if not 0 <= codimension <= n:
        return
    if codimension <= 1 or codimension == n:
        yield from enumerate_subspaces(eye(field, n), codimension, budget)
        return
    for pivots in combinations(range(n), codimension):
        free = tuple(c for c in range(n) if c not in pivots)
        columns = tuple(tuple(c for c in free if c > p) for p in pivots)
        suffix_cells = [0] * (codimension + 1)
        for i in range(codimension - 1, -1, -1):
            suffix_cells[i] = suffix_cells[i + 1] + len(columns[i])
        rows = []

        def visit(depth):
            for encoded in range(field.q ** len(columns[depth])):
                budget.tick()
                row = [0] * n
                row[pivots[depth]] = 1
                for column in reversed(columns[depth]):
                    encoded, row[column] = divmod(encoded, field.q)
                rows.append(row)
                prefix = Matrix(field, rows, ncols=n)
                if depth + 1 == codimension:
                    yield prefix
                elif viable(prefix, field.q ** suffix_cells[depth + 1]):
                    yield from visit(depth + 1)
                rows.pop()

        yield from visit(0)


def _hyperplane_values(space, row):
    """Evaluate one already validated functional on a maintained basis."""
    f = space.field
    if f.q == 2:
        packed = pack_binary(row)
        return tuple((bits & packed).bit_count() & 1 for bits in space._binary_rows())
    if f.degree == 1:
        return tuple(sum(a*b for a, b in zip(v, row)) % f.p for v in space.rows)
    mul, add = f._multiplication(), f._add
    values = []
    for v in space.rows:
        value = 0
        for a, b in zip(v, row):
            if a and b:
                value = add(value, mul(a, b))
        values.append(value)
    return tuple(values)


def _restrict_hyperplane(space, values, budget):
    """One-pivot kernel update; input rows are independent, not necessarily RREF."""
    pivot = next((i for i, value in enumerate(values) if value), None)
    if pivot is None:
        return space
    f = space.field
    if f.q == 2:
        source = space._binary_rows()
        rows = (unpack_binary(bits ^ (source[pivot] if values[i] else 0), space.ncols)
                for i, bits in enumerate(source) if i != pivot)
        result = Matrix._from_validated(f, rows, space.ncols)
    else:
        scale, subtract = row_operations(f)
        normalized = scale(space.rows[pivot], reciprocal(f, values[pivot]))
        rows = []
        for i, row in enumerate(space.rows):
            if i % 16 == 0:
                budget.check()
            if i == pivot:
                continue
            if values[i]:
                row = list(row)
                subtract(row, normalized, values[i])
            rows.append(row)
        result = Matrix._from_validated(f, rows, space.ncols)
    budget.count("dual_kernel_rank_one_updates")
    return result


def _normal_kernel_prefixes(task, codimension, budget, viable):
    """Canonical normal enumeration with reversible exact intersection states.

    At a feasible prefix keep C_i=A_i intersect ker(N) and
    D_i=U_i intersect ker(N).  Appending v preserves feasibility precisely
    when C_i v is nonzero or D_i v is zero for every user.  Accepted steps
    update all intersections by one-pivot elimination; no full nullspace
    or growing image matrix is recomputed.  Sibling states are immutable.
    """
    f, n = task.field, task.n
    if not 0 <= codimension <= n:
        return
    if codimension <= 1 or codimension == n:
        for normal in enumerate_subspaces(eye(f, n), codimension, budget):
            budget.count("dual_normal_candidates")
            spaces = normal_relay_spaces(task.side, task.augmented, normal)
            if spaces is None:
                budget.count("dual_pruned_infeasible_or_nonlocal")
            else:
                yield spaces
        return
    for pivots in combinations(range(n), codimension):
        free = tuple(c for c in range(n) if c not in pivots)
        columns = tuple(tuple(c for c in free if c > p) for p in pivots)
        suffix = [0] * (codimension + 1)
        for i in range(codimension - 1, -1, -1):
            suffix[i] = suffix[i + 1] + len(columns[i])

        def visit(depth, local, induced):
            leaf = depth + 1 == codimension
            for encoded in range(f.q ** len(columns[depth])):
                budget.tick()
                budget.count("dual_normal_candidates" if leaf else "dual_normal_prefixes")
                row = [0] * n
                row[pivots[depth]] = 1
                for column in reversed(columns[depth]):
                    encoded, row[column] = divmod(encoded, f.q)
                new_local, new_induced = [], []
                for a, u in zip(local, induced):
                    av = _hyperplane_values(a, row)
                    uv = _hyperplane_values(u, row)
                    if not any(av) and any(uv):
                        budget.count("dual_pruned_infeasible_or_nonlocal" if leaf
                                     else "dual_pruned_prefix_infeasible")
                        break
                    new_local.append(_restrict_hyperplane(a, av, budget))
                    new_induced.append(_restrict_hyperplane(u, uv, budget))
                else:
                    new_local, new_induced = tuple(new_local), tuple(new_induced)
                    if leaf:
                        relay = row_sum(*new_local)
                        if relay.nrows == n - codimension:
                            yield relay, new_local, new_induced
                        else:
                            budget.count("dual_pruned_infeasible_or_nonlocal")
                    elif viable(new_local, f.q ** suffix[depth + 1]):
                        yield from visit(depth + 1, new_local, new_induced)

        yield from visit(0, task.side, task.augmented)


def _exact_dual_relay_search(task, upload_count, broadcast_count, budget, accept):
    """Exact normal-prefix search using incremental side/demand kernels."""
    def viable(local, completions):
        # Bound expensive work by its potential saving. Small residual trees
        # reach their complete candidate directly, preserving cheap exits.
        if completions < 4:
            return True
        optimistic = row_sum(*local)
        # Every locally generated final relay is contained in optimistic,
        # even when ker(normal) itself is not locally generated.
        if optimistic.nrows < upload_count:
            budget.count("dual_pruned_prefix_capacity")
            return False
        if not _feasible(task, optimistic):
            budget.count("dual_pruned_prefix_local_feasibility")
            return False
        if completions >= 32 and broadcast_count < upload_count:
            budget.count("dual_prefix_profile_checks")
            if _relay_profile(task, optimistic).cost > broadcast_count:
                budget.count("dual_pruned_prefix_profile")
                return False
        return True

    for relay,local,induced in _normal_kernel_prefixes(
            task, task.n-upload_count, budget, viable):
        if broadcast_profile(local,induced).cost>broadcast_count:
            budget.count("dual_pruned_profile")
            continue
        candidate=_uploads_from_local(local,relay)
        if accept is None or accept(candidate):
            return candidate
        budget.count("rejected_broadcast_realizations")
    return None


def _exact_relay_search(task, upload_count, broadcast_count, budget,
                        max_cache_entries=2048, accept=None):
    """Adaptively enumerate canonical local uploads or dual relay spaces.

    ``accept`` returns true only after original-field broadcast realization.
    A profile bound alone does not establish scalar attainability over GF(2).
    Its answer must depend only on the relay space, not the uploaded basis,
    because failed-state memoization identifies equal row spaces. Both search
    representations are complete; the smaller exact candidate-count bound
    determines the representation, never an arbitrary scalar-search limit.
    """
    f,n=task.field,task.n
    dims=[A.nrows for A in task.side]
    allocations=_upload_allocations(task,upload_count,budget)
    local_count=sum(count for count,_ in allocations)
    dual_count=gaussian_binomial(n,upload_count,f.q)
    root_spaces = {}
    # Root tight cuts can turn an apparently huge local enumeration into a
    # unique relay. Re-estimate a bounded number of promising allocations,
    # retaining the original rigorous upper bound for every untouched one.
    # Do not tax the one-candidate or small-tree early-exit paths.
    if dual_count >= 32 and dual_count <= local_count:
        cut_data = _residual_cut_data(task)
        empty = zeros(f, 0, n)
        revised = []
        for index, (count, rates) in enumerate(allocations):
            if index < 16:
                users = tuple(i for i in range(3) if rates[i])
                allowed = _residual_upload_spaces(task, empty, users, rates, budget, cut_data)
                root_spaces[rates] = allowed
                budget.count("root_cut_estimates")
                count = (prod(gaussian_binomial(allowed[i].nrows, rates[i], f.q)
                              for i in users) if allowed is not None else 0)
            if count:
                revised.append((count, rates))
        allocations = sorted(revised)
        local_count = sum(count for count, _ in allocations)
    if 0<=upload_count<=n and dual_count<=local_count:
        budget.count("dual_relay_searches")
        return _exact_dual_relay_search(task,upload_count,broadcast_count,budget,accept)
    budget.count("local_relay_searches")
    return _exact_local_relay_search(task, upload_count, broadcast_count, budget,
                                    max_cache_entries, accept, allocations, root_spaces)


def _exact_local_relay_search(task, upload_count, broadcast_count, budget,
                              max_cache_entries=2048, accept=None, allocations=None,
                              root_spaces=None):
    """Complete local search with residual cuts and dynamic constrained order."""
    f, n = task.field, task.n
    if allocations is None:
        allocations = _upload_allocations(task, upload_count, budget)
    pool = _SubspacePool(task, budget, max_cache_entries)
    cut_data = _residual_cut_data(task)
    failed = set()
    memo_cells = 0
    for _,rates in allocations:
        budget.check()
        picked=[zeros(f, 0, n) if not r else None for r in rates]

        def visit(users,P):
            nonlocal memo_cells
            budget.check()
            key=(tuple((j,rates[j]) for j in users),P.rows)
            if key in failed:
                budget.count("failed_subtree_cache_hits")
                return None
            if not users:
                if _feasible(task,P) and _relay_profile(task,P).cost<=broadcast_count:
                    candidate=tuple(picked)
                    if accept is None or accept(candidate):
                        return candidate
                    budget.count("rejected_broadcast_realizations")
                budget.count("rejected_leaves")
            else:
                if not P.nrows and root_spaces is not None and rates in root_spaces:
                    allowed = root_spaces[rates]
                    budget.count("root_cut_estimate_reuses")
                else:
                    allowed = _residual_upload_spaces(task, P, users, rates,
                                                      budget, cut_data)
                if allowed is not None:
                    # A tight group has a forced combined relay, so all of
                    # its quota decompositions are equivalent for acceptance.
                    # Keep cheap one-candidate cases on the ordinary path.
                    group = next(((ids, target) for ids, target in
                                  getattr(allowed, "tight_groups", ())
                                  if len(ids) > 1 and any(
                                      quotient_rank(allowed[j], P) > rates[j]
                                      for j in ids)), None)
                    if group is not None:
                        ids, combined = group
                        assignment = _forced_group_uploads(P, ids, rates, allowed, budget)
                        for j in ids:
                            picked[j] = assignment[j]
                        budget.tick()
                        budget.count("tight_groups_collapsed")
                        budget.count("tight_group_users", len(ids))
                        rest = tuple(j for j in users if j not in ids)
                        answer = visit(rest, combined)
                        if answer is not None:
                            return answer
                    else:
                        choices = []
                        for j in users:
                            overlap = intersection(allowed[j], P) if P.nrows else P
                            extended = extend_basis(overlap, allowed[j]) if overlap.nrows else allowed[j]
                            complement = (Matrix(f, extended.rows[overlap.nrows:], ncols=n)
                                          if overlap.nrows else extended)
                            count = gaussian_binomial(complement.nrows, rates[j], f.q)
                            choices.append((count, j, complement, overlap.nrows))
                        count, i, complement, overlap_size = min(choices, key=lambda x: (x[0], x[1]))
                        rest = tuple(j for j in users if j != i)
                        future = (row_sum(*(allowed[j] for j in rest)) if rest
                                  else zeros(f, 0, n))
                        optimistic = row_sum(P, allowed[i], future)
                        feasible = _feasible(task, optimistic)
                        if not feasible:
                            budget.count("pruned_unattainable")
                        # A feasible larger relay gives a valid *lower* broadcast
                        # bound. Never use the incomplete P's profile here.
                        elif count >= 32 and broadcast_count < upload_count and len(users) < 3:
                            budget.count("local_optimistic_profile_checks")
                            if _relay_profile(task, optimistic).cost > broadcast_count:
                                budget.count("pruned_optimistic_profile")
                                feasible = False
                        if feasible:
                            if overlap_size:
                                budget.count("quotient_local_enumerations")
                            if complement == task.side[i]:
                                locals_iter = pool.iterate(i, rates[i])
                            else:
                                locals_iter = enumerate_subspaces(complement, rates[i], budget)
                            remaining_count = sum(rates[j] for j in rest)
                            for local in locals_iter:
                                combined=row_sum(P,local)
                                if combined.nrows!=P.nrows+rates[i]:
                                    budget.count("pruned_dependent")
                                    continue
                                if rest and not _feasible(task,row_sum(combined,future)):
                                    budget.count("pruned_unattainable")
                                    continue
                                if any(quotient_rank(W,row_sum(A,combined))>remaining_count
                                       for A,W in zip(task.side,task.demand)):
                                    budget.count("pruned_deficit")
                                    continue
                                picked[i]=local
                                answer=visit(rest,combined)
                                if answer is not None:
                                    return answer
            cells=max(1,P.nrows*P.ncols)
            if len(failed)<max_cache_entries and memo_cells+cells<=1_000_000:
                failed.add(key)
                memo_cells+=cells
                budget.count("cached_failed_subtrees")
            return None
        answer=visit(tuple(i for i in range(3) if rates[i]),zeros(f,0,n))
        if answer is not None:return answer
    return None


class _RelayProbeStopped(Exception):
    """Private control flow: a same-length warm start used its local allowance."""


class _RelayProbeBudget:
    """Forward every global limit and cancellation check without resetting it."""
    def __init__(self, parent, limit):
        self.parent, self.limit, self.used = parent, limit, 0

    def __getattr__(self, name):
        return getattr(self.parent, name)

    def tick(self, amount=1):
        self.parent.check()
        if self.used + amount > self.limit:
            raise _RelayProbeStopped()
        self.parent.tick(amount)
        self.used += amount


def _exact_relay_probe(task, upload_count, broadcast_count, budget,
                       max_cache_entries=2048, accept=None, max_states=32):
    """Try a small exact search at the *same* blocklength before preprocessing.

    Only the private local stop is caught. Global SearchBudgetExceeded and
    cancellation propagate unchanged; all work is charged to the parent.
    A stopped probe establishes neither infeasibility nor a larger length.
    """
    probe = _RelayProbeBudget(budget, max_states)
    start = budget.states
    budget.count("same_length_probe_searches")
    try:
        result = _exact_relay_search(task, upload_count, broadcast_count, probe,
                                     max_cache_entries, accept)
        if result is not None:
            budget.count("same_length_probe_successes")
        return result
    except _RelayProbeStopped:
        budget.count("same_length_probe_stops")
        return None
    finally:
        budget.count("same_length_probe_states", budget.states - start)


def _complete_broadcast(task, uploads, target, *, budget=None, exhaustive=False):
    raw=vstack(*uploads)
    E=row_basis(raw)
    # Canonical relay coordinates make constructive acceptance invariant
    # under alternative local upload bases, as required by search memoization.
    # Convert the completed broadcast back to the actual upload order.
    side=tuple(coordinates(intersection(A,E),E) for A in task.side)
    want=tuple(coordinates(intersection(U,E),E) for U in task.augmented)
    from .lcbc import BinaryScalarRealizationUnavailable
    try:
        bc=build_lcbc(side,want,round_up=True)
    except BinaryScalarRealizationUnavailable:
        if not exhaustive:
            return None
        # A non-separated binary task can fail the sufficient constructive
        # conditions without being impossible. Enumerating all target-rank
        # broadcast spaces proves (non)existence for this fixed relay. This
        # last-resort pass is exponential and shares the compile budget.
        if budget is None:
            raise ValueError("exhaustive broadcast realization requires a budget")
        for B in enumerate_subspaces(eye(task.field,E.nrows),target,budget):
            budget.count("broadcast_subspaces")
            if all(contains(row_sum(A,B),W) for A,W in zip(side,want)):
                return B @ coordinates(E,raw)
        return None
    B=bc.broadcast
    if B.nrows!=target:
        raise ConstructionError('LCBC construction disagrees with the target cost')
    return B @ coordinates(E,raw)


def _compile_impl(task, *, budget, fast_paths, force_blocklength, max_cache_entries):
    """Synthesize at the original field and at most two source instances.

    General relay selection retains a complete exponential fallback. Binary
    profile feasibility is checked separately from scalar realizability; a
    failed sufficient construction never becomes an infeasibility claim.
    """
    if not isinstance(task,Task):
        raise TypeError('task must be a Task')
    if (force_blocklength is not None and (isinstance(force_blocklength, bool) or
            not isinstance(force_blocklength, int) or force_blocklength not in (1,2))):
        raise ValueError('force_blocklength counts original-field instances and must be 1 or 2')
    if not isinstance(fast_paths, bool):
        raise TypeError('fast_paths must be a bool')
    started=budget.start
    budget.set_stage("bounds")
    U=Fraction(upload_cost(task))
    D=Fraction(broadcast_profile(task.side,task.augmented).cost)
    if force_blocklength is not None and (
            (U*force_blocklength).denominator != 1 or (D*force_blocklength).denominator != 1):
        raise BlocklengthError("Requested original-field blocklength does not clear the exact rate denominators")
    budget.set_stage("preprocessing")
    field=task.field
    F=row_sum(*task.side)
    reduced=Task(field,tuple(coordinates(A,F) for A in task.side),
                 tuple(coordinates(W,F) for W in task.demand))
    minimum_length=1 if U.denominator==D.denominator==1 else 2
    lengths=[force_blocklength if force_blocklength is not None else minimum_length]
    for L in lengths:
        budget.set_stage(f"relay-search-L{L}")
        lifted=reduced if L==1 else reduced.lift(L)
        r,s=int(U*L),int(D*L)
        B=None
        unavailable=False
        exhaustive=False
        structural_attempted=False
        strategy='exact-local-subspace-search'

        def accept(candidate):
            nonlocal B,unavailable
            relay_stage=budget.stage
            budget.set_stage("broadcast")
            B=_complete_broadcast(lifted,candidate,s,budget=budget,exhaustive=exhaustive)
            if B is None:
                unavailable=True
                budget.set_stage(relay_stage)
                return False
            return True

        def try_structural():
            nonlocal structural_attempted
            structural_attempted=True
            from .structural_compiler import structural_relay_candidates
            for P in structural_relay_candidates(reduced,L,r,s,budget):
                candidate=_accept(lifted,P,r,s)
                if candidate is not None and accept(candidate):
                    return candidate
            budget.set_stage(f"relay-search-L{L}")
            return None

        uploads=None
        if fast_paths:
            if r==lifted.n:
                candidate=_accept(lifted,eye(field,lifted.n),r,s)
                if candidate is not None and accept(candidate):
                    uploads=candidate
                    strategy='full-relay'
            if uploads is None and all(Ui.nrows==lifted.n for Ui in lifted.augmented):
                from .structure import omniscience_relay
                P=omniscience_relay(lifted)
                if P is not None:
                    candidate=_accept(lifted,P,r,s)
                    if candidate is not None and accept(candidate):
                        uploads=candidate
                        strategy='constructive-omniscience'
            if uploads is None and all(2*A.nrows==lifted.n for A in lifted.side):
                from .structure import pure_tripod_relay
                P=pure_tripod_relay(lifted)
                if P is not None:
                    candidate=_accept(lifted,P,r,s)
                    if candidate is not None and accept(candidate):
                        uploads=candidate
                        strategy='constructive-pure-tripod'
            # Multiple side relations are the natural repeated-component
            # regime.  On larger integral-upload tasks, try the bounded
            # structural constructor before corank and coordinate menus.
            # Single-relation tasks retain their inexpensive lazy path.
            if (uploads is None and U.denominator==1 and reduced.n>=10
                    and sum(A.nrows for A in reduced.side)-reduced.n>=2):
                budget.count("early_structural_dispatches")
                uploads=try_structural()
                if uploads is not None:
                    strategy='constructive-structural-components'
            # Pull one relay at a time.  Cheap successful candidates avoid
            # every later recognizer and coordinate-subspace warm start.
            # For L=2, retain the bounded menu and test each new cross-pair;
            # no old/new combination is lost by streaming.  Profile merging
            # is only a sufficient warm start, never an exact binary quotient.
            profiled=[]
            signatures=set()
            if uploads is None:
                for scalar in _scalar_choices(reduced,U,budget):
                    budget.check()
                    profile=_relay_profile(reduced,scalar).doubled
                    if L==2 and profile in signatures:
                        continue
                    signatures.add(profile)
                    profiled.append((scalar,profile))
                    j=len(profiled)-1
                    options=((j,),) if L==1 else ((i,j) for i in range(j+1))
                    for option in options:
                        budget.tick()
                        if any(sum(profiled[i][1][k] for i in option)>2*s for k in range(15)):
                            budget.count("pruned_profile_combinations")
                            continue
                        P=(scalar if L==1 else
                           block_diag(*(profiled[i][0] for i in option)))
                        candidate=_accept(lifted,P,r,s)
                        if candidate is not None and accept(candidate):
                            uploads=candidate
                            strategy='constructive-scalar-relay-combination'
                            break
                    if uploads is not None or (L==2 and len(profiled)>=64):
                        break
            # Edge extraction and flag isomorphism are useful repairs, but
            # substantially more expensive than already available corank
            # relays. Run them only after every inexpensive construction has
            # failed, and test only genuinely new relay combinations.
            if (uploads is None and U.denominator==1 and
                    sum(A.nrows for A in reduced.side)-reduced.n==1):
                from .mixing import demand_cycle_candidates
                budget.count("demand_cycle_searches")
                previous_count=len(profiled)
                seen_spaces={P.rows for P,_ in profiled}
                for P in demand_cycle_candidates(reduced,budget):
                    budget.tick()
                    P=row_basis(P)
                    if P.rows in seen_spaces or P.nrows!=int(U):
                        continue
                    if not _feasible(reduced,P) or locally_generated_uploads(reduced,P) is None:
                        continue
                    seen_spaces.add(P.rows)
                    profiled.append((P,_relay_profile(reduced,P).doubled))
                indices=(((i,) for i in range(previous_count,len(profiled))) if L==1 else
                         ((i,j) for j in range(previous_count,len(profiled))
                          for i in range(j+1)))
                for option in indices:
                    budget.tick()
                    if any(sum(profiled[i][1][k] for i in option)>2*s for k in range(15)):
                        budget.count("pruned_profile_combinations")
                        continue
                    P=profiled[option[0]][0] if L==1 else block_diag(*(profiled[i][0] for i in option))
                    candidate=_accept(lifted,P,r,s)
                    if candidate is not None and accept(candidate):
                        uploads=candidate
                        strategy='constructive-demand-cycle-repair'
                        break
        if uploads is None and fast_paths and L == 1:
            # Release measurements found easy scalar instances finishing in
            # 3--20 exact states, before active reduction's fixed setup paid
            # off. A 32-state same-L warm start covers those cheap exits.
            uploads=_exact_relay_probe(lifted,r,s,budget,max_cache_entries,accept)
            if uploads is not None:
                strategy='exact-same-length-probe'
        if uploads is None and fast_paths and not structural_attempted:
            uploads=try_structural()
            if uploads is not None:
                strategy='constructive-structural-components'
        if uploads is None and fast_paths:
            from .active_relay import active_relay_uploads
            uploads=active_relay_uploads(reduced,L,r,s,budget,max_cache_entries,accept)
            if uploads is not None:
                strategy='constructive-active-reduction'
        if uploads is None:
            budget.set_stage(f"relay-search-L{L}")
            previous_dual_searches=budget.counters.get("dual_relay_searches",0)
            uploads=_exact_relay_search(lifted,r,s,budget,max_cache_entries,accept)
            if (uploads is not None and
                    budget.counters.get("dual_relay_searches",0)>previous_dual_searches):
                strategy='exact-dual-relay-search'
        if uploads is None and unavailable:
            # A binary scalar construction can be insufficient on a particular
            # relay. First try all relay choices constructively; only if none
            # succeeds, jointly enumerate relay and broadcast spaces.
            # Exhaustion contradicts the existence theorem at the selected
            # denominator-cleared length, so it is an implementation error.
            exhaustive=True
            budget.set_stage(f"joint-exact-search-L{L}")
            uploads=_exact_relay_search(lifted,r,s,budget,max_cache_entries,accept)
            if uploads is not None:
                strategy='exact-relay-and-broadcast-search'
        if uploads is None:
            continue
        budget.set_stage("broadcast")
        if B is None:
            raise ConstructionError('accepted relay has no original-field broadcast')
        budget.set_stage("certificate")
        source_map=F if L==1 else lift(F,L)
        original_uploads=tuple(E@source_map for E in uploads)
        original_lift=task if L==1 else task.lift(L)
        cert=make_certificate(original_lift,original_uploads,B,blocklength=L,
                              base_field=field,expected_upload_count=r,expected_broadcast_count=s)
        fingerprint=task_fingerprint(task)
        budget.set_stage("completed")
        return CompileResult(cert,U,D,strategy,{'search_states':budget.states,
            'elapsed_seconds':monotonic()-started,'working_field':field.q,
            'working_blocklength':L,'original_blocklength':L,
            'maximum_original_blocklength':2,'field_extension_degree':1,
            'minimum_linear_blocklength':minimum_length,
            'blocklength_is_minimal':L==minimum_length,
            'blocklength_policy':'minimum' if force_blocklength is None else 'forced',
            'exact_arithmetic':True,'stage_seconds':dict(budget.timings),
            'search_counters':dict(budget.counters),
            'max_cache_entries':max_cache_entries},fingerprint)
    raise ConstructionError(
        f"No code found at original-field blocklength {lengths[0]}; "
        "implementation/theorem consistency error, not task infeasibility")


def compile_task(task: Task, *, max_states: int | None = 100_000,
                 max_seconds: float | None = 60.0, fast_paths: bool = True,
                 force_blocklength: int | None = None,
                 max_cache_entries: int = 2048,
                 cancel_event: CancellationToken | None = None,
                 progress: Callable[[ProgressEvent], None] | None = None,
                 progress_interval: float = 0.25) -> CompileResult:
    """Compile an exact certified three-user code, with bounded cooperative work.

    Every returned code uses the input field and at most two source instances.
    ``force_blocklength`` is the original-field count, including binary inputs.
    By default the theorem-minimal blocklength is selected: one when both
    optima are integral, otherwise two. An exhausted search budget is reported
    explicitly and never changes that blocklength. ``force_blocklength=2``
    remains available for callers intentionally requesting two instances.
    Constructive paths precede a complete adaptive primal/dual subspace
    search, which is exhaustive without resource limits and can be exponential.
    ``max_seconds`` covers bounds, search, construction and verification at
    checkpoints; it is NOT a hard/preemptive process timeout. ``max_states``
    counts enumerated/visited candidates, including subspace-cache hits.
    ``cancel_event`` implements ``is_set()`` (e.g. threading.Event).
    Progress callbacks run synchronously, are throttled between stage changes,
    and their exceptions propagate to the caller. Nested compiles are isolated.
    Set ``max_cache_entries=0`` to disable per-search memoization.
    """
    if isinstance(max_cache_entries, bool) or not isinstance(max_cache_entries, int) or max_cache_entries < 0:
        raise ValueError("max_cache_entries must be a nonnegative integer")
    budget=SearchBudget(max_states, max_seconds, cancel_event, progress, progress_interval)
    token=_checker.set(budget.check)
    try:
        budget.check()
        return _compile_impl(task, budget=budget, fast_paths=fast_paths,
                             force_blocklength=force_blocklength, max_cache_entries=max_cache_entries)
    finally:
        _checker.reset(token)
