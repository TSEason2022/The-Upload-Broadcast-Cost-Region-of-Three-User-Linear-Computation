"""Coordinate-invariant private-edge extraction and resonant cycle repair.

The supplied TIT manuscript, Lemma 12 / Appendix D-B, splits private demand
edges by invariant projections. Lemma 13 then mixes one such cycle with an
R_n component. This module recognizes a single resonant remainder after all
private edges have been extracted; it is not a general quiver decomposition.
All returned relay candidates still require the compiler's exact acceptance.
"""
from __future__ import annotations

from itertools import permutations

from .linalg import (Matrix, coordinates, extend_basis, eye, intersection,
                     row_basis, row_sum, vstack)
from .task import Task


def extract_private_edges(task: Task, budget):
    """Split all six E_(owner -> receiver) summands in original coordinates.

    Return the complementary task and edge bases. The projection for an edge
    k -> j has image W in A_k intersect U_j and kills U_i + A_j. Its kernel
    therefore preserves all six flags. Equation (110) proves that extracting
    one edge type does not change the multiplicities of the other five.
    """
    residual = task
    edges = {}
    for owner, receiver in permutations(range(3), 2):
        budget.check()
        other = 3 - owner - receiver
        A, U = residual.side, residual.augmented
        N = intersection(A[owner], U[receiver])
        B = row_sum(A[receiver], intersection(U[other], U[receiver]))
        forbidden = intersection(N, B)
        expanded = extend_basis(forbidden, N)
        W = Matrix(task.field, expanded.rows[forbidden.nrows:], ncols=task.n)
        edges[owner, receiver] = W
        if not W.nrows:
            continue
        # Since W intersects U_other + A_receiver trivially, putting W first
        # makes all later basis rows a complementary kernel containing it.
        killed = row_sum(U[other], A[receiver])
        partial = vstack(W, killed)
        source = row_sum(*A)
        completed = extend_basis(partial, source)
        kernel = Matrix(task.field, completed.rows[W.nrows:], ncols=task.n)
        residual = Task(task.field,
                        tuple(intersection(a, kernel) for a in A),
                        tuple(intersection(u, kernel) for u in U))
        budget.count("extracted_private_edge_dimensions", W.nrows)
    return residual, edges


def demand_cycle_candidates(task: Task, budget) -> tuple[Matrix, ...]:
    """Original-field R_n-plus-private-edges relays, including cycle mixing.

    Invertible source changes and user relabelings are supported by exact
    flag isomorphism after invariant edge extraction. Recognition failures
    return an empty tuple and never establish infeasibility.
    """
    source = row_sum(*task.side)
    if (sum(a.nrows for a in task.side) - source.nrows != 1 or
            any(intersection(task.side[i], task.side[j]).nrows
                for i, j in ((0, 1), (0, 2), (1, 2)))):
        return ()
    residual, edges = extract_private_edges(task, budget)
    edge_count = sum(E.nrows for E in edges.values())
    if not edge_count:
        return ()
    basis = row_sum(*residual.side)
    n, remainder = divmod(basis.nrows - 2, 3)
    if (remainder or n < 1 or
            any(A.nrows != n + 1 for A in residual.side) or
            any(U.nrows != 2*n + 1 for U in residual.augmented)):
        return ()
    compact = Task(task.field,
                   tuple(coordinates(A, basis) for A in residual.side),
                   tuple(coordinates(U, basis) for U in residual.augmented))
    # Delayed import avoids the compiler -> mixing -> compiler import cycle.
    from .compiler import _flag_isomorphism, resonant_task
    reference = resonant_task(task.field, n)
    H = (eye(task.field, compact.n)
         if compact.side == reference.side and compact.augmented == reference.augmented
         else _flag_isomorphism(reference, compact, budget))
    if H is None:
        return ()
    mapped = H @ basis
    f, d = task.field, task.n
    X = list(mapped.rows[:3*n])
    V, R = mapped.rows[3*n:]
    T = tuple(f.sub(r, v) for r, v in zip(R, V))
    edge_rows = [row for E in edges.values() for row in E.rows]
    candidates = [row_basis(Matrix(f, X + [V] + edge_rows, ncols=d)),
                  row_basis(Matrix(f, X + [R] + edge_rows, ncols=d))]
    altered = X.copy()
    altered[n-1] = tuple(f.add(x, v) for x, v in zip(altered[n-1], V))
    candidates.append(row_basis(Matrix(f, altered + [T] + edge_rows, ncols=d)))
    # Positive cycle: user 1 z -> y, user 2 y -> x, user 3 x -> z.
    positive = ((0, 2), (1, 0), (2, 1))
    if all(edges[e].nrows for e in positive):
        z = edges[0, 2].rows[0]
        remaining = [row for e, E in edges.items()
                     for k, row in enumerate(E.rows) if e != (0, 2) or k]
        mixed = tuple(f.sub(a, b) for a, b in zip(z, V))
        candidates.append(row_basis(Matrix(f, X + [R, mixed] + remaining, ncols=d)))
        budget.count("positive_demand_cycle_repairs")
    # Reverse cycle: user 1 z -> x, user 2 y -> z, user 3 x -> y.
    negative = ((0, 1), (1, 2), (2, 0))
    if all(edges[e].nrows for e in negative):
        y = edges[1, 2].rows[0]
        remaining = [row for e, E in edges.items()
                     for k, row in enumerate(E.rows) if e != (1, 2) or k]
        mixed = tuple(f.sub(a, b) for a, b in zip(y, R))
        candidates.append(row_basis(Matrix(f, X + [V, mixed] + remaining, ncols=d)))
        budget.count("negative_demand_cycle_repairs")
    budget.count("recognized_resonant_edge_remainders")
    return tuple(candidates)
