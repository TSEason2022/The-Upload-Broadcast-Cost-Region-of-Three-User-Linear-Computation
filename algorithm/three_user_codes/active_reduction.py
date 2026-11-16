"""Constructive active reduction with exact maps to the original source.

The scalar rank formula alone does not expose its useful decomposition.
This module carries out Proposition 2 and Lemma 18: it removes pair-demand
graphs by side-preserving shears, deletes side-only directions, cancels
passive private-to-tripod graphs, and separates omniscience and residual
tasks. All discarded information is retained as a certified passive
component; no assumption about the input coordinate basis is made.
"""
from __future__ import annotations

from dataclasses import dataclass

from ._resources import checkpoint
from .linalg import (Matrix, block_diag, coordinates, coordinates_many, eye, intersection,
                     inverse, nullspace, rank, row_basis, row_sum, solve,
                     vstack, zeros)
from .task import Task
from .upload_bound import (_additions, _select_columns, _task_normal_form,
                           UploadParameters, upload_parameters)


@dataclass(frozen=True)
class ReducedComponent:
    """A direct-sum flag component and its original-source row embedding.

    ``matrix @ embedding`` expresses component coefficient rows in the
    original source coordinates. Demands represent augmented spaces;
    adding locally known demand rows does not change the computation task.
    """
    task: Task
    embedding: Matrix


@dataclass(frozen=True)
class ActiveReduction:
    """Certified omniscience/residual/passive decomposition of a task."""
    omniscience: ReducedComponent
    residual: ReducedComponent
    passive: ReducedComponent
    parameters: UploadParameters

    @property
    def components(self) -> tuple[ReducedComponent, ...]:
        return self.omniscience, self.residual, self.passive

    @property
    def removed_dimension(self) -> int:
        return self.passive.task.n

    def verify(self, original_task: Task) -> bool:
        """Check exact flag reconstruction, independence, and component roles.

        These checks also certify locality after embedding any component
        upload and permit original demands to be reconstructed by an exact
        coordinate solve. No numerical tolerance or rate formula is used.
        """
        if not isinstance(original_task, Task):
            raise TypeError("original_task must be a Task")
        f, n = original_task.field, original_task.n
        for component in self.components:
            if (component.task.field != f or component.embedding.field != f
                    or component.embedding.ncols != n
                    or component.embedding.nrows != component.task.n):
                raise ArithmeticError("invalid active-reduction embedding")
        basis = vstack(*(component.embedding for component in self.components))
        if rank(basis) != basis.nrows:
            raise ArithmeticError("active-reduction components are not independent")
        if row_basis(basis) != row_sum(*original_task.side):
            raise ArithmeticError("active reduction changed the observed source span")
        for name in ("side", "augmented"):
            for i in range(3):
                reconstructed = row_sum(*(getattr(c.task, name)[i] @ c.embedding
                                          for c in self.components))
                if reconstructed != getattr(original_task, name)[i]:
                    raise ArithmeticError("active reduction changed an original flag")
        om = self.omniscience.task
        if any(u != eye(f, om.n) for u in om.augmented):
            raise ArithmeticError("omniscience component is not an omniscience task")
        if self.passive.task.side != self.passive.task.augmented:
            raise ArithmeticError("discarded component contains an active demand")
        p = self.parameters
        if om.n != 2 * p.c + sum(p.tau):
            raise ArithmeticError("incorrect omniscience component dimension")
        if self.residual.task.n != p.rho + 2 * (p.r0 + p.b):
            raise ArithmeticError("incorrect residual component dimension")
        return True


def _change_coordinates(task: Task, embedding: Matrix, basis: Matrix):
    """Use rows of basis as a new basis; maintain its original embedding."""
    converted = coordinates_many(task.side + task.augmented, basis)
    return Task(task.field, converted[:3], converted[3:]), basis @ embedding


def _split(task: Task, embedding: Matrix, bases):
    """Split flags over a proposed direct sum, checking projection exactness."""
    bases = tuple(bases)
    basis = vstack(*bases)
    reframed, source = _change_coordinates(task, embedding, basis)
    result, offset = [], 0
    for block in bases:
        cols = range(offset, offset + block.nrows)
        projected = Task(task.field,
                         tuple(_select_columns(a, cols) for a in reframed.side),
                         tuple(_select_columns(u, cols) for u in reframed.augmented))
        result.append(ReducedComponent(projected,
            Matrix._from_validated(task.field, source.rows[offset:offset + block.nrows], embedding.ncols)))
        offset += block.nrows
    # Projection would spuriously add information if a graph has not been
    # removed. Equality of the sum of projected ranks detects that exactly.
    for attr in ("side", "augmented"):
        for user in range(3):
            if sum(getattr(c.task, attr)[user].nrows for c in result) != getattr(task, attr)[user].nrows:
                raise ArithmeticError("a proposed active summand still contains a graph")
    return tuple(result)


def _join(components, field, original_n):
    components = tuple(components)
    if not components:
        empty = zeros(field, 0, 0)
        return ReducedComponent(Task(field, (empty,) * 3, (empty,) * 3),
                                zeros(field, 0, original_n))
    task = Task(field,
                tuple(block_diag(*(c.task.side[i] for c in components)) for i in range(3)),
                tuple(block_diag(*(c.task.augmented[i] for c in components)) for i in range(3)))
    return ReducedComponent(task, vstack(*(c.embedding for c in components)))


def _apply_nilpotent_shear(task: Task, embedding: Matrix, graph: Matrix):
    """Apply I-N, with N squared zero and every side space invariant."""
    if not any(any(row) for row in graph.rows):
        return task, embedding
    ident = eye(task.field, task.n)
    if graph @ graph != zeros(task.field, task.n, task.n):
        raise ArithmeticError("active-reduction shear is not nilpotent")
    forward, backward = ident - graph, ident + graph
    if any(row_basis(a @ forward) != a for a in task.side):
        raise ArithmeticError("active-reduction shear changed an observation")
    transformed = Task(task.field, task.side,
                       tuple(u @ forward for u in task.augmented))
    normal = getattr(task, "_side_normal_form_data", None)
    if normal is not None:
        # The checked shear preserves each side, so its simultaneous normal
        # form is still the same data in these unchanged source coordinates.
        object.__setattr__(transformed, "_side_normal_form_data", normal)
    return transformed, backward @ embedding


def _remove_pair_graphs(task: Task, embedding: Matrix, normal):
    """Extend each demand graph into its passive pair space and subtract it."""
    f, n = task.field, task.n
    graph = zeros(f, n, n)
    for user, pair in enumerate(normal.pair):
        checkpoint()
        active = intersection(task.augmented[user], pair)
        passive = _additions(active, pair)
        if not passive.nrows:
            continue
        known_and_pair = vstack(task.side[user], active, passive)
        other = _additions(known_and_pair, eye(f, n))
        basis = vstack(known_and_pair, other)
        coeff = coordinates(task.augmented[user], basis)
        pstart = task.side[user].nrows + active.nrows
        rhs = _select_columns(coeff, range(pstart, pstart + passive.nrows))
        projected = _select_columns(coeff, range(known_and_pair.nrows, n))
        extension = solve(projected, rhs)
        other_projection = _select_columns(inverse(basis), range(known_and_pair.nrows, n))
        graph = graph + other_projection @ extension @ passive
    return _apply_nilpotent_shear(task, embedding, graph)


def _tripod_graph_data(task: Task, normal):
    """Retain the exact graph witnesses used by the upload rank formula."""
    f = task.field
    t = normal.tripod_v.nrows
    pdims = tuple(x.nrows for x in normal.private)
    ptotal = sum(pdims)
    offsets = (0, pdims[0], pdims[0] + pdims[1], ptotal)
    pindices = sum((normal.slices[f"P{i}"] for i in range(3)), ())
    ds, ls, gs, brows = [], [], [], []
    coefficients = coordinates_many(task.augmented, normal.basis)
    for user, coeff in enumerate(coefficients):
        pp = _select_columns(coeff, pindices).to_list()
        for row in pp:
            row[offsets[user]:offsets[user + 1]] = [0] * pdims[user]
        cv = _select_columns(coeff, normal.slices["v"])
        cr = _select_columns(coeff, normal.slices["r"])
        tt = cr if user == 0 else cv if user == 1 else cv + cr
        quotient = row_basis(Matrix._from_validated(f, (tuple(p) + tr for p, tr in zip(pp, tt.rows)), ptotal + t))
        qp = _select_columns(quotient, range(ptotal))
        qt = _select_columns(quotient, range(ptotal, ptotal + t))
        ds.append(row_basis(nullspace(qp.T) @ qt))
        selected = _additions(zeros(f, 0, ptotal), qp)
        ls.append(selected)
        gs.append(Matrix._from_validated(f, (qt.rows[qp.rows.index(row)] for row in selected.rows), t))
        for row in selected.rows:
            out = list(row)
            if user == 1:
                for col in range(offsets[2], offsets[3]):
                    out[col] = f.neg(out[col])
            brows.append(out)
    return tuple(ds), tuple(ls), vstack(*gs), Matrix._from_validated(f, brows, ptotal), offsets


def active_reduce(task: Task) -> ActiveReduction:
    """Decompose an arbitrary feasible task, over its original finite field.

    This construction covers nonzero graph-relation rank ``b`` as well as
    functional pure-tripod, private, and pairwise-known inputs. It does not
    assume that minimum broadcast costs are additive: callers must combine
    the fifteen branch profiles before constructing a joint broadcast.
    """
    if not isinstance(task, Task):
        raise TypeError("task must be a Task")
    checkpoint()
    cached = getattr(task, "_active_reduction_data", None)
    if cached is not None:
        return cached
    original, parameters = task, upload_parameters(task)
    f, original_n = task.field, task.n
    normal = _task_normal_form(task)
    # The initial rectangular embedding also discards completely unobserved
    # source coordinates without requiring a square ambient inverse.
    converted = coordinates_many(task.side + task.augmented, normal.basis)
    task = Task(f, converted[:3], converted[3:])
    embedding = normal.basis
    ident = eye(f, task.n)
    count = normal.common.nrows
    common, remainder = _split(task, embedding,
        (Matrix._from_validated(f, ident.rows[:count], task.n), Matrix._from_validated(f, ident.rows[count:], task.n)))
    passive_components = [common]
    task, embedding = remainder.task, remainder.embedding
    normal = _task_normal_form(task)

    # Proposition 2: remove graphs into passive pair directions. Private
    # directions used by no remote demand then split off at the same time.
    task, embedding = _remove_pair_graphs(task, embedding, normal)
    active_pairs = tuple(intersection(task.augmented[i], normal.pair[i]) for i in range(3))
    passive_pairs = tuple(_additions(a, p) for a, p in zip(active_pairs, normal.pair))
    coeff = coordinates_many(task.augmented, normal.basis)
    active_private, passive_private = [], []
    for owner, private in enumerate(normal.private):
        projected = row_sum(*(_select_columns(coeff[user], normal.slices[f"P{owner}"])
                              for user in range(3) if user != owner))
        active = projected @ private
        active_private.append(active)
        passive_private.append(_additions(active, private))
    active_basis = vstack(*active_pairs, *active_private, normal.tripod_v, normal.tripod_r)
    passive_basis = vstack(*passive_pairs, *passive_private)
    active, passive = _split(task, embedding, (active_basis, passive_basis))
    passive_components.append(passive)
    task, embedding = active.task, active.embedding
    normal = _task_normal_form(task)

    # Lemma 18: only im(G|ker B) can obstruct simultaneous private graph
    # cancellation modulo the pure demands. Retain it; solve away its
    # complement, including over characteristic two and extension fields.
    ds, ls, gm, bm, offsets = _tripod_graph_data(task, normal)
    dsum = row_sum(*ds)
    relations = nullspace(bm.T) @ gm
    active_tripod = row_sum(dsum, relations)
    passive_tripod = _additions(active_tripod, eye(f, normal.tripod_v.nrows))
    if passive_tripod.nrows:
        tripod_basis = vstack(active_tripod, passive_tripod)
        graph_passive = _select_columns(coordinates(gm, tripod_basis),
            range(active_tripod.nrows, tripod_basis.nrows))
        correction = solve(bm, graph_passive)
        inverse_basis = inverse(normal.basis)
        graph = zeros(f, task.n, task.n)
        views = (normal.tripod_v, normal.tripod_r,
                 normal.tripod_r - normal.tripod_v)
        for owner, private in enumerate(normal.private):
            selector = _select_columns(inverse_basis, normal.slices[f"P{owner}"])
            local_correction = Matrix._from_validated(f, correction.rows[offsets[owner]:offsets[owner + 1]],
                                      passive_tripod.nrows)
            graph = graph + selector @ local_correction @ passive_tripod @ views[owner]
        task, embedding = _apply_nilpotent_shear(task, embedding, graph)

    # Every pure-demand space contains C. Thus its two tripod copies are
    # already a common augmented-space summand, for any complement in T.
    common_tripod = intersection(intersection(ds[0], ds[1]), ds[2])
    residual_tripod = _additions(common_tripod, active_tripod)
    om_basis = vstack(*normal.pair,
                      common_tripod @ normal.tripod_v,
                      common_tripod @ normal.tripod_r)
    res_basis = vstack(*normal.private,
                       residual_tripod @ normal.tripod_v,
                       residual_tripod @ normal.tripod_r)
    pas_basis = vstack(passive_tripod @ normal.tripod_v,
                       passive_tripod @ normal.tripod_r)
    omniscience, residual, passive = _split(task, embedding, (om_basis, res_basis, pas_basis))
    passive_components.append(passive)
    reduction = ActiveReduction(omniscience, residual,
        _join(passive_components, f, original_n), parameters)
    reduction.verify(original)
    object.__setattr__(original, "_active_reduction_data", reduction)
    return reduction
