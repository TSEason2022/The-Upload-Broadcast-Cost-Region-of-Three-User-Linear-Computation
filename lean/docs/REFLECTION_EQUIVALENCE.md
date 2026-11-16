# Actual representation reflection API

`UploadBroadcast/QuiverRepresentation.lean` and
`UploadBroadcast/ReflectionEquivalence.lean` implement the linear-algebraic
reflection step. They do not assert Kac classification or a positive-excess
canonical-form theorem.

## Representation objects

`Orientation V E` gives sources and targets; `Rep K Q` contains a module at
every vertex and an actual linear map on every arrow. `Hom` and `Iso` impose
commutativity for every arrow. `Rep.prod` is vertexwise direct sum.
`Indecomposable` means nonzero and every isomorphism to a binary direct sum has
a zero factor. The theorem `indecomposable_iff` identifies this with nonzero
and triviality of endomorphism idempotents, using explicit kernel/image
subrepresentations and the actual splitting isomorphism `splitIso`.

## Local coordinate chart

For an arbitrary unchanged peripheral quiver `Q` and representation `R`,
`attachSinkOrientation Q neighbour` adds a vertex `none`, with one incoming
edge per index `i : I` from `some (neighbour i)`. Source attachment reverses
those edges and preserves every peripheral edge. `reflect_attachSink` and
`reflect_attachSource` identify these with orientation reversal.

The boundary space is the finite product of neighbouring spaces. Sink arrows
are encoded by `f : Boundary R neighbour →ₗ[K] X`. This loses no incoming-arrow
data: `aggregateIncoming` is a linear equivalence from all lists of incoming
maps. Source arrows are encoded by `g : X →ₗ[K] Boundary R neighbour` and
recovered by coordinate projections.

## Proved actual reflection operations

* `sink f` is the inclusion of `ker f` into the boundary.
* `source g` is the quotient map to the cokernel `Boundary / range g`.
* Both transport commuting squares, preserve identities, composition, zero,
  and two-sided inverse morphisms.
* `sinkRecovery` for surjective `f` and `sourceRecovery` for injective `g`
  are explicit inverse-reflection linear equivalences; arrow compatibility
  and naturality are proved.
* `sinkHomEquiv` and `sourceHomEquiv` give inverse bijections on commuting
  squares, with unchanged boundary maps.
* `reflectAttachedSinkHom` / `reflectAttachedSourceHom` and
  `attachedSinkHomEquiv` / `attachedSourceHomEquiv` lift this to morphisms of
  the full attached representations, including the peripheral arrows.
* `attachedSinkRecovery` and `attachedSourceRecovery` are isomorphisms of
  actual full representations after two reflections.
* Triviality of all representation idempotents, and genuine direct-sum
  indecomposability, are preserved under the stated local epi/mono hypotheses.
* Failure of the epi/mono hypothesis constructs a nonzero idempotent supported
  at the reflected vertex. Therefore a representation with trivial
  idempotents and any nonzero peripheral vertex satisfies the needed local
  surjectivity/injectivity. If every peripheral space is zero, an actual
  indecomposable has central dimension one, as the explicit simple exception.
* `sinkProdEquiv` and `sourceProdEquiv` explicitly commute kernel and cokernel
  reflection with binary sums, with the corresponding arrow equations.
* Dimension formulas are consequences of these actual kernels/quotients and
  rank-nullity. `attachedSink_finrank` / `attachedSource_finrank` use the sum
  of the actual neighbour dimensions, not an assumed dimension-vector rule.

## Remaining integration obligations

The attachment chart is general, but the current files do not supply a
vertex/edge relabelling from every intermediate seven-vertex E6 orientation
to a chosen chart. Nor do they connect the manuscript's nested-subspace
configuration indecomposability to `QuiverRepresentation.Indecomposable`.
The finite E6 reflection sequence and vertex-chart changes, scalar-extension
compatibility, and sequence-level reverse uniqueness still need to be assembled.
The local simple-vertex exception and local forward/backward isomorphism
transport are proved. The
zero-defect regular classification remains a separate substantial theorem.
These files do not close the overall affine-E6 representation gap.

## Verified checkpoint (2026-10-08)

* `lake build UploadBroadcast.ReflectionEquivalence`: passed, no warnings.
* `lake env lean scripts/AuditReflectionEquivalence.lean`: 227 namespaced
  theorems passed; only `propext`, `Classical.choice`, `Quot.sound` occurred.
* `python3 scripts/audit_source.py`: passed across 100 Lean source files at
  this checkpoint.

Logs: `logs/reflection-equivalence-build.log`,
`logs/reflection-equivalence-axioms.log`,
`logs/reflection-equivalence-source-audit.log`.
