# Residual decomposition source audit, 2026-10-08

## Source and verdict

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

This audit covers `prop:exhaustion` (Residual decomposition, lines 1240–1255),
its proof in the Activity and Upload Additivity appendix (lines 2014–2040),
and the optimal full-relay conclusion in the immediately following
zero-excess explanation (lines 1260–1267).

The source-facing implementation is
`UploadBroadcast/ResidualComponentAdditivity.lean`. Its endpoint
`source_residual_decomposition` starts with an arbitrary original feasible
finite-dimensional task over a finite field. It constructs the source's
post-common, post-passive residual and an actual finite indecomposable
coefficient decomposition. Neither component activity, component optimality,
a decomposition-existence certificate, nor operational separability is an
input.

The more general `residual_decomposition` applies to **any** finite exact
coefficient product decomposition of an active residual, including every
indecomposable decomposition and every refinement. Thus existence of one
selected decomposition has not replaced the proposition's assertion about
an arbitrary decomposition.

The source's displayed intermediate choice-dependent identity
`G0 = direct_sum G0,a` (`eq:xi-block`) and additivity of every separate rank
parameter are not separately exported here. The named proposition is proved
by a coordinate-free route through actual activity and ambient/side ranks.
That alternative proof closes the named proposition, but this audit does not
claim independent coverage of those additional unnumbered intermediate
assertions or full-manuscript coverage.

## Source dictionary and genuine activity

`ActiveResidual` is a coordinate-free predicate on the actual six labeled
coefficient subspaces. Its conditions are:

1. The three side spaces span the ambient and are pairwise disjoint.
2. Every two distinct signal spaces span the ambient.
3. The intrinsic first tripod side `A0 ∩ (A1 + A2)` is contained in
   `U2 + (U0 ∩ U1)`.
4. Writing `W = U0 ∩ U1 ∩ U2`, the common fully-demanded tripod seed
   `(A0 ∩ W) ∩ ((A1 ∩ W) + (A2 ∩ W))` vanishes.

These are genuine activity conditions, not a renaming of an upload-optimality
assumption:

- `ResidualIntrinsicGeometry.tripod_side_core` identifies the intrinsic
  tripod side with the canonical `v` copy of the row space.
- `GeometricUploadConverse.fully_used_of_pair_spans` identifies full remote
  use of each private coordinate; `signal_pair_spanning` supplies the
  converse implication for the constructed task.
- `canonical_rows_fully_active` proves that every row has an actual signed
  zero-private relation witness. Consequently the selected demand-data
  active row space is the entire row space. This uses actual signal
  membership and the signed incidence equations, not a rank certificate.
- `commonSeed_eq_pure_image` identifies the common seed with the `v` image
  of the intersection of the three pure-demand row spaces.
- `canonical_zero_common` excludes all common pure rows.
- `pair_ranks_zero` proves the actual pair-known coefficient spaces and the
  original intrinsic active-pair ranks all vanish.

`finalResidual_active` derives every condition from the already constructed
source residual: its private-use equalities, canonical sides, signal bridge,
and common-row deletion. `source_residual_active` applies this to the
chart selected from an arbitrary original task.

A stronger assertion that `U2 + (U0 ∩ U1)` equals the whole ambient is **not**
assumed. It fails even for some active pure-private examples. The proof uses
only the source's tripod inclusion.

## Actual components, not a numerical proxy

`FiniteComponentCoordinates.exists_operational_component_coordinates`
constructs nonzero simultaneous indecomposable subspaces `P a` of the actual
residual coefficient space, an explicit product equivalence, exact transport
of all six labeled spaces, and the exact ambient dimension sum. The component
spaces satisfy literal comap identities along each subtype inclusion, which
are precisely the source's `Ai ∩ Fa` and `Ui ∩ Fa` in subtype coordinates.

Every activity condition is a finite expression of joins, intersections,
bottom, top and inclusion. `ActiveResidual.map` transports these expressions
through the exact coefficient equivalence. `ActiveResidual.component`
restricts them to each actual coordinate factor using the proved product
subspace identities and projection images. Thus component activity is a
conclusion for all components, not a supplied certificate.

## Operational minimum and additivity

`uploadValue T` is the real expression

    2 dim F - (dim A0 + dim A1 + dim A2).

The real subtraction prevents truncated natural-number subtraction from
concealing a missing dimension inequality.

`code_lower` proves this lower bound for arbitrary nonlinear finite-alphabet
codes at every positive blocklength. It constructs the canonical chart from
the actual side spaces, obtains private recovery from the signal-pair joins,
and invokes the proved Shannon residual converse with the actual tripod
bridge. No encoder, relay or decoder is assumed linear or componentwise.

`exists_optimal_relay` constructs a locally generated feasible relay of
exactly this dimension over the original field. The proof selects the actual
zero-common pure-row decomposition, constructs the private corrections and
row relay, and transports it back through the coefficient chart.
`scalar_upload_exact` turns it into an actual scalar linear code, with exact
attained-alphabet upload cost, including over the binary field.

`minimum_upload` then uses `uploadOptimum_eq_of_code`, whose proof handles
all blocklengths and the closure of the operational achievable region.

`uploadValue_product` derives additivity from the ambient product dimension
and the dimensions of each actual side product. Combining it with the
separately proved universal minimum formula yields
`minimum_upload_additive`. The lower bound applies to the whole task, so
competitors may jointly and nonlinearly encode all factors. No general
additivity of arbitrary operational regions is asserted or used.

`finalResidual_uploadValue` and the unconditional original-task wrapper
`source_residual_upload_formula` identify the common value with the source's
pre-common private rank plus retained noncommon pure-and-mixed tripod rank.
It uses `finalRows_finrank`, not a separately assigned residual rate.

## Zero excess and degenerate cases

`side_dimension_le` proves nonnegative side-information excess.
`zero_excess_side_complement` proves that zero excess gives an actual direct
sum of the side spaces. The supplementary `ResidualComponentFactors` module
also proves the broader source statement for every normalized task, without
activity or pair-disjointness assumptions: `spanning_side_dimension_le` and
`spanning_zero_excess_iff`. The latter derives both needed disjointness
conditions from zero excess and proves the converse.

`zero_excess_full_relay` proves that full relay `P = top` is locally generated,
feasible and optimal with minimum upload `dim F`. `full_relay_profile` proves
that every one of the fifteen induced fully informed profile entries is
unchanged. The scalar code construction applies to this relay as well.

The zero ambient space is allowed; its actual indecomposable decomposition
is the empty finite family. No nonempty-family or positive-excess hypothesis
has been silently added. For nonzero components, `exists_nontrivial_demand`
excludes a side-only task; positive excess together with the common-row
condition gives `exists_nonfull_signal`, excluding a remaining all-omniscience
component.

## Mechanical verification

- Endpoint build: `logs/residual-component-build.log`
- Full source-facing signatures and reachable-axiom audit:
  `verification/ResidualComponentAdditivityAudit.lean`
- Axiom output: `logs/residual-component-axioms.log`

The reachable-axiom audit must contain only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. No new axiom, `sorry`, `admit`, or
assumed component rate or classification theorem is used.


## Supplementary factor APIs

`ResidualComponentFactors.lean` supplies binary-factor restriction and
arbitrary-product closure of intrinsic activity, along with zero-excess
inheritance and product identities. These apply after further actual physical
component extraction and use no classification or rate certificates. Its
warning-free build and seven standard-axiom checks are recorded in
`logs/residual-component-factors-build.log` and
`logs/residual-component-factors-axioms.log`; the audit source is
`verification/ResidualComponentFactorsAudit.lean`.
