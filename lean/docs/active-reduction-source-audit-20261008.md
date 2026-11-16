# Active-reduction source audit, 2026-10-08

## Source scope and verdict

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

This audit concerns `prop:active-pair` (lines 598–616), its proof (lines
1943–1964), and the additional passive-tripod reduction at
`lem:active-empty-row` (lines 1991–2010). The proposition's scope is:

1. An invertible quotient-coordinate change preserving all three side spaces.
2. Complementary active/passive pair-known subspaces with the stated original
   quotient-intersection dimensions.
3. Exact separation of each demand quotient into its active pair part and a
   demand subspace involving only the two remote private spaces and tripod rows.
4. Deletion of passive pair spaces and all remotely unused private directions
   preserving every fixed-block nonlinear achievable region.

`UploadBroadcast.ActiveReductionEndpoint` assembles these conclusions from an
arbitrary feasible finite-dimensional task over a finite field. Its operational
endpoint additionally performs the passive-tripod cancellation. No normal form,
chosen complement, graph map, active-row hypothesis, or equality of cost regions
is an input to `Task.active_reduction_source`.

The separate appendix assertion that **all six rank parameters are unchanged
between arbitrary normal-form choices** is not part of the named proposition.
This audit does not claim a new proof of that broader unnumbered assertion.
The intrinsic active-pair ranks, actual retained row ranks, and operational
invariance are established here. A full-paper claim still requires separate
review of the unnumbered coordinate-independence assertion.

## Exact algebra and source dictionary

### Common quotient and pair ranks

`Task.commonKnown` is the intersection of the three actual side spaces.
`Task.pairKnown i` is the intersection of the other two sides;
`Task.pairKnown_eq_pair` identifies it for any enumeration of the three users.
`intrinsicActivePairRank i` is

    finrank (U i ∩ pairKnown i) - finrank commonKnown.

`intrinsicActivePairRank_quotient` identifies this with the dimension in the
common quotient. The subtraction is the dimension of a quotient, not a free
parameter: the common-known subspace lies in each signal/side intersection.
`preResidual_pairKnown_finrank` transports the same original rank through
normalization and passive-pair deletion.

### One invertible simultaneous shear

`Task.selectedPairs` is selected from the proved existence of simultaneous
active-pair data on the common quotient. Its active factor is the actual
signal intersection with the pair block, as certified by `active_factor_eq`.
Its `complementary` field is proved by the graph construction, not postulated
by a source-endpoint premise. `active_pair_source_geometry` packages:

- complementary passive and active factors in each pair block;
- active dimensions equal to the original intrinsic ranks;
- one global linear equivalence preserving every side space exactly;
- exact product separation of all three transformed signals.

The global correction is square-zero because every mixed product vanishes.
Thus `I - N` has inverse `I + N`, over the original field including
characteristic two. This is the actual automorphism in the source proof.

### Private/tripod quotient coordinates

`pairResidualEquivalence` separates the surviving pair factor from a pair-free
residual task. `pairFreeChart` is constructed by the proved three-subspace
normal-form theorem, not supplied as a hypothesis. Its sides are precisely
private-plus-`v`, private-plus-`r`, and private-plus-`r-v`.

The extracted pair task has full signal space at every user and each side
omits precisely its own pair coordinate. `PairOmniscienceAdapter.pairEquiv`
and `side_iff_coordinate_zero` give the explicit product coordinates. Hence
its demand quotient is exactly the missing active pair block. The other
factor's quotient is given by the actual demand-quotient maps; the third
map uses `v+r`, which is invariant modulo the side line `r-v`.
`activeResidual_signal_quotients` proves the exact signal decomposition into
its side space and the lifted remote-private-plus-tripod demand. The maps
have identity compositions on their quotient targets and the remainder is
locally known, so these are genuine quotient coordinates, not merely upper
bounds on demand spaces. Together with the pair product, this is the stated
`K_i^act ⊕ Q_i` decomposition.

### One-pass private trimming

`used₁`, `used₂`, and `used₃` are the sums of the two remote signal projections
onto the corresponding private block. The remote sides have zero projection
onto that block, so these equal the source's projections of `L_i`.
`privateTrim` retains precisely those subspaces. `privateTrim_fully_used`
proves that every retained private block is completely used.

No iteration or termination premise is needed: all three trims happen
simultaneously, and `activeRowReduction_used` proves that the subsequent
private gauge and row deletion preserve each private-use subspace.
`activeResidual_fully_used` supplies the final exact equalities to top.

### Passive tripod cancellation and retained row rank

The demand graphs use the actual pure intersections `pureRows_i`, not the
tripod projections of all demand vectors. The signed incidence map is the
source's `B`; `relationRows` is a lift of `G`. If `S` is the sum of the three
pure spaces, the retained row space is

    S + relationRows(ker B).

`exists_empty_cancellation` factors the complementary quotient component
through `B`; `privateGaugeShear_sides` proves that the resulting shear preserves
all sides. `correctedTask_rows` proves simultaneously that every nonlocal
demand row lies in the retained space. The discarded complement is therefore
side-only and is removed by an actual coefficient retraction.
`activeResidual_rows_finrank` proves the exact dimension

    dim S + dim image((G mod S)|ker B).

`mixedRows_stacked_rank` also identifies the mixed term with the source's
stacked-rank difference. `ResidualPureTransport` supplies exact pure-space
transport through private trimming, the gauge, and row deletion. No row-rank
or activity certificate is assumed at the original-task endpoint.

## Operational semantics and coupled codes

`Task.activeReductionRetraction` composes the actual coefficient maps through:

1. normalization to the span of the side spaces;
2. quotienting common-known coordinates;
3. simultaneous active-pair shear and passive-pair removal;
4. exact pair/residual factorization and private/tripod chart;
5. simultaneous unused-private removal;
6. private gauge and passive-tripod removal.

The residual retraction is multiplied by the identity on the actual pair
factor, using `PassiveRetraction.prod`. This is essential: equality of the
isolated residual's rate region would not justify substitution under arbitrary
joint nonlinear encoding. The product retraction acts on the full task, and
its generic `delete`/`restore` constructions transport every code.

`activeReduction_achievableAt_eq` covers every blocklength, all nonlinear
encoders, relay functions and decoders, and both actual upload and broadcast
alphabet costs. `activeReduction_costRegion_eq` covers the regularized closure.
There is no separability or independently encoded factor assumption.

## Choice and termination scope

Complement and lift selection uses `Classical.choice` on proved existence.
"Canonical" in these implementation names means a fixed selected construction,
not uniqueness of a normal form or a computable algorithm. The proof has a
fixed finite sequence of reductions and needs no unproved termination bound.
The proposition is existential and does not request a canonical deterministic
basis-selection algorithm, so this meets its actual scope.

## Mechanical checks

The endpoint build and axiom audit are recorded in
`logs/active-reduction-endpoint-build.log` and
`logs/active-reduction-endpoint-axioms.log`.
`verification/ActiveReductionEndpointAudit.lean` prints the full source-facing
signatures and checks their reachable axioms. The coverage promotion is made
only after compilation and the standard-axiom audit pass.

Result: both new Lean modules compiled without warnings or errors. All ten
active-reduction audit roots and all five additional intrinsic-geometry roots
have reachable axiom sets contained in `propext`, `Classical.choice`, and
`Quot.sound`. The source hash matches the frozen manifest. The proposition is
promoted to `reviewed_complete`; no other coverage entry is changed by this
work. The umbrella import and final integrated build remain the coordinator's
integration step.

The independently useful `ResidualIntrinsicGeometry` module additionally
proves pairwise signal spanning from full private use, identifies the first
intrinsic tripod side core, and identifies the exact common tripod seed with
the image of the common pure-demand rows. Its `commonSeed_eq_bot_iff` and
`all_signal_pairs_spanning` require only canonical side equalities, together
with private-use equalities for the latter. These support the separate
residual-component audit; they are not needed to justify the proposition's
coverage promotion.
