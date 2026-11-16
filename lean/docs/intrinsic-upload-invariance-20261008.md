# Intrinsic upload-parameter invariance: source audit

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

## Verdict and exact scope

The unnumbered coordinate-independence conclusion at source lines 1966–1988
is proved by `Task.intrinsic_upload_parameters`, imported through
`UploadBroadcast.IntrinsicUploadInvariance`.

This closes the specific unnumbered gap noted in
`active-reduction-source-audit-20261008.md` and
`new-source-endpoint-semantic-audit-20261008.md`. It does **not** close the
separate full-paper unnumbered/external-dependency gate. The standalone audit
of those obligations is `unnumbered-coverage-audit-20261008.md`.

The theorem is quantified over an arbitrary original finite-dimensional
feasible task over its original finite field, and independently over:

- two legal active/passive pair selections on its common-side quotient;
- two legal pair-factor complement selections after those reductions;
- two arbitrary private/tripod charts of the resulting residual tasks.

Its conclusions identify each retained pair rank with the original
`intrinsicActivePairRank`, equate private, common, pure, mixed and total tripod
ranks between the two constructions, and identify the computed upload formula
with the previously verified original-task `minimumUploadFormula`.
`minimum_upload_all_choices` additionally identifies every such formula with
the operational nonlinear upload infimum.

These are arbitrary choices, not two copies of `pairFreeChart`. Neither rank
equality, an upload optimum, nor an equality of operational regions is an
input. The `ActivePairSelection` fields are the actual complementary subspaces,
side-preserving charts and exact demand-graph separation conditions of a legal
normal form. `PrivateTripodChart` requires the actual ambient linear
equivalence and its three side-space identities. Existing existence theorems
construct these data, so their use does not conceal an existence oracle.

## Intrinsic formulas before choosing coordinates

The new core `IntrinsicUploadRanks` uses zero-based users. Put

- R0 = A0 ∩ ((A1 ∩ U0) + A2)
- R1 = (A0 ∩ (A1 + A2)) ∩ U1
- R2 = (A0 ∩ (A1 + A2)) ∩ U2

For any pair-free private/tripod chart, `pure_eq_images` proves that these are
precisely the images of the three pure demand-row spaces under the **same**
injective v-coordinate embedding. The first identity aligns User 0's
r-quotient rows with the other two users' v-quotient rows by the third side
line; it does not confuse a pure demand intersection with a projection of
mixed demands.

Consequently:

- d_com = dim(R0 ∩ R1 ∩ R2)
- d_pure = dim(R0 + R1 + R2) − dim(R0 ∩ R1 ∩ R2)
- d_priv is the sum, over the three remote pairs j,k, of
  crk(Uj + Uk | Aj + Ak)

`private_kernels` proves that the kernel of each private-coordinate projection
is exactly the sum of the other two sides. Rank-nullity then proves the private
formula. `privateTrim_pureRows` removes the apparent dependence on the selected
unused-private complement. All three intrinsic formulas commute with every
ambient linear equivalence (`ranks_map`). Thus
`PrivateTripodChart.dimensions_eq_intrinsic` and
`private_common_pure_independent` prove chart independence without relying on
a preferred chart.

The use of dimension differences is legitimate: the common intersection lies
in the pure sum. `tripodDimension_eq_pure_mixed` and
`mixedRows_stacked_rank` remain the source dictionary for equations `rho`,
`c-r0`, `b`, and the appendix definitions of d_pure and d_mix.

## Every selection has the same actual pair quotient

`ActivePairSelection.residualQuotient_mapTask` proves that an arbitrary pair
complement, with its actual side and signal images, is equivalent to
F / sum_i(pairKnown i).

`simultaneous_mkQ` proves the simultaneous active-pair shear induces the
identity on that quotient. Its correction vectors lie in the intrinsic pair
sum. `pairReduced_pairOmniscience` proves that the surviving pair sum is
exactly the original pair sum intersected with the kernel of the passive
projection.

`postResidualQuotient_mapTask` then identifies the residual after **both**
arbitrary reduction stages with that same original quotient. Its equivalence
is constructed from the actual quotient map: injectivity and surjectivity are
proved, rather than inferred from equality of dimensions.
`postResidualChoice_mapTask` gives a concrete task isomorphism between any two
such residuals. This includes arbitrary passive-pair complements, arbitrary
active-pair corrections and arbitrary pair-factor complements.

For the three pair dimensions, `pairRank_all_choices` composes the actual
surviving-pair equivalence, the signal intersection rank and the original
common-quotient rank identity. It does not merely compare canonical pair
choices.

## Mixed rows and arbitrary demand-graph lifts

`quotient_relationRows_eq` shows that **any two** exact `DemandData`
presentations of a fixed task induce the same map G modulo the pure-row sum,
before restriction to ker B. The proof constructs actual signal vectors and
uses the two exact membership descriptions to show each difference of graph
lifts lies in that user's pure space. `mixedRank_lift_independent` and
`PrivateTripodChart.mixedDimension_eq_any_lifts` expose arbitrary lift choice.

For general chart changes, the proof uses a different valid route from the
manuscript's block-matrix argument. The already verified minimum-upload
construction and converse imply, for **every** legal chart c of a pair-free
task T,

    T.uploadOptimum = c.uploadFormula 0 0 0.

`uploadOptimum_self` proves this by adding a genuine zero-dimensional pair
factor and applying `OriginalUpload.uploadOptimum`. Coordinate isomorphisms
preserve the operational infimum through actual code retractions. Since
private and common counts are already intrinsic, this identifies the total
tripod count. Subtracting the independently intrinsic pure count identifies
the mixed count. The natural-number cancellation is exact, using
`tripod_eq_pure_add_mixed`.

There is no circular import or mathematical assumption of coordinate
independence: `OriginalUploadTheorem` proves the minimum in a selected
construction, using explicit maps, entropy converse and codes. It neither
imports these new modules nor assumes their target conclusion. The new
invariance theorem is a consequence of that already established optimum.
The algebraic core works over any field; the operational step uses a finite
field, exactly as the source assertion does.

## Files and mechanical evidence

New proof modules:

- `UploadBroadcast/IntrinsicUploadRanks.lean`
- `UploadBroadcast/IntrinsicUploadSelections.lean`
- `UploadBroadcast/IntrinsicUploadReduction.lean`
- `UploadBroadcast/IntrinsicUploadInvariance.lean`

Checks:

- `logs/intrinsic-upload-invariance-lake-build.log`
- `verification/IntrinsicUploadInvarianceAudit.lean`
- `logs/intrinsic-upload-invariance-axioms.log`

The focused Lake build completed successfully and without warnings (2,692
jobs including dependencies). The audit prints the actual source-facing
signatures, checks representative endpoint axiom sets, and traverses all
imported project theorem dependencies, allowing only `propext`,
`Classical.choice` and `Quot.sound`. The audit passed for all 2,273 imported project theorem roots, with exactly
those three standard axioms. The lexical source audit also passed across 275
Lean files; see `logs/intrinsic-upload-invariance-source-audit.log`.
No numbered coverage entry or global unnumbered gate is changed by this work.
