# Constructed active-pair reduction

**Historical/module-local development note.** This records the boundary of the intermediate modules at the time it was written. Statements below about remaining work are not the current project-wide gap list. For the later assembled source-facing result, see `active-reduction-source-audit-20261008.md`. Current completion status is governed by `../coverage.json`, `../README.md`, and the final frozen-source verification report.

`UploadBroadcast.ActiveTaskAssembly` and `UploadBroadcast.ReducedTask` prove the following end-to-end statement: every feasible `Task K F` has a concretely defined `Task.pairReduction`; for finite fields and finite-dimensional coefficient spaces, it has exactly the same fixed-block nonlinear achievable regions and regularized cost region.

## Construction

1. Form the actual common-known space `Task.commonKnown = iInf A` and quotient every coefficient space by it. A linear section produces a `PassiveRetraction`, including concrete nonlinear code deletion and restoration.
2. In the common-zero quotient, define `Task.pairKnown i` as the intersection of the other users' side spaces. This is disjoint from `A i`, so a complement containing `A i` exists. These three independent complement choices provide compatible pair charts without assuming a normal form.
3. Apply the graph lemma to each actual signal `U i`. This constructs its active factor, a passive complement, and the passive-valued graph correction. The corrections kill their own side spaces and have images in the other users' side spaces.
4. Mixed products therefore vanish. The sum correction gives one invertible square-zero shear preserving every side space, and `ActivePairSelection.simultaneous_separation` proves that it realizes all three selected signal separations simultaneously.
5. Construct the three projections onto the selected passive factors. Their mixed products vanish and their sum is idempotent. For every transformed signal, its projected component is locally known. `Task.idempotentPassiveRetraction` deletes that image, defining the reduced task on the kernel.

## Main operational theorems

- `Task.pairReduction_achievableAt_eq`
- `Task.pairReduction_costRegion_eq`

Neither theorem takes normal-form existence, preselected corrections, separated demands, or a rate-preservation assumption as input.

## Rank identification

`Task.selectedPairs_activeFactor_finrank` identifies each constructed active factor with

`dim(U i ∩ pairKnown i) - dim(commonKnown)`

in the original task. `Task.pairKnown_eq_pair` identifies the intrinsic pair block with the intersection of the two other side spaces for any enumeration of the three labels. `Task.activePairRank_eq_quotient` also gives the explicit three-label quotient identity.

## Residual graph data

`pureDemandGraph_characterization` proves the full equivalence

`(p,t) ∈ Q` iff `p ∈ projection_private(Q)` and `φ(p) = t mod D`,

where `D` is the intersection of `Q` with the tripod summand, represented by `comap inr`. This intentionally does not use the tripod projection as the pure-demand space.

## Remaining scope

This construction does not yet extract the entire final private/tripod residual model, delete every unused private direction, or assemble the active-empty-tripod cancellation with the final residual coding theorem and invariant upload formula. The general idempotent deletion and graph/gauge primitives are available for those steps; their availability is not a proof of the remaining assembly.

## Verification

Both files compile with Lean 4.19.0 without warnings. `verification/ActiveTaskAssemblyAxioms.lean` checks representative construction, rank, and operational theorems; the recorded output in `logs/active-task-assembly-axioms.log` contains only `propext`, `Classical.choice`, and `Quot.sound`. No additional axioms or placeholders are used.
