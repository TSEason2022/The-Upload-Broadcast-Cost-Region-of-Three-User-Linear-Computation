# Matrix-to-coefficient model and redundant columns

## Frozen source and conclusion

Source: `../source/TIT_LCBC_optimized.tex`, the unnumbered setup around lines
315–350, `eq:task-spaces`, `eq:model-code`, `eq:costs`,
`eq:regularized-region`, and `eq:ustar-definition`.

The new formalization supplies an actual original-matrix code frontend. It does
not treat the original matrix model and the dual-source task model as equal by
definition. It constructs and verifies conversions between their observations,
encoders, relay maps, decoders, attained alphabets, costs, and fixed-blocklength
budget sets.

Files:

- `UploadBroadcast/MatrixTaskFrontend.lean`
- `UploadBroadcast/MatrixTaskEndpoints.lean`
- `scripts/AuditMatrixTaskFrontend.lean`

All names below lie under `UploadBroadcast.MatrixFrontend`, and most are in its
`Data` namespace.

## Concrete shapes and transpose convention

- A source is `Matrix (Fin d) (Fin L) K`; source instances are its columns.
- `Data.side i` and `Data.demand i` are finite matrices with `d` rows. No column
  independence assumption is imposed on the original data.
- `sideObs i X` and `demandObs i X` are literally `X.transpose * V` with `L`
  rows, exactly the paper's convention, without a conjugate transpose.
- `sourceEquiv d L` is the linear equivalence from these source matrices to
  `Source K (Fin d → K) L`; `sourceEquiv_apply` identifies its entrywise formula
  as the sum of `X k l * v k`.
- `task` forms the side column span and the supremum of side/demand column
  spans. Its only task-specific assumption is the paper's pooled-side
  feasibility condition.

All algebraic observation/code constructions work over any field. Cost-region
statements assume `[Finite K]`, with the logarithm base `Nat.card K`. Positive
blocklength is enforced by `achievableAt`, exactly as in `Model.lean`.

## Observation and demand reconstruction

`sideEval_observe`, `demandEval_observe`, and `jointEval_observe` connect
coefficient restrictions to the literal matrix products.

`sideEval_injective` and `jointEval_injective` prove that every linear
coefficient observation on the side or signal span is determined by its
original column evaluations, even when those columns are redundant.
`recoverSide` and `recoverJoint` are linear left inverses. Their identities on
actual sources are `recoverSide_observe` and `recoverJoint_observe`.

The joint inverse is substantive: the coefficient decoder reconstructs all of
`U_i` from side values and the original decoded demand values. The opposite
decoder evaluates the recovered signal on the original demand columns.
Unattainable raw matrix inputs receive arbitrary **linear** extensions, so all
maps remain total and linear transports remain linear.

## Actual nonlinear code equivalence and costs

`Data.Code` uses arbitrary deterministic functions on the original raw matrix
alphabets and zero-error correctness for every original source matrix. Its
relay has only the upload tuple as input.

- `Code.toTask` and `Code.ofTask` construct the two directions of operational
  conversion with identical `L`, message types, and relay function.
- `Code.toTask_upload_range` and `Code.toTask_broadcast_range` prove equality
  of attained alphabets, rather than assuming a rank/cost interpretation.
- `Code.toTask_uploadCost`, `Code.toTask_broadcastCost`,
  `Code.ofTask_uploadCost`, and `Code.ofTask_broadcastCost` prove exact costs.
- `achievableAt_eq` identifies every fixed-L matrix budget region with the
  existing `Task.achievableAt` region.
- `costRegion_eq` and `uploadOptimum_eq` transfer closure/regularization and
  unconstrained-broadcast upload optimum exactly.

For redundant raw side columns, upload cost counts actual attained outputs;
encoder outputs on impossible side matrices do not count. After full column
rank normalization, `sideObs_surjective_of_independent` and
`Code.upload_range_of_independent` prove that this is exactly the paper's
`im e_i` formula. This distinction avoids silently charging impossible inputs.

## Redundant-column removal and dimensions

There are two verified normalization constructions:

1. `normalized` uses a basis of each side space and a basis of a complementary
   demand subspace inside the signal space. `normalized_dimensions` proves the
   side width, conditional demand width, and independence of the concatenated
   columns. `normalized_joint_rank` gives rank equal to the sum of widths.
2. `exists_retained_column_sets`, `finite_set_matrix`, and
   `exists_retained_matrices` prove literal selection of nonrepeating original
   side columns and original demand columns. Side columns are selected first;
   an independent extension inside selected-side ∪ original-demand columns
   provides the retained demands. `exists_retained_normalization` constructs
   simultaneous finite matrices for all three users, with the same coefficient
   task and identical fixed-L nonlinear regions. Thus literal column removal,
   not only arbitrary basis replacement, is covered.

`redundant_columns_achievableAt_eq` also applies to *any* two matrix
presentations preserving the side and joint spans.

`normalize_code` and `denormalize_code` preserve each individual nonlinear
code's exact costs. `normalize_linearCode` and `denormalize_linearCode` do the
same for linear codes, preserving `L`, upload lengths `r`, and broadcast length
`s`. The general `code_costs_of_task_eq` and `linearCode_costs_of_task_eq`
apply equally to the literal retained-column normalization returned above.

## Linearity and ambient restriction

`Data.LinearCode` has genuinely linear matrix encoders, broadcast, and
decoders. `LinearCode.toTask` and `LinearCode.ofTask` consist solely of linear
maps; their `toCode` identities and cost theorems are verified. The statement
`linearCode_nonempty_iff` preserves the same `L,r,s`, including scalar `L=1`.

`MatrixTaskEndpoints.lean` composes this frontend with the existing
`Task.normalizationRetraction`:

- `ambient_achievableAt_eq`: equality of every fixed-L nonlinear budget region
  after removing ambient directions outside the total side span.
- `ambient_spanning`: the restricted coefficient task is genuinely spanning.
- `ambient_linearCode_nonempty_iff`: identical-L linear feasibility.
- `ambient_linear_forward` and `ambient_linear_reverse`: linear codes in both
  directions with no cost increase. These use the existing passive-retraction
  code proofs; no additional rate-preservation hypothesis is assumed.

Choosing a basis of the retained ambient subspace is then handled by the
existing coordinate-transport theorems. No uniform source law is used in any
of these model or normalization proofs.

## Verification

Run:

    source scripts/env.sh
    lake build UploadBroadcast.MatrixTaskFrontend UploadBroadcast.MatrixTaskEndpoints
    lake env lean scripts/AuditMatrixTaskFrontend.lean

The dedicated audit covers the matrix/source equivalence, observation
reconstruction, actual code constructors, exact attained ranges/costs,
fixed-blocklength and regularized endpoints, both linear directions, literal
column selection, and ambient restriction. Dependencies are only the standard
Lean axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or
custom mathematical axiom is introduced.
