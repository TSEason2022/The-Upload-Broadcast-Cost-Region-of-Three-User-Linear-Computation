# Operational endpoint assembly: proved scope and remaining input

**Historical/module-local development note.** This records the boundary of the intermediate modules at the time it was written. Statements below about remaining work are not the current project-wide gap list. The intermediate APIs below retain their stated hypotheses. The later unconditional source-facing global endpoints are in `UploadBroadcast/SourceMain.lean`; see `final-semantic-coverage-review-20261008.md` for their review. Current completion status is governed by `../coverage.json`, `../README.md`, and the final frozen-source verification report.

Frozen manuscript: `../source/TIT_LCBC_optimized.tex`, theorem `thm:intro-main`,
corollary `cor:scalar-budget`, and propositions `small-field-lcbc` and
`binary-lcbc`.

## Unconditional operational consequences

`DoubleOperationalScaling.lean` constructs arbitrary-block flattening from
`M ⊕ M` to twice as many original-field instances, preserving attained
message ranges and dividing both costs by two. It proves
`Task.uploadOptimum_double` using that nonlinear-code transformation and the
previously proved actual optimal length-two upload code. No additivity theorem
for unrelated tasks is assumed.

`EndpointArithmetic.lean` proves:

- `uploadOptimum_halfInteger` and `broadcastOptimum_halfInteger` for the actual
  operational optima, not just numerical programs;
- exact doubling of both optima and integrality of the doubled optima;
- `uploadOptimum_integral_iff_omega_integral` and scalar optimal uploads whenever
  the original upload optimum is integral;
- both converse bounds throughout the closed nonlinear region;
- necessity of integral optima for any scalar linear joint-corner code;
- rectangle equality once a genuine length-two corner is supplied.

`BroadcastFiniteEndpoints.lean` proves actual fully informed endpoint
attainment at an explicit length in `{1,2,4}`. When the original field has at
least three elements it uses length one for integral broadcast optimum and
two otherwise. The unrestricted binary fallback uses the already established
four-original-instance code. This is a fully informed result, **not** a
four-instance or two-instance joint upload–broadcast result.

## Explicit geometric input and conditional conclusions

`JointRegionEndpoints.lean` defines `Task.ScalarRelayWitness D`. Its fields
require an actual subspace, local generation, relay feasibility, actual
minimum-upload dimension, all fifteen induced-profile budget inequalities,
and (only in the binary case) a user permutation with separated induced sides.
Local generation supplies the spanning condition automatically.

Given such a concrete witness at the ceiling broadcast budget,
`scalar_ceiling_of_actual_relay` constructs an original-field scalar linear
code with **exact attained-alphabet costs** `(U*, ceil D*)`. The direct
`scalar_ceiling_of_large_field_relay` and
`scalar_ceiling_of_separated_relay` interfaces expose the respective geometric
hypotheses without a selection procedure.

`joint_two_of_actual_doubled_relay` constructs an exact original-field
length-two corner from a concrete witness on `M ⊕ M`.
`region_eq_rectangle_of_actual_doubled_relay` then proves the rectangle equality.

`ScalarRelaySelection` explicitly names the still-required geometric property
that every admissible integer budget for an integral-upload task has such a
witness. It is a definition, not an unconditional theorem. Conditional on this
property for the task and its double,
`least_linear_joint_blocklength_of_selection` proves the exact `IsLeast`
statement: minimum positive linear joint blocklength is one when both optima
are integral and two otherwise.

## Remaining main-theorem obligation

The arbitrary original task still needs an actual relay-selection theorem
that supplies these witnesses, including global decomposition/physical cycle
repair, all fifteen entries, upload optimality, and binary separation. The
conditional assembly does not close that gap or upgrade source coverage.
The source's nonlinear tightness example is also not newly proved here.

## Verification

Run:

```
source scripts/env.sh
lake build UploadBroadcast.JointRegionEndpoints UploadBroadcast.BroadcastFiniteEndpoints
lake env lean scripts/AuditJointRegionEndpoints.lean
```

The dedicated audit traverses the transitive axiom dependencies of every
imported project theorem and permits only `propext`, `Classical.choice`, and
`Quot.sound`. The audit is separate from source-statement coverage review.

## Operational nonlinear tightness supplement

`BinaryOperationalTightness.scalar_broadcast_cost_strict` now bridges the tightness claim directly to the actual `Task.Code` model. The concrete task is the five-coordinate resonant task over `ZMod 2`, with one-dimensional private blocks, zero Jordan map, and identity marking. Its fully informed optimum is exactly 3/2. Three explicit source functionals form a confusion triangle, forcing at least three attainable broadcast symbols for every scalar nonlinear code. Thus scalar broadcast cost is strictly greater than 3/2. No equivalence with the earlier Boolean toy-code model is assumed. The endpoint is audited in `scripts/AuditBinaryOperationalTightness.lean`; actual global two-block joint existence remains the separate selection obligation.
