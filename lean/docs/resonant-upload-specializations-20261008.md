# Resonant upload and five-bit source specializations

Date: 2026-10-08.

## Source obligations

The frozen manuscript `../source/TIT_LCBC_optimized.tex` states:

- Lines 2885–2887: the literal resonant family is active residual and has
  `U*(R_n) = 3n + 1`.
- Lines 1272–1279: the scalar resonant example has upload optimum four.
- Lines 191–204 and 732–744: the five-bit binary task has `U* = 4` and
  `D* = 3/2`.

`UploadBroadcast/ResonantUploadSpecializations.lean` supplies the missing
unconditional operational upload endpoints and a concrete-model existence
statement for the length-two simultaneous optimum.

## Exact statements and indexing

- `jordan_active K n` proves intrinsic `ActiveResidual` for the literal
  `ResonantRelay.jordanTask K n`, over every field. It assumes no activity,
  classification chart, target rank, or optimal code.
- `jordan_uploadOptimum K n` proves that the actual nonlinear regularized
  `Task.uploadOptimum` is `3*(n+1)+1` over every finite field.
- `source_uploadOptimum K n hn` uses the manuscript index: for `1 ≤ n`,
  `ResonantRelay.jordanTask K (n-1)` has upload optimum `3*n+1`.
  The library's `jordanTask K n` is source `R_(n+1)`, not source `R_n`.
- `map_scalarCoordinates K` identifies `jordanTask K 0` with the literal
  scalar task `ResonantRelay.task K K 0 LinearMap.id`. Its explicit linear
  equivalence evaluates each of the three private `Fin 1 → K` blocks at 0
  and leaves both scalar tripod coordinates unchanged. Both directions,
  linearity, and equality of all six coefficient subspaces are checked.
- `binary_active` and `binary_uploadOptimum` apply to the exact existing
  `BinaryOperationalTightness.task`, whose field is `ZMod 2`, private block
  is the scalar field, `J=0`, and `h=LinearMap.id`. The upload optimum is 4.
- `binary_joint_two` states existence of an actual
  `BinaryOperationalTightness.task.LinearCode 2 r b` with attained-alphabet
  upload cost 4 and broadcast cost `3/2`. It instantiates the unconditional
  `Task.joint_two` endpoint from `SourceMainTheorem` and the already proved
  literal-task broadcast optimum.

## Proof of intrinsic activity

The proof does not infer optimality merely from the existence of a relay
with a desired rank. `CycleUploadOptimality.canonical_active` establishes
all seven intrinsic activity properties for the actual positive-cycle
coordinate task. `CycleDirectSumCoordinates.map_directSum` identifies
that task with the direct sum of the literal resonant task and a scalar
cycle. Mapping back along its genuine linear equivalence preserves
activity, and `ActiveResidual.directSum_left` restricts it to the actual
resonant factor. The operational minimum-upload theorem then applies;
`RegularRelayOptimality.jordan_uploadValue` computes its value from the
original coefficient subspaces.

## Verification

Focused Lean compilation is warning-free. Reproduce from the repository:

    source scripts/env.sh
    lake env lean -o .lake/build/lib/lean/UploadBroadcast/ResonantUploadSpecializations.olean UploadBroadcast/ResonantUploadSpecializations.lean
    lake env lean scripts/AuditResonantUploadSpecializations.lean

The audit prints all seven endpoint types and their transitive axioms, then
checks every safe declaration originating in this new module, including
compiler-generated/private declarations, against the allowed standard
axioms `propext`, `Classical.choice`, and `Quot.sound`. It also verifies the
roots are present in the checked environment and rejects disabled kernel
checking. Logs are `logs/resonant-upload-specializations.log` and
`logs/resonant-upload-specializations-axioms.log`.

This focused result does not substitute for the repository's separate
independent semantic review, integrated clean build, full declaration audit,
or final source-manifest-bound coverage gate.
