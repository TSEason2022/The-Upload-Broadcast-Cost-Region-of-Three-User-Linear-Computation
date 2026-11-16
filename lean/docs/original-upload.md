# Original-task minimum upload assembly

## Exact reduction maps

`OriginalUploadOptimum` constructs coefficient retractions rather than merely
substituting an equality of isolated residual cost regions inside a product.

- `Task.pairCanonicalRetraction` starts from an arbitrary feasible original
  task. It composes normalization, common-side quotient, active-pair correction,
  passive-pair deletion, actual pair factor separation, and the private/tripod
  side chart.
- `ResidualTaskAssembly.splitActiveRetraction` trims unused private directions,
  separates common pure-demand tripod rows, and removes passive relation rows.
  Every operation is lifted to the full omniscience product before composition.
- `OriginalUpload.reduction` also applies `PairOmniscienceAdapter.combinedEquiv`
  to the actual pair/common factor, obtaining `OmniscienceOperational.task`.

`PassiveComposition` records the composition of ambient maps, side maps,
signal maps, and locally recoverable remainders. Both nonlinear operational
region preservation and same-blocklength linear-code restoration apply to the
whole jointly encoded task. Coupling uploads across factors is permitted.

## Source rank parameters

The order is the same as the manuscript: private trimming, common pure rows,
then active/noncommon tripod rows.

- `privateDimension` is the sum of dimensions of the remote-use private spaces.
- `commonDimension` is the dimension of the intersection of the three actual
  pure demand spaces after trimming.
- `tripodDimension` is the retained active-row dimension before the common split,
  minus the common pure dimension.
- `OriginalUploadRanks.finalRows_finrank` identifies this source expression with
  the actual final residual row dimension, using
  `CommonTripodRanks.residual_activeRows_finrank` for arbitrary graph lifts.
- `tripodDimension_eq_pure_mixed` identifies the pure-noncommon-plus-mixed formula.
- `tripodDimension_eq_stacked_rank` identifies the mixed term with `[B;G]−B`.
- `Task.preResidual_pairKnown_finrank` identifies the three final pair dimensions
  with the original task's intrinsic active-pair intersection ranks, including
  invariance under ambient normalization.

The `Task.PrivateTripodChart` wrappers expose the same parameters before
specializing the deeply nested original-task subtype instances. They do not
introduce a new normal-form assumption.

## Operational equality and attainment

`OriginalUploadCanonical` has compiled exact operational equality and concrete
scalar/two-instance codes for the constructed canonical task. The converse is
valid for arbitrary nonlinear fixed-length zero-error codes and the closure.
The upper bound constructs an actual locally generated residual relay and
combines it with the actual canonical omniscience code. Every code is over the
original field.

The final `OriginalUploadTheorem` interface is compiled and exposes:

- `Task.minimum_upload`
- `Task.minimum_upload_source_formula`
- `Task.minimum_upload_scalar`
- `Task.minimum_upload_scalar_of_integral`
- `Task.minimum_upload_two_instance`
- `Task.minimum_upload_attainment`
- `Task.minimum_upload_closed_lower`

All these endpoints compile without warnings. The independent endpoint axiom
audit verifies only `propext`, `Classical.choice`, and `Quot.sound`. `uploadOmniscienceValue_nonneg` and `uploadOmniscienceValue_integral_iff_nat`
identify the natural-number witness with integrality in the usual integer sense.
The combined attainment theorem chooses one instance in that branch and two
otherwise.

## Verification evidence

- `logs/original-upload-build.log`
- `logs/original-upload-ranks-build.log`
- `logs/original-upload-canonical-build.log`
- `verification/OriginalUploadCoreAudit.lean`
- `logs/original-upload-core-axioms.log`
- `logs/original-upload-chart-build.log`
- `logs/original-upload-formula-build.log`
- `logs/original-upload-model-build.log`
- `logs/original-upload-theorem-build.log`
- `verification/OriginalUploadAudit.lean`
- `logs/original-upload-axioms.log`
- `logs/original-upload-lake-build.log`
- `logs/original-upload-source-audit.log`

The final original-task endpoints and their complete reachable dependencies use only `propext`, `Classical.choice`, and
`Quot.sound`. No project axiom, `sorry`, or target-as-hypothesis is used.

The final focused Lake build completed successfully (2,684 dependency jobs).
The source audit passed across 198 Lean files. All final endpoint axiom checks
were rerun after the current converse dependencies rebuilt.
