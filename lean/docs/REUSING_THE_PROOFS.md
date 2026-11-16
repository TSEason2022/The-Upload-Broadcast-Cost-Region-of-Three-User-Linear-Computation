# Reusing the verified interfaces

Start with [the compiled examples](../examples/ReusableAPI.lean). They are generic
applications of the paper-facing theorems, not numerical test cases. They use
only two imports:

```lean
import UploadBroadcast.SourceMainTheorem
import UploadBroadcast.MatrixTaskEndpoints
```

`SourceMainTheorem` discharges the geometric selection premises internally.
Call its public endpoints rather than supplying a `ScalarRelaySelection` to an
intermediate conditional theorem. The matrix import adds ordinary source,
side-information, and demand matrices and their verified task conversion.

## Check the examples

After the [pinned setup](../TOOLCHAIN.md), run from the repository root:

```sh
source scripts/env.sh
lake build UploadBroadcast.SourceMainTheorem UploadBroadcast.MatrixTaskEndpoints
lake env lean examples/ReusableAPI.lean
```

The last command checks every example and prints the transitive axiom set of
all twelve declarations. The permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`; declarations may use only a subset.
Successful elaboration alone is not a semantic review of the manuscript or an
independent rebuild of imported dependency objects. See
[the reproduction procedure](REPRODUCIBILITY.md) for the full frozen-source gate.

## State the original hypotheses

The coefficient-space examples explicitly quantify over:

```lean
{K F : Type} [Field K] [Finite K]
[AddCommGroup F] [Module K F] [FiniteDimensional K F]
(T : UploadBroadcast.Task K F)
```

`Task` contains the three side spaces `A i`, the three joint side-and-demand
spaces `U i`, and proofs of `A i ≤ U i` and `U i ≤ ⨆ j, A j`.
`Three` means `Fin 3`. No spanning, active-reduction, field-size-greater-than-two,
or extra relay-selection hypothesis is required here. `K` is the original
finite field, including the binary field. `F` need not itself be the total
side-information span.

The costs are real numbers measured in q-ary symbols per source instance,
where `q = Nat.card K`. Upload cost uses the encoder's attained alphabet;
broadcast cost uses the attained relay output over actual source blocks.
Nominal coordinate lengths `r i` and `b` can contain redundancy and must not be
silently identified with those costs.

## Region, actual code, and scalar endpoints

All example names below have prefix `UploadBroadcast.ReusableAPI`.

- `closed_and_two_region` directly applies `T.main_region`. It identifies both
  `T.achievableAt 2` and the regularized closed `T.costRegion` with
  `Task.budgetRectangle T.minimumUploadFormula (Profile.rankBound T)`.
  The rectangle consists of budget pairs `(u, d)` satisfying the two lower
  bounds. Membership permits a code costing **at most** those budgets; it does
  not assert that every point is an exact pair of code costs.
- `joint_two_code` opens `T.joint_two` with
  `obtain ⟨r, b, c, hu, hd⟩ := T.joint_two` and returns an actual
  `T.LinearCode 2 r b` with both optimal attained costs. Its `encode`,
  `broadcast`, `decode`, and `zero_error` fields are available inside the proof.
  The broadcast field consumes only the upload tuple.
- `scalar_criterion` gives the exact equivalence between `T.LinearJointAt 1`
  and integrality of **both** source optima. The same field `K` is used at
  blocklength one and two. This is a scalar **linear** criterion; it does not
  claim that every individual nonlinear scalar problem has the same criterion.
- `scalar_ceiling` applies `T.scalar_budget hU`, assuming
  `hU : ∃ z : ℤ, T.uploadOptimum = (z : ℝ)`. It supplies a scalar linear code
  with upload exactly `T.uploadOptimum` and broadcast exactly
  `((⌈broadcastOptimum T.A T.U⌉ : ℤ) : ℝ)`. Only upload integrality is needed;
  the broadcast optimum itself may be half-integral.
- `minimum_blocklength` applies `T.minimum_linear_blocklength`. Its `IsLeast`
  conclusion asserts both attainment and minimality among positive lengths.
  `T.linearJointLengthFormula` is one when both optima are integral and two
  otherwise.
- `upload_formula` rewrites the operational infimum via `T.minimum_upload`.
  For the expanded private/tripod/omniscience expression, use
  `T.minimum_upload_source_formula`. Upload-only scalar attainment in
  `OriginalUploadTheorem` has its own Ω-integrality criterion; do not confuse
  it with simultaneous scalar attainment of both optima.

`Profile.rankBound T` is the maximum of the fifteen explicit conditional-rank
entries. It is defined independently of the operational broadcast optimum.
`task_general_broadcastOptimum_eq_rankBound` is the theorem that identifies the
two. The examples use this theorem and `T.minimum_upload` to put code costs in
the source formula's notation.

## Start from ordinary matrices

`matrixData` shows how to package supplied matrices without a basis or rank
independence assumption. For an ambient dimension `d`, supply:

- `sideWidth demandWidth : Three → ℕ`
- `side i : Matrix (Fin d) (Fin (sideWidth i)) K`
- `demand i : Matrix (Fin d) (Fin (demandWidth i)) K`
- A proof that each side-and-demand column span lies in the pooled side span

The resulting `D : MatrixFrontend.Data (K := K) d` has a coefficient-space
problem `D.task`. A source block `X` has shape `d × L`, with instances in its
columns. Observations and demands are literally `X.transpose * D.side i` and
`X.transpose * D.demand i`; no conjugate transpose is used.

- `matrix_region` transfers the full theorem through `D.achievableAt_eq` and
  `D.costRegion_eq`, with no new task-specific hypothesis.
- `matrix_joint_two_code` obtains the joint code for `D.task`, then uses
  `MatrixFrontend.Data.LinearCode.ofTask` to return a genuine
  `D.LinearCode 2 r b`, preserving both costs exactly.
- `matrix_zero_error` exposes the resulting literal matrix recovery equation,
  for every source matrix and every user, using the code's `zero_error` field.
- `matrix_linear_costs` illustrates the reverse direction `c.toTask` and its
  exact upload/broadcast cost equalities.
- `matrix_ambient_region` shows that removing unused ambient directions
  preserves the nonlinear region at each original blocklength.

For redundant columns, impossible raw side-information matrices do not add to
the charged alphabet. `Code.upload_range_of_independent` recovers the usual
whole-encoder-image formula after side columns are independent. Verified
column and ambient normalization endpoints are documented in the
[matrix frontend review](matrix-task-frontend-source-audit-20261008.md).

## Proof witnesses are not an executable matrix synthesis program

These endpoints prove existence of genuine functions/linear maps and their
zero-error and cost properties. They are stronger than a numerical optimum or
a formal code template with unproved feasibility. Nevertheless, an existential
`∃ r b c, ...` is a proposition, and destructuring it inside a proof is not a
runtime extraction algorithm.

The library uses classical choices of subspaces, bases, complements, inverses,
and finite coordinates. In particular, matrix `recoverSide`, `recoverJoint`,
`LinearCode.toTask`, and `LinearCode.ofTask` are declared `noncomputable`.
`basisMatrix`, matrix normalization, rank-bound expressions, optimum definitions,
and the integrality-dependent length formula are also noncomputable.
`Classical.choice` is visible in their transitive axiom reports.

Some elementary definitions, such as `matrixData`, `sideObs`, `demandObs`, and
turning a supplied linear code into its ordinary code, are ordinary `def`s.
With explicit computable field operations and supplied computable matrices/maps,
the elementary matrix operations can be evaluated. This does **not** make the
chosen optimal code produced by an existence theorem executable by `#eval`.

An executable encoder synthesizer would need a concrete finite-field
representation, effective basis/rank/selection routines, and proofs connecting
those routines to this API, plus executable encoder and decoder matrices.
That algorithmic layer is not supplied by these examples. Reusers can prove
properties of supplied implementations against the existing specifications
without changing the paper's mathematical statements.

## Navigate from the source to Lean

The checked source identity and complete claim map are in
[`coverage.json`](../coverage.json). The release source ledger supplies the
frozen source locations; the manifest remains the authority on coverage.

| Source label or definition | Lean declaration(s) | Module |
| --- | --- | --- |
| `thm:intro-main`: full region | `UploadBroadcast.Task.main_region` | [SourceMainTheorem](../UploadBroadcast/SourceMainTheorem.lean) |
| `thm:intro-main`: simultaneous code and least linear length | `UploadBroadcast.Task.joint_two`, `minimum_linear_blocklength`, `scalar_joint_iff_integral` (same `Task` prefix) | [SourceMainTheorem](../UploadBroadcast/SourceMainTheorem.lean) |
| `thm:intro-main`: uniform nonlinear tightness | `UploadBroadcast.nonlinear_uniform_bound_tight` | [SourceMainTheorem](../UploadBroadcast/SourceMainTheorem.lean) |
| `thm:upload` | `UploadBroadcast.Task.minimum_upload_source_formula`, `minimum_upload_attainment`, `minimum_upload_two_instance` (same `Task` prefix) | [OriginalUploadTheorem](../UploadBroadcast/OriginalUploadTheorem.lean) |
| `prop:stable` | `UploadBroadcast.Task.stable_relay_source` | [SourceMainTheorem](../UploadBroadcast/SourceMainTheorem.lean) |
| `cor:scalar-budget` | `UploadBroadcast.Task.scalar_budget` | [SourceMainTheorem](../UploadBroadcast/SourceMainTheorem.lean) |
| `lem:binary-integer-relay` | `UploadBroadcast.Task.binary_integer_relay` | [SourceMainTheorem](../UploadBroadcast/SourceMainTheorem.lean) |
| `eq:task-spaces`, `eq:model-code`, `eq:costs` | `UploadBroadcast.Task`, `Task.Code`, `Task.Code.uploadCost`, `Task.Code.broadcastCost` (all under `UploadBroadcast`) | [Model](../UploadBroadcast/Model.lean) |
| Original matrix observations and exact code transport | `UploadBroadcast.MatrixFrontend.Data.task`, `Data.LinearCode.ofTask`, `Data.achievableAt_eq`, `Data.costRegion_eq` (all under `UploadBroadcast.MatrixFrontend`) | [MatrixTaskFrontend](../UploadBroadcast/MatrixTaskFrontend.lean) |
| Ambient restriction | `UploadBroadcast.MatrixFrontend.Data.ambient_achievableAt_eq` | [MatrixTaskEndpoints](../UploadBroadcast/MatrixTaskEndpoints.lean) |

Use fully qualified declaration names in downstream projects when similarly
named definitions are open. Inspect the theorem type before specializing it.
A build of this example is useful compatibility evidence, not a replacement
for the source-to-statement review or the full clean-release audit. Licensing
and manuscript rights are described separately in [RIGHTS.md](../RIGHTS.md).
