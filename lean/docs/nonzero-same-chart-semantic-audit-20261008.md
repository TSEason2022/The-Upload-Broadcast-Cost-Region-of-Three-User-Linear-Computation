# Nonzero-defect same-chart source audit

Source: frozen `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
Target: `lem:same-chart`, lines 2463–2495; its proof and indexed-arm discussion
continue through line 2785. This audit covers this lemma, not the entire paper.

## Verdict

`lem:same-chart` is semantically complete and is promoted to
`reviewed_complete`. The proof covers all eight families, every n >= 1,
all listed indexed choices, all arm permutations, and the actual nonlinear
operational upload optimum. This is a statement-level promotion only.

## Statement and hypotheses

The source quantifies over the original finite field with cardinality at least
three and all eight positive-defect indecomposable families at admissible
vectors `gamma + n delta`, **n >= 1**. It asserts locally generated,
upload-optimal actual relay subspaces, the displayed six full/induced first
entries, all nine full/induced doubled second entries, and alternative indexed
arms followed by arm permutations realizing the nonzero-defect rows of Table
`tab:menus`.

The formal inputs are:

- `K` is an actual field with a finite type instance and `3 <= Fintype.card K`.
- `T : Task K F` is the actual finite-dimensional coefficient task, including
  `A_i <= U_i` and feasibility in the side-information span.
- `TaskDecomposition.Indecomposable (EdgeExtraction.configuration T).spaces top`
  means the original six subspaces admit no nontrivial simultaneous split.
- `Dimensions T g n` records exactly the ambient dimension and the three side
  and three signal dimensions in the source family tables.
- `1 <= n`. There is no large-n, characteristic, assumed geometric rank,
  algebraic-closure genericity, requested-profile, optimality, or existence-of-code
  input.

For a permuted instance the same seven dimensions are imposed on
`Profile.reindexTask (pathPerm k) T`, and actual indecomposability is transported
by `TaskUserPermutation.reindex_indecomposable`. The conclusion concerns relay
subspaces of the original `F`, feasibility and local generation for original
`T`, and original `T.uploadOptimum`.

## Newly closed operational gap

`GeometricUploadConverse.code_lower` constructs a canonical private/tripod
chart of the actual pairwise-disjoint, spanning side spaces. Pair-signal
spanning implies that every private coordinate occurs in remote signals;
this is proved by mapping each pair join under its private projection. The
triple-join condition supplies the tripod bridge. The actual uniform-source
Shannon converse `ResidualConverse.code_rank_lower_bound` then proves

`2 dim F - (dim A_0 + dim A_1 + dim A_2) <= code.uploadCost`

for every positive blocklength and arbitrary nonlinear finite-alphabet
zero-error code. Codes are transported into the constructed chart using the
proved equality of fixed-block achievable regions. Nothing about the desired
minimum is an assumption.

`NonzeroSameChartOptimality.family_code_lower` obtains every geometric input
from the existing actual indecomposable rank calculations. The numerical
expression is exactly `fullAmbient g n - codimension g`, where codimension is
two for R2 and one for the other seven families.

`relay_rank_eq_uploadOptimum` constructs a genuine scalar code from the actual
locally generated feasible relay with `ResidualOperational.finiteCode_of_local_relay`.
It combines that upper bound with the nonlinear converse through
`Task.uploadOptimum_eq_of_code`, which explicitly treats every blocklength
and closure. Thus the equality to `uploadOptimum` is operational; it is not a
synonym for a numeric rank or a linear-only lower bound. The proof does not
need to assume or numerically evaluate the original-task minimum-upload formula.

## Full and induced profiles

`NonzeroSameChartOptimality.same_chart_full_and_optimal_relay` joins the
existing canonical all-eight-family profile construction to the operational
minimum. It includes an actual `P`, local generation, relay feasibility,
`dim P = f - chi`, `dim P = uploadOptimum`, and
`sum_i dim(P intersect A_i) = dim P`, followed by all six first and all nine
doubled second entries. The full-task profiles are also conclusions.

The values are exactly those in the source:

- T1: first `n 1_6 + e1 + e2`, canonical increment e5; doubled seconds 3n+1.
- T2: first `n 1_6 + e1 + e2 + e3 + e4`, zero increment; seconds 3n+1.
- T3: first `(n+1) 1_6`, zero increment; seconds 3n+1.
- R0: first `n 1_6`, zero increment; seconds 3n.
- R1: first `n 1_6 + e1 + e2`, zero increment; seconds 3n.
- R2: first `n 1_6`, zero increment; seconds 3n-1.
- O: first `n 1_6 - e5 - e6`, canonical increment e5; seconds 3n-1.
- H: first `n 1_6`, zero increment; seconds 3n-1.

Lean indexes e1,...,e6 by `Fin 6` values 0,...,5. The ordering is the existing
`Profile.firstOrder`, corresponding to the source's equation `eq:F-order`.

## All alternative indexed arms and relabelings

`NonzeroSameChartMenus.same_chart_all_menu_choices` proves the exact additional
choices, rather than only componentwise upper bounds:

- T1 has e5 and e3 (distinguished arms 2 and 3 in source numbering).
- O has e6, e5, and e1+e3 (distinguished arms 1, 2, and 3).
- The other six families preserve the first profile.

The new hyperplane construction proves the relation projection lies outside
the selected signal using the actual enlarged-tripod Euler inequality for
that arm. The finite-field kernel selection simultaneously enforces the two
remote conditional ranks. The dimension-rank difference then proves equality
of each first entry. This avoids treating the weaker binary-menu upper bounds
as exact profiles.

`NonzeroSameChartPermutations.same_chart_all_permuted_choices` covers all six
actual user relabelings through `pathPerm`; `pathPerm_exhaustive` checks that
these exhaust every permutation of the three users. `inverseFirst` transports all six
first entries; `inverseUser` and the proved second-entry symmetry transport all
nine second entries. Local dimensions sum invariantly under the permutation.
The operational converse is independently transferred through the geometric
conditions, so minimum equality is for the original task.

`indexed_arms` checks which user has the enlarged signal (T1) or enlarged
side (O). `indexed_menu_table` checks the exact six indexed rows of
`tab:menus` coordinate by coordinate. Choice order differs in two rows, but
the sets of choices are the source sets. The uniform three-choice interface
repeats one T1 choice and repeats the single choice of the other families;
it does not omit any source choice.

## Small indices and scope boundaries

Every endpoint uses `1 <= n`, so n=1 is included, including the R2 relay's
zero-dimensional third local side and O's zero full entries. Natural-number
subtractions are checked by the family arithmetic under this exact hypothesis;
there is no strengthened n>=2 hypothesis. The codimension-two R2 construction
uses the actual two-dimensional relation wedge and works for n=1.

The separate prose headed “The case n=0” follows the lemma's proof and is
outside the lemma's quantified statement. These endpoints do not claim the
n=0 boundary tasks, the resonant T0 family, all-field component classification,
full residual decomposition/additivity, or the final global region theorem.
Those require their own coverage entries. In particular, completion of this
lemma must not be described as completion of the entire paper.

## Verification evidence

Passed evidence:

- `logs/nonzero-same-chart-endpoint-build.log`: focused Lake build of
  `UploadBroadcast.NonzeroSameChartPermutations` completes successfully.
- `logs/nonzero-same-chart-endpoint-recheck.log`: a second focused Lake build
  confirms the final source dependency graph is up to date.
- `logs/nonzero-same-chart-endpoint-axioms.log`: actual elaborated endpoint
  signatures and eight explicit `#print axioms` checks. The independent
  namespace-wide collector checks all 44 endpoint/supporting theorems against
  the whitelist; the complete union is `propext`, `Classical.choice`, `Quot.sound`.
- `logs/nonzero-same-chart-endpoint-source-audit.log`: lexical proof-escape
  audit passes across 251 project Lean sources at the time of that run.
- `verification/NonzeroSameChartEndpoint.lean`: reproducible signature/axiom
  harness.
- `verification/nonzero-same-chart-endpoint-snapshot-20261008.json`: frozen
  source identity, harness hash, and hashes of all 88 project modules in the
  endpoint's import closure. All have compiled artifacts.

One pre-existing dependency had a newer source mtime than its compiled mtime:
`NonzeroDefectRelays.lean`. Both successful Lake builds accepted its content
hash. To resolve the anomaly independently, the current source was recompiled
to a separate temporary artifact; its SHA-256 exactly equals the shared
compiled artifact (`bfb5b74b5c972faae230f720a38eccd54d355cb58d539e40bbd78eb15a7e5005`).
Evidence is in `logs/nonzero-same-chart-relay-dependency-recheck.log`. This was
a harmless timestamp anomaly, not an unverified dependency. No shared source
or compiled artifact was changed for that check.

There are no errors, warnings, `sorryAx`, or `Lean.ofReduceBool` in the focused
build and axiom logs. These checks do not replace the repository-wide
integration run after concurrent work finishes.
