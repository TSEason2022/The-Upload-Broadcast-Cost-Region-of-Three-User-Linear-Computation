# Literal graph direct sums and individual upload parameters

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
Scope: source lines 2021–2028, especially equation `eq:xi-block`.
This report does not change the global unnumbered-coverage flag.

## Source correspondence

The source chooses normal-form complements and graph lifts separately on the
summands, then asserts B = direct sum B_a, G = direct sum G_a,
G0 = direct sum G0,a and individual rank additivity.

`ActualBlockGraph.combinedTask` is an actual `Task`, obtained from
`FiniteRelayAssembly.task T` by the explicit `ambientChart`. This chart
regroups the finite product of canonical private/tripod ambient spaces into
the canonical ambient on products of the private and tripod factors.
It does not replace the task with numerical rank data.

The three `quotientSignal*_map`/`quotientSignal*_mem` identities identify the
actual combined quotient-demand spaces. `privateDomain*_mem` and
`pureRows*_eq` then identify the actual three private-demand domains and
pure-row spaces. These identities are derived from the six task subspaces.

`combinedData` constructs a genuine
`ResidualTaskAssembly.DemandData (combinedTask T)`. Its fields include exact
signal-membership equivalences, proved from each chosen component's graph
presentation. Its maps are therefore validated demand graphs for the
actual combined task, not independently introduced maps bearing the same
names as the manuscript objects.

`relationChart` identifies the actual combined domain
`DemandData.Relations` with the product of the component relation domains.
`incidence_conjugacy` proves the signed incidence map B is the componentwise
B under the genuine private-coordinate and relation-domain charts.
`actualQuotientChart` is the proved equivalence from the actual quotient by
all combined pure rows to the product of component pure-row quotients.
`graph_conjugacy` uses this quotient chart and proves the corresponding G
identity for `combinedData.relationRows`.

`actualKernelChart` is a linear equivalence between the actual incidence
kernel and the product of component kernels. `actualG0` is defined by
restricting the actual quotient-valued graph map to that kernel.
`G0_direct_sum` is the literal equality of these linear maps, after the
explicit domain and quotient-coordinate identifications. In particular,
no dimension equality or direct-sum rank certificate is assumed.

## Individual parameters

- `ActualBlockGraph.mixed_image` identifies the actual mixed-row image as
  the product of the component images after the quotient chart.
- `ActualBlockGraph.mixed_rank_additive` gives d_mix additivity for the
  actual source incidence and quotient graph maps.
- `ActualBlockGraph.common_rank_additive` gives the common pure-row rank.
- `ActualBlockGraph.pure_rank_additive` gives the noncommon pure-row quotient
  term separately, with the required nonnegative subtractions proved by
  subspace inclusion.
- `ActualBlockGraph.tripod_rank_additive` adds the two actual source terms,
  giving d_tri additivity independently of total minimum-upload additivity.
- `UploadParameterDirectSum.retained_private_spaces` identifies all three
  actual remotely used private subspaces.
  `private_dimension_additive` then proves the literal d_priv sum.
- `IntrinsicUploadDirectSums.activePairRank_additive` proves every original
  active-pair rank separately, before selecting complements or reductions.
- `IntrinsicUploadDirectSums.chart_private_common_pure` and
  `UploadParameterDirectSum.arbitrary_chart_ranks` transfer the corresponding
  intrinsic identities to arbitrary legal charts, including charts on the
  genuinely regrouped product task.

The graph theorems quantify over actual component tasks and arbitrary
validated graph lifts. They can in particular be applied to the source's
already privately trimmed summands. The manuscript's coordinate invariance
is independently covered by `IntrinsicUploadInvariance`; the direct-sum
map proof does not use total upload equality to deduce the mixed rank.

## Field and finiteness scope

The coordinate/domain/quotient identities hold over an arbitrary field.
The rank sums assume a finite index set and finite-dimensional relevant
coefficient factors. Thus they include every original finite field,
including characteristic two, without a field extension or cardinality
lower bound. The signs in B are exactly those of
`DemandData.incidence`; characteristic two needs no special exception.

## Verification

Focused build and `verification/UploadDirectSumAudit.lean` are the dedicated
checks. The latter enumerates every imported project theorem and rejects
any axiom dependency except `propext`, `Classical.choice`, and `Quot.sound`.
Final run details are appended after verification completes.

Final focused verification on 2026-10-08:

- `lake build UploadBroadcast.IntrinsicUploadDirectSums UploadBroadcast.BlockGraphDirectSum UploadBroadcast.ActualBlockGraph UploadBroadcast.UploadParameterDirectSum` passed without warnings.
- `lake env lean verification/UploadDirectSumAudit.lean` passed for 2,540 imported project theorem roots. The complete reachable axiom set was exactly `propext`, `Quot.sound`, and `Classical.choice`.
- `python3 scripts/audit_source.py` passed across 294 Lean files at this run.
- Frozen manuscript hash was rechecked and matched the value above.
- Logs: `logs/upload-direct-sum-build-20261008.log` and `logs/upload-direct-sum-axioms-20261008.log`.

The independent source reviewer inspected the actual combined-DemandData
bridge and accepted that it resolves the earlier semantic concern about a
merely defined block-diagonal map. This focused report does not assert that
all unrelated manuscript obligations or the final integrated build are done.
