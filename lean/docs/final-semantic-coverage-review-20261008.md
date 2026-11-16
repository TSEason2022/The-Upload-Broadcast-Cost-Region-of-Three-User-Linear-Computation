# Independent final semantic coverage review

Review started 2026-10-08, against the frozen manuscript
`../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

## Latest reviewed status

At the final 14:26 UTC recovery checkpoint, all 28 named claims and all inventoried paper-specific
unnumbered conclusions have passed this review. The four global
endpoints and both local demand-cycle orientations now pass unconditionally;
see the subsequent reviews below. The matrix frontend, literal direct-sum ranks, opposite-demand example
and both cited counterexample assertions are also independently approved.
The final unconditional R_n/five-bit upload specialization is now checked.
The additional exact primitive-table and theta-block construction audit also
passes, including actual relation and annihilation identities.
The semantic-review gate is true. This is a source-correspondence certificate
for these compiled conclusions, with the explicit external/proof-route
replacement boundary below. Final clean release integration remains a
separate requirement and is not asserted complete by this review.

## Initial snapshot verdict

The 23 named claims marked `reviewed_complete` at the start of this review
retain that verdict. Inspection of their source clauses, actual declarations,
and central definitions found no added target-as-hypothesis, narrowed field,
hidden coding-linearity assumption, dropped positive blocklength, or replaced
operational optimum. This is **not full-paper completion**.

The five remaining named claims are not approved by this snapshot:

- `thm:intro-main`: simultaneous corner, R2 equality and exact least linear blocklength;
- `thm:endpoint`: both actual cycle-repair relays exist, but the current mapped
  construction roots do not themselves establish their operational upload optimality;
- `prop:stable`: unconditional global scalar selection;
- `cor:scalar-budget`: unconditional original-task scalar joint code;
- `lem:binary-integer-relay`: unconditional binary global selection.

The global unnumbered/external gate must remain false while its standalone
obligations and the final integrated checks remain open. Fresh modules can
close those obligations only after their actual signatures and source
correspondence are reviewed.

## Mechanical evidence and its limits

`verification/FinalSemanticReview20261008.lean` independently imports the
current complete endpoints and prints the actual elaborated type and reachable
axioms of all 85 declaration occurrences mapped to the 23 complete claims.
The run exits 0, with no warnings/errors, and every reported axiom belongs to
`{propext, Classical.choice, Quot.sound}`. Output:
`verification/final-semantic-review-signatures-20261008.log`.

`verification/FinalUnnumberedReview20261008.lean` also resolves 42 selected
source-facing model, entropy/rank, operational benchmark, arbitrary-choice
invariance, profile-sum, margin, omniscience, root-table, example and arithmetic
endpoints and audits their dependency union. It passes with precisely the
same three standard axioms. Both the normal invocation and the direct pinned
Lean invocation pass and emit byte-identical logs:
`verification/final-unnumbered-review-signatures-20261008.log` and
`verification/final-unnumbered-review-direct-signatures-20261008.log`.
These selected checks do not automatically promote the remaining unnumbered
gate, and include the deliberately conditional original-selection reduction.

`verification/final-semantic-review-snapshot-20261008.json` hashes the source,
the signature log and all 253 project modules in the audit import closure.
Its timestamp check identifies `NonzeroDefectRelays.lean` as newer than its
olean. The coordinating reviewer reports that an independent recompilation of
that precise source produced a bit-identical olean; this is recorded in
`nonzero-same-chart-semantic-audit-20261008.md`. The timestamp discrepancy is
therefore not evidence of a known semantic discrepancy, but this review still
requires the separate final clean integrated build.

The signature checks establish that the advertised declarations exist and
their proofs have the stated trust boundary. They do not establish that a
source statement was translated faithfully; the semantic checks below do
that. The number of theorems is not a completeness argument.

## Core model correspondence

The source at lines 310–480 uses finite-dimensional coefficient spaces over
the original finite field. The formal task records A_i ≤ U_i ≤ sum A_j;
the ambient may initially contain unused directions. A source block is an
arbitrary linear functional into K^L, which is a coordinate-free source
matrix, not a restriction on the coding maps. General encoders, broadcasts,
and decoders in `Task.Code` are ordinary functions, and correctness quantifies
over every source block. The relay has only the upload tuple as input.

Uploads are charged by actual local encoder images. Every abstract side
restriction extends to an ambient source, so these images are attainable.
Broadcast costs use the image of the actual source-to-broadcast composite,
not unattainable combinations in the product of local message alphabets.
`achievableAt` requires positive L, finite canonical alphabets, nonnegative
budgets and cost inequalities. `costRegion` is the closure of the union over
L. `uploadOptimum` is its operational infimum. Finite relabeling justifies
the canonical alphabets.

The fully informed model separately permits arbitrary nested A_i ≤ U_i,
without feasible-upload or side-spanning premises. Its `broadcastOptimum` is
an infimum over actual finite-alphabet nonlinear codes of every positive
blocklength. `general_broadcastOptimum_eq_rankBound` proves the fifteen-rank
formula; it is not the definition. Its binary proof restricts an actual
extension-field code to four original-field instances. That general
attainment is sufficient for the benchmark and does not itself certify the
paper's stronger two-instance joint corner.

The matrix frontend under active construction is reviewed separately below;
until its current source builds and passes its own audit, the starting
subspace model alone does not constitute a formal arbitrary-matrix frontend.

## Named source statements retained as complete

Each entry was compared against the frozen source and the current type,
rather than accepted from its earlier audit title.

1. **Active reduction**, lines 598–616. The active-pair geometry identifies
   actual complementary coefficient spaces and the prescribed intrinsic pair
   ranks. The source-facing reduction joins that geometry to fixed-L nonlinear
   region equality and to all remote-private-use equalities. Quotient signal
   and row-rank theorems identify the exact residual demand subspaces. The
   private deletion clause is not inferred only from pair-rank equality.
2. **Minimum upload**, lines 707–721. The source formula takes only an original
   feasible task and field/dimension instances. Private, common, pure/mixed and
   active-pair ranks refer to constructed original-task reductions. The
   all-block nonlinear converse and closure bound are matched to actual
   original-field L=1/L=2 linear attainment. This theorem only promises upload
   optimality, consistently with the source.
3. **Common-function entropy**, lines 844–874. The actual conditional Shannon
   quantities, conditional independence, local recovery, common-function
   recovery and tripod bridge match the source. The two retained CMIs have
   the correct conditioning sets and signs. Finite conditioning matches Ω in
   the manuscript's finite source model. Cyclic renaming is unrestricted.
4. **Omniscience lift**, lines 911–935. The three retained inequalities are
   source premises, rather than hidden assumptions of the desired lift.
   Independence is joint for Ω versus the residual tuple and pairwise for
   residual observations, exactly as stated. The conclusion is the maximum
   deficit/half-sum bound.
5. **Signal-intersection bridges**, lines 996–1012. Actual canonical residual
   geometry supplies all cyclic tripod inclusions. The joint Ω-plus-residual
   endpoint accepts arbitrary uploads coupling both factors and retains all
   three Ω-conditioned CMI inequalities; it does not replace them by a weaker
   final sum-rate bound.
6. **Omniscience upload**, lines 1053–1067. Exact natural-length feasibility is
   equivalent to the three pair-deficit bounds. The LP optimum is the source
   maximum/half-sum and is attained over the same field at L=1 if integral,
   L=2 otherwise. Block lower bounds cover all L>0.
7. **Relay reduction**, lines 1111–1123. The decoder equivalence takes an
   arbitrary broadcast function, no local-generation premise, and exactly
   A≤U≤A+P. It works at every L by taking target K^L. A separate range equality
   preserves attained alphabets exactly.
8. **Residual decomposition**, lines 1240–1254. The component theorem applies
   to every actual finite product decomposition, not only a chosen one;
   existence of a genuine indecomposable decomposition is additionally
   proved. Activity passes through the exact labeled subspace equivalence.
   Whole-task nonlinear codes may mix components. The source value is
   2 dim F−sum dim A, with real subtraction. Literal individual-parameter
   additivity remains a separate unnumbered obligation.
9. **Residual profiles**, lines 1376–1382. Classification starts with a genuine
   active residual and indecomposability. The outside-table branch includes
   zero excess and the T2 index-zero boundary. All T1/O/Z exact choices and
   all arm permutations are present. `from_actual_regular` constructs the
   regular chart, so the chart argument in `profiles` is not an unproved
   normal-form oracle. All nine Q changes are exactly zero.
10. **Aggregate selection**, lines 1493–1502. The ten multiplicities and six
    capacities have precisely the source table coefficients. The internal
    coordinate permutation is accounted for. The ordered-ring theorem works
    over both reals and integers, yielding the actual nonnegative weights and
    multiplicity sums in each case.
11. **Demand-cycle extraction**, lines 1557–1572. Multiplicity is the actual
    quotient rank of A_k∩U_j modulo A_j+U_ij. Six disjoint source-coordinate
    edge spaces and a splitting complement are constructed simultaneously.
    Both orientations and arbitrary fields are included. The deficit endpoint
    uses an actual supplied resonant decomposition, as does this source lemma.
12. **Scalar LCBC for q≥3**, lines 1796–1801. There is no side-spanning premise.
    The returned original-field scalar linear code has exact attained-range
    cost ceil(D*), with D* the nonlinear operational optimum.
13. **Separated binary scalar LCBC**, lines 1808–1814. An arbitrary two-element
    field and arbitrary arm permutation are allowed. The exact separation
    and spanning assumptions are preserved, and the code is transported back
    to the original user order.
14. **Passive tripod deletion**, lines 1991–1998. The actual signed private
    incidence kernel produces the active-row space. A private shear by locally
    known tripod terms preserves all sides and removes the remaining row
    complement. Fixed-L nonlinear regions and the exact pure-plus-mixed
    retained dimension are conclusions. `DemandData` has an existence proof.
15. **Row completion**, lines 2146–2162. The prescribed complement W of the
    pure row span is preserved. One actual side-preserving shear fixes the
    entire tripod, and its extension fixes the pair factor. The relay has
    the exact private⊕Prow⊕Wv form, the prescribed pure rank, independent local
    row generators and directness. Exact scalar residual cost is obtained on
    the actual trimmed active residual.
16. **Original-field components**, lines 2330–2337. The source theorem uses
    actual representation indecomposability, spanning sides and positive
    excess. It concludes indecomposability of literal vertexwise tensor
    extension over an arbitrary extension field. `IsRealRoot` is a Weyl orbit
    of simple roots, not a definition by Tits norm one; the equivalence is
    proved. There is no supplied classification or extension-splitting oracle.
17. **Nonzero-family relays**, lines 2463–2494. All eight families, every n≥1,
    original q≥3 fields and all indexed-arm alternatives are covered. The
    full/induced six first and nine doubled second entries match the table.
    Family input is only the seven dimensions and genuine indecomposability;
    operational minimum upload is a conclusion.
18. **Optimal residual side separation**, lines 3124–3133. The theorem
    quantifies over arbitrary L>0 and P in the actual blocked ambient.
    `dim P=L U*` is legitimately its source premise. Pairwise disjoint sides
    suffice for the proved stronger theorem. Independence and exact spanning
    of P follow; auxiliary doubling is confined to the converse.
19. **Original binary menus**, lines 3163–3166. Exact first increments, every
    choice, all nine unchanged second entries and all permutations hold over
    the original field, including F2. T1/O, Z boundaries and positive-size
    regular tasks are covered by distinct actual constructions.
20. **Additional binary menus**, lines 3201–3242. Every selected menu element
    yields an optimal actual relay with the source's coordinatewise upper
    bound. Charges are bounded by actual margins at the exact parameter
    thresholds. Selection uses natural capacities, not fractional substitutes.
    The R2 orbit has six permutations. The three n=1 exceptions and jointly
    permuted component/profile/charge coordinates are explicitly covered.
21. **Integer allocation**, lines 3537–3542. All common, pair, aligned and
    individual quotas are natural and satisfy actual rank constraints. The
    common quota is maximal and total length equals ceil(operational D*).
22. **Column coordination**, lines 3579–3589. Actual matrix-column slice
    hypotheses follow from the source homogeneous distinct-group columns.
    Separate witnesses and the cardinality condition yield a common
    invertible assignment. Finite deterministic exhaustive search is proved;
    the source promises no complexity bound.
23. **Maximum disjoint subspace**, lines 3662–3669. Any field and finite ambient
    are allowed. Only the stated separation is assumed. The exact dimension
    and all three disjointness clauses are conclusions, including zero cases.

## Unnumbered and external obligations

The 125-display inventory is a routing aid. Definitions are not extra claims;
an alternative proof can replace internal proof steps, but cannot erase a
stronger standalone assertion. The following distinctions remain mandatory:

- Arbitrary-choice upload-rank invariance is genuinely quantified over both
  pair-reduction selections, arbitrary private/tripod charts and legal graph
  lifts. Its operational derivation of mixed-rank invariance is noncircular:
  the original upload theorem is already established without this module.
- Fully informed D* survives the actual passive retractions through code maps
  and range bounds. Restored relay witnesses preserve the same field, scalar
  blocklength, induced fifteen-entry profile and binary separation.
- `CanonicalScalarSelection K` in `OriginalJointReduction` is explicitly an
  unproved input. Its restoration theorem is correct conditionally and must
  not be promoted to unconditional main coverage.
- Literal B/G/G0 direct-sum identities and all individual rank sums at
  lines 2021–2026 are separate from already proved residual total U*
  additivity. Their new endpoint still requires review.
- The opposite-demand strict-subadditivity example at lines 1182–1186 needs
  the two actual task optima, their direct-sum optimum and the specified x+y
  scalar broadcast, rather than only the generic maximum subadditivity bound.
- Matrix redundancy/complement-basis normalization needs actual per-code
  transforms preserving original L and attainable costs. The current
  `MatrixTaskFrontend` source appears to provide that exact stronger interface,
  including literal retained original columns, but its latest build is pending
  in this snapshot.
- The entropy-insufficiency assertion at lines 434–436 and the distinct
  scalar-field-size-necessity assertion at lines 1804–1806 both need witnesses.
  The latter was absent as a separate item from the original routing ledger.
  See `cited-counterexample-review-20261008.md`: the cited F3 entropy examples
  fail their stated demand-triple entropy equality, while an F5 repair passes
  exact finite checks. These checks are not Lean proofs.
- The five-bit example has actual Boolean code/range certificates, an
  all-block fixed-relay lower bound, and a separate actual Task.Code scalar
  obstruction at D*=3/2. That obstruction does not establish field-size
  necessity for cost ceil(D*); those assertions must not be conflated.
- General Kac, finite-field uniqueness, Krull–Schmidt, preinjectivity and
  open-orbit assertions cited as proof routes are not entire imported Lean
  theorems. Their needed conclusions are instead proved constructively at
  the project endpoints. This replacement is acceptable and must be stated
  explicitly. No citation is an extra trusted axiom.

## Completion rule

Do not convert this snapshot to a full-paper certificate until the five open
named statements and all standalone source conclusions have faithful actual
endpoints; the latest matrix, direct-sum and counterexample work has been
reviewed; and the final source snapshot passes a clean integrated build,
declaration resolution, lexical admission check and dependency-axiom audit.
Any later proof-file change affecting these roots requires verification of
the resulting snapshot, not reliance on this timestamped report.

## Subsequent completed review: matrix frontend

The final `MatrixTaskFrontend`/`MatrixTaskEndpoints` sources now build, and
`verification/FinalMatrixFrontendReview20261008.lean` independently resolves
17 source-facing transport/normalization endpoints and checks their joint
axiom closure. The run exits 0 with only the three standard axioms; output is
`verification/final-matrix-frontend-review-20261008.log`. Both source files
are older than their freshly compiled artifacts. The builder reports one
harmless unused-field-instance warning, not an admitted or unchecked proof.

Verdict: the model-correspondence obligation at source lines 315–343 is closed.
The initial-snapshot references above to a pending frontend are superseded
by this section. No numbered claim is added by closing this separate item.

The Data model accepts arbitrary dependent original side and demand columns.
Its observations are literally X.transpose multiplied by each input matrix.
The source-to-coefficient map is a proved linear equivalence at each original
L. Side-column evaluation and joint side/demand evaluation are injective;
linear total left inverses recover the coefficient restrictions. These maps
give both nonlinear code transports and exact equalities of attainable
upload/broadcast ranges and costs. Independent side columns additionally
prove that every raw side matrix is attainable, recovering exactly the
manuscript's im(e_i) convention after normalization.

Both directions of the linear transports preserve K, L and the full nominal
length vectors. The normalized side and demand matrices have independent
concatenated columns and the source dimensions. The final
`exists_retained_normalization` is stronger than a mere replacement by
arbitrary basis vectors: every retained side/demand column comes from the
corresponding original matrix. Task equality and every fixed-L budget region
are conclusions. Finally, ambient restriction composes with the constructed
passive retraction and preserves every fixed-L region and linear feasibility.
No matrix full-rank, code linearity, source distribution or optimality premise
is imposed where the original source does not impose it.

## Subsequent completed review: unconditional global endpoints

At 11:18 UTC, `verification/FinalGlobalReview20261008.lean` passes against the
fresh `SourceMainTheorem` artifact, resolving 12 actual declarations and
auditing their combined dependencies. The only reachable axioms are the
three standard axioms, with no warnings/errors. The actual signatures are in
`verification/final-global-review-20261008.log`.

This approves `thm:intro-main` (lines 485–505), `prop:stable` (1716–1727),
`cor:scalar-budget` (1820–1825) and `lem:binary-integer-relay` (3396–3404).
The previous conditional-status descriptions apply to the initial snapshot
and are superseded for these four claims. Coverage-file changes are left to
the coordinating reviewer.

### The geometric premise is discharged

`ResidualBackgroundSelectionTheorem.exists_optimal_relay` takes only an
actual active residual S, an arbitrary fully demanded background O, and an
integer D at least the full S⊕O profile bound. It constructs an original-space
locally generated feasible P, rank equal to the operational S.uploadOptimum,
and all fifteen inequalities entry(S_P)+entry(O)≤D.

The proof constructs an actual finite indecomposable decomposition, derives
activity of each factor, partitions by dimensions and defect, and obtains
actual Jordan charts or admissible family dimensions. Positive-excess
indecomposables have no extractable edge by a proved physical splitting
argument; no Krull–Schmidt oracle is assumed. The untouched zero-excess product
therefore supplies the physical cycles without changing charged menu factors.

Component charge inequalities come from actual original profile margins.
Signed integer slacks are D minus actual first entries. The proof derives
nonnegative slacks, all three strengthened pair inequalities and all nine
second-entry bounds. Integer repair counts are bounded by physical cycle
multiplicities; at most one orientation needs repair. An injection selects
distinct resonant factors, an actual coefficient chart pairs them with
independent cycle coordinates, and the leftover zero-excess component is
retained. The final rank identity accounts for both repaired factors and
their removed cycle dimensions. All actual menu choices are realized over
the original field, including low-index boundaries and binary exceptions.

The public wrapper supplies every decomposition, family, activity, no-edge,
charge, menu, physical-cycle and optimal-rank premise of the internal assembly.
It equates the constructed rank sum with the original residual's nonlinear
operational optimum and transports the relay back through the exact
coefficient equivalence. No target relay, desired profile or desired optimum
is a hypothesis of the source-facing theorem.

`CanonicalSelectionAssembly` adds the actual omniscience relay. Its upload
integrality is derived from nonlinear Ω-plus-residual additivity and the
residual's integral rank, rather than assumed separately. Every feasible
omniscience relay preserves its full fifteen-entry profile. Optimal residual
side separation and the omniscience construction give the required binary
separation after a genuine user permutation. Actual passive and coordinate
retractions then restore every original task.

Thus `canonical_scalar_selection` and `Task.scalar_relay_selection` are
unconditional theorems. `CanonicalScalarSelection` and
`ResidualBackgroundSelection` are no longer unproved inputs to the main
source endpoints, even though earlier conditional helper APIs remain valid.

### Exact source conclusions

- `Task.stable_relay_source` gives the actual relay, its operational optimal
  rank and all fifteen bounds for every integer D≥D*. It strengthens the
  source from active reduced to arbitrary original feasible tasks. Binary
  separation is stated on actual ambient intersections P∩A_i; their sum is
  P by the returned local-generation proof.
- `Task.binary_integer_relay` specializes that theorem to any presentation
  of a two-element field and keeps the stronger separation conclusion.
- `Task.scalar_budget` gives an actual K-linear blocklength-one code with
  exact attained upload U* and broadcast ceil(D*) costs. The decoder/encoder
  type, not only an informal label, enforces original-field linearity.
- `Task.joint_two` gives an actual K-linear L=2 corner code for every task.
  It applies the scalar theorem to two copies, uses proved operational
  half-integrality and doubling, and flattens exactly to two original-field
  instances. There is no four-instance or extension-field substitution.
- `Task.main_region` proves both R2 and the closed arbitrary-block nonlinear
  region equal the rectangle of the original upload formula and the original
  fifteen-entry maximum. The previously established operational formula
  theorems identify these bounds with U* and D*. Upward closure and the
  all-block/closed-region converses justify the full rectangle equality.
- `Task.minimum_linear_blocklength` is an `IsLeast` statement over positive
  blocklengths admitting actual linear joint codes. The displayed candidate
  `linearJointLengthFormula` is 1 exactly when both operational optima are
  integers, otherwise 2. Necessity uses attained-range linear rank
  integrality, so padded nominal alphabets do not create an exception.
- `nonlinear_uniform_bound_tight` simultaneously supplies the actual binary
  example's linear L=2 corner and excludes every finite-alphabet nonlinear
  scalar code from attaining its D*=3/2. This is the manuscript's tightness
  clause in the same operational model.

Audited source hashes:

- `SourceMainTheorem.lean`: `d0ba99d861ad99ef1bfae60b85233915b7ebc0317e5d4ec57812953100fed3e8`
- `ResidualBackgroundSelectionTheorem.lean`: `edbd5d548a5443af200a32a0d32aafd7199371c985d756f9486fc525016c0062`
- `CanonicalSelectionAssembly.lean`: `8f0745478d93648fa10be36716e79af402e427c65a0a7950089d879b988bea15`

## Subsequent completed review: literal direct sums and rank parameters

At 11:25 UTC the standalone obligation at lines 2021–2026 is independently
approved. `verification/FinalDirectSumReview20261008.lean` resolves 11 actual
map/rank endpoints and checks their joint dependency axioms, exiting 0 with
the three standard axioms and no diagnostics. The output is
`verification/final-direct-sum-review-20261008.log`; the four proof modules
also have fresh clean builds.

The first proposed helper defined B and G directly by blocks, which alone
would not identify the manuscript's maps. This review requested a source
bridge before approval. The final `ActualBlockGraph` closes that concern:

- `combinedTask` is the genuine finite product transported into canonical
  product-private/tripod coordinates by an explicit ambient equivalence.
- Actual quotient signals, private domains and pure rows are identified with
  their component products. `combinedData` is constructed with exact
  signal-membership proofs for this task.
- `actualB` is literally `DemandData.incidence` for the combined task.
  `actualG` is literally its constructed relationRows map followed by the
  quotient by its actual pure-row sum. They are not postulated block maps.
- `incidence_conjugacy` and `graph_conjugacy` identify these maps with the
  component maps under genuine private/domain and pure-quotient equivalences.
  `actualKernelChart` identifies the actual cancellation kernel.
- `G0_direct_sum` is the equality of the resulting actual restricted maps,
  with both coordinate identifications explicit. `mixed_image` gives the
  exact product of component images, and `mixed_rank_additive` takes ranks.
- Common pure, noncommon pure and total retained-tripod rank additivity are
  stated separately in `common_rank_additive`, `pure_rank_additive` and
  `tripod_rank_additive`. Required nonnegative dimension subtraction is
  justified by inclusion of the common rows in the pure sum.
- `UploadParameterDirectSum.retained_private_spaces` identifies each actual
  remotely used private subspace; `private_dimension_additive` proves d_priv
  additivity. The intrinsic active-pair formula adds before any choices.
  Arbitrary legal chart transfer and the separately proved arbitrary-choice
  invariance cover other source choices.

The map equalities hold over arbitrary original fields; rank sums assume
only the source's finite index set and finite-dimensional relevant factors.
Graph lifts are arbitrary validated component presentations, including the
already privately trimmed summands used by the manuscript. This establishes
individual parameter sums independently of total operational U* additivity.

## Subsequent completed review: the two additional concrete examples

At 11:26 UTC the following two source assertions are independently approved.

### Strict broadcast subadditivity, lines 1182–1186

`OppositeDemandExample.strict_subadditivity_example` uses exactly the two
one-dimensional source tasks: A=(top,bot,bot), U=(top,top,bot), and
A=(bot,top,bot), U=(top,top,bot). Their `combined` task is the literal
coefficient direct sum on K×K. Every original finite field is included.

The endpoint proves all three actual nonlinear broadcast optima equal one,
then the strict inequality between the joint optimum and the sum. It returns
a genuine scalar linear encoder equal to x(1,0)+x(0,1), with constructed
zero-error linear decoders and exact attained-alphabet cost one. Specific
actual profile entries give the lower bounds, while the constructed codes
give the upper bounds. No profile, optimum or successful code is supplied as
a premise. This closes `OPEN-OPPOSITE-DEMAND-EXAMPLE`.

`FinalStandaloneReview20261008.lean` checks this endpoint together with the
11 direct-sum roots; it exits 0 and reports only the three standard axioms.
Output: `verification/final-standalone-review-20261008.log`.
Audited example source SHA-256:
`ba664077cca558c661b8f4426855b83d51d2029088c211eb03809dc495e9885f`.

### Binary scalar field-size necessity, lines 1804–1806

`CitedBinaryFieldNecessity` uses ZMod 2 and the coefficient plane. Its side
spaces are the lines generated by (1,0), (0,1), (1,1). The separate
`signal_from_demands` theorem proves that the literal cited demand columns
(0,1), (1,1), (1,0), together with these sides, give exactly its three full
signal spaces. Thus it matches Example 4, rather than relying on an unrelated
fully demanded model.

`broadcastOptimum_eq_one` evaluates the actual fifteen-entry profile and
uses the proved general nonlinear operational formula. For any arbitrary
scalar `BlockBroadcastCode`, a finite kernel-checked binary-line calculation
finds a user with the same side observation on any pair of sources. If their
broadcasts coincide, that user's full signal decoder forces the sources to
coincide. This proves injectivity on the four actual binary source vectors.

`scalar_broadcast_card`, `scalar_cost_ge_two` and `scalar_cost_gt_ceiling`
therefore give at least four attainable messages, cost at least two, and
strictly greater cost than ceil(D*)=1. No linearity is assumed in the scalar
obstruction. This independently proves the source's claimed necessity of
the q≥3 hypothesis at the rounded benchmark, unlike the five-bit
half-integral tightness example.

`FinalBinaryNecessityReview20261008.lean` independently checks the six actual
endpoint types and their joint axiom dependency union, exiting 0 with only
the standard three axioms. Output:
`verification/final-binary-necessity-review-20261008.log`.
Audited source SHA-256:
`72dda5540de7daa4e6dc3454d51facc2ec4b0673f3f84d879545e611ffc22835`.

## Subsequent completed review: local demand-cycle optimality

At 11:34 UTC, `thm:endpoint` (source lines 1609–1622) is independently
approved. This closes the last named statement. The current source endpoint
does not merely repeat the earlier construction/rank profiles: it adds
genuine nonlinear operational upload optimality.

`CycleSourceEndpoint.positive_directSum` and `negative_directSum` take only
the original finite field and a natural n. Their actual task is the literal
direct sum of the source's canonical Jordan representative R_(n+1) with the
appropriate scalar directed cycle, identified by exact coefficient-space
charts. Thus every source size at least one is covered. The transpose/head
convention is the one already checked for the original resonant model;
`repair_of_equiv` preserves the full conclusion under actual labeled charts.

Their `Repair` conclusion contains:

- an actual original-space P, local generation and relay feasibility;
- dim P=3(n+1)+4 and equality of that rank to the operational nonlinear U*;
- the exact e2 first increment in the positive orientation, e4 in reverse;
- every one of the nine second-family entries unchanged;
- an actual original-field `T.LinearCode 1 uploads d`, with total nominal
  uploads d and exact attained upload cost d.

Activity is constructed from the explicit side/signal geometry. Side ranks
and signal-pair spans are proved, a fixed-head witness gives the precise
tripod inclusion, and the common triple signal intersection is zero.
The reverse proof uses the actual coordinate flip with an inverse
automorphism and a proved user swap; it does not assume the stronger false
whole-ambient tripod join. The established residual converse consequently
applies to arbitrary nonlinear codes at every positive blocklength and to
closure. The actual dimension calculation gives 3(n+1)+4, and the constructed
relay attains it. No operational-optimality hypothesis is supplied by the
caller.

`verification/FinalCycleReview20261008.lean` independently prints the full
`Repair` definition, resolves eight geometry/optimality/source theorem types,
and checks their joint dependency axioms. It exits 0 with no diagnostics and
only the three standard axioms. Output:
`verification/final-cycle-review-20261008.log`.
The local author's separate audit also checked all 4,632 imported project
theorem roots against that same whitelist.

Audited source hashes:

- `CycleSourceEndpoint.lean`: `b5d403a6372122b817453ea471b37753e7c089d05305bc14b5c60ef443e56754`
- `CycleUploadOptimality.lean`: `d16e5e5ad032068ae635c8722811ede909fc1c992eef0402693ac7ad7efcc895`
- `CycleUploadGeometry.lean`: `fb8878eb9bc8b817ac96a36d7de0ed60a29e61730acc0cc8440fd8c30fb59f77`

## Subsequent completed review: corrected entropy-insufficiency witness

The source assertion at lines 434–436 is independently approved through
`CitedEntropyCounterexample.corrected_entropy_counterexample` and
`equal_subset_entropies_distinct_operational_optima`.

The exact side observations are A,B,C and demands B+C,A+C,A+tB, comparing
t=1 and t=2 over F5. The mask s:Fin 6→Bool selects exactly the original six
variables, with constant zero in unselected coordinates. It does not select
bundled signal spaces U_i. Kernel-checked finite arithmetic proves equal
kernel cardinalities for all 64 selections on the actual 125-point source.
Finite-field cardinality and rank-nullity give equality of actual observation
ranks, and the established finite-field Shannon law proves equal entropies.
`all_block_subset_entropies` includes every L and hence every positive
original blocklength.

`CitedEntropyModel.scalarSource` bijectively identifies source triples with
actual one-instance coefficient functionals. The uniform law is established,
and `joint_original_coefficients`, `original_side`, `original_demand` and
`task_signal_eq` bind the six maps to their actual operational tasks.

The profile proof uses finite carriers whose closure fields construct genuine
submodules. Join/meet equalities and cardinality-to-finrank conversion are
proved; no matrix-rank or operational-optimum result is assumed. It evaluates
the six first entries as one for both tasks, and the nine second entries as
one versus 3/2. The already proved universal LCBC optimum theorem therefore
gives actual nonlinear operational D*=1 versus 3/2.

This is a corrected witness for the frozen manuscript's existential claim.
The primary cited article's F3 pair is not certified as entropy-identical:
its demand triple has ranks three and two, respectively. The F5 construction
proves the intended source conclusion without perpetuating that error or
changing the frozen manuscript.

`verification/FinalEntropyWitnessReview20261008.lean` independently checks
13 actual source/entropy/operational theorem types and their joint reachable
axioms. It passes both before and after the author's warning-free
dependency-aware rebuild of all eight modules. The two independent output
logs have identical SHA-256
`33e91a7db3cedc989e6b43cd1ec768cc7cd0c693f4e1bf422d43c9534ae0ab75`:

- `verification/final-entropy-witness-review-20261008.log`
- `verification/final-entropy-witness-review-after-rebuild-20261008.log`

Only `propext`, `Classical.choice`, and `Quot.sound` are reached. The author's
separate fresh audit checks all 888 imported project theorem roots with the
same result. The complete source hashes and build evidence are retained in
`verification/cited-entropy-evidence-20261008.json`; the source-facing umbrella
hash is `e1d02a00882935b9081259f0b260df2dec3b21dc8a4ed7cdc23935fd32088bc3`.

## Final completed specialization and semantic disposition

The last source-facing specialization, at lines 1277 and 2885–2887 and in
the five-bit example, is now unconditionally proved by
`ResonantUploadSpecializations`:

- `jordan_active` pulls the already proved cycle activity through the exact
  resonant-plus-cycle coordinate equivalence and restricts to the actual
  resonant direct factor. It assumes neither activity nor a chart.
- `jordan_uploadOptimum` and `source_uploadOptimum` give actual nonlinear
  U*(R_n)=3n+1 for every original finite field and every source n≥1.
- `map_scalarCoordinates` explicitly evaluates the unique private coordinate
  of each size-one Jordan vector and identifies all six labeled subspaces
  with the literal scalar-coordinate model.
- `binary_uploadOptimum` proves `BinaryOperationalTightness.task.uploadOptimum=4`.
- `binary_joint_two` supplies an actual original-field `LinearCode 2` on that
  same task with exact attained-alphabet costs (4,3/2).

`verification/FinalResonantSpecializationReview20261008.lean` independently
checks all seven endpoint signatures and their combined dependency axioms.
It exits 0, without diagnostics, using only the three standard axioms.
Output: `verification/final-resonant-specialization-review-20261008.log`.
Audited proof source SHA-256:
`92db7fb272a910ce4cbb50e84401c06de06af5d067a82815cd1e57d9dd51d820`.

The final generated unnumbered inventory now has no open standalone or model
correspondence conclusions. All 125 display items, 32 proof blocks, five
numbered tables and 13 supplementary groups have explicit routes. The
semantic flag `unnumbered_and_external_dependencies_reviewed` is set true
with the coordinating reviewer's authorization. That flag concerns source
conclusions and review of substituted proof inputs, not whole external
theories, exact reproduction of every proof construction, release build
completion, publication or licensing.

The complete semantic snapshot is
`verification/full-source-semantic-review-20261008.json`. It records exact
source/log hashes and the proof-source snapshot, and keeps release verification
separate. Subsequent mathematical source changes must be rechecked rather
than silently inheriting this approval.

The final combined check, `verification/FinalAllCoverageReview20261008.lean`,
resolves 611 distinct theorem roots covering every current named mapping, the
exact primitive/theta constructions, and
the selected source-facing unnumbered/model conclusions. It passes with only
the standard three axioms and no diagnostics; log:
`verification/final-all-coverage-review-20261008.log`.
The coverage-manifest and lexical gates also pass, the latter scanning 396
Lean files in the current workspace at its initial checkpoint; the final
post-literal audit scans 413 files. The semantic snapshot hashes all 311
project modules in this combined import closure. Its source/artifact timestamp
exceptions are retained explicitly for the release verifier rather than
silently presented as a fresh clean build.

Current `ClassifiedRelayPartition.lean` was additionally recompiled to a
separate temporary artifact. It passes, with two unused-[Finite K] instance
warnings and no errors. Its compiled hash differs from the shared artifact,
so final dependency-aware rebuilding is still required. No shared source
or artifact was changed by this reviewer. The exact result and hashes are
recorded in the semantic snapshot and
`verification/classified-partition-current-source-recheck-20261008.log`.
The coordinating reviewer subsequently excluded those two unused section
instances and verified the revised current source with an empty
warning/error log at
`verification/classified-partition-final-source-recheck-20261008.log`.
Shared downstream artifacts intentionally await the clean release rebuild.
The proof-source hash inventory was refreshed after the coordinator froze
the final root imports and the construction author froze all mathematical
modules. Shared artifacts still do not stand in for the fresh release build.

The additional literal audit of the primitive flag/relay matrices and the
R0(theta)/D(theta) proof constructions is complete. The independent
`verification/FinalLiteralConstructionReview20261008.lean` resolves 411
actual theorem signatures and passes with only `propext`, `Quot.sound`, and
`Classical.choice`; its log is
`verification/final-literal-construction-review-20261008.log`.
All 100 literal side/demand/signal/form matrices across ten relay choices
match the seven flag rows and ten relay rows in the frozen source, checked
independently by `verification/check_literal_primitive_transcription_20261008.py`.
This transcription check is diagnostic; Lean proves the mathematical ranks
uniformly over every field from exact integer factorizations and split identity
minors. It uses neither finite-prime sampling nor an external rank oracle.

The checked primitive endpoints include actual column-span/kernel identities,
full and induced RankConditions, every profile entry, locally generated
feasible relays, genuine side-relation basis/slice/component identities,
nonzero opposite relation values, designated-signal annihilation, and the
actual R2 wedge determinant one. There is no characteristic restriction or
requested-rank hypothesis. The literal R0(theta) and D(theta) vector spans
are independently checked over arbitrary fields with theta != 0,1, including
the three exact pair lines, actual induced-task identification, profiles,
and actual one-copy append dimension/conditional/profile increments. The
append construction is certified one copy at a time; the separately proved
family theorem supplies the complete unconditional parameterized conclusion.

The phrase about pair-conditional ranks has its explicit preceding scope
`crk(U_ij | A_j)`, with a participating conditioning arm. It is not enlarged
to arbitrary third-arm conditioning (the full R0 example has
`crk(U_23 | A_1)=2`). The complete external open-orbit/geometric transfer
theory remains outside the claimed formalization. Detailed construction
routes and trust boundaries are in `docs/LITERAL_PRIMITIVE_TABLES.md` and
`docs/LITERAL_THETA_BLOCKS.md`. The author's separate all-safe-declaration
audits cover 1,807 primitive declarations and 121 theta declarations,
including proof-bearing definitions, with the same standard axiom boundary.

A separate literal cross-check of the three conclusion tables found no
discrepancy. It confirmed every residue row and legal threshold, every exact
T1/O/Z/R increment and printed margin vector, and all binary-extra parameter
ranges, charges and the R2 permutation orbit. The regular library's n=0 is
the source's R1, as checked by `every_positive_length` and the exact resonant
margin formula. One important distinction is retained: the global
`ActualComponentCapacities` implementation sometimes uses smaller sufficient
T1 charges. The source's stronger literal T1 margin table follows from the
exact full-profile theorems, not from equating these smaller charges to the
printed table. This three-table cross-check is separate from the completed primitive
proof-construction audit above.
The detailed independent cross-check is saved in
`docs/literal-menu-residue-tables-review-20261008.md`.


## Warning-only release recovery, 14:24 UTC

The first fresh release build checked its first 274 project modules and then
stopped at the strict warning gate: `MatrixTaskFrontend.finite_set_matrix`
retained an unused section `[Field K]` instance. The preserved failed snapshot
is not a release. The sole mathematical-source edit is `omit [Field K] in`
before this finite-set enumeration helper. Its statement text and proof body
are unchanged; the elaborated declaration is stronger, applying to arbitrary
`K : Type u` without a field structure. No paper conclusion is weakened.

`verification/FiniteSetMatrixFieldOmissionReview20261008.lean` independently
checks that exact compiled signature and applies it in an explicit no-field
example. Its standard-axiom check passes. A separate diagnostic tree rebuilt
all 39 remaining targets warning-free and passed all-module axiom collection
(11,018 safe declarations, including 8,398 theorems from 313 project modules),
the 95-reference coverage audit, 12 public examples, and integrated gates.
It reused project artifacts from the interrupted run and is explicitly a
diagnostic, not a substitute for the next fresh complete-source release build.
Source comparison confirms no other mathematical-source change.

The final 611-root independent endpoint harness was rerun against those
recovered diagnostic artifacts and passed with only the same standard three
axioms; log `verification/final-all-coverage-review-recovery-20261008.log`. The source/evidence receipt records this
recovery separately from the original checkpoint, retaining the explicit
requirement for a new clean release build. Evidence is in
`verification/semantic-recovery-diagnostic-20261008.json` and
`verification/finite-set-matrix-field-omission-review-20261008.log`.
