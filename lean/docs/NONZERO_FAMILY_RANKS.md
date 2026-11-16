# Original-field nonzero-defect family ranks

`IntersectionProbes.lean` constructs actual connected thin flag configurations:
its center is the base field, each selected vertex is the full one-dimensional
space, and other vertices are zero. Every probe is proved indecomposable. Its
quiver Hom space into a six-subspace task is linearly equivalent to the literal
selected intersection.

`QuiverHomTerminal.lean` identifies Hom into a source-supported target with the
linear maps at its supporting vertex. Combined with `QuiverEuler.lean`, actual
simultaneous source reflections calculate the Hom dimension as
`max 0 (Euler probe target)` whenever the target is an indecomposable of positive
defect. A source-simple probe reached first gives Hom zero and nonpositive
Euler pairing; a source-simple target reached first gives its vertex rank.

`NonzeroFamilyRanks.lean` applies these results to all eight listed full families
at n >= 1. Only actual task indecomposability and its seven defining dimensions
are assumed. Conclusions include:

- All pair signal intersections and side/signal intersections
- The common triple signal dimension and its disjointness from every side
- Pairwise side disjointness and side-space spanning
- The full geometric `RankConditions`
- All six full first-family entries and all nine doubled second-family entries

`NonzeroRelationRestrictions.lean` also calculates the genuine relation-kernel
dimension (one or two) and proves injectivity of every relation projection.
For the seven codimension-one families, an actual enlarged-tripod probe proves
the needed relation projection lies outside the designated signal space.
Finite-field kernel avoidance then constructs a feasible, locally generated
hyperplane of dimension f-1 while simultaneously enforcing both remote maximal
conditional ranks.

No dense-orbit transfer, desired profile, custom axiom, or `sorry` is used in
these statements. The full-rank and relation audits are in
`verification/NonzeroFamilyRanksAxioms.lean` and
`verification/NonzeroRelationAxioms.lean`; they report only the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`.

`NonzeroHyperplaneProfiles.lean` proves the exact six first-entry increments
and all nine unchanged doubled second entries for the seven hyperplane families.
`NonzeroHyperplaneUpload.lean` also proves that the sum of local side-intersection
dimensions equals the relay dimension.

`NonzeroSameChart.lean` combines those constructions with `R2ExactProfile.lean`
into `exists_same_chart_relay` for all eight families. It gives local generation,
feasibility, dimension f-codimension, exact local upload cost, and all fifteen
induced profile values. `same_chart_full_and_relay` includes the full-task values
as well. Its standard-axiom audit is
`verification/NonzeroSameChartAxioms.lean`, with results recorded in
`verification/nonzero-same-chart-axioms.log`. It does not package the separate global upload converse/optimality
argument into this local existence statement.

The codimension-two wedge and binary menu consumers are in separate files.
Full global theorem coverage still depends on the other assembly steps and must
not be inferred from this local result alone.
