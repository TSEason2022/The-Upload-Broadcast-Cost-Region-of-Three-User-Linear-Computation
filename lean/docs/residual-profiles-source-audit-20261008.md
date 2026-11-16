# Source audit: sufficient residual relay choices

Source: frozen `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.
Target: Proposition `thm:profiles`, beginning at line 1376, including Table `tab:menus`, the component classification at 2365ff, and the low-index paragraph at 2786–2801.

## Source-faithful endpoint

`ResidualProfiles.profiles` is a single compiled theorem with these actual inputs:

- the original finite coefficient field K and `3 <= Fintype.card K`;
- an actual finite-dimensional operational task T;
- genuine simultaneous indecomposability of its six coefficient subspaces;
- `ResidualComponentAdditivity.ActiveResidual T`, whose fields are actual side disjointness/spanning, private signal use, the tripod signal bridge, and absence of fully demanded common tripod rows.

The activity predicate does not include an upload formula, profile condition, relay, family membership, classification result or desired optimum. `ResidualComponentAdditivity.finalResidual_active` derives it for the constructed source residual. The component/decomposition theorems derive it for each actual indecomposable component.

The endpoint gives all four source clauses together:

1. Every component outside the listed exceptional families has an actual feasible, locally generated relay with dimension equal to the original nonlinear operational `T.uploadOptimum` and all fifteen induced entries exactly unchanged.
2. Every labeled T1 instance has every stated exact increment choice. Natural index zero is included and is exactly the Z boundary; all positive indices use the nonzero-family construction.
3. Every labeled O instance at its legal index n >= 1 has all three exact increment choices.
4. Every actual regular R_n chart has all three exact increment choices.

`OptimalExactMenu` records an actual relay for every choice, equality of relay rank to the operational optimum, and exact equality of all fifteen entries to the original entries plus the menu increment. `permutedIncrement` and `ResonantFiniteAssembly.increment` are definitionally zero on all nine second-family entries.

## Exhaustion and source labels

`ResidualComponentClassification.residual_exhaustion` starts with the actual indecomposable active residual. It separates zero excess and then constructs a concrete user permutation, a natural family index, or an actual labeled linear-equivalence chart to the Jordan task. It assumes no real-root or family oracle.

For nonzero defect, Tits value one follows from the actual reflection-functor classification. `RootClassification` supplies the nine numerical rows; the new bridge converts them into actual `pathPerm` arm labels and natural indices. For zero defect, the proved original-field regular classification supplies a genuine configuration isomorphism; `mapTask_of_configurationIso` converts it to an exact operational task equality.

The eight positive-index families are exhaustive. R0/R2 at index zero are passive; R1/T3 at zero are omniscience; O/H cannot have index zero. The active residual geometry excludes those removed endpoints. T1 at zero is retained as Z. T2 at zero is retained separately and proved profile-preserving. It is not silently dropped as passive or omniscience.

`ListedExceptional` expresses exactly the T1/O/Z/regular families using their actual dimensions, permutations, and the regular task chart. The six-permutation table is proved exhaustive. `NonzeroSameChartPermutations.indexed_menu_table` identifies the increments with the three labeled T1 and O rows; the same T1 permutation table gives the Z rows at index zero. Choice ordering and the repeated padding of two-choice menus are immaterial.

## Regular original-field exactness

`RegularExactMenus.from_actual_chart` transports the canonical exact profile equalities, actual relay and its rank into the original coefficient space. It strengthens a menu upper bound to the exact six first-family increments and equality of all nine Q entries. Optimality is obtained from the proved intrinsic residual minimum and the independently calculated Jordan upload rank, not from an assumption that the relay is optimal.

`RegularExactMenus.from_actual_regular` removes the chart input: actual indecomposability, residual geometry, zero defect and positive excess construct one n and all three exact optimal relay choices on the original task. The library parameter n is the manuscript's positive index n+1. There is no extension-field requirement or additional characteristic restriction. These regular and boundary constructions work over every finite field, including the binary field.

## Verification and remaining scope

The new assignment, boundary, exact-regular, outside-table and full proposition modules have focused Lean builds. Their corresponding `verification/*Audit.lean` files print only `propext`, `Classical.choice`, and `Quot.sound`; no new axioms, admissions or unsafe proof certificates are used.

This closes the local proposition. It does not by itself prove global relay allocation, the demand-cycle repair algorithm, the scalar endpoint for an arbitrary original task, or the complete source paper. Those are separate source claims with separate assembly obligations.
