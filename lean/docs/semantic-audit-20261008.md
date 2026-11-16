# Independent source-semantic audit, 2026-10-08

## Scope and verdict

Frozen source: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

This review checks the mathematical meaning of the 12 claims currently marked complete in `coverage.json`, not the number of supporting declarations. All 12 pass in the paper's finite-field, finite-dimensional, finite-alphabet model. No downgrade of that existing count is indicated. This is not a declaration that the whole paper, or the remaining 16 named claims, is verified.

The three additional residual claims have different outcomes:

- `lem:active-empty-row`: semantic pass for the constructed canonical residual task, using the bundle described below. It is eligible for a separate coverage promotion after the integrated declaration/axiom audit includes the new modules.
- `lem:bridges`: the actual geometric bridge and isolated-residual retained-information bounds are proved. The full source endpoint for arbitrary jointly coded omniscience/residual observations, retaining the Ω-conditioned mutual-information terms, is not exposed as a public source-level theorem. Do not promote solely on the final global upload lower bound.
- `lem:zero-common-row-relay`: genuine unrestricted original-field relay existence and the correct total rank are proved. The exact source statement additionally specifies the pure/mixed decomposition of that relay and its coordinate change. Those clauses are not in the current public endpoint. Do not promote the full named claim yet.

No coverage file, umbrella import, or mathematical proof module was edited for this review.

## Mechanical checks

- `verification/SemanticAudit20261008.lean` checks the 21 mapped declarations belonging to the 12 complete claims, prints their actual elaborated signatures, and asks Lean for their reachable axioms. It additionally inspects the residual candidates.
- `logs/semantic-audit-20261008-signatures.log` records the results. All 21 mapped declarations resolve; each reaches only `propext`, `Classical.choice`, and `Quot.sound`.
- `logs/semantic-audit-20261008-build.log` records a successful targeted Lake build of the complete claims' endpoint modules and the new residual modules. There were no errors or warnings.
- The source hash was recomputed and matches `coverage.json`. The audited source modules were not newer than their corresponding compiled `.olean` files when checked.

These checks supplement the project-wide `scripts/AuditAxioms.lean` union-of-roots audit; they do not replace a fresh final integrated build after concurrent work finishes. Axiom cleanliness establishes kernel trust, not source-semantic equivalence. The latter is the purpose of the review below.

## Shared model checks

`Model.lean` represents a source block as `F →ₗ[K] (Fin L → K)`. This is the coefficient-space form of the paper's source matrix, rather than a linearity restriction on encoders. `Task.Code.encode`, `broadcast`, and `decode` are ordinary functions, so arbitrary nonlinear fixed-length zero-error coding is included. `FiniteCode` requires positive blocklength and finite message types.

`Task.Code.uploadCost` uses the sum of logarithms of the actual encoder ranges, divided by L. `broadcastCost` uses the actual range of the source-to-broadcast composite, not all formal relay-input tuples. `achievableAt` contains nonnegative budgets bounding these exact costs; `costRegion` is the closure of their union. `uploadOptimum` is an operational infimum over that region.

For fully informed LCBC, `BlockBroadcastCode` imposes no upload-feasibility or side-spanning condition. Its encoder and decoders are arbitrary functions. `broadcastCosts` ranges over every positive L and finite alphabet `Fin n`; `finite_relabel` justifies this canonical alphabet restriction. `broadcastOptimum` is the infimum of these actual costs, not a rank expression defined to be optimal. `general_broadcastOptimum_eq_rankBound` proves the equality using a universal nonlinear converse and actual attaining block codes. Its binary general case really restricts an extension-field code to four ground-field instances, preserving the attained alphabet; it does not silently change the original task's field.

## The 12 existing complete claims

### 1. `lem:five-cmi`, source lines 844–881

Endpoint: `FiniteAlphabet.commonFunction`.

The variables are genuine heterogeneous finite-alphabet random variables on an arbitrary probability sample space. Coordinate sets merely permit tuple notation; they can be singleton coordinates for each source variable. Conditional independence, local encoder functional dependence, local Y recovery, common-function recovery, and the final tripod recovery hypothesis all correspond to the source assumptions. The conclusion contains Γ and both retained conditional mutual informations with precisely the source conditioning sets. The theorem actually needs only two of the three tripod-recovery assumptions, so that is a strengthening, not an extra condition. Cyclic versions follow by permuting its unrestricted named arguments.

Entropy is in nats. The inequality is homogeneous and hence is identical after positive rescaling to q-ary units. The conditioning variable O is finite-alphabet too. This matches Ω in the paper's finite-field block model; this audit does not claim a separate extension to arbitrary infinite-alphabet conditioning variables.

Verdict: complete in the stated paper model.

### 2. `lem:omni-lift`, source lines 911–939

Endpoint: `FiniteAlphabet.omniscience_lift`.

The theorem assumes joint independence of Ω from the residual tuple, residual pairwise independence, omniscience sides determined by Ω, uploads determined by the corresponding pair of side variables, and all three recoveries. Its three residual-bound premises are exactly source equation `ol-three`, which is an assumption of this lemma rather than its desired conclusion. The final maximum is the maximum of the three actual conditional entropies and their half-sum. No interaction inequality or final lift is assumed as a hypothesis. The same finite-conditioning scope applies as above.

Verdict: complete in the paper model.

### 3. `lem:ck-omniscience`, source lines 1053–1069

Endpoints: `Omniscience.exists_code`, `nonempty_code_iff`, `exists_scalar_optimal`, `exists_two_instance_optimal`, `block_cost_lower`.

`Omega V X₁ X₂ X₃ = V × V × X₁ × X₂ × X₃`; the three local observations are respectively `(v,X₂,X₃)`, `(r,X₁,X₃)`, and `(r-v,X₁,X₂)`. These are exactly the common-tripod and three pair-known blocks in `ck-space`/`ck-side`. The missing dimensions are `dim V + dim Xᵢ`.

Each encoder is a K-linear map of only its local observation. Each decoder receives its local observation and only the other two uploads and recovers all of Ω pointwise. `nonempty_code_iff` proves necessity and sufficiency of the three integer deficit bounds. The allocation lemmas prove that their real LP optimum is the explicit maximum/half-sum value and supply integral or half-integral optimizers. The two attainment theorems use the same field K and prove equality of actual alphabet costs, not just nominal vector lengths. `block_cost_lower` quantifies over every positive L. The additionally available `no_scalar_optimum_of_nonintegral` proves the expected obstruction.

Verdict: complete; all-block converse and exact original-field one/two-instance attainment are linked.

### 4. `lem:pis`, source lines 1111–1124

Endpoints: `relay_decoder_equivalence`, `relay_attainable_range`.

For arbitrary broadcast function g, the equivalence constructs deterministic decoders on both sides. It only assumes A≤U and U≤A+P. It imposes neither local generation of P nor linearity of g. Choosing W=K^L gives all blocklengths, and the theorem is in fact more general in W. Its induced observations are precisely restrictions to A∩P and U∩P. The separate range equality proves exact preservation of the attained broadcast alphabet. Applying this per user supplies the three-user assertion.

Verdict: complete, including nonlinear broadcasts and alphabet equality.

### 5. `thm:packing`, source lines 1493–1503

Endpoint: `Allocation.aggregate_selection_paper_coordinates`.

The internal slack order is `(e1,e4,e5,e6,e2,e3)`. Inspection of every row of `ordinaryMenu` recovers the nine nonresonant rows of Table 1, with repeated generators only padding a two-choice menu. `resonantConsumption` yields exactly `(e1+e3)`, `(e2+e5)`, and `(e4+e6)` in source coordinates. `paperOrdinaryMultiplicities` removes only the resonant table row.

The three explicit pair-capacity premises have the table's exact coefficients. The endpoint's two inequalities are μ_R≤s1+s4+s5 and μ_R≤s2+s3+s6. The theorem holds over a linearly ordered commutative ring, so the real and integer specializations respectively prove fractional feasibility and integral allocations. `AggregateFeasible` contains the actual nonnegative menu weights, required multiplicity sums, and coordinatewise capacity inequalities.

Verdict: complete; no table/permutation mismatch found.

### 6. `lem:edge-identity`, source lines 1557–1573

Endpoints: `EdgeExtraction.simultaneous_maximal_extraction`, `EdgeProfile.edge_price_identity`, `edge_price_le_extractable`, `EdgeDeficits.demand_cycles_from_decomposition`.

The extractable multiplicity is the exact quotient dimension of A_k∩U_j modulo its intersection with A_j+(U_i∩U_j). `exists_extraction` constructs a stable idempotent with this rank; the dimension upper bound establishes maximality. The simultaneous theorem supplies six independent actual subspaces and a complement splitting every designated side and signal space. `EdgeBlock.signature` verifies the physical source/target flags, not just a numerical edge label.

The price identity uses the actual F and Q conditional-rank entries. A user permutation ranges over all six directed edges and both orientations. The final cycle theorem takes an actual task decomposition under a linear coordinate equivalence; it does not assume profile additivity or resonant prices. It constructs independent cycle vectors and a task-splitting complement. Each list element n denotes R_(n+1); the actual number of blocks is `L.length`. `resonant_count_le_weight` correctly relates this to the weighted resonant price sum. This matches the source's inequality in `total-edge-bound`.

Verdict: complete for the source's supplied resonant decomposition, over every field. It does not independently prove the later classification theorem that produces all component families.

### 7. `prop:small-field-lcbc`, source lines 1796–1802

Endpoint: `scalar_at_operational_ceiling`.

Its only geometric assumption is Aᵢ≤Uᵢ; there is no F=ΣAᵢ hypothesis. K is the original finite field and card K≥3. The returned `ScalarBroadcastCode` has linear encoder and decoders. Its conclusion is exact attained-range cost equal to the integer n=ceil(broadcastOptimum A U). The proof uses both actual scalar achievability and the universal nonlinear converse to rule out padded unused coordinates lowering the actual cost below n.

Verdict: complete.

### 8. `prop:binary-lcbc`, source lines 1808–1815

Endpoint: `binary_at_operational_ceiling_permuted`.

The hypotheses are exactly card K=2, Aᵢ≤Uᵢ, ΣAᵢ=F, and separation after an arbitrary permutation p. This works for any presentation of a two-element field, not only a hard-coded ZMod 2 representation. The returned code is transported back to the original user labeling, and the operational optimum is invariant under this reindexing. Actual cost is again exactly its ceiling.

Verdict: complete, including the user-permutation clause.

### 9. `lem:optimal-residual-sides`, source lines 3124–3133

Endpoint: `OptimalRelaySeparation.optimal_block_residual_sides_ambient`.

The theorem quantifies over all L>0 and arbitrary P in the actual blocked ambient F^L. It assumes local generation, relay feasibility, pairwise disjoint side spaces, and exactly dim P=L·uploadOptimum. Pairwise disjointness is the established active-residual geometry, and the theorem is stronger by covering any task with that geometry. Its conclusion is genuine `iSupIndep` plus equality P=Σ(P∩Aᵢ^L), in the original ambient space.

The proof constructs a cheaper two-instance code on a blocked task if a tripod remains, flattens it to a 2L-instance code, and contradicts the operational infimum. It does not assume an unproved closed-form global upload theorem. No circular optimality certificate was found.

Verdict: complete.

### 10. `lem:integer-lcbc-allocation`, source lines 3537–3542

Endpoint: `integer_allocation_at_operational_optimum`.

`ScalarAllocation` stores natural-number common, pair, aligned, and individual quotas. Its fields include every source allocation constraint, together with equalities defining the individual residual quotas. The complementary pair convention is x=λ23, y=λ13, z=λ12 in one-based source labels. `commonRank`, `pairRank`, `pairSumRank`, and `enlargedRank` are the actual source conditional ranks. `length` includes twice the aligned quota.

The result fixes the common quota to r123 and gives exact integer length ceil(D*) where D* is the operational nonlinear optimum. The general binary LCBC operational identification is proved separately by actual extension restriction, so the assertion does not smuggle a numerical LP optimum into the definition of D*.

Verdict: complete.

### 11. `lem:column-reconciliation`, source lines 3579–3589

Endpoints: `homogeneous_column_coordination_invertible`, `homogeneous_column_search`.

`HomogeneousColumnGroups` says that updating a group either leaves a matrix unchanged or changes exactly one column by a homogeneous linear image. The source's fixed distinct-column condition implies this slice condition; the Lean theorem does not impose a stronger unsupported condition. Matrix sizes and group dimensions may vary. Separate invertible witnesses and card I≤card K are the actual assumptions.

The first theorem gives the common invertible assignment. The second supplies a deterministic finite search, proves that it returns something for a complete finite enumeration, and proves every returned assignment makes all matrices invertible. The source promises deterministic findability, not a specific complexity bound, so exhaustive enumeration is sufficient. Allowing zero-dimensional groups is harmless extra generality.

Verdict: complete, including deterministic findability.

### 12. `lem:binary-common-complement`, source lines 3662–3672

Endpoint: `maximum_disjoint_subspace`.

For an arbitrary field and finite-dimensional ambient T, the only hypothesis is T1∩(T2+T3)=0. The conclusion gives an actual subspace disjoint from each Ti and dimension dim T−max_i dim Ti. Natural-number subtraction is safe because each Ti is a subspace of T. No side-spanning or binary-only restriction is added, and the zero-dimensional cases are included.

Verdict: complete.

## Additional residual candidates

### `lem:active-empty-row`: semantic pass

`ResidualTaskAssembly.exists_demandData` derives lifted demand graphs from the actual quotient signal subspaces and canonical side identities. Consequently passing `DemandData` to downstream declarations is not an unproved normal-form oracle: it is constructible for every task of the required canonical side form.

For those actual graphs, `activeRows` is S+G(ker B), where S is the pure-row span. `exists_empty_cancellation` factors the projection of G outside this space through B, chooses an actual complement, and constructs a correction into that complement. `privateGaugeShear` changes each private summand by its owner's known tripod line; `privateGaugeShear_sides` proves all side spaces are preserved. `correctedTask_rows` proves every residual demand coordinate lies in the retained row space after this simultaneous shear. `rowRetraction` then removes the passive complement. `activeRowReduction_achievableAt_eq` proves equality of all fixed-block nonlinear budget regions, including actual range costs through the retraction machinery.

Finally, `activeRows_finrank` proves dim(activeRows)=dim S+rank((G mod S)|ker B), and `mixedRows_stacked_rank` gives the source stacked-rank formula. Since S≤activeRows by definition, this is precisely the source's dmix-dimensional retained lift outside the pure-row span. The complement removed from D is, equivalently, a lift of a complement of im G0 in D/S. The theorem bundle therefore includes the operational and dimensional content of the source lemma, rather than just a gauge-invariance primitive.

Recommended coverage declarations include `exists_demandData`, `DemandData.exists_empty_cancellation`, `privateGaugeShear_sides`, `DemandData.correctedTask_rows`, `DemandData.activeRowReduction_achievableAt_eq`, and `DemandData.activeRows_finrank`. A single bundled source-spelled theorem would improve usability but is not needed to resolve a substantive mathematical gap here.

### `lem:bridges`: geometry closed; exact conditioned endpoint still unexposed

The actual active reduced task now has constructed `DemandData.signalBridge` and `canonicalReductionBridge`. `activeRowReduction_tripod_bridge` and `SignalBridge.all_tripod_bridges` prove the whole tripod inclusion in all cyclic orientations. `ResidualPrivateSplit.fully_used_splits` removes the earlier need to assume private recovery for fully used canonical sides. The recovery maps in `SignalBridge` and the finite entropy machinery genuinely cover nonlinear codes and arbitrary blocklengths.

`ResidualConverse.explicit_residual_retained_bound` and `code_retained_rank_bound_ordered` publicly retain the two CMIs for isolated residual codes. In the jointly coded omniscience/residual setting, `GlobalUploadConverse.code_omniscience_entropy_bound` constructs the conditioned encoding, recovery, common-function, and bridge facts, while `lift_from_common` internally establishes all three retained inequalities before applying the omniscience lift. Its exported conclusion, however, only states the final global entropy lower bound.

The source lemma itself concludes the Ω-conditioned residual-three inequalities for arbitrary joint codes. That exact conclusion is not implied merely by the final sum-rate bound. To close the named coverage item, expose the conditioned common-function/recovery facts or, preferably, a theorem retaining Γ+Ji+Jj≤ΣH(Mℓ|Ω), parameterized by the actual canonical reduction and arbitrary positive-block finite code, with all cyclic pairs. This is mainly extraction/composition of existing checked proof material.

### `lem:zero-common-row-relay`: correct operational relay, incomplete source shape

`ZeroCommonRowNormalForm.exists_chart` proves usable row coordinates from only zero triple pure intersection; it does not assume the desired relay or an abstract row-normal-form certificate. `ResidualRelayAssembly.signal_graphs` reconstructs the actual signals. `exists_relay_of_zero_common` then gives a genuine K-subspace that is locally generated, feasible for those signals, and has rank dim P1+dim P2+dim P3+dim D. `exists_scalar_linear_upload` turns it into an actual original-field scalar code. This is substantive completion of the relay-existence/size problem.

The public endpoint does not preserve a named pure-row span B0, a named retained mixed lift W_empty, or their distinguished decomposition. The current general zero-common chart can combine those row coordinates. The source additionally promises a coordinate change fixing tripod and pair-known spaces and a relay exactly of the form private ⊕ P_row ⊕ (W_empty⊗v), with P_row⊆B0⊗E, dim P_row=dpure, and local row generators. A generic correct-total-rank relay does not state these extra structural clauses.

To close this named item at full source strength, keep the pure/mixed row split in the normal-form transport, expose the chosen private shear (with its fixed-subspace assertions), and state the relay sum/decomposition and pure-row rank in the theorem conclusion. The scalar cost equality can then be obtained by combining the constructed code with the residual converse. A later global upload-optimum theorem alone should not be used to erase the source's structural promises.
