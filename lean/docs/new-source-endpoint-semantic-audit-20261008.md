# Independent audit of the new source endpoints, 2026-10-08

## Verdict and scope

Frozen manuscript: `../source/TIT_LCBC_optimized.tex`, SHA-256
`b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`.

The following three named source claims pass this independent semantic review:

- `thm:upload` (lines 707–720): minimum upload for every original feasible task,
  including arbitrary nonlinear converse and original-field one/two-instance attainment.
- `lem:bridges` (lines 996–1011): all signal-intersection bridges and the three
  retained Ω-conditioned residual inequalities for arbitrary joint codes.
- `lem:zero-common-row-relay` (lines 2146–2159): the precise pure/retained-row
  relay decomposition, fixed coordinate subspaces, and scalar residual attainment.

These three claims are promoted to `reviewed_complete` in `coverage.json`.
This supplements `semantic-audit-20261008.md`: its two residual endpoint gaps
were real at the time of that review and are now closed by the declarations
below. The previously reviewed claims are not re-audited here. The ledger now
has 16 of 28 named claims complete; this is **not full-paper verification**.
The optimal simultaneous upload/broadcast corner, exact minimum corner
blocklength, other remaining named claims, and unnumbered/external-dependency
review are outside this promotion.

## Independent mechanical evidence

The focused Lake build imports `OriginalUploadTheorem` and
`ResidualRowPaperEndpoint` (which also imports `ConditionedResidualBridges`).
The verification file `verification/NewSourceEndpointSemanticAudit20261008.lean`
prints actual elaborated signatures and reachable axioms for 25 endpoint and
transport roots, then independently checks the union of their reachable axioms.
The permitted axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`.

Evidence:

- `logs/new-source-endpoint-semantic-audit-build-20261008.log`
- `logs/new-source-endpoint-semantic-audit-signatures-20261008.log`
- `verification/new-source-endpoint-semantic-audit-snapshot-20261008.json`
- `logs/new-source-endpoint-semantic-audit-source-20261008.log`
- `logs/new-source-endpoint-coverage-status-20261008.log`

The snapshot records the frozen source hash and hashes of all 109 project
modules in the two endpoints' import closure. None was missing a compiled
`.olean` or newer than its `.olean` at inspection. The focused build and final
signature/axiom run pass without errors or warnings. These checks do not
replace the final integrated repository build after concurrent work finishes.
The lexical source audit passes across 221 Lean files. The full-coverage gate
continues to fail as intended, reporting 12 of 28 named claims still open.
No mathematical proof module or umbrella import was changed by this audit.

## 1. `thm:upload`: unconditional original-task minimum

Primary endpoints:

- `UploadBroadcast.Task.minimum_upload_source_formula`
- `UploadBroadcast.Task.minimum_upload_attainment`
- `UploadBroadcast.Task.minimum_upload_scalar_of_integral`
- `UploadBroadcast.Task.minimum_upload_two_instance`
- `UploadBroadcast.Task.minimum_upload_closed_lower`

### Hypotheses and operational meaning

The expanded formula's only mathematical input is `T : Task K F`, over a finite
field K and finite-dimensional K-space F. `Task` contains the original
conditions Aᵢ≤Uᵢ and Uᵢ≤ΣⱼAⱼ. The theorem does not require a canonical chart,
a decomposition certificate, an optimum value, an achieving code, or an
entropy lower bound as an input. Even side spanning is constructed by
normalization rather than assumed.

`uploadOptimum` is the infimum of upload budgets over the closure of the union
of all positive-blocklength operational regions. General `Code` encoders,
broadcasts, and decoders are ordinary functions. The converse therefore covers
nonlinear codes, including uploads coupling the eventual summands. Costs are
logarithms of attained alphabets, not postulated entropy or vector length.
`GlobalUploadOptimal.uploadOptimum_eq_of_omniscience_code` applies the proved
joint-code converse to every positive blocklength; `upload_lower_on_region`
extends it to closure. The supplied two-instance code makes the operational
set nonempty. No infimum over an empty set or target-as-hypothesis shortcut is
used.

### Source rank expression

The formal ranks have the manuscript's meaning:

- `intrinsicActivePairRank i` is dim(Uᵢ∩Aⱼ∩Aₖ)−dim(A₁∩A₂∩A₃).
  `intrinsicActivePairRank_quotient` and `preResidual_pairKnown_finrank` identify
  it with the retained pair factor after the common-side quotient,
  normalization, and passive-pair deletion.
- `privateDimension` sums the dimensions of the private projections of the
  two actual remote signals, matching equation `rho`.
- `commonDimension` is the dimension of the actual threefold pure-demand
  intersection after private trimming.
- `tripodDimension_eq_pure_mixed` gives dim(S/C)+rank(G|ker B), with S the pure
  span and G projected modulo S. `incidence` has exactly the source signs
  (ξ₂₁+ξ₃₁, ξ₁₂+ξ₃₂, ξ₁₃−ξ₂₃), and `relationRows` sums the three graph lifts.
  `tripodDimension_eq_stacked_rank` proves the stated [B;G]−B identity.
  Containment C≤S justifies the natural-number dimension subtraction.
- `finalRows_finrank` identifies this pre-common-split source expression with
  the dimension of the actual final residual row space. The formula is not
  silently evaluated on unrelated auxiliary ranks.

`uploadOmniscienceValue_eq` is precisely max{maxᵢ(dcom+dpairᵢ),
Σᵢ(dcom+dpairᵢ)/2}. These are constructed source coordinates; this review does
not promote a separate claim that every individual parameter is invariant
under every possible coordinate choice.

### Original-task conversion and attainment

`pairCanonicalRetraction` constructs the complete original-task conversion:
normalization, common-side quotient, simultaneous active-pair correction,
passive-pair removal, pair-factor separation, and private/tripod chart.
`splitActiveRetraction` then trims private directions, separates common rows,
and removes passive tripod rows inside the full product task.
`OriginalUpload.reduction` additionally identifies the pair/common factor
with the actual canonical omniscience task. These are concrete coefficient,
side, signal, and locally recoverable-remainder maps; they are not an assumed
substitution of an isolated cost-region equality inside a product.

`restoreLinear` restores an actual `T.LinearCode L r b`, keeping exactly K and L.
The resulting attainable-alphabet upload cost is squeezed between the
constructed upper bound and the independently proved operational lower bound,
so the final conclusion is equality. Nominal upload length is also exactly
L times the formula. No field extension or hidden larger blocklength occurs.
The combined endpoint chooses L=1 in the integral-Ω branch and L=2 otherwise;
`minimum_upload_scalar_of_integral` uses ordinary integer integrality. This is
an upload-only theorem and makes no assertion of optimal broadcast at that
same code.

Verdict: complete at the named source theorem's strength.

## 2. `lem:bridges`: original Ω-conditioned retained terms

Primary endpoints:

- `UploadBroadcast.ConditionedResidualBridges.canonicalReduction_all_tripod_bridges`
- `UploadBroadcast.ConditionedResidualBridges.canonicalReduction_conditioned_retained_bounds`

The geometry theorem states the whole active tripod's inclusion in
U₃+(U₁∩U₂), and both cyclic inclusions. `canonicalResidualGeometry` constructs
actual common intersections, private projections, pairwise independence
geometry, and tripod recovery from the canonical reduction. Full private use
and `fully_used_splits` establish the slice inverses; they are not assumptions
at the public canonical endpoint.

The entropy theorem takes an arbitrary code on Ω⊕residual. An encoder can
jointly depend on its omniscience and residual observations; there is no
factorwise encoding assumption. The only omniscience condition is that each
user demands the entire omniscience factor, exactly as in `ck-space`.
The source is uniform over all original-field source blocks. Arbitrary finite
message types admit the displayed discrete measurable instances; these
instances do not restrict their encoders. The result holds for every natural
blocklength, hence in particular every positive one.

Its Jᵢ is the actual conditional mutual information I(Mⱼ;Mₖ | Wᵢ,res,Ω),
normalized by log(card K). The right side retains Σ H(Mℓ|Ω) in the same q-ary
units, and Γ is L times the actual retained private-plus-tripod dimension.
The proven row-rank identities identify that dimension with the source
residual parameter after common rows have been separated. All i≠j are
quantified, so all three unordered J pairs are present.

Inside `code_entropy_bounds`, the actual common functions are observations of
the signal intersections. Their two recoveries and the remaining tripod
recovery are derived from the zero-error decoder and the geometric bridge.
`conditioned_retained_from_common` converts conditioning on (Mᵢ,Tᵢ,Ω) to
(Wᵢ,res,Ω) using the proved two-way determination. Thus this endpoint closes the
previously identified gap; a final global sum-rate lower bound is no longer
being substituted for the source's stronger retained inequalities.

Verdict: complete in the manuscript's finite-field, finite-alphabet model.

## 3. `lem:zero-common-row-relay`: exact row shape

Primary endpoints:

- `UploadBroadcast.ResidualRowShape.exists_exact_row_completion`
- `UploadBroadcast.ResidualRowShape.row_completion_paper`
- `UploadBroadcast.ResidualRowShape.canonicalReduction_scalar_upload_exact`

The first two accept the actual canonical side identities, zero common pure
intersection, and any prescribed complement W of the pure span S. Those are
exactly the noncommon residual circumstances after the paper's reductions;
`finalResidual_zero_common` supplies the zero-common condition for the
constructed final residual. An arbitrary prescribed retained lift W is
preserved, rather than replaced with an unspecified subspace of equal rank.

The conclusion constructs one invertible shear f and gives, simultaneously:

- f preserves each side-information subspace and fixes the entire tripod
  pointwise;
- the transformed original signals are feasible with
  Q=privateSpace⊕Prow⊕embedV(W);
- Prow lies in S×S with no private coefficients, has dimension dim S, and is
  locally generated;
- an explicit basis of Prow consists of individually owned local rows;
- Prow is disjoint from embedV(W), and their sum is disjoint from privateSpace;
- Q is locally generated and has rank dpriv+dim S+dim W;
- the same f, extended by identity on an arbitrary coefficient factor E,
  fixes tripod and E pointwise, hence also every pairwise-known subspace of E.

`embedV(w)` is exactly the coefficient vector w⊗v. The row chart is constructed
inside S, with W transported identically into the retained v-upload. Thus the
source's distinguished pure and mixed row subspaces are not lost in a generic
normal-form equivalence. The zero-common chart itself is proved from the three
pure subspaces, not supplied as a relay-existence certificate.

`row_completion_paper` pulls this precise Q back through f and constructs a
scalar original-field code on the pre-shear task. Its code statement is an
upper bound, as it must be for a possibly untrimmed general task.
`canonicalReduction_scalar_upload_exact` supplies equality of actual upload
cost for the constructed active, fully used residual; its matching lower
bound is the nonlinear residual converse with all geometry constructed.
Together with the rank identities and reduction transports, this is exactly
the source's dpriv+dpure+dmix one-instance residual cost, including the promised
relay shape. It is not a claim that arbitrary untrimmed zero-common tasks have
that dimension as their optimum.

Verdict: complete at the named source lemma's strength.
