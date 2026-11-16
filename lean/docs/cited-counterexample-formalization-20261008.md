# Cited counterexamples: corrected witness and exact field-size witness

The uploaded manuscript is frozen and has not been edited.

## Entropy vector insufficiency (source lines 434–436)

The cited article's F3 pair is not a valid entropy-vector witness: its three
demands have joint ranks 3 and 2. The following construction is therefore a
**corrected F5 witness**, not a verification of the erroneous F3 equality.

Let A, B, C be independent uniform elements of F5. The six original observations
are (A, B, C, B+C, A+C, A+tB), comparing t=1 and t=2. The first three are the side
observations, and the last three are their respective demands.

`CitedEntropyCounterexample.lean` constructs these exact linear maps and actual
coefficient-space tasks. Subsets are indexed by arbitrary Boolean selections of
the original six scalar variables. Unselected coordinates are constant zero.
The finite certificate counts the zero kernel on all 125 source points, for all
64 selections. Equality of these actual finite kernel cardinalities implies
equal kernel dimensions; rank-nullity gives equal actual observation ranks.
`LinearEntropy.linear_entropy` then identifies the genuine Shannon entropies
under `uniformOn Set.univ`. Its block theorem gives the same equality at every
original blocklength L.

The fifteen-entry profile is separately derived from finite coefficient-space
carrier cardinalities. `FiniteSubspaceCertificate.Space.submodule` provides the
actual submodule, its join/meet bridges are proved, and `Space.finrank_eq` derives
its dimension from the finite-field cardinality theorem. No rank-equality oracle
is assumed. The general operational optimum theorem then applies to all
nonlinear finite-alphabet zero-error codes, not only scalar linear codes.

The checked endpoint is D*=1 at t=1 and D*=3/2 at t=2, despite equality of every
original-variable subset entropy. The conjunction is
`corrected_entropy_counterexample`; the explicit insufficiency statement is
`equal_subset_entropies_distinct_operational_optima`.

The finite computations are isolated in `CitedEntropyKernelCertificate.lean`
and `CitedEntropyCertificates.lean`. The former checks all subset kernels; the
latter checks the coefficient-space cardinalities needed by the operational
profile. `CitedEntropyShannon.lean`, `CitedEntropyProfile.lean`, and
`CitedEntropyModel.lean` give the Shannon, operational, and literal-source
bridges, respectively. In particular, the scalar coordinate source is proved
bijective onto the actual `Source K V 1`; it carries uniform coordinate input
to the actual uniform model source; and the exact side/demand observations are
proved to be the printed formulas.

`scripts/AuditCitedEntropyCounterexample.lean` checks the reachable axiom set
against exactly `propext`, `Classical.choice`, and `Quot.sound`; it rejects every
other axiom. The final dependency-aware build and audit logs are under
`logs/cited-entropy-clean-lake-build.log` and
`logs/cited-entropy-final-axioms.log`.

## Binary scalar ceiling necessity (source lines 1804–1806)

The exact cited Example 4 has source (A,B) over F2, sides A,B,A+B, and respective
demands B,A+B,A. Every signal space is the plane. Its fully informed block
optimum is 1, while any scalar zero-error broadcast is injective on all four
source values and therefore has cost at least 2. This is the required failure
of scalar achievability at ceil(D*)=1.

The distinct five-bit resonant example in `BinaryOperationalTightness.lean`
proves a factor-two blocklength obstruction at D*=3/2, but does not prove this
particular scalar-ceiling assertion. The exact plane witness is proved
separately in `CitedBinaryFieldNecessity.lean`.

## Primary sources and independent finite evidence

- [arXiv v3](https://arxiv.org/pdf/2206.10049v3), Examples 1, 2, 4 and Remark 6.1
- [Journal-layout author PDF](https://escholarship.org/content/qt44b1c5hm/qt44b1c5hm.pdf), pages 8–9
- `docs/cited-counterexample-review-20261008.md`
- `verification/check_cited_counterexamples_20261008.py`
- `verification/cited-counterexamples-finite-check-20261008.json`

The Python enumeration is independent diagnostic evidence only. Lean certificates
use kernel-checked `decide +kernel`, which does not invoke native computation or
`Lean.ofReduceBool`.

## Frozen-source ledger note

- Manuscript: `source/TIT_LCBC_optimized.tex`
- SHA-256: `b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`
- Lines 434–436 are justified by a corrected, formally proved F5 existential
  witness; the incorrect F3 assertion in the cited article is not promoted.
- Lines 1804–1806 are justified by the exact F2 plane example, with actual
  optimum 1 and nonlinear scalar cost at least 2, as proved by the separate
  field-size-necessity module.
- No change was made to the manuscript or to the cited publications.
