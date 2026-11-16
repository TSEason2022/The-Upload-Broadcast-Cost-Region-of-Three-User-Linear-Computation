# Review of the two cited counterexample assertions

Both manuscript assertions below now have independently checked Lean proofs.
The entropy assertion uses a corrected F5 witness; this does not validate the
cited article's erroneous F3 equality. The initial finite diagnosis and the
subsequent formal verification are distinguished below.

The frozen manuscript separately asserts:

- Lines 434–436: subset entropies of the original observations need not determine the LCBC optimum.
- Lines 1804–1806: the field-size restriction in the general scalar LCBC result is necessary.

Primary references inspected on 2026-10-08:
[arXiv v3](https://arxiv.org/pdf/2206.10049v3), Examples 1, 2, 4 and Remark 6.1;
[journal-layout author PDF](https://escholarship.org/content/qt44b1c5hm/qt44b1c5hm.pdf), article pages 8–9, same examples and remark.

## Entropy assertion: the cited F3 example has a defect

Both primary versions give side observations A, B, C and demands B+C, A+C, A+tB over F3, comparing t=1 with t=2. The stated equality of all 63 nonempty subset entropies does not hold for this pair: the three demand coefficient vectors have ranks 3 and 2. At t=2, W3=W2−W1. Thus their joint demand entropies are 3L and 2L in ternary units.

This does not refute the frozen manuscript's existential assertion. Over F5, the same two coefficient configurations have identical ranks for all 64 subsets (including the empty set). The independent finite calculation also gives six first entries all equal to 1 in both configurations, and nine second entries all equal to 1 versus 3/2. The subsequent Lean proof now connects those facts to genuine Shannon entropies and actual operational task optima, as recorded below.

In the order (A,B,C,B+C,A+C,A+tB), both F5 configurations have:

- empty rank 0; singleton rank 1; every pair rank 2;
- rank 2 for exactly the triples {1,2,3}, {0,2,4}, {0,1,5}, with zero-based indices;
- rank 3 for all other subsets of size at least three.

At the initial diagnostic checkpoint, the F5 repair was an independently checked candidate without a Lean proof. The later verification below closes that proof obligation. It remains a corrected witness rather than a verbatim reproduction of the cited F3 example.

## Binary field-size necessity: exact Example 4

The cited task is over F2 on coordinates (A,B), with sides A, B, A+B and respective demands B, A+B, A. Its three signal spaces are the whole plane. Every pair of distinct source vectors agrees on one user's side information and differs on that user's demand. Every valid scalar broadcast is therefore injective on four source values, so its attained cost is at least two bits. Its fully informed operational optimum is one.

The two-instance broadcast printed in the source is (A1+A2+B2, A1+B1+B2). Exhaustive checking confirms all users recover both demands and all four broadcast values occur. The extension-field polynomial expansion later in the cited paragraph contains a different second coordinate; the literal displayed two-instance code above is independently valid. Formalization need not depend on that expansion.

## Reproducible finite evidence

Run `python3 verification/check_cited_counterexamples_20261008.py`.
The output is retained in `verification/cited-counterexamples-finite-check-20261008.json`.
This calculation is a diagnostic and source-correction aid. It does not by itself authorize marking either assertion formally complete. At the initial review both still needed actual Lean task, operational-optimum and entropy/alphabet statements.

## Subsequent Lean verification

At 11:26 UTC the binary necessity assertion is independently approved through
`CitedBinaryFieldNecessity.signal_from_demands`, `broadcastOptimum_eq_one`,
`broadcast_source_injective`, `scalar_broadcast_card`, `scalar_cost_ge_two`
and `scalar_cost_gt_ceiling`. The independent six-root audit exits 0 with
only `propext`, `Classical.choice`, and `Quot.sound`; see
`verification/final-binary-necessity-review-20261008.log` and the completed
binary section in `final-semantic-coverage-review-20261008.md`.
At 11:46 UTC the corrected F5 entropy witness is also independently approved
through `CitedEntropyCounterexample.corrected_entropy_counterexample` and its
source-model/entropy/operational supporting endpoints. The independent
13-root audit passes on the fresh rebuilt artifacts, with only the same
three standard axioms. See `verification/final-entropy-witness-review-after-rebuild-20261008.log`
and the entropy section in `final-semantic-coverage-review-20261008.md`.
