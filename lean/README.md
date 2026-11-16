# Lean checks for three-user upload–broadcast computation

This directory contains the Lean 4 formalization accompanying the three-user linear computation results of Shuo Tan and Syed A. Jafar. The current source-alignment update includes **314 library modules**, a declaration map for **28 named results**, and **103 distinct mapped theorem targets**. Four explicit current-source interfaces were added in [CurrentSourceAlignment.lean](UploadBroadcast/CurrentSourceAlignment.lean).

The manuscript is not distributed here. Raw manuscript-derived LaTeX ledgers and original full-payload manifests have also been withheld. [PUBLIC_SOURCE_MANIFEST.json](PUBLIC_SOURCE_MANIFEST.json) identifies this public source subset; the passed current check and its exact boundaries are in [PUBLIC_RECHECK.md](docs/PUBLIC_RECHECK.md).

## Reproduce

From the repository root:

```sh
cd lean
bash scripts/bootstrap.sh
bash scripts/check_public.sh
```

Requirements: macOS or Linux, official [elan](https://github.com/leanprover/elan), Git, curl, tar, a C toolchain, Python 3.11 or later, and network access for pinned dependencies and the official mathlib cache. Initial setup downloads a substantial toolchain and proof-library cache. On macOS the pinned mathlib cache program runs through Lean's interpreter, avoiding a native executable compatibility issue on newer macOS releases.

The exact pins are Lean **4.19.0**, mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**, and PFR **859f6b23d5532de385cff18fc25381e715dba199**. `lake-manifest.json` records all transitive revisions. Bootstrap loads these revisions without `lake update`.

The public check verifies toolchain/dependency identity, rejects source proof escapes, compiles all 314 library modules (including two outside the umbrella import closure), audits theorem dependencies and all safe project declarations, runs the reuse examples, and resolves the 103 current-source theorem targets with their types and reachable axioms. It does not need the withheld manuscript files.

For just the all-library build and its two axiom audits:

```sh
source scripts/env.sh
python3 scripts/check_all_modules.py
```

## Formalization scope

The declaration map covers the operational upload–broadcast cost region, minimum upload, broadcast optimum, joint endpoints, scalar versus two-instance achievability, and minimum linear blocklength, with their finite-field, decomposition, allocation, and entropy support results. See [coverage.json](coverage.json), [current-source-coverage.json](current-source-coverage.json), the [module guide](docs/MODULE_GUIDE.md), and [reuse examples](docs/REUSING_THE_PROOFS.md).

The current alignment review compares the 28 named statements against the supplied manuscript identity. Twenty-one normalized statements are unchanged; seven text revisions have separate assumption and quantifier-order reviews. The new interfaces make the listed menu-vector witness, capacity-constrained relay selection, and nonlinear binary scalar obstruction explicit. Current checks establish the mapped formal conclusions; correspondence of an informal statement remains a separate review step.

Finite-alphabet Shannon entropy uses the pinned PFR library. Python enumeration and numerical examples are supplemental diagnostics. The original formalization includes documented alternative proof routes and a corrected finite-field witness for one cited entropy example; see the [historical semantic review](docs/final-semantic-coverage-review-20261008.md) and [counterexample review](docs/cited-counterexample-review-20261008.md).

## Verification boundary and historical evidence

The source audit rejects `sorry`, `admit`, custom axioms, `native_decide`, and selected unsafe proof escapes. Kernel-environment audits inspect both theorem dependencies and every safe project declaration by module origin. The only permitted standard axioms are **`propext`, `Classical.choice`, and `Quot.sound`**.

A successful Lean build proves the formal declarations from their explicit hypotheses. It does not establish that every sentence, unnumbered calculation, or changed proof exposition in a manuscript is equivalent to those declarations. The compiler and imported compiled dependency caches remain part of the operational trust boundary. No independent peer review or kernel rebuild of upstream dependencies is asserted.

The current manuscript identity is SHA-256 `420218e9eb1b3c721a4270c39f505a057ad23b62a866ead698761bac476efdd5` (the supplied manuscript snapshot used for mathematical alignment; subsequent private edits update introduction wording and citations/bibliography, acknowledgment availability wording/URL, URL-package support and author biographies without changing mathematical statements, proofs or verified code). Current named-claim source correspondence is documented separately from the kernel build.

Files in `verification-results/`, `verification/`, and `logs/` include preserved historical campaign and focused-check records. The original clean report concerns project-source SHA-256 `6e7af788509fbf182f2830754a8d611c088140f273af1d8a7b16b031ff83a8cd` and manuscript SHA-256 `b1c77e1cf7f7245fc8781b362d69ca06ba9b42448bc6d90ad65ddf628d4b2682`. The old coverage map is preserved as [historical-coverage-20261008.json](verification-results/historical-coverage-20261008.json). Those records are not a current-source certificate.

Historical technical notes may refer to withheld raw ledgers or original full-source manifests. The original edition verifier is omitted because its complete-inventory assumptions do not hold here. `check_complete.sh`, original full-manuscript packaging, and manuscript-inventory regeneration require the complete private historical archive; use `check_public.sh` for this repository.

## Rights

No general reuse license has been granted for new project material. See [RIGHTS.md](RIGHTS.md). Third-party dependencies retain their own upstream licenses and attribution in [third_party_notices/](third_party_notices/).
