# Current-source verification

**Certified:** the current public Lean library passed a fresh build of all 314 modules, both full-library axiom audits, integrated reuse/coverage checks, and the 103 mapped theorem signatures and axiom dependencies. Exact formal inputs were unchanged throughout verification.

The source identity is `7ee8f58643fcad782e99373da67c0e7e06a571cbfea506725b3ab827b19ae486`. See [the report](../verification-current/report.json), [per-file formal inputs](../verification-current/formal-input-manifest.json), [module inventory](../verification-current/module-inventory.json), and [module results](../verification-current/module-build-timings.json).

## Results actually obtained

| Check | Observed result |
|---|---|
| Lean/Lake identity | Lean 4.19.0, commit `6caaee842e9495688c1567e78c0e68dbb96942aa`; Lake 5.0.0 |
| Dependency source identity | All 11 locked revisions matched and tracked sources were clean, before and after the run |
| Source lexical gate | Passed 416 scanned Lean files |
| Existing verification-tool regression tests | 28 passed |
| Complete library | 314/314 compiled, including two outside the umbrella import closure |
| Namespaced theorem axiom audit | 7987 theorem roots passed |
| Module-origin safe-declaration audit | 11023 safe declarations, including 8403 theorems and 504 private/out-of-namespace declarations, passed |
| Complete reachable axiom union | Exactly `propext`, `Quot.sound`, `Classical.choice` |
| Integrated build, reusable examples and mapped declarations | Passed |
| Current-source declaration audit | All 103 distinct theorem targets resolved with printed types and approved axiom dependencies |
| Four new current-source interfaces | Targeted elaboration and full library compilation passed |
| Frozen formal inputs | Byte-identical before/after; exact manifest supplied |

The run used native arm64 Lean on Darwin 25.3.0 and Python 3.12.14. The main library compiler used two Lean threads and built one new project module at a time. A separate read-only elaboration of the four new interfaces used at most one additional two-thread process. No project `.olean` files were imported from an older campaign. Official mathlib compiled caches and exact dependency sources were reused; the PFR entropy dependency was compiled locally during this preparation. Runtime measurements are host-dependent. Random seeds, numerical solver status, instance dimension and floating-point tolerance are not applicable to these exact kernel/source checks.

## Reproduce from the public checkout

```sh
cd lean
bash scripts/bootstrap.sh
bash scripts/check_public.sh
```

The check needs no manuscript files or withheld raw LaTeX ledgers. It verifies toolchain/dependency identity, audits source proof escapes, compiles the complete library, runs both axiom audits, checks reusable examples, and resolves the current theorem map. On macOS, the same pinned cache downloader runs through Lean's interpreter to avoid a native cache-executable loader compatibility issue.

## Source correspondence

The supplied manuscript snapshot used for mathematical alignment has SHA-256 `420218e9eb1b3c721a4270c39f505a057ad23b62a866ead698761bac476efdd5`. Subsequent private edits update introduction wording and citations/bibliography, acknowledgment availability wording/URL, URL-package support and author biographies without changing mathematical statements, proofs, equations, tables, notation or verified code. The final local manuscript hash is `26c429ce52b8cd6e09c48e77cbff1d205c0663be86fd2d71cbb778a6e5808f2e`; the paper itself remains outside this repository.

The 28 named results were reviewed against the current source: 21 normalized statements are unchanged and seven textual revisions received assumption/quantifier reviews. The private deterministic comparison also checked 125 displayed mathematical items, five table data sets and 32 proof blocks; documented alternative formal proof routes and the limit on free-prose comparison are recorded in [current-source-coverage.json](../current-source-coverage.json).

Kernel checking proves the formal declarations under their actual hypotheses. The correspondence review is a separate step; this release does not claim word-for-word formalization of every exposition sentence, independent peer review, a rebuild of all upstream dependencies, or a Python-to-Lean refinement theorem. The compiler and imported dependency objects remain in the operational trust boundary.

Historical reports retain their original frozen-source scope. The original full-manuscript procedures and full-payload identities are not substitutes for this current public report.
