# Release validation

The final source passed **256 tests in 17.924 seconds**. All **57 frozen benchmark cases** completed successfully in all three repetitions: **171/171 independently checked trials**, with no budget stops or verification failures. This includes 44 established regression cases and 13 additional structural cases over GF(2), GF(3), GF(4), GF(5), and GF(9).

## Protocol and environment

Each trial ran in a fresh Python process with a 3-second cooperative compilation budget, 100,000 search-state limit, and 15-second outer process timeout. The compiler selected its minimum original-field blocklength. The same frozen inputs, options, repeat count, limits, and verifier were used for the reference and final implementation. Other project test, profiling, and document-build jobs were paused during the accepted benchmark runs.

The timer starts immediately before `compile_task`. It includes bound computation, algorithm selection, structural analysis, code construction, and the compiler's internal verification. It excludes interpreter startup, imports, input parsing and normalization, and additional verification after compilation. No bounds or compiler candidates were precomputed to warm the timed call. Reported case times are medians of three fresh-process compilations.

- Python: `3.12.14`.
- Platform: `Linux-6.18.44-x86_64-with-glibc2.39`.
- Runtime source SHA-256: `70a562a3b68b5814325b4ea9a77595ea521173b5e2b9cc68c85749de529e76cd`.
- Frozen fixture-set SHA-256: `ffe141c92ca7c9982adcc316b3d45bb9799262c7d1c42a1060845a599283a0ee`.
- The measured runtime source remained unchanged throughout the run.

The runtime digest covers the package's Python modules in filename order, including each filename and a null-byte separator before its contents. Raw trial records, stage timings, strategy names, and fingerprints are in [benchmark_results.json](benchmark_results.json). Input matrices and expected exact targets are shipped in `benchmarks/validation_fixtures`.

## Exact verification

Every successful trial passes native original-task-bound certificate verification. Native verification checks the algebraic identities, locality, ranks, and exact upload and broadcast costs. The harness also requires the frozen optimum targets, the original finite field, and the expected minimum blocklength.

A separate polynomial-arithmetic implementation evaluates every original source basis vector. It uses the production adapter's original-row encoder and decoder matrices, but does not use the package's finite-field arithmetic, matrix multiplication, rank, elimination, or lifting operations to evaluate decoding. These checks establish the end-to-end linear identities for those matrices, including extension-field inputs. They do not independently prove the universal optimum-rate theorem or replace tests of the optimized runtime execution plans.

## Structural cases resolved

The reference completed 49/57 cases in every repetition. Each of the following eight cases exhausted its 3-second budget in all three reference trials; every final trial now completes and verifies. These resource stops were never treated as infeasibility results or assigned artificial speedups.

| Structural input | Field order | Source dimension | Blocklength | Final median, ms |
|---|---:|---:|---:|---:|
| Dense R1 + R2 | 3 | 13 | 2 | 61.04 |
| Dense R2 + R1 + both cycle orientations | 3 | 19 | 2 | 104.63 |
| Dense R2 + R1 + pair omniscience | 9 | 16 | 2 | 93.23 |
| Dense three R1 components | 2 | 15 | 2 | 55.00 |
| Dense two R1 components + positive cycle | 2 | 13 | 2 | 43.01 |
| Two R1 + positive-cycle bundles | 3 | 16 | 1 | 32.88 |
| Dense two R1 components + tripod omniscience | 4 | 12 | 2 | 48.59 |
| Dense two R3 components | 3 | 22 | 1 | 105.30 |

For the **49 cases completed by both implementations in every repetition**, the geometric mean of the per-case median speedups is **1.202x**. There are no newly incomplete cases. Individual timings can regress: `dense_q5_n9_seed20261022` increased from 27.47 to 33.86 ms. All paired medians are retained in the JSON summary; these measurements do not imply uniform speedups or polynomial worst-case compilation.

## Reproduction

Run from the source-package root:

```sh
python -m unittest discover -s tests -v
python benchmarks/release_validation.py --repeats 3 --output validation/local_benchmark_results.json
```

The validation command exits unsuccessfully if any trial fails, stops on a resource limit, violates an exact target, or if the runtime source changes during measurement. `--suite adversarial` and `--suite regression` select the two frozen subsets. `--allow-budget-stops` is available for diagnostic collections; it does not relax certificate checks or convert a stopped search into success.

## Distribution checks

The wheel built offline and installed successfully into a fresh virtual environment with `--no-index --no-deps`. Isolated Python (`-I`) outside the checkout imported the installed 1.5.0 package; binary GF(2) cases at blocklengths 1 and 2 and an extension-field GF(4) case at blocklength 2 all passed compilation, certificate verification, and simulation. The quickstart also passed.

The standalone zipapp passed an isolated compile, verify, and simulate workflow outside the checkout for a GF(3) task containing repeated resonant components and a directed cycle. Its SHA-256 is `c8a92fe966b78547b9fc9acc6cd1953e63b75159fad76a0ae8cf661e2e46a2cc`. Distribution details are recorded in [distribution_checks.json](distribution_checks.json).
