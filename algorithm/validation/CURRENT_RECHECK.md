# Local recheck, 15 November 2026

**Evidence level: computed, using exact finite-field arithmetic.** These results
check the supplied implementation and concrete generated codes. They do not
independently prove the universal rate-region theorem or establish a formal
connection between the Python program and the Lean development.

The runtime package is byte-identical to the supplied version 1.5.0. Its source
digest is `70a562a3b68b5814325b4ea9a77595ea521173b5e2b9cc68c85749de529e76cd`.
Documentation was adjusted for this repository's source-only layout.

## Reproduced checks

| Check | Result |
| --- | --- |
| Existing regression suite | 256 tests passed (10.505 seconds in this run) |
| Frozen benchmark set | 57 cases, three repetitions, 171/171 successful trials |
| Fields / source dimensions | GF(2), GF(3), GF(4), GF(5), GF(9); dimensions 3–30 |
| Budgets | 100,000 search states; 3 seconds cooperative; 15 seconds outer timeout |
| Certificate checks | Original-task binding, exact identities/ranks/costs, original field and expected blocklength |
| Independent checks | Every original source basis vector evaluated using separate polynomial field arithmetic |
| CLI / API examples | Eight commands passed: binary demo, verification and execution; integer and extension-field examples; Python quickstart |
| Distribution | Wheel built, installed with no dependencies into a new local environment, and imported with Python isolated mode outside the checkout |
| Installed-package examples | GF(2), R1: L=2; GF(2), R2: L=1; GF(4), R1: L=2; all certificates passed |

Python was 3.12.14 on macOS arm64. Timings depend on the host and concurrent
work; no speedup claim is inferred from this recheck. Numerical tolerance is
**not applicable**: field elements, ranks and costs are computed exactly.
There is no external numerical solver. Status was `success` for all 171 trials.

Compilation and the CLI examples are deterministic and use no random seed.
The benchmark consumes frozen JSON matrices; their generation seeds are
recorded per case in [the fixture manifest](../benchmarks/validation_fixtures/manifest.json).
The regression suite also contains explicitly seeded random checks, with each
seed retained in the corresponding test source. No global seed was substituted.

## Commands

Run from `algorithm/` with Python 3.12:

```sh
python -m unittest discover -s tests -v
python benchmarks/release_validation.py --repeats 3 --max-seconds 3 --max-states 100000 --hard-timeout 15 --label public-source-local-recheck --output validation/local_benchmark_results.json
python -m three_user_codes demo --q 2 --n 1 --output code.json
python -m three_user_codes verify code.json
python -m three_user_codes simulate code.json
python -m three_user_codes compile examples/integer_cycle_mix.json --output code.json
python -m three_user_codes simulate code.json
python -m three_user_codes compile examples/extension_field.json --output code.json
python -m three_user_codes simulate code.json
python examples/quickstart.py
```

The recorded benchmark is [recheck_20261115.json](recheck_20261115.json). It
contains the platform, source/validator/fixture digests, all limits, per-trial
statuses and detailed timings. The original handover results remain separately
in [RELEASE_VALIDATION.md](RELEASE_VALIDATION.md) and [benchmark_results.json](benchmark_results.json).
