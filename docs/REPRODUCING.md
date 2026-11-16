# Reproducing the results

Run the commands below in a fresh checkout. Keep generated code certificates, environments, proof caches and build logs outside version control.

## Algorithm

Python 3.12 is recommended; Python 3.10 or newer is supported. The runtime has no third-party dependencies.

```sh
cd algorithm
python3.12 -m venv .venv
. .venv/bin/activate
python -m pip install .
python -m unittest discover -s tests -v
python benchmarks/release_validation.py --repeats 3 --max-seconds 3 --max-states 100000 --hard-timeout 15 --label reproduction --output validation/local_benchmark_results.json
python examples/quickstart.py
```

The [current recheck](../algorithm/validation/CURRENT_RECHECK.md) records the actual environment, seeds, limits, source identities and successful commands. The archived benchmark uses fixed JSON inputs and exact finite-field arithmetic; no numerical solver or floating-point tolerance is involved. Runtime measurements vary with the machine.

## Lean

Install the official elan toolchain manager if it is not already available. The project specifies its Lean version in `lean-toolchain` and dependency revisions in `lake-manifest.json`. Initial setup requires network access and a substantial proof-library cache.

```sh
cd lean
bash scripts/bootstrap.sh
bash scripts/check_public.sh
```

Use the [Lean guide](../lean/README.md), [toolchain notes](../lean/TOOLCHAIN.md), and [current verification report](../lean/docs/PUBLIC_RECHECK.md) for platform details, checked commands and actual results. The public checks do not require the manuscript. Historical full-manuscript packaging scripts may require private source ledgers that are deliberately absent from this repository.

## Interpreting evidence

| Label | Meaning |
| --- | --- |
| Proven in the research | A mathematical statement attributed to the accompanying research and its hypotheses |
| Certified by Lean | Formal declarations passed the kernel and the stated trust-boundary audits for an identified source snapshot |
| Computed | A reproducible execution, finite-field identity check, regression result or benchmark result |
| Suggested | A possible extension or future direction, without a proof or certification claim |

A green implementation test is not a universal theorem. A successful Lean build alone is not a semantic review of a manuscript. Read the source identities and scope in the corresponding reports.
