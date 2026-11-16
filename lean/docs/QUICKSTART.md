# Reproduction quick start

This guide applies to the public GitHub checkout. The manuscript and raw manuscript ledgers are maintained separately. For the actual verification outcome and source identities, read [the current report](PUBLIC_RECHECK.md) and [the current statement mapping](../current-source-coverage.json).

## Set up a fresh checkout

Requirements: macOS or Linux, Git, curl, tar, a C toolchain, the official [elan toolchain manager](https://github.com/leanprover/elan), Python 3.11 or later, and network access. Python 3.12 is recommended. The initial setup downloads the pinned Lean toolchain and a substantial dependency cache.

```sh
git clone https://github.com/TSEason2022/The-Upload-Broadcast-Cost-Region-of-Three-User-Linear-Computation.git
cd The-Upload-Broadcast-Cost-Region-of-Three-User-Linear-Computation/lean
python3.12 -m venv .venv
. .venv/bin/activate
bash scripts/bootstrap.sh
bash scripts/check_public.sh
```

Use an empty project checkout for independent reproduction. Dependency caches may be reused; do not copy this project's compiled `.olean` files from another build. Do not run `lake update`, which would change the pinned dependency selection. Do not set `LEAN_PATH` or `LEAN_SRC_PATH`, which can override normal import resolution.

## What the public check does

`scripts/check_public.sh` verifies the actual toolchain and locked dependency revisions, scans project source for prohibited proof escapes, compiles every library module, runs theorem and safe-declaration axiom audits, checks public reuse examples, and resolves the declarations listed for the current manuscript alignment.

The allowed standard axioms are `propext`, `Classical.choice`, and `Quot.sound`. A passing kernel check verifies formal declarations under their actual hypotheses. Correspondence with an informal manuscript is a separate review recorded in [coverage.json](../coverage.json) and [current-source-coverage.json](../current-source-coverage.json). No formal refinement proof connecting the Python algorithm to the Lean implementation is claimed.

The pins are recorded in `lean-toolchain`, `lake-manifest.json`, and `toolchain-lock.json`. See [TOOLCHAIN.md](../TOOLCHAIN.md) for dependency provenance and [REPRODUCIBILITY.md](REPRODUCIBILITY.md) for evidence interpretation.

## Results and generated files

Read `docs/PUBLIC_RECHECK.md` for the checks actually completed for this release. Running a command successfully is distinct from configuring a command that has not yet been run. Build outputs are generated under `.lake/`; the verification runners also generate `logs/` and `.verification-results/`. Keep newly generated local outputs out of a source publication.

Record the Git commit, compiler version, dependency revisions, source digests, executed commands, exit statuses and resulting reports for a reproduction. Random seeds, numerical solver tolerances and floating-point errors are not applicable to Lean kernel checks.

## Historical and private procedures

The October 2026 reports and technical notes retain their original snapshot scope. They do not certify a later source tree. The original English-edition manifests, full-payload verifier, manuscript ledgers and attachment checksums are not part of this public checkout.

Historical `check_complete.sh`, `clean_rebuild.py --require-complete`, and `package_release.py` procedures concern the complete private archive and its source-ledger gates. They are not the public quick start. Do not substitute their original full-payload identity for the public source manifest or describe their historical reports as a new build.

## Citation and rights

The accompanying research is *The Upload–Broadcast Cost Region of Three-User Linear Computation*, by Shuo Tan and Syed A. Jafar. Cite the research and record the formalization's Git commit and matching report when using the results. See [RIGHTS.md](../RIGHTS.md) and retained dependency notices; public visibility does not itself grant a general reuse license for new project material.
