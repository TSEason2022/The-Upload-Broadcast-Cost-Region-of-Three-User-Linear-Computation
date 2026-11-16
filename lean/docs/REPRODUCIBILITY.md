# Reproducibility and evidence

This guide describes the public Lean source checkout. Start with [QUICKSTART.md](QUICKSTART.md), then read [PUBLIC_RECHECK.md](PUBLIC_RECHECK.md) for the verification actually completed for the identified source snapshot.

## Reproduce from source

Use a fresh Git checkout with the official elan toolchain manager and Python 3.12 in a local environment:

```sh
cd lean
python3.12 -m venv .venv
. .venv/bin/activate
bash scripts/bootstrap.sh
bash scripts/check_public.sh
```

The initial bootstrap fetches dependencies at the revisions recorded in `lake-manifest.json` and obtains their official compiled cache. It verifies the pinned Lean and Lake executables. It does not intentionally advance dependency revisions. Keep `LEAN_PATH` and `LEAN_SRC_PATH` unset, and do not run `lake update` during reproduction.

To see individual steps after bootstrap:

```sh
. scripts/env.sh
python3 scripts/verify_toolchain.py
python3 scripts/verify_dependency_pins.py
python3 scripts/audit_source.py
python3 scripts/check_all_modules.py
bash scripts/check.sh
python3 scripts/generate_current_coverage_audit.py
lake env lean -DwarningAsError=true verification/CurrentSourceDeclarations.lean
```

`check_public.sh` runs this public verification sequence. A source publication should include the matching report and source identity, rather than treating these command examples as evidence that the commands passed.

## Separate verification questions

| Question | Evidence to inspect |
| --- | --- |
| Which compiler and dependencies were used? | `lean-toolchain`, `toolchain-lock.json`, `lake-manifest.json`, actual identity-check output |
| Did every library module compile? | All-module inventory, per-module exit statuses and build log |
| Which trusted axioms were reached? | Theorem-dependency and module-origin safe-declaration audits |
| Do listed mathematical declarations exist with their stated types? | Current coverage-declaration audit and elaborated signatures |
| How do formal declarations correspond to the current manuscript? | `coverage.json`, `current-source-coverage.json`, and their explicitly stated semantic-review boundaries |
| Which exact source files were distributed? | `PUBLIC_SOURCE_MANIFEST.json` and the repository commit |

The kernel checks declarations under their actual hypotheses. They do not automatically establish correspondence with informal prose, peer-review status, or correctness of a separate Python program. The algorithm's exact code certificates and regression tests are independent evidence; no Python-to-Lean refinement theorem is supplied.

The project audit permits only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. The source and environment audits reject the listed proof escapes. The compiler and imported dependency artifacts remain part of the operational trust boundary.

## Clean-build boundary

For an independent project build, use an empty checkout rather than copying project `.olean`, `.ilean`, native objects or `.lake/build` from a prior run. Reusing a dependency cache is allowed only when recorded as such; it does not mean every dependency was rebuilt from source.

The all-module runner compiles every library module, including modules outside the umbrella import closure, and extends both axiom audits to that full inventory. `check.sh` checks the umbrella import, reuse examples and coverage declarations. The final current-source audit separately resolves the declarations mapped during the current manuscript alignment.

A complete reproduction record should include:

- Git commit and per-file source identity;
- actual Lean and Lake versions and dependency revisions;
- platform and Python version;
- exact commands, exit codes, module inventory and audit output;
- whether dependency caches or project compiled outputs were reused;
- the source snapshot and scope of the semantic correspondence review.

Lean proof checking uses exact formal reasoning. Random seed, numerical solver, problem dimension and floating-point tolerance are not applicable; module and declaration counts should be recorded instead. Runtime measurements are host-dependent and do not establish mathematical claims.

Generated `.lake/`, `.verification-results/` and local logs must not be mistaken for source inputs. Reports that are intentionally retained in the public tree are identified as current or historical. Do not overwrite a historical report and retain its old identity as if it certified the new files.

## Source identities and historical records

`PUBLIC_SOURCE_MANIFEST.json` describes this public distribution. It has a public-subset scope and is distinct from the original full-payload `SOURCE_MANIFEST.json` and English-edition inventory. The original full-source verifier has different selection assumptions; passing the public manifest to that historical verifier is not the public verification procedure.

The retained October 2026 reports, signature logs and review notes describe their original frozen source. They provide historical context. Current correspondence and build results must identify the updated source and the actual new checks. A matching compiler build does not silently extend an old manuscript review to newly written prose.

The manuscript and raw source ledgers are deliberately withheld. Current public coverage metadata contains identifiers and authored scope descriptions, rather than a copy of the paper. It can state exactly which named and unnumbered mathematical conclusions were reviewed, including any alternative formal proof route or unchanged-snapshot boundary.

## Private-archive procedures

The original `check_complete.sh`, `clean_rebuild.py --require-complete`, source-inventory generation and `package_release.py` workflows were designed for the complete private archive and its source-selection rules. `check_complete.sh` explicitly refuses to run without the original raw ledgers. Other historical workflows can check metadata without performing a new manuscript-correspondence review; their metadata or full-paper flags do not by themselves certify this public subset. These procedures are not the public installation path and do not imply that the manuscript is distributed here.

Any private re-audit should retain the original manuscript bytes, detailed correspondence evidence and a matching source identity outside the public repository. Publish only the authorized source code, public coverage descriptions and appropriately scoped verification evidence.

## Attribution and licensing

The accompanying research is by Shuo Tan and Syed A. Jafar. Keep its attribution separate from the formalization's verification status. The project preparation does not select a new software license. See [RIGHTS.md](../RIGHTS.md) and [third-party notices](../third_party_notices/); dependency licenses apply only to their respective material.
