# Reproducible proof toolchain

This project pins Lean `leanprover/lean4:v4.19.0` (release compiler commit `6caaee842e94`) and mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` (v4.19.0). The committed `lake-manifest.json` pins all transitive source dependencies. PFR is pinned to `859f6b23d5532de385cff18fc25381e715dba199`; LeanAPAP is pinned to `61769c82c1a8e2efd65da4490925180c54a611a7`.

On Linux x86_64 with curl, git, tar, a C toolchain and Python 3.11 or newer:

```sh
bash scripts/bootstrap.sh
bash scripts/check.sh
```

On other platforms install official elan from https://github.com/leanprover/elan first, then use the same commands. Bootstrap installs elan 4.2.4 only if no elan is available. Lean's released toolchain is always selected by `lean-toolchain`. Dependencies come from the repositories in `lakefile.toml` and the lockfile. Mathlib's official compiled cache is used to avoid recompiling thousands of dependencies. It introduces no extra logical axiom, but cached `.olean` files and their provenance remain in the operational trust boundary: imported compiled declarations are not re-kernel-checked by the normal build.

`source scripts/env.sh` activates a project-local installation on the cloud executor. When the exact pinned toolchain is already installed, it puts that toolchain's own binaries before the elan shims, avoiding needless shim/network resolution. It puts mathlib's download cache in `.tooling/cache/mathlib`, which is safe when the executor's home directory is read-only.

`Smoke.lean` proves a polynomial identity over the reals and explicitly runs `#print axioms toolchain_smoke`. It is exclusively a toolchain test, not a paper theorem.

`python3 scripts/audit_source.py` rejects proof placeholders, declared axioms and selected proof escapes in project sources after stripping comments and strings. This conservative lexical gate is not a security boundary against malicious metaprogramming. `scripts/AuditAxioms.lean` imports the project, enumerates its namespaced theorems, and uses Lean's kernel-environment dependency traversal to permit only `propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx`, custom axioms and any other axiom dependency. It also refuses an empty theorem collection. Standard classical axioms must not be represented as absence of all axioms.

`check.sh` builds the configured umbrella library, runs the smoke test and both audits, and rejects warning diagnostics in the build/audit output. Logs are written under `logs/`. The CI workflow runs these commands on Ubuntu; this distribution includes the workflow but makes no claim that hosted CI has run.

A successful kernel check proves the Lean statement from its explicit hypotheses. It does not establish that the statement is equivalent to an informal manuscript claim, that assumptions capture the operational problem, or that every manuscript proof has been translated. Consult the manuscript-to-Lean coverage report separately.

## Rights and dependency notices

No license is granted here for the manuscript or user-owned project sources. Their publication and licensing remain the author's choice. Third-party dependencies retain their respective licenses; copies of available notices are in `third_party_notices/`. PFR and mathlib are Apache-2.0 licensed. The lockfile and bootstrap scripts fetch the original upstream packages with their original notices. Do not infer that dependency licensing applies to the manuscript.

Bootstrap uses `scripts/cache-current-imports.py` to collect direct mathlib imports from project sources and recursively from PFR or other non-mathlib source imports. Mathlib's official `lake exe cache get` then fetches their transitive closure. This avoids downloading unrelated mathlib modules. If imports are added during development, source `scripts/env.sh` and rerun the script. To fetch the entire official mathlib cache instead, use `lake exe cache get` without arguments.

A separate `dependency-sources.tar.gz` may accompany this repository: it contains upstream source trees and licenses only, without git history, compiler or compiled artifacts. It is a source reference bundle, not a verified offline installation. `scripts/bundle-dependency-sources.sh` recreates it deterministically from exact Git-tracked upstream trees after dependencies have been fetched. It embeds a revision, license, and per-file checksum manifest. An upstream-tracked empty fake shared-library fixture is retained; installed binaries and generated build outputs are excluded.

## Clean source and all-module verification

Run `source scripts/env.sh` and `python3 scripts/check_all_modules.py` to build
every `UploadBroadcast/*.lean` source, even when the umbrella does not import
it. This is stronger than assuming that the default target reaches all source
files. The generated all-module axiom audit has the same three-axiom whitelist.

`python3 scripts/clean_rebuild.py ../independent-check --dependency-cache
.lake/packages --require-complete` creates a new source-only project snapshot,
copies only dependency caches, and runs the all-module, integrated, and full
coverage gates. The destination must not already exist. Omit the dependency-cache
option for fresh network setup. Its `.verification-results/report.json` records
cache use, platform, commands, runtimes, and the exact project source identity.
This is not a claim that all dependencies or the compiler were rebuilt from source.

Bootstrap loads the locked workspace without invoking `lake update`, then
`verify_dependency_pins.py` checks every actual dependency HEAD and tracked-source
cleanliness against the lockfile. Updating dependencies is a separate development
operation that invalidates prior release evidence.

`toolchain-lock.json` also pins the full Lean compiler Git hash and Lake version.
`scripts/verify_toolchain.py` checks the actual executables, records their hashes,
and refuses ambient `LEAN_PATH` or `LEAN_SRC_PATH` overrides that could shadow
the locked imports. These variables should be unset in the invoking shell;
Lake sets its own dependency search path for its child Lean processes. The
clean release report includes this gate before compilation.

A second gate, `scripts/AuditAllDeclarations.lean`, selects declarations by
originating project module and audits every safe declaration, including private
names, out-of-namespace declarations, and proof-valued definitions. Generated
unsafe compiler implementation helpers are inventoried separately. Both audits
run from the integrated check and from the generated all-module environment.
`check_complete.sh` now requires this all-module pass before full coverage.

See [the kernel trust-boundary review](docs/kernel-trust-boundary-audit-20261008.md) for the precise distinction between checked safe declarations, generated implementation helpers, imported cache trust, and source-semantic review.
