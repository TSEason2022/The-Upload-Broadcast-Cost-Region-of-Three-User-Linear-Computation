# Current verification evidence

`report.json` records the current clean project build, all-library axiom audits, integrated reuse checks and current-source declaration audit. `formal-input-manifest.json` binds every project Lean source, checker/orchestration script and compiler/dependency pin used in that run. No project compiled artifacts from another campaign were imported; exact dependency sources and compiled caches were reused as recorded.

`module-inventory.json` lists all 314 library modules, including the two outside the umbrella import closure. `module-build-timings.json` records each module's exit status and host-dependent elapsed time. The complete library theorem and safe-declaration axiom unions are in `all-library-modules-and-both-axiom-audits.log`; current mapped signatures and their axiom union are in `current-source-declarations-and-axioms.log`.

Only JSON formatting and local filesystem/interpreter/output paths have been normalized in distributed evidence. `evidence-normalization.json` records raw private and distributed hashes. Source and dependency identities are unmodified. The retained October 2026 evidence elsewhere is historical and is not this run's certificate.

Manuscript hashes identify the reviewed source and the final private manuscript derivative. The manuscript, its raw extracted text and private comparison diff are not distributed. Source correspondence is explicitly bounded in `../current-source-coverage.json`; no Python-to-Lean refinement theorem or independent rebuild of upstream dependencies is claimed.
