# Portable reproduction audit, 2026-10-08

This is a lightweight release-tooling review, separate from mathematical review
and the final clean Lean build. Checks were performed on Linux. No macOS machine
or iOS device was used, and no hosted GitHub Actions run is asserted.

## Issues found and repaired

- The documented dependency-cache copy used GNU-only `cp --reflink=auto`.
  `copy_dependency_cache` now checks for that capability and otherwise uses
  Python's `shutil.copytree`, preserving symlinks. Both the actual GNU path and
  a simulated BSD-style `cp` rejecting `--help` passed independent tests.
- `source scripts/env.sh` assumed Bash's `BASH_SOURCE`, which selected the
  wrong root under zsh. It now detects its source path under Bash or zsh.
  Both shells passed tests with strict error handling, a project path containing
  spaces, and a working directory outside the project.
- The source allowlist omitted supplementary Python checks in `verification/`.
  These are now included. Their inclusion does not make finite Python checks
  part of Lean's proof trust boundary.

## Checks performed

- Every shell script passed `bash -n`; every Python script in `scripts/` parsed.
- Nine release-tool regression tests and twelve source-audit regression tests
  passed at the time of review.
- The actual compiler reported Lean 4.19.0 and Git commit
  `6caaee842e9495688c1567e78c0e68dbb96942aa`; Lake reported
  `Lake version 5.0.0-6caaee8 (Lean version 4.19.0)`.
- All eleven actual dependency checkouts matched the lockfile, had clean tracked
  sources, preserved the checked notices, and had no unexpected untracked
  Lean/Lake input files.
- Temporary test fixtures confirmed that packaging rejects missing clean-build
  evidence, incomplete coverage evidence, and edits made after verification.
  The source-manifest verifier also rejected added selected source files.
  `PYTHONOPTIMIZE=1` was rejected before assertion-based gates could be disabled.
  Rejected packaging attempts did not create a release output directory.
- Dependency-copy tests preserved source bytes, cache bytes, hidden Git metadata,
  and symlinks, including paths containing spaces. Reusing an existing copy
  destination was rejected.
- The selected project sources passed the release script's private-path and
  credential-pattern scan. This is a bounded lexical check, not a security
  certification.
- The existing dependency-source companion had unique member names and exactly
  the eleven locked revisions. Two previously generated companion files were
  byte-identical. These observations do not replace the per-file checksum
  validation performed by the final packaging gate.

## Reproduction conditions and limits

Python 3.11 or newer is required because the pin verifier uses `tomllib`.
The shell entry points use Bash; the environment file may be sourced from Bash
or zsh. Automatic installation of checksum-pinned elan 4.2.4 is provided only
for Linux x86_64. On macOS, install official elan first as described in
`TOOLCHAIN.md`. A real macOS build remains untested by this audit.

Normal bootstrap needs public upstream network access for the Lean toolchain,
Git checkouts, and the official mathlib cache. It does not run `lake update`.
No account credentials are embedded or requested by these scripts. The source
companion contains no Git checkout metadata, installed compiler, or proof cache
and is explicitly not an offline installation.

The GitHub workflow is configured for Ubuntu, not macOS. Its proof job runs the
all-module and integrated gates; a separate job requires reviewed coverage.
Configuration alone is not evidence of a successful hosted run.

The final release must still come from a fresh snapshot that passes
`clean_rebuild.py --require-complete`, with unchanged selected source hashes,
and then passes `package_release.py`. Dependency compiled caches remain within
the stated trust boundary. This report does not claim a final all-module build,
complete manuscript verification, license approval, or publication.
