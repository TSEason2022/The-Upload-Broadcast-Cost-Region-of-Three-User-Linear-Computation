#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
mkdir -p logs
python3 scripts/verify_toolchain.py | tee logs/toolchain-identity.log
python3 scripts/audit_source.py | tee logs/source-audit.log
lake env lean --version | tee logs/lean-version.log
lake build 2>&1 | tee logs/build.log
lake env lean Smoke.lean 2>&1 | tee logs/smoke.log
python3 scripts/check_reuse_example.py 2>&1 | tee logs/reusable-api-check.log
python3 scripts/generate_coverage_declaration_audit.py
lake env lean verification/CoverageDeclarations.lean 2>&1 | tee logs/coverage-declarations.log
lake env lean scripts/AuditAxioms.lean 2>&1 | tee logs/axioms.log
lake env lean scripts/AuditAllDeclarations.lean 2>&1 | tee logs/all-declarations.log
# Any diagnostic warning is conservatively disallowed in our sources/audits.
if grep -E 'warning:|sorryAx|Lean\.ofReduceBool' logs/build.log logs/smoke.log logs/axioms.log logs/all-declarations.log logs/reusable-api-check.log logs/coverage-declarations.log; then
  echo 'Unexpected warning or proof escape in Lean diagnostics.' >&2
  exit 1
fi
