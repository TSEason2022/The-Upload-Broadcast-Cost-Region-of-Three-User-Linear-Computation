#!/usr/bin/env bash
# Kernel/source checks for the public subset; no manuscript ledgers required.
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
python3 scripts/verify_toolchain.py
python3 scripts/verify_dependency_pins.py
python3 scripts/audit_source.py
python3 scripts/check_all_modules.py
bash scripts/check.sh
python3 scripts/generate_current_coverage_audit.py
lake env lean -DwarningAsError=true verification/CurrentSourceDeclarations.lean 2>&1 | tee logs/current-source-declarations.log
