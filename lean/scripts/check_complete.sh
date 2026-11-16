#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
# This historical full-manuscript gate requires the private source ledgers.
# The public subset supports check_public.sh instead.
if [[ ! -f source-ledger/claims_inventory.json || ! -f source-ledger/proof_blocks.json ]]; then
  echo 'Full-manuscript gate requires the complete private historical archive.' >&2
  echo 'Use bash scripts/check_public.sh for public kernel and axiom checks.' >&2
  exit 1
fi
python3 scripts/verify_toolchain.py
python3 scripts/audit_source.py
python3 scripts/check_coverage.py
python3 scripts/check_all_modules.py
bash scripts/check.sh
python3 scripts/check_coverage.py
