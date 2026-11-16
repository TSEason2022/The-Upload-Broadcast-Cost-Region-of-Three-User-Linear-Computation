#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/bundle_dependency_sources.py "${1:-../dependency-sources.tar.gz}"
