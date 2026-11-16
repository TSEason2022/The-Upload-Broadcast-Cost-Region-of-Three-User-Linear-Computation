#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
source scripts/env.sh
if ! command -v elan >/dev/null; then
  case "$(uname -s)/$(uname -m)" in
    Linux/x86_64) asset=elan-x86_64-unknown-linux-gnu.tar.gz ;;
    *) echo 'Install elan from https://github.com/leanprover/elan, then rerun.' >&2; exit 1 ;;
  esac
  mkdir -p .tooling/install
  curl --fail --location "https://github.com/leanprover/elan/releases/download/v4.2.4/$asset" -o .tooling/install/elan.tar.gz
  echo "42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  .tooling/install/elan.tar.gz" | sha256sum --check
  tar -xzf .tooling/install/elan.tar.gz -C .tooling/install
  export ELAN_HOME="$PWD/.tooling/elan"
  .tooling/install/elan-init -y --no-modify-path --default-toolchain none
  export PATH="$ELAN_HOME/bin:$PATH"
fi
toolchain="$(cat lean-toolchain)"
encoded_toolchain="${toolchain//\//--}"
encoded_toolchain="${encoded_toolchain//:/---}"
if [[ ! -x "$ELAN_HOME/toolchains/$encoded_toolchain/bin/lean" ]]; then
  elan toolchain install "$toolchain"
fi
source scripts/env.sh
# Loading the workspace fetches missing dependencies at lockfile revisions.
# Do not run lake update: inherited inputRev values may name moving branches.
python3 scripts/verify_toolchain.py
lake env lean --version
python3 scripts/verify_dependency_pins.py
python3 scripts/cache-current-imports.py
lake env lean Smoke.lean
