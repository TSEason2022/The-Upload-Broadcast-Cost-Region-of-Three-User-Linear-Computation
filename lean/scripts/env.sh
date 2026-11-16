#!/usr/bin/env bash
# Source this file; prefer the exact installed toolchain over the elan shim.
if [[ -n "${BASH_VERSION:-}" ]]; then
  _paper_env_source="${BASH_SOURCE[0]}"
elif [[ -n "${ZSH_VERSION:-}" ]]; then
  _paper_env_source="${(%):-%x}"
else
  echo 'Use bash or zsh to source scripts/env.sh.' >&2
  return 1
fi
ROOT="$(cd "$(dirname "$_paper_env_source")/.." && pwd)"
unset _paper_env_source
if [[ -d "$ROOT/../tooling/elan/bin" ]]; then
  export ELAN_HOME="$ROOT/../tooling/elan"
elif [[ -d "$ROOT/.tooling/elan/bin" ]]; then
  export ELAN_HOME="$ROOT/.tooling/elan"
else
  export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
fi
if [[ -d "$ELAN_HOME/bin" ]]; then
  export PATH="$ELAN_HOME/bin:$PATH"
fi
# Elan encodes owner/repository:version as owner--repository---version.
# Avoid slow or blocked shim resolution when this precise toolchain is present.
IFS= read -r _paper_toolchain < "$ROOT/lean-toolchain"
_paper_toolchain="${_paper_toolchain//$'\r'/}"
_paper_toolchain="${_paper_toolchain//\//--}"
_paper_toolchain="${_paper_toolchain//:/---}"
_paper_bin="$ELAN_HOME/toolchains/$_paper_toolchain/bin"
if [[ -x "$_paper_bin/lean" && -x "$_paper_bin/lake" ]]; then
  export PATH="$_paper_bin:$PATH"
fi
unset _paper_toolchain _paper_bin
# Keep cache writes inside the project on executors with a read-only home.
export MATHLIB_CACHE_DIR="$ROOT/.tooling/cache/mathlib"
mkdir -p "$MATHLIB_CACHE_DIR"
