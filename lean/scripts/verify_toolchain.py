#!/usr/bin/env python3
"""Verify the actual compiler/Lake identity and reject ambient import overrides."""
from pathlib import Path
import argparse, json, os, shutil, subprocess
from release_support import dump_json, sha256

parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
lock = json.loads((root / 'toolchain-lock.json').read_text())
assert (root / 'lean-toolchain').read_text().strip() == lock['lean_toolchain'], 'Toolchain pin/lock mismatch'
for name in ('LEAN_PATH', 'LEAN_SRC_PATH'):
    if os.environ.get(name):
        raise SystemExit(f'Inherited {name} can shadow pinned imports; unset it before running release checks.')
executables = {}
for name in ('lean', 'lake'):
    resolved = shutil.which(name)
    if not resolved:
        raise SystemExit(f'{name} is not on PATH. Source scripts/env.sh or run bootstrap first.')
    executables[name] = Path(resolved).resolve()
run = lambda name, arg: subprocess.check_output([str(executables[name]), arg], text=True, timeout=30).strip()
version = run('lean', '--short-version')
githash = run('lean', '--githash')
lake_version = run('lake', '--version')
assert version == lock['lean_version'], f'Wrong Lean executable version: {version}'
assert githash == lock['lean_githash'], f'Wrong Lean compiler commit: {githash}'
assert lake_version == lock['lake_version'], f'Wrong Lake executable version: {lake_version}'
result = {'schema_version':1, 'lean_toolchain':lock['lean_toolchain'],
          'lean_version':version, 'lean_githash':githash, 'lake_version':lake_version,
          'inherited_import_path_overrides':False,
          'executable_sha256':{name:sha256(path.read_bytes()) for name,path in executables.items()},
          'note':'Executable hashes identify launcher binaries, not every linked runtime/library byte. Compiler and dependency provenance remain part of the trust boundary.'}
if args.output:
    dump_json(args.output, result)
print(f'Actual toolchain verified: Lean {version}, commit {githash}; {lake_version}.')
