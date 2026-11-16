#!/usr/bin/env python3
"""Check lockfile consistency and exact, clean tracked dependency sources."""
from pathlib import Path
import argparse, json, subprocess, tomllib
from release_support import sha256, dump_json

parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'lake-manifest.json').read_text())
config = tomllib.loads((root / 'lakefile.toml').read_text())
locked = {p['name']: p for p in manifest['packages']}
for dep in config.get('require', []):
    assert dep['name'] in locked, f"Dependency absent from lockfile: {dep['name']}"
    assert dep['rev'] == locked[dep['name']]['rev'], f"Direct pin mismatch: {dep['name']}"
    assert dep['git'] == locked[dep['name']]['url'], f"Direct URL mismatch: {dep['name']}"
records = []
for dep in sorted(locked.values(), key=lambda p:p['name']):
    folder = root / '.lake/packages' / dep['name']
    run = lambda *cmd: subprocess.check_output(['git', '-C', str(folder), *cmd])
    actual = run('rev-parse', 'HEAD').decode().strip()
    assert actual == dep['rev'], f"Revision mismatch: {dep['name']}"
    assert not run('status', '--porcelain', '--untracked-files=no').strip(), f"Modified tracked source: {dep['name']}"
    tracked = set(run('ls-tree', '-r', '--name-only', actual).decode().splitlines())
    extra_inputs = []
    for candidate in folder.rglob('*'):
        relative = candidate.relative_to(folder)
        if any(part in {'.git', '.lake', '__pycache__'} for part in relative.parts):
            continue
        if candidate.is_file() and (candidate.suffix == '.lean' or candidate.name in
                                     {'lakefile.toml', 'lakefile.lean', 'lean-toolchain', 'lake-manifest.json'}):
            if relative.as_posix() not in tracked:
                extra_inputs.append(relative.as_posix())
    assert not extra_inputs, f"Untracked dependency proof/config inputs: {dep['name']}: {extra_inputs}"
    notices = []
    for name in ('LICENSE', 'LICENSE.md', 'LICENSE.txt', 'COPYING', 'NOTICE'):
        file = folder / name
        if file.is_file():
            notices.append({'path': name, 'sha256': sha256(file.read_bytes())})
    assert notices, f"Missing dependency license/notice: {dep['name']}"
    copy = root / 'third_party_notices' / (dep['name'] + '-LICENSE')
    if (folder / 'LICENSE').is_file():
        assert copy.is_file() and copy.read_bytes() == (folder / 'LICENSE').read_bytes(), f"Attribution copy mismatch: {dep['name']}"
    records.append({'name': dep['name'], 'url': dep['url'], 'revision': actual, 'notices': notices})
result = {'schema_version': 1, 'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
          'lockfile_sha256': sha256((root / 'lake-manifest.json').read_bytes()), 'dependencies': records}
if args.output:
    dump_json(args.output, result)
print(f"Verified exact revisions and clean tracked sources for {len(records)} dependencies; no unexpected untracked Lean/Lake inputs.")
