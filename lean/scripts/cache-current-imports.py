#!/usr/bin/env python3
"""Download official mathlib cache for current project and PFR import closure."""
from pathlib import Path
import re, subprocess, sys
root = Path(__file__).resolve().parents[1]
roots = [root] + list((root / '.lake/packages').iterdir())
seen, mathlib = set(), set()
def visit(name):
    if name in seen: return
    seen.add(name)
    if name == 'Mathlib' or name.startswith('Mathlib.'):
        mathlib.add(name); return
    rel = Path(*name.split('.')).with_suffix('.lean')
    for base in roots:
        file = base / rel
        if file.is_file():
            for line in file.read_text().splitlines():
                match = re.match(r'^\s*import\s+(.+?)(?:\s*--.*)?$', line)
                if match:
                    for child in match.group(1).split(): visit(child)
            return
for file in [root / 'Smoke.lean', *sorted((root / 'UploadBroadcast').glob('*.lean'))]:
    for line in file.read_text().splitlines():
        match = re.match(r'^\s*import\s+(.+?)(?:\s*--.*)?$', line)
        if match:
            for name in match.group(1).split(): visit(name)
if not mathlib: raise SystemExit('No mathlib imports found')
print(f'Fetching dependency closure of {len(mathlib)} mathlib import roots.', flush=True)
if sys.platform == 'darwin':
    # Run the pinned cache program through Lean's interpreter. Native cache
    # binaries linked by older Lean releases can be rejected by newer macOS
    # loaders; this changes only cache transport, never proof verification.
    subprocess.run(['lake', '--wfail', 'build', '+Cache.Main'], cwd=root, check=True)
    subprocess.run(['lake', 'env', 'lean', '--run',
                    '.lake/packages/mathlib/Cache/Main.lean',
                    'get', *sorted(mathlib)], cwd=root, check=True)
else:
    subprocess.run(['lake', 'exe', 'cache', 'get', *sorted(mathlib)], cwd=root, check=True)
