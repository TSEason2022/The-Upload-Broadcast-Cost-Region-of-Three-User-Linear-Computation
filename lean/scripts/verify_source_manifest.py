#!/usr/bin/env python3
"""Verify exact release source identity without trusting existing build outputs."""
from pathlib import Path
import argparse,json
from release_support import source_manifest
parser=argparse.ArgumentParser()
parser.add_argument('manifest',type=Path,nargs='?',default=Path('SOURCE_MANIFEST.json'))
args=parser.parse_args()
root=Path(__file__).resolve().parents[1]
saved=json.loads(args.manifest.read_text())
actual=source_manifest(root)
if actual != saved:
    expected={f['path']:f['sha256'] for f in saved['files']}
    observed={f['path']:f['sha256'] for f in actual['files']}
    for name in sorted(expected.keys() | observed.keys()):
        if expected.get(name)!=observed.get(name):
            print('MISMATCH',name)
    raise SystemExit('Release source manifest does not match this project.')
print('Verified exact project source identity:',actual['project_source_sha256'])
