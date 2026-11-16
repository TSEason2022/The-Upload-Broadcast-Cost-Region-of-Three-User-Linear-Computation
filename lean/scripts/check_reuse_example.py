#!/usr/bin/env python3
"""Compile the public reuse examples and strictly check every declared axiom report."""
from pathlib import Path
import os, subprocess
from release_support import dump_json, sha256, validate_axiom_reports

root = Path(__file__).resolve().parents[1]
source = root / 'examples/ReusableAPI.lean'
results = root / '.verification-results'
results.mkdir(exist_ok=True)
(root / 'logs').mkdir(exist_ok=True)
env = dict(os.environ, LEAN_NUM_THREADS=os.environ.get('PAPER_RELEASE_THREADS', '1'))
result = subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', 'examples/ReusableAPI.lean'],
                        cwd=root, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(root / 'logs/reusable-api.log').write_text(result.stdout)
print(result.stdout, end='', flush=True)
if result.returncode:
    raise SystemExit(result.returncode)
if 'warning:' in result.stdout:
    raise SystemExit('Unexpected warning in reuse example.')
audit = validate_axiom_reports(source.read_text(), result.stdout)
audit.update({'source': 'examples/ReusableAPI.lean', 'source_sha256': sha256(source.read_bytes()),
              'scope': 'Every declaration explicitly named by a #print axioms command in the public example; project library declarations have separate all-module audits.'})
dump_json(results / 'reuse-example-audit.json', audit)
print(f"Verified {audit['declaration_count']} public example declarations against the standard-axiom whitelist.")
