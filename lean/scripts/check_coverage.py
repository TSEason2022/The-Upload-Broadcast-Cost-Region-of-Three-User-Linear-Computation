#!/usr/bin/env python3
"""Fail closed when asked to certify the entire manuscript.
This checks a human-reviewed coverage manifest, not mathematical semantics.
"""
from pathlib import Path
import json, sys
root = Path(__file__).resolve().parents[1]
data = json.loads((root / 'coverage.json').read_text())
claims = data['claims']
if len(claims) != 28 or len({c['id'] for c in claims}) != 28:
    sys.exit('Expected the 28 distinct named claims in the frozen paper.')
accepted = {'reviewed_complete'}
open_claims = [c for c in claims if c['status'] not in accepted
               or c['remaining_obligations'] or not c['lean_declarations']]
for c in open_claims:
    print(f"OPEN {c['id']}: {c['status']}")
if open_claims:
    sys.exit(f'Full-paper coverage NOT complete: {len(open_claims)}/{len(claims)} claims require work/review.')
if not data.get('unnumbered_and_external_dependencies_reviewed', False):
    sys.exit('Unnumbered claims and external dependencies are not closed/reviewed.')
print('Coverage manifest has no recorded gaps. This must accompany the kernel and semantic audits.')
