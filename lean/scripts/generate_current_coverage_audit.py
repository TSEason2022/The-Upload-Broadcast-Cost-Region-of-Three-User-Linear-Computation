#!/usr/bin/env python3
"""Generate a kernel-environment audit for the current source declaration map.
The separate source-to-statement review remains an explicit trust boundary.
"""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[1]
current = json.loads((root / 'current-source-coverage.json').read_text())
historical = json.loads((root / 'coverage.json').read_text())
claims = current['claims']
ids = [claim['id'] for claim in claims]
if len(ids) != 28 or len(set(ids)) != 28 or set(ids) != {c['id'] for c in historical['claims']}:
    raise SystemExit('Current source map must name the same 28 distinct results.')
source_hash = current['source_sha256']
if not re.fullmatch('[0-9a-f]{64}', source_hash):
    raise SystemExit('Expected the exact current manuscript SHA-256.')
names = sorted({name for claim in claims for name in claim['lean_declarations']})
for name in names:
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', name):
        raise SystemExit(f'Invalid declaration name: {name}')
if not names:
    raise SystemExit('Refusing an empty current declaration audit.')
lines = [
    'import UploadBroadcast', 'import Lean', '',
    'open Lean Elab Command in', 'run_cmd do', '  let env ← getEnv',
    '  if Lean.debug.skipKernelTC.get (← getOptions) then',
    '    throwError "Kernel checking is disabled in the audit environment"',
    '  let names : List Name := [' + ', '.join('`' + n for n in names) + ']',
    '  for n in names do', '    match env.find? n with',
    '    | none => throwError "Missing current-source declaration: {n}"',
    '    | some ci =>',
    '      unless ci.isTheorem do throwError "Current-source declaration is not a theorem: {n}"',
    '      logInfo m!"{n} : {ci.type}"',
    '  let work : Lean.CollectAxioms.M Unit := names.forM Lean.CollectAxioms.collect',
    '  let (_, state) := (work.run env).run {}',
    '  for ax in state.axioms do',
    '    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do',
    '      throwError "Unapproved axiom {ax} reachable from current-source declarations"',
    '  logInfo m!"Checked {names.length} current-source theorem declarations; semantic review is separate."',
    '  logInfo m!"Complete reachable axiom set: {state.axioms}"',
    '  logInfo "Current manuscript SHA-256: ' + source_hash + '"', '',
]
output = root / 'verification' / 'CurrentSourceDeclarations.lean'
output.write_text('\n'.join(lines))
print(f'Generated current-source audit: {len(claims)} claims, {len(names)} unique theorem declarations.')
