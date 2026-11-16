#!/usr/bin/env python3
"""Generate a kernel-environment existence/type audit for every mapped claim.
This complements, but cannot replace, source-semantic review.
"""
from pathlib import Path
import json,re
root=Path(__file__).resolve().parents[1]
claims=json.loads((root/'coverage.json').read_text())['claims']
names=sorted({n for c in claims for n in c['lean_declarations']})
for n in names:
    if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*',n):
        raise SystemExit(f'Invalid declaration name: {n}')
out=['import UploadBroadcast','import Lean','','open Lean Elab Command in','run_cmd do','  let env ← getEnv',
     '  let names : List Name := ['+', '.join('`'+n for n in names)+']',
     '  for n in names do',
     '    match env.find? n with',
     '    | none => throwError "Missing coverage declaration: {n}"',
     '    | some ci =>',
     '      unless ci.isTheorem do throwError "Coverage declaration is not a theorem: {n}"',
     '      logInfo m!"{n} : {ci.type}"',
     '  logInfo m!"Checked {names.length} mapped theorem declarations; semantic review is separate."','']
(root/'verification'/'CoverageDeclarations.lean').write_text('\n'.join(out))
print(f'Generated coverage declaration audit for {len(names)} theorem references.')
