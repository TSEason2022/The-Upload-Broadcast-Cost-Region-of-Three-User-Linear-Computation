#!/usr/bin/env python3
"""Conservative lexical gate; dependency axioms are checked separately by Lean.

This is an accidental-proof-escape check, not a sandbox for hostile Lean code.
Audit-only metaprograms in scripts/ and verification/ are separately reviewed.
"""
from pathlib import Path
import re, sys
root = Path(__file__).resolve().parents[1]
files = sorted(root.glob('*.lean'))
for directory in ('UploadBroadcast', 'scripts', 'verification'):
    files.extend(sorted((root / directory).rglob('*.lean')))
if not files:
    sys.exit('No project Lean sources found')
bad = []
for path in files:
    text = path.read_text()
    # Retain line breaks while masking nested comments and string literals.
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; out.extend('  '); i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; out.extend('  '); i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end == -1: end = len(text)
            out.extend(' ' * (end-i)); i = end
        elif text[i] == '"':
            out.append(' '); i += 1
            while i < len(text):
                c = text[i]; out.append('\n' if c == '\n' else ' '); i += 1
                if c == '\\' and i < len(text): out.append(' '); i += 1
                elif c == '"': break
        else:
            out.append(text[i]); i += 1
    masked = ''.join(out)
    forbidden = (r'\b(sorry|admit|axiom|unsafe|native_decide|'
                 r'ofReduceBool|ofReduceNat|trustCompiler|'
                 r'addDeclWithoutChecking|addDeclCore|axiomDecl|'
                 r'setEnv|modifyEnv|addConstAsync)\b|'
                 r'\bset_option\s+debug\.skipKernelTC\b|'
                 r'^\s*axioms\s+[A-Za-z_\u00ab]')
    if path == root / 'UploadBroadcast.lean' or root / 'UploadBroadcast' in path.parents:
        # The mathematical library has no custom command elaborators or
        # environment-mutating metaprograms. Such additions require review.
        forbidden += (r'|\b(run_cmd|run_meta|run_elab|run_tac|elab|elab_rules|'
                      r'macro|macro_rules|initialize|builtin_initialize)\b')
    for m in re.finditer(forbidden, masked, re.M):
        bad.append(f'{path.relative_to(root)}:{masked.count(chr(10), 0, m.start())+1}: {m.group()}')
if bad:
    sys.exit('Forbidden proof escape or custom axiom:\n' + '\n'.join(bad))
print(f'Source audit passed ({len(files)} Lean files). This is a lexical check, not semantic equivalence.')
