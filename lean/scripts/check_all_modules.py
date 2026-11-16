#!/usr/bin/env python3
"""Build and axiom-audit every library module, including umbrella omissions."""
from pathlib import Path
import os, subprocess, time
from release_support import module_inventory, dump_json

root = Path(__file__).resolve().parents[1]
result = root / '.verification-results'
result.mkdir(exist_ok=True)
inventory = module_inventory(root)
dump_json(result / 'module-inventory.json', inventory)
print(f"Checking {inventory['module_count']} library modules; "
      f"{len(inventory['outside_umbrella'])} outside umbrella import closure.", flush=True)
threads = int(os.environ.get('PAPER_RELEASE_THREADS', '1'))
assert threads >= 1, 'PAPER_RELEASE_THREADS must be positive'
env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
# Every project import has already been built before the next module starts.
# This bounds project compilation to one new module at a time even when Lake
# itself has no documented command-line job-count option.
build_metrics = []
for index, module in enumerate(inventory['topological_modules'], start=1):
    print(f'[{index}/{inventory["module_count"]}] {module}', flush=True)
    started = time.monotonic()
    build = subprocess.run(['lake', '--wfail', 'build', '+' + module], cwd=root, env=env, check=False)
    build_metrics.append({'module': module, 'duration_seconds': round(time.monotonic() - started, 3),
                          'exit_code': build.returncode})
    dump_json(result / 'module-build-timings.json', build_metrics)
    build.check_returncode()
for source_name, generated_name in (
    ('AuditAxioms.lean', 'AllModulesAxiomAudit.lean'),
    ('AuditAllDeclarations.lean', 'AllModulesDeclarationAudit.lean'),
):
    audit = (root / 'scripts' / source_name).read_text()
    assert audit.startswith('import UploadBroadcast\n')
    # Keep each strict audit body unchanged while extending its import roots.
    audit = '\n'.join('import ' + m for m in inventory['modules']) + '\n' + audit.split('\n', 1)[1]
    audit_path = result / generated_name
    audit_path.write_text(audit)
    subprocess.run(['lake', 'env', 'lean', '-DwarningAsError=true', str(audit_path.relative_to(root))],
                   cwd=root, env=env, check=True)
print('Every library module compiled; theorem and module-origin safe-declaration axiom audits passed.', flush=True)
