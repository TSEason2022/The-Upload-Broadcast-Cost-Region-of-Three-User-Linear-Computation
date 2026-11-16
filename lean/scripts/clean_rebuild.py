#!/usr/bin/env python3
"""Create a fresh source snapshot, rebuild it, and bind evidence to its hashes.

Dependency .olean caches may be copied. Project .olean files are never copied.
The destination must not exist. This is a check, never a publication action.
"""
from pathlib import Path
import argparse, datetime, json, os, platform, shutil, subprocess, time
from release_support import source_manifest, project_files, dump_json, module_inventory, sha256, referenced_historical_logs, copy_dependency_cache

parser = argparse.ArgumentParser()
parser.add_argument('destination', type=Path)
parser.add_argument('--dependency-cache', type=Path, help='Existing .lake/packages at the exact pinned revisions')
parser.add_argument('--require-complete', action='store_true', help='Also require reviewed full-paper coverage')
args = parser.parse_args()
origin = Path(__file__).resolve().parents[1]
dest = args.destination.resolve()
if dest.exists():
    raise SystemExit('Destination already exists; choose a fresh directory. No old project outputs may be reused.')
if origin == dest or origin in dest.parents:
    raise SystemExit('Clean destination must be outside the source repository.')
dest.mkdir(parents=True)
for src in project_files(origin):
    target = dest / src.relative_to(origin)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(src, target)
results = dest / '.verification-results'
results.mkdir()
historical_logs = []
for relative in referenced_historical_logs(dest):
    source = origin / relative
    target = dest / relative
    item = {'path': relative, 'available': source.is_file()}
    if source.is_file():
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
        item.update({'sha256': sha256(target.read_bytes()), 'size': target.stat().st_size})
    historical_logs.append(item)
dump_json(results / 'historical-log-inputs.json', historical_logs)
manifest = source_manifest(dest)
dump_json(results / 'source-manifest.json', manifest)
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
report = {'schema_version': 1, 'started_utc': started,
          'project_source_sha256': manifest['project_source_sha256'],
          'project_compiled_artifacts_reused': False,
          'dependency_compiled_cache_reused': bool(args.dependency_cache),
          'platform': {'system': platform.system(), 'architecture': platform.machine(),
                       'python': platform.python_version(), 'logical_cpus': os.cpu_count()},
          'build_policy': {'project_modules': 'topological-sequential',
                           'lean_threads': int(os.environ.get('PAPER_RELEASE_THREADS', '1'))},
          'checks': [], 'passed': False, 'whole_paper_release_gate_passed': False}
dump_json(results / 'report.json', report)
if args.dependency_cache:
    cache = args.dependency_cache.resolve()
    assert cache.is_dir(), 'Dependency cache directory not found'
    (dest / '.lake').mkdir()
    report['dependency_cache_copy_method'] = copy_dependency_cache(cache, dest / '.lake/packages')
    dump_json(results / 'report.json', report)
assert not (dest / '.lake/build').exists(), 'Project build artifacts unexpectedly present before clean build'
checks = [('toolchain', 'python3 scripts/verify_toolchain.py --output .verification-results/toolchain.json'),
          ('dependency-pins', 'python3 scripts/verify_dependency_pins.py --output .verification-results/dependency-pins.json'),
          ('release-regressions', 'python3 scripts/test_release_tools.py && python3 scripts/test_audit_source.py && python3 scripts/test_package_release.py'),
          ('source-preflight', 'python3 scripts/audit_source.py' + (' && python3 scripts/check_coverage.py' if args.require_complete else '')),
          ('all-modules', 'python3 scripts/check_all_modules.py'),
          ('integrated-check', 'bash scripts/check.sh')]
if not args.dependency_cache:
    checks.insert(0, ('bootstrap', 'bash scripts/bootstrap.sh'))
if args.require_complete:
    checks.append(('complete-coverage', 'python3 scripts/check_coverage.py'))
for name, cmd in checks:
    print(f'[{name}] {cmd}', flush=True)
    start = time.monotonic()
    with (results / (name + '.log')).open('w') as log:
        proc = subprocess.Popen(['bash', '-c', 'set -euo pipefail; source scripts/env.sh; ' + cmd],
                                cwd=dest, env=dict(os.environ, LEAN_NUM_THREADS=str(report['build_policy']['lean_threads'])),
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        try:
            for line in proc.stdout:
                print(line, end='', flush=True)
                log.write(line)
            code = proc.wait()
        except KeyboardInterrupt:
            proc.terminate()
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                proc.kill()
                proc.wait()
            code = 130
            report['interrupted'] = True
    report['checks'].append({'name': name, 'command': cmd, 'exit_code': code,
                             'duration_seconds': round(time.monotonic() - start, 3), 'log': name + '.log'})
    dump_json(results / 'report.json', report)
    if code:
        report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        dump_json(results / 'report.json', report)
        print(f'FAILED: {name}. This snapshot is not a release.', flush=True)
        raise SystemExit(code)
after = source_manifest(dest)
report['source_unchanged_during_checks'] = after == manifest
report['finished_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
report['passed'] = after == manifest
report['whole_paper_release_gate_passed'] = report['passed'] and args.require_complete
# Existing check.sh regenerates a coverage audit. It must be byte-identical in a frozen release.
dump_json(results / 'report.json', report)
if after != manifest:
    dump_json(results / 'source-manifest-after.json', after)
    raise SystemExit('Source changed during verification; inspect the before/after manifests and rebuild a fresh snapshot.')
print('Clean snapshot checks passed. Source identity: ' + manifest['project_source_sha256'])
