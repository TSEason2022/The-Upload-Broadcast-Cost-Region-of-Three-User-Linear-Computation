#!/usr/bin/env python3
"""Portable exact-code validation and reproducible compilation measurements.

Run from the project root::

    python benchmarks/release_validation.py --repeats 3 --output benchmark_results.json

Each trial runs in a fresh process. Timings exclude imports, input loading,
and independent verification. Budget stops never imply infeasibility and are
never assigned fictitious speedups. All successful trials verify every source
basis vector using separate polynomial field arithmetic, including extensions.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import math
from pathlib import Path
import platform
import statistics
import subprocess
import sys
from time import perf_counter, process_time
import traceback

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = Path(__file__).resolve().parent / 'validation_fixtures'


def json_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def package_digest(root):
    digest = hashlib.sha256()
    for path in sorted((root / 'three_user_codes').glob('*.py')):
        digest.update(path.name.encode())
        digest.update(b'\0')
        digest.update(path.read_bytes())
    return digest.hexdigest()


def worker(package):
    sys.path.insert(0, str(package.resolve()))
    from fractions import Fraction
    import three_user_codes
    from three_user_codes import compile_task, SearchBudgetExceeded
    from three_user_codes.io import task_from_dict
    from three_user_codes.provenance import task_fingerprint
    from independent_verifier import independently_check

    request = json.load(sys.stdin)
    task = task_from_dict(request['task'])
    case, limits = request['case'], request['limits']
    expected = case['expected']
    record = {'name': case['name'], 'suite': case['suite'], 'repeat': request['repeat'],
              'version': three_user_codes.__version__, 'field_order': task.field.q,
              'source_dimension': task.n, 'task_sha256': json_digest(request['task']),
              'task_fingerprint': task_fingerprint(task)}
    if record['task_fingerprint'] != expected['task_fingerprint']:
        raise AssertionError('Frozen input fingerprint changed')
    started, cpu = perf_counter(), process_time()
    try:
        result = compile_task(task, max_seconds=limits['max_seconds'],
                              max_states=limits['max_states'], **case['options'])
    except SearchBudgetExceeded as exc:
        record.update(status='budget_exhausted', message=str(exc), stats=exc.stats,
                      compile_seconds=perf_counter()-started, compile_cpu_seconds=process_time()-cpu)
    except Exception as exc:
        record.update(status='error', error_type=type(exc).__name__, message=str(exc),
                      traceback=traceback.format_exc(), compile_seconds=perf_counter()-started,
                      compile_cpu_seconds=process_time()-cpu)
    else:
        record.update(compile_seconds=perf_counter()-started, compile_cpu_seconds=process_time()-cpu)
        verify_started = perf_counter()
        try:
            result.verify(task)
            independent = independently_check(result, task)
            assert result.upload_optimum == Fraction(expected['upload']), 'Upload target changed'
            assert result.broadcast_optimum == Fraction(expected['broadcast']), 'Broadcast target changed'
            assert result.certificate.task.field == task.field, 'Working field changed'
            assert result.certificate.blocklength == expected['minimum_blocklength'], 'Nonminimal blocklength'
            record.update(status='success', strategy=result.strategy, stats=result.stats,
                          upload=str(result.upload_optimum), broadcast=str(result.broadcast_optimum),
                          blocklength=result.certificate.blocklength,
                          original_field_preserved=True, minimum_blocklength_verified=True,
                          independent_verification=independent)
        except Exception as exc:
            record.update(status='verification_error', error_type=type(exc).__name__,
                          message=str(exc), traceback=traceback.format_exc())
        record['independent_verification_seconds'] = perf_counter()-verify_started
    json.dump(record, sys.stdout)


def summarize(records, repeats):
    names = sorted({r['name'] for r in records})
    cases = []
    for name in names:
        trials = [r for r in records if r['name'] == name]
        successful = [r for r in trials if r['status'] == 'success']
        item = {'name': name, 'suite': trials[0]['suite'],
                'status_counts': dict(Counter(r['status'] for r in trials)),
                'complete': len(successful) == repeats,
                'successful_repeats': len(successful), 'requested_repeats': repeats}
        if successful:
            item['successful_compile_median_seconds'] = statistics.median(r['compile_seconds'] for r in successful)
            item['successful_compile_min_seconds'] = min(r['compile_seconds'] for r in successful)
            item['successful_compile_max_seconds'] = max(r['compile_seconds'] for r in successful)
        cases.append(item)
    return {'case_count': len(cases), 'complete_case_count': sum(c['complete'] for c in cases),
            'trial_count': len(records), 'status_counts': dict(Counter(r['status'] for r in records)),
            'cases': cases}


def compare(before, after):
    comparable = (before.get('fixture_set_sha256') == after.get('fixture_set_sha256')
                  and before.get('limits') == after.get('limits')
                  and before.get('repeats') == after.get('repeats'))
    if not comparable:
        raise ValueError('Comparison requires identical fixtures, options, limits and repeat counts')
    first = {c['name']: c for c in before['summary']['cases']}
    second = {c['name']: c for c in after['summary']['cases']}
    paired, newly_completed, newly_incomplete = [], [], []
    for name in sorted(first.keys() & second.keys()):
        a, b = first[name], second[name]
        if a['complete'] and b['complete']:
            paired.append({'name': name, 'baseline_seconds': a['successful_compile_median_seconds'],
                           'candidate_seconds': b['successful_compile_median_seconds'],
                           'speedup': a['successful_compile_median_seconds']/b['successful_compile_median_seconds']})
        elif b['complete']:
            newly_completed.append(name)
        elif a['complete']:
            newly_incomplete.append(name)
    return {'paired_complete_case_count': len(paired),
            'paired_geometric_mean_speedup': math.exp(statistics.mean(math.log(p['speedup']) for p in paired)) if paired else None,
            'newly_completed_cases': newly_completed, 'newly_incomplete_cases': newly_incomplete,
            'paired_cases': paired,
            'interpretation': 'Only cases completing every repeat in both runs enter speedup calculations. Budget stops and failures are reported separately.'}


def positive_float(text):
    value = float(text)
    if not math.isfinite(value) or value <= 0:
        raise argparse.ArgumentTypeError('must be a finite positive number')
    return value


def positive_int(text):
    value = int(text)
    if value <= 0:
        raise argparse.ArgumentTypeError('must be positive')
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, default=ROOT, help='source tree to measure')
    parser.add_argument('--suite', choices=('all', 'adversarial', 'regression'), default='all')
    parser.add_argument('--repeats', type=positive_int, default=1)
    parser.add_argument('--max-seconds', type=positive_float, default=3.0)
    parser.add_argument('--max-states', type=positive_int, default=100000)
    parser.add_argument('--hard-timeout', type=positive_float, default=15.0)
    parser.add_argument('--output', type=Path, default=Path('benchmark_results.json'))
    parser.add_argument('--compare', type=Path)
    parser.add_argument('--label', default='validation')
    parser.add_argument('--allow-budget-stops', action='store_true', help='collect diagnostic evidence without treating resource stops as command failure')
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.worker:
        worker(args.package)
        return 0
    package = args.package.resolve()
    manifest = json.loads((FIXTURES / 'manifest.json').read_text())
    cases = [c for c in manifest['cases'] if args.suite == 'all' or c['suite'] == args.suite]
    tasks = {c['name']: json.loads((FIXTURES / c['file']).read_text()) for c in cases}
    source_before = package_digest(package)
    limits = {'max_seconds': args.max_seconds, 'max_states': args.max_states, 'hard_timeout': args.hard_timeout}
    records = []
    started = perf_counter()
    for repeat in range(args.repeats):
        for case in cases:
            request = {'case': case, 'task': tasks[case['name']], 'repeat': repeat, 'limits': limits}
            try:
                completed = subprocess.run([sys.executable, str(Path(__file__).resolve()), '--worker', '--package', str(package)],
                    input=json.dumps(request), text=True, capture_output=True, timeout=args.hard_timeout)
                if completed.returncode:
                    record = {'name': case['name'], 'suite': case['suite'], 'repeat': repeat,
                              'status': 'worker_error', 'returncode': completed.returncode,
                              'stderr': completed.stderr[-4000:]}
                else:
                    record = json.loads(completed.stdout)
            except subprocess.TimeoutExpired:
                record = {'name': case['name'], 'suite': case['suite'], 'repeat': repeat,
                          'status': 'hard_timeout', 'hard_timeout_seconds': args.hard_timeout}
            records.append(record)
            print(f"[{repeat+1}/{args.repeats}] {case['name']}: {record['status']}", file=sys.stderr, flush=True)
    source_after = package_digest(package)
    report = {'schema': 'three-user-release-validation-v1', 'label': args.label,
              'created_utc': datetime.now(timezone.utc).isoformat(), 'python': platform.python_version(),
              'platform': platform.platform(), 'source_sha256': source_before,
              'source_unchanged_during_run': source_before == source_after,
              'source_sha256_after': source_after,
              'validator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'fixture_set_sha256': json_digest({'cases': cases, 'tasks': tasks}),
              'suite': args.suite, 'repeats': args.repeats, 'limits': limits,
              'timing_scope': 'Fresh worker per trial; compilation timing excludes imports, fixture loading and independent verification. max_seconds is a cooperative limit.',
              'verification_scope': 'Exact original-task binding, frozen U/D targets, minimum original-field blocklength, and independent polynomial arithmetic on every original source basis vector. This does not independently prove the universal rate theorem.',
              'elapsed_seconds': perf_counter()-started, 'summary': summarize(records, args.repeats), 'records': records}
    if args.compare:
        report['comparison'] = compare(json.loads(args.compare.read_text()), report)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'output': str(args.output), **{k:v for k,v in report['summary'].items() if k != 'cases'}}))
    allowed = {'success', 'budget_exhausted', 'hard_timeout'} if args.allow_budget_stops else {'success'}
    return 0 if source_before == source_after and all(r['status'] in allowed for r in records) else 1


if __name__ == '__main__':
    raise SystemExit(main())
