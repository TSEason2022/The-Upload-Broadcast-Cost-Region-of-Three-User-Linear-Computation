"""Independent literal-vector-set oracle for small prime-field test cases.

This module has no release-comparison or measurement workflow. Exact-set
checks exhaust every scalar upload/broadcast subspace of each sampled task.
The implementation under test supplies the target rates, so these checks do
not independently establish the universal rate theorem.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import random
import sys
from time import perf_counter

@lru_cache(maxsize=20000)
def sum_space(p, left, right):
    return frozenset(tuple((x + y) % p for x, y in zip(a, b)) for a in left for b in right)


def vector_span(p, n, vectors):
    result = frozenset({(0,) * n})
    for vector in vectors:
        line = frozenset(tuple(a * x % p for x in vector) for a in range(p))
        result = sum_space(p, result, line)
    return result


def space_dimension(p, space):
    size, dimension = len(space), 0
    while size > 1:
        size, remainder = divmod(size, p)
        if remainder:
            raise AssertionError('not a finite-field subspace')
        dimension += 1
    return dimension


@lru_cache(maxsize=10)
def explicit_subspaces(p, n):
    vectors = tuple(product(range(p), repeat=n))
    initial = frozenset({(0,) * n})
    found, pending = {initial}, [initial]
    lines = tuple(dict.fromkeys(vector_span(p, n, (v,)) for v in vectors))
    while pending:
        current = pending.pop()
        for line in lines:
            if not line <= current:
                enlarged = sum_space(p, current, line)
                if enlarged not in found:
                    found.add(enlarged)
                    pending.append(enlarged)
    return tuple(sorted(found, key=lambda s: (len(s), tuple(sorted(s)))))


def explicit_basis(p, n, space):
    result = []
    current = frozenset({(0,) * n})
    for vector in sorted(space):
        if vector not in current:
            result.append(list(vector))
            current = vector_span(p, n, result)
    return result


def scalar_joint_witness(p, sides, demands, spaces, upload, download):
    """Exhaust every local upload subspace and target broadcast subspace."""
    broadcasts = [b for b in spaces if space_dimension(p, b) == download and all(
        w <= sum_space(p, a, b) for a, w in zip(sides, demands))]
    if not broadcasts:
        return None
    choices = [[s for s in spaces if s <= a and space_dimension(p, s) <= upload]
               for a in sides]
    for uploads in product(*choices):
        if sum(space_dimension(p, s) for s in uploads) != upload:
            continue
        relay = sum_space(p, sum_space(p, uploads[0], uploads[1]), uploads[2])
        for broadcast in broadcasts:
            if broadcast <= relay:
                return uploads, broadcast
    return None


def independent_code_check(result, task):
    # Reuse the shipped all-source-basis verifier, whose polynomial arithmetic
    # is independent of the package under test, including extension fields.
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    from independent_verifier import independently_check
    return independently_check(result, task)


def oracle_cases(seed=20261005, samples=120):
    from three_user_codes import Task
    rng = random.Random(seed)
    for index in range(samples):
        p, n = ((2, 2), (2, 3), (3, 2), (3, 3))[index % 4]
        spaces = explicit_subspaces(p, n)
        sides = tuple(rng.choice(spaces) for _ in range(3))
        available = sum_space(p, sum_space(p, sides[0], sides[1]), sides[2])
        choices = [s for s in spaces if s <= available]
        demands = tuple(rng.choice(choices) for _ in range(3))
        task = Task.from_rows(p, [explicit_basis(p, n, s) for s in sides],
                              [explicit_basis(p, n, s) for s in demands], n=n)
        yield task, sides, demands, spaces


def run_oracle(seed=20261005, samples=120):
    from three_user_codes import BlocklengthError, compile_task
    from three_user_codes.profile import broadcast_profile
    from three_user_codes.upload_bound import upload_cost
    expected_counts = {(2, 1): 2, (2, 2): 5, (2, 3): 16,
                       (3, 1): 2, (3, 2): 6, (3, 3): 28}
    assert all(len(explicit_subspaces(p, n)) == count
               for (p, n), count in expected_counts.items())
    started, records = perf_counter(), []
    for index, (task, sides, demands, spaces) in enumerate(oracle_cases(seed, samples)):
        upload = Fraction(upload_cost(task))
        download = Fraction(broadcast_profile(task.side, task.augmented).cost)
        record = {'index': index, 'q': task.field.q, 'n': task.n,
                  'upload': str(upload), 'download': str(download)}
        if upload.denominator != 1 or download.denominator != 1:
            record['status'] = 'nonintegral_skipped'
            records.append(record)
            continue
        exists = scalar_joint_witness(task.field.q, sides, demands, spaces,
                                      int(upload), int(download)) is not None
        try:
            result = compile_task(task, force_blocklength=1, max_states=None,
                                  max_seconds=None, fast_paths=False)
        except BlocklengthError:
            assert not exists, f'compiler rejected feasible scalar task {index}'
            record['status'] = 'infeasibility_matched'
        else:
            assert exists, f'compiler contradicted scalar impossibility at {index}'
            assert result.certificate.blocklength == 1
            assert result.certificate.task.field == task.field
            result.verify(task)
            independent_code_check(result, task)
            record['status'] = 'feasibility_matched'
        records.append(record)
    return {'schema': 'three-user-prime-scalar-oracle-v1', 'seed': seed, 'samples': samples,
            'scope': 'GF(2), GF(3); n <= 3; exhaustive scalar feasibility per sampled feasible task',
            'limitation': 'The package supplies the rate target; this checks scalar realizability independently, not the universal rate formula.',
            'elapsed_seconds': perf_counter() - started, 'records': records,
            'status_counts': dict(Counter(r['status'] for r in records)),
            'all_comparisons_matched': True}

def dense_regression_cases():
    """Frozen seeded dense-task descriptions used by structural tests."""
    data = json.loads((Path(__file__).resolve().parent / 'validation_fixtures' / 'manifest.json').read_text())
    return [case['provenance'] for case in data['cases']
            if case['suite'] == 'regression' and case['provenance'].get('kind') == 'dense']


def make_dense_task(case):
    """Deterministic feasible tasks with dense demand and observation rows."""
    from three_user_codes import Field, Task
    from three_user_codes.linalg import eye
    if case.get('kind') != 'dense':
        raise ValueError('Only the seeded dense regression generator is supported')
    field, n = Field(case['q']), case['n']
    whole = eye(field, n)
    rng = random.Random(case['seed'])
    sides = [[list(whole.rows[j]) for j in range(n) if j % 3 == user] for user in range(3)]
    for rows in sides:
        rows.extend([[rng.randrange(field.q) for _ in range(n)] for _ in range(1+n//6)])
    wants = [[[rng.randrange(field.q) for _ in range(n)] for _ in range(1+n//4)] for _ in range(3)]
    return Task.from_rows(field, sides, wants, n=n)
