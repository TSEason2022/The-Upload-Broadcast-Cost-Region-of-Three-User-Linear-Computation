"""Independent finite-vector-set checks of structural search pruning.

The reference enumeration uses literal tuples and modular arithmetic, rather
than package rank, nullspace, containment or subspace enumeration routines.
These finite checks establish the sampled comparisons, not a universal theorem.
"""
import importlib.util
from itertools import product
from pathlib import Path
import random
import unittest

from three_user_codes import Field, Matrix, Task, compile_task
from three_user_codes.compiler import _exact_dual_relay_search, _residual_upload_spaces
from three_user_codes.progress import SearchBudget

PATH = Path(__file__).resolve().parents[1] / 'benchmarks' / 'independent_oracle.py'
SPEC = importlib.util.spec_from_file_location('breakthrough_independent_sets', PATH)
oracle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(oracle)


def join(p, n, spaces):
    result = frozenset({(0,) * n})
    for space in spaces:
        result = oracle.sum_space(p, result, space)
    return result


def as_matrix(p, n, space):
    return Matrix(Field(p), oracle.explicit_basis(p, n, space), ncols=n)


def independent_rank(field, rows, n):
    """Small elimination using the separate polynomial-arithmetic oracle."""
    import sys
    sys.path.insert(0, str(PATH.parent))
    from independent_verifier import PolynomialOracle
    arithmetic = PolynomialOracle(field)
    matrix = [list(row) for row in rows]
    rank = 0

    def power(value, exponent):
        answer = 1
        while exponent:
            if exponent & 1:
                answer = arithmetic.mul(answer, value)
            value = arithmetic.mul(value, value)
            exponent //= 2
        return answer

    for column in range(n):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = power(matrix[rank][column], field.q - 2)
        matrix[rank] = [arithmetic.mul(inverse, v) for v in matrix[rank]]
        for i in range(rank + 1, len(matrix)):
            coefficient = arithmetic.mul(field.p - 1, matrix[i][column])
            if coefficient:
                matrix[i] = [arithmetic.add(a, arithmetic.mul(coefficient, b))
                             for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def independently_embed(matrix, embedding):
    import sys
    sys.path.insert(0, str(PATH.parent))
    from independent_verifier import PolynomialOracle
    arithmetic = PolynomialOracle(matrix.field)
    return [tuple(arithmetic.dot(row, [v[column] for v in embedding.rows])
                  for column in range(embedding.ncols)) for row in matrix.rows]


class BreakthroughIndependentOracleTests(unittest.TestCase):
    def test_active_maps_reconstruct_original_flags_and_additive_branches(self):
        from three_user_codes.active_reduction import active_reduce
        from three_user_codes.profile import broadcast_profile
        from three_user_codes.upload_bound import upload_cost
        tasks = [row[0] for row in oracle.oracle_cases(seed=20261008, samples=48)]
        unresolved = (20261013, 20261016, 20261018, 20261020, 20261021, 20261022)
        tasks += [oracle.make_dense_task(case) for case in oracle.dense_regression_cases()
                  if case.get('seed') in unresolved]
        tasks += [oracle.make_dense_task({'kind': 'dense', 'q': q, 'n': 7, 'seed': 20262006 + q})
                  for q in (4, 8, 9)]
        for task in tasks:
            with self.subTest(q=task.field.q, n=task.n):
                reduced = active_reduce(task)
                self.assertTrue(reduced.verify(task))
                basis = [row for c in reduced.components for row in c.embedding.rows]
                observed = [row for a in task.original_side for row in a.rows]
                self.assertEqual(independent_rank(task.field, basis, task.n), len(basis))
                self.assertEqual(independent_rank(task.field, basis + observed, task.n), len(basis))
                self.assertEqual(independent_rank(task.field, observed, task.n), len(basis))
                for attr in ('side', 'augmented'):
                    for user in range(3):
                        reconstructed = [row for c in reduced.components
                                         for row in independently_embed(getattr(c.task, attr)[user], c.embedding)]
                        original = list(task.original_side[user].rows)
                        if attr == 'augmented':
                            original += list(task.original_demand[user].rows)
                        dimension = independent_rank(task.field, original, task.n)
                        self.assertEqual(independent_rank(task.field, reconstructed, task.n), dimension)
                        self.assertEqual(independent_rank(task.field, reconstructed + original, task.n), dimension)
                profiles = [broadcast_profile(c.task.side, c.task.augmented).branches
                            for c in reduced.components]
                expected = broadcast_profile(task.side, task.augmented).branches
                self.assertEqual(tuple(map(sum, zip(*profiles))), expected)
                self.assertEqual(sum(upload_cost(c.task) for c in reduced.components), upload_cost(task))

    def test_tight_cut_contraction_keeps_every_sampled_valid_completion(self):
        rng = random.Random(20261006)
        witnessed_completions = witnessed_prefixes = 0
        for index in range(24):
            p, n = ((2, 2), (3, 2), (2, 3), (3, 3))[index % 4]
            spaces = oracle.explicit_subspaces(p, n)
            side_menu = [s for s in spaces if oracle.space_dimension(p, s) <= 2]
            sides = tuple(rng.choice(side_menu) for _ in range(3))
            available = join(p, n, sides)
            demands = tuple(rng.choice([s for s in spaces if s <= available]) for _ in range(3))
            task = Task(Field(p), tuple(as_matrix(p, n, a) for a in sides),
                        tuple(as_matrix(p, n, w) for w in demands))
            menus = [[s for s in spaces if s <= a] for a in sides]
            for uploads in product(*menus):
                rates = tuple(oracle.space_dimension(p, s) for s in uploads)
                relay = join(p, n, uploads)
                if sum(rates) != oracle.space_dimension(p, relay):
                    continue
                if not all(w <= oracle.sum_space(p, a, relay) for a, w in zip(sides, demands)):
                    continue
                witnessed_completions += 1
                for mask in range(1, 8):
                    users = tuple(i for i in range(3) if mask >> i & 1)
                    previous = join(p, n, [uploads[i] for i in range(3) if i not in users])
                    allowed = _residual_upload_spaces(
                        task, as_matrix(p, n, previous), users, rates, SearchBudget(None, None))
                    self.assertIsNotNone(allowed, (index, rates, mask))
                    for i in users:
                        self.assertLessEqual(uploads[i], oracle.vector_span(p, n, allowed[i].rows))
                    witnessed_prefixes += 1
        self.assertGreater(witnessed_completions, 50)
        self.assertGreater(witnessed_prefixes, 350)

    def test_dual_prefix_pruning_matches_exhaustive_relay_sets(self):
        comparisons = feasible_relays = 0
        for task, sides, demands, spaces in oracle.oracle_cases(seed=20261006, samples=28):
            p, n = task.field.q, task.n
            for dimension in range(n + 1):
                expected = set()
                for relay in spaces:
                    if oracle.space_dimension(p, relay) != dimension:
                        continue
                    if not all(w <= oracle.sum_space(p, a, relay) for a, w in zip(sides, demands)):
                        continue
                    if join(p, n, [a & relay for a in sides]) == relay:
                        expected.add(relay)
                observed = []

                def collect(uploads):
                    observed.append(join(p, n, [oracle.vector_span(p, n, a.rows) for a in uploads]))
                    return False

                result = _exact_dual_relay_search(task, dimension, n,
                                                   SearchBudget(None, None), collect)
                self.assertIsNone(result)
                self.assertEqual(set(observed), expected)
                self.assertEqual(len(observed), len(expected), 'duplicate relay from normal enumeration')
                comparisons += 1
                feasible_relays += len(expected)
        self.assertEqual(comparisons, 98)
        self.assertGreater(feasible_relays, 50)

    def test_structural_and_fallback_paths_decode_all_original_basis_vectors(self):
        fractional = 0
        tasks = [row[0] for row in oracle.oracle_cases(seed=20261007, samples=48)]
        tasks.append(Task.from_rows(2, [[[1, 0]], [[0, 1]], [[1, 1]]],
                                    [[[1, 0], [0, 1]]] * 3, n=2))
        for task in tasks:
            # Preserve deliberately redundant original observation/output rows.
            original = Task(task.field,
                            tuple(Matrix(task.field, a.rows + a.rows[:1], task.n) for a in task.side),
                            tuple(Matrix(task.field, w.rows + w.rows[:1], task.n) for w in task.demand))
            for fast in (True, False):
                result = compile_task(original, fast_paths=fast, max_states=None, max_seconds=None)
                self.assertTrue(oracle.independent_code_check(result, original)['passed'])
                expected_length = (1 if result.upload_optimum.denominator == 1
                                    and result.broadcast_optimum.denominator == 1 else 2)
                self.assertEqual(result.certificate.blocklength, expected_length)
                self.assertEqual(result.certificate.task.field, original.field)
                fractional += expected_length == 2
        self.assertGreater(fractional, 0)


if __name__ == '__main__':
    unittest.main()
