"""Original-field two-instance compiler and joint-exhaustion regressions."""
from fractions import Fraction
from itertools import product
import unittest
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task, compile_task, resonant_task
from three_user_codes.compiler import _complete_broadcast
from three_user_codes.errors import BlocklengthError, SearchBudgetExceeded, ConstructionError
from three_user_codes.linalg import eye, zeros
from three_user_codes.lcbc import BinaryScalarRealizationUnavailable
from three_user_codes.progress import SearchBudget


class TwoInstanceCompilerTests(unittest.TestCase):
    def test_uniform_original_field_bound(self):
        for q, n in product((2, 3, 4, 5, 9), (1, 2, 3)):
            task = resonant_task(Field(q), n)
            result = compile_task(task, force_blocklength=2)
            with self.subTest(q=q, n=n):
                self.assertEqual(result.certificate.blocklength, 2)
                self.assertEqual(result.certificate.base_field, task.field)
                self.assertEqual(result.certificate.task.field, task.field)
                self.assertEqual(result.stats['working_field'], q)
                self.assertEqual(result.stats['field_extension_degree'], 1)
                self.assertTrue(result.verify(task))

    def test_binary_resonance_changed_coordinates_and_source_order(self):
        task = resonant_task(Field(2), 1)
        f = task.field
        embedding = Matrix(f, [tuple(int(j == i or j > i) for j in range(7))
                               for i in range(5)], ncols=7)
        task = Task(f, tuple(A @ embedding for A in task.side),
                    tuple(W @ embedding for W in task.demand))
        result = compile_task(task)
        self.assertEqual(result.certificate.blocklength, 2)
        self.assertEqual(result.upload_optimum, 4)
        self.assertEqual(result.broadcast_optimum, Fraction(3, 2))
        self.assertTrue(result.verify(task))
        columns = tuple(product(range(2), repeat=task.n))
        source = Matrix(f, [tuple(c[i] if i < task.n else c[(i + 1) % task.n]
                                 for c in columns) for i in range(2 * task.n)])
        code = result.operating_code(task)
        received = code.execute(tuple(A @ source for A in code.original_side))
        for W, actual in zip(code.original_demand, received.decoded):
            expected = tuple(tuple(sum(a * b for a, b in zip(w, col)) % 2
                                   for col in zip(*source.rows)) for w in W.rows)
            self.assertEqual(actual.rows, expected)

    def test_binary_half_integral_upload(self):
        f = Field(2)
        task = Task.from_rows(f, [[[1, 0]], [[0, 1]], [[1, 1]]], [eye(f, 2).rows] * 3)
        result = compile_task(task, fast_paths=False)
        self.assertEqual(result.upload_optimum, Fraction(3, 2))
        self.assertEqual(result.broadcast_optimum, 1)
        self.assertEqual(result.certificate.blocklength, 2)
        self.assertTrue(result.verify(task))
        with self.assertRaises(BlocklengthError):
            compile_task(task, force_blocklength=1)

    @staticmethod
    def cycle():
        f = Field(2)
        a = tuple(Matrix(f, [row]) for row in eye(f, 3).rows)
        return Task(f, a, (a[1], a[2], a[0]))

    def test_binary_scalar_preserved_and_forced_two(self):
        task = self.cycle()
        for forced, expected in ((None, 1), (1, 1), (2, 2)):
            result = compile_task(task, force_blocklength=forced)
            self.assertEqual(result.certificate.blocklength, expected)
            self.assertTrue(result.verify(task))

    def test_integral_scalar_search_avoids_unnecessary_lifting(self):
        # A dense four-coordinate task missed by the structural candidate
        # menu. Previously default synthesis lifted immediately and exhausted
        # 2 seconds; exact scalar synthesis visits only a few dozen states.
        task = Task.from_rows(5,
            [[[1, 0, 0, 0], [0, 0, 0, 1], [1, 3, 0, 2]],
             [[0, 1, 0, 0]], [[0, 0, 1, 0]]],
            [[[0, 2, 2, 1]],
             [[1, 2, 3, 2], [4, 3, 1, 3], [1, 1, 2, 2]],
             [[4, 1, 1, 3], [0, 2, 0, 3]]])
        result = compile_task(task, max_states=200)
        self.assertEqual(result.certificate.blocklength, 1)
        self.assertTrue(result.verify(task))

    def test_large_binary_omniscience_uses_constructive_two_instances(self):
        f = Field(2)
        n = 9
        e = eye(f, 2 * n)
        a0 = Matrix(f, e.rows[:n], 2 * n)
        a1 = Matrix(f, e.rows[n:], 2 * n)
        task = Task(f, (a0, a1, a0 + a1), (e, e, e))
        result = compile_task(task, max_states=10)
        self.assertEqual(result.strategy, 'constructive-omniscience')
        self.assertEqual(result.certificate.blocklength, 2)
        self.assertEqual(result.upload_optimum, Fraction(3 * n, 2))
        self.assertEqual(result.broadcast_optimum, n)
        self.assertTrue(result.verify(task))

    def test_functional_tripod_avoids_lifted_subspace_search(self):
        # The non-omniscient GF(8) stress task has r0=c=1. Generic lifted
        # enumeration is enormous, whereas row completion is constructive.
        task = Task.from_rows(8,
            [[[1, 0, 0, 0], [0, 0, 0, 1]],
             [[1, 0, 4, 7], [0, 1, 0, 0]],
             [[0, 1, 0, 5], [0, 0, 1, 0]]],
            [[[1, 0, 0, 7], [0, 1, 0, 6], [0, 0, 1, 1]],
             [[1, 4, 7, 0]], [[1, 4, 7, 3]]])
        result = compile_task(task, max_states=10)
        self.assertEqual(result.strategy, 'constructive-pure-tripod')
        self.assertEqual(result.certificate.blocklength, 2)
        self.assertEqual(result.upload_optimum, Fraction(5, 2))
        self.assertEqual(result.broadcast_optimum, 2)
        self.assertTrue(result.verify(task))

    def test_joint_exact_fallback_is_actual_scalar_synthesis(self):
        task = self.cycle()
        with patch('three_user_codes.compiler.build_lcbc',
                   side_effect=BinaryScalarRealizationUnavailable('insufficient construction')):
            result = compile_task(task, force_blocklength=1, max_states=1000)
        self.assertEqual(result.strategy, 'exact-relay-and-broadcast-search')
        self.assertEqual(result.certificate.blocklength, 1)
        self.assertGreater(result.stats['search_counters']['broadcast_subspaces'], 0)
        self.assertTrue(result.verify(task))

    def test_binary_profile_does_not_imply_scalar_realizability(self):
        f = Field(2)
        task = Task.from_rows(f, [[[1, 0]], [[0, 1]], [[1, 1]]], [eye(f, 2).rows] * 3)
        uploads = (task.side[0], task.side[1], zeros(f, 0, 2))
        budget = SearchBudget(None, None)
        self.assertIsNone(_complete_broadcast(task, uploads, 1, budget=budget, exhaustive=True))
        self.assertEqual(budget.counters['broadcast_subspaces'], 3)

    def test_joint_fallback_respects_budget(self):
        with patch('three_user_codes.compiler.build_lcbc',
                   side_effect=BinaryScalarRealizationUnavailable('insufficient construction')):
            with self.assertRaises(SearchBudgetExceeded):
                compile_task(self.cycle(), force_blocklength=1, max_states=1)

    def test_default_scalar_exhaustion_reports_construction_inconsistency(self):
        task = resonant_task(Field(2), 2)
        from three_user_codes.compiler import _complete_broadcast as real_complete
        def fail_only_scalar(task, uploads, target, **kwargs):
            if task.n == 8:
                return None
            return real_complete(task, uploads, target, **kwargs)
        with patch('three_user_codes.compiler._complete_broadcast', side_effect=fail_only_scalar):
            with self.assertRaises(ConstructionError):
                compile_task(task, max_states=None, max_seconds=None)


if __name__ == '__main__':
    unittest.main()
