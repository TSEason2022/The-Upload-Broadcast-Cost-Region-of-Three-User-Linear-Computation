"""Scalar cycle repair that cannot be obtained from componentwise menus."""
from fractions import Fraction
from itertools import permutations
import unittest
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task, compile_task, resonant_task
from three_user_codes.compiler import _accept, _complete_broadcast, _relay_profile
from three_user_codes.linalg import block_diag, contains, eye, row_sum
from three_user_codes.mixing import demand_cycle_candidates, extract_private_edges
from three_user_codes.profile import broadcast_profile
from three_user_codes.progress import SearchBudget
from three_user_codes.upload_bound import upload_cost


def resonant_cycle(q=2, n=1, positive=True):
    f = Field(q)
    resonant = resonant_task(f, n)
    unit = eye(f, 3)
    side = tuple(Matrix(f, [unit.rows[i]], ncols=3) for i in (2, 1, 0))
    demand = tuple(side[i] for i in ((1, 2, 0) if positive else (2, 0, 1)))
    return Task(f,
                tuple(block_diag(a, b) for a, b in zip(resonant.side, side)),
                tuple(block_diag(a, b) for a, b in zip(resonant.demand, demand)))


def dense_transform(task):
    """An invertible source map, with off-diagonal mixing in both directions."""
    f, d = task.field, task.n
    upper = Matrix(f, [[int(i == j) if j <= i else (i + 2*j + 1) % f.q
                        for j in range(d)] for i in range(d)], ncols=d)
    lower = Matrix(f, [[int(i == j) if j >= i else (2*i + j + 1) % f.q
                        for j in range(d)] for i in range(d)], ncols=d)
    transform = upper @ lower
    return Task(f, tuple(A @ transform for A in task.side),
                tuple(W @ transform for W in task.demand))


class DemandCycleUpgradeTests(unittest.TestCase):
    def test_scalar_repair_beats_all_three_separate_relay_choices(self):
        for q in (2, 3, 4, 5):
            for positive in (False, True):
                with self.subTest(q=q, positive=positive):
                    task = resonant_cycle(q, positive=positive)
                    candidates = demand_cycle_candidates(task, SearchBudget(None, None))
                    self.assertEqual(upload_cost(task), 7)
                    self.assertEqual(broadcast_profile(task.side, task.augmented).cost, 3)
                    self.assertEqual([_relay_profile(task, P).cost for P in candidates[:3]],
                                     [4, 4, 4])
                    good = [P for P in candidates if _relay_profile(task, P).cost == 3]
                    self.assertEqual(len(good), 1)
                    uploads = _accept(task, good[0], 7, 3)
                    self.assertIsNotNone(uploads)
                    self.assertIsNotNone(_complete_broadcast(task, uploads, 3))

    def test_invariant_edge_extraction_and_relabeling(self):
        for q in (2, 3, 4):
            for order in permutations(range(3)):
                with self.subTest(q=q, order=order):
                    task = dense_transform(resonant_cycle(q))
                    task = Task(task.field, tuple(task.side[i] for i in order),
                                tuple(task.demand[i] for i in order))
                    residual, edges = extract_private_edges(task, SearchBudget(None, None))
                    self.assertEqual(sum(E.nrows for E in edges.values()), 3)
                    self.assertEqual(row_sum(*residual.side).nrows, 5)
                    # Every original flag is exactly its residual plus the
                    # edge summands that belong to that flag.
                    for user in range(3):
                        side = row_sum(residual.side[user],
                                       *(E for (owner, _), E in edges.items() if owner == user))
                        signal = row_sum(residual.augmented[user],
                                         *(E for (owner, receiver), E in edges.items()
                                           if user in (owner, receiver)))
                        self.assertEqual(side, task.side[user])
                        self.assertEqual(signal, task.augmented[user])
                    candidates = demand_cycle_candidates(task, SearchBudget(None, None))
                    self.assertTrue(any(_accept(task, P, 7, 3) is not None for P in candidates))

    def test_half_integral_family_keeps_exact_profile(self):
        for q in (2, 3, 4):
            task = dense_transform(resonant_cycle(q, n=2))
            candidates = demand_cycle_candidates(task, SearchBudget(None, None))
            self.assertEqual(upload_cost(task), 10)
            self.assertEqual(min(_relay_profile(task, P).cost for P in candidates), Fraction(9, 2))

    def test_all_six_edges_and_repeated_edge_dimensions(self):
        f = Field(2)
        residual = resonant_task(f, 1)
        edge_types = list(permutations(range(3), 2)) + [(0, 2)]
        unit = eye(f, len(edge_types))
        edge_side = tuple(Matrix(f, [unit.rows[j] for j, e in enumerate(edge_types)
                                     if e[0] == i], ncols=unit.ncols) for i in range(3))
        edge_want = tuple(Matrix(f, [unit.rows[j] for j, e in enumerate(edge_types)
                                     if e[1] == i], ncols=unit.ncols) for i in range(3))
        task = dense_transform(Task(f,
            tuple(block_diag(a, b) for a, b in zip(residual.side, edge_side)),
            tuple(block_diag(a, b) for a, b in zip(residual.demand, edge_want))))
        candidates = demand_cycle_candidates(task, SearchBudget(None, None))
        self.assertEqual(len(candidates), 5)
        self.assertEqual(upload_cost(task), 11)
        for P in candidates:
            self.assertEqual(P.nrows, 11)
            self.assertTrue(all(contains(row_sum(A, P), W)
                                for A, W in zip(task.side, task.demand)))

    def test_compiler_uses_scalar_mixing_under_small_state_budget(self):
        for q in (2, 3, 4):
            task = dense_transform(resonant_cycle(q))
            # Force the existing warm menu to miss, so this exercises the
            # necessary cycle repair rather than eagerly doing unused work.
            with patch('three_user_codes.compiler._scalar_choices', return_value=[]):
                result = compile_task(task, max_states=100, max_seconds=15)
            self.assertEqual(result.certificate.blocklength, 1)
            self.assertEqual(result.upload_optimum, 7)
            self.assertEqual(result.broadcast_optimum, 3)
            self.assertTrue(result.verify(task))
            self.assertGreater(result.stats['search_counters'].get(
                'recognized_resonant_edge_remainders', 0), 0)

    def test_successful_warm_start_does_not_extract_cycle_edges(self):
        task = resonant_cycle(2)
        with patch('three_user_codes.mixing.demand_cycle_candidates',
                   side_effect=AssertionError('unnecessary cycle extraction')):
            result = compile_task(task, max_states=100)
        self.assertEqual(result.certificate.blocklength, 1)
        self.assertTrue(result.verify(task))

    def test_lazy_cycle_repair_also_covers_two_instance_pairing(self):
        for q in (2, 3, 4):
            task = dense_transform(resonant_cycle(q, n=2))
            with patch('three_user_codes.compiler._scalar_choices', return_value=[]):
                result = compile_task(task, max_states=100, max_seconds=15)
            self.assertEqual(result.certificate.blocklength, 2)
            self.assertEqual(result.strategy, 'constructive-demand-cycle-repair')
            self.assertTrue(result.verify(task))


if __name__ == '__main__':
    unittest.main()
