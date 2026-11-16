"""Exact group contraction, incremental kernels, and lazy candidate regressions."""
from fractions import Fraction
from itertools import product
import random
import unittest
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task, compile_task
from three_user_codes.compiler import (
    _accept, _complete_broadcast, _exact_local_relay_search, _forced_group_uploads,
    _hyperplane_values, _local_capacity_groups, _normal_kernel_prefixes,
    _restrict_hyperplane, _scalar_choices, enumerate_subspaces, resonant_task,
)
from three_user_codes.linalg import (
    block_diag, contains, eye, intersection, nullspace, row_basis, row_sum, zeros,
)
from three_user_codes.progress import SearchBudget
from three_user_codes.relay import normal_relay_spaces


def unlimited():
    return SearchBudget(None, None)


class FrontierSolverTests(unittest.TestCase):
    def test_pair_capacity_detects_what_singleton_and_total_miss(self):
        f = Field(3)
        e = eye(f, 3)
        allowed = {0: Matrix(f, [e.rows[0]], 3),
                   1: Matrix(f, [e.rows[0]], 3),
                   2: Matrix(f, e.rows[1:], 3)}
        budget = unlimited()
        self.assertTrue(all(a.nrows >= 1 for a in allowed.values()))
        self.assertEqual(row_sum(*allowed.values()).nrows, 3)
        self.assertIsNone(_local_capacity_groups(zeros(f, 0, 3), (0, 1, 2),
                                                (1, 1, 1), allowed, budget))
        self.assertEqual(budget.counters['pruned_group_capacity'], 1)

    def test_hall_test_and_quota_construction_match_every_small_assignment(self):
        # These checks enumerate the underlying local subspaces, rather than
        # assuming the capacity conditions characterize feasible assignments.
        comparisons = 0
        for q in (2, 3, 4):
            f, n = Field(q), 2
            full = eye(f, n)
            lines = list(enumerate_subspaces(full, 1, unlimited()))
            allowed_cases = ((full, full, lines[0]),
                             (lines[0], lines[0], full),
                             (lines[0], lines[-1], full))
            for spaces in allowed_cases:
                allowed = dict(enumerate(spaces))
                for P in (zeros(f, 0, n), lines[-1]):
                    for rates in product(range(3), repeat=3):
                        users = tuple(i for i in range(3) if rates[i])
                        menus = [list(enumerate_subspaces(a, r, unlimited()))
                                 for a, r in zip(spaces, rates)]
                        expected = any(row_sum(P, *choice).nrows == P.nrows + sum(rates)
                                       for choice in product(*menus))
                        groups = _local_capacity_groups(P, users, rates, allowed, unlimited())
                        self.assertEqual(groups is not None, expected, (q, rates, P.rows))
                        if expected:
                            selected = _forced_group_uploads(P, users, rates, allowed, unlimited())
                            self.assertEqual(row_sum(P, *selected.values()).nrows,
                                             P.nrows + sum(rates))
                            for i in users:
                                self.assertEqual(selected[i].nrows, rates[i])
                                self.assertTrue(contains(allowed[i], selected[i]))
                        comparisons += 1
        self.assertEqual(comparisons, 486)

    def test_tight_group_collapse_retains_all_final_relay_spaces(self):
        for q in (2, 3, 4):
            f = Field(q)
            e = eye(f, 4)
            first, second = Matrix(f, e.rows[:2], 4), Matrix(f, e.rows[2:], 4)
            task = Task(f, (first, first, second), (zeros(f, 0, 4),) * 3)
            expected = {row_sum(first, line).rows for line in
                        enumerate_subspaces(second, 1, unlimited())}
            observed = set()
            budget = unlimited()
            _exact_local_relay_search(
                task, 3, 3, budget, allocations=[(1, (1, 1, 1))],
                accept=lambda uploads: observed.add(row_sum(*uploads).rows) or False)
            self.assertEqual(observed, expected)
            self.assertGreater(budget.counters.get('tight_groups_collapsed', 0), 0)
            # Without contraction there are (q+1)^3 local line tuples.
            self.assertLess(budget.states, (q + 1) ** 3)

    def test_rank_one_intersection_matches_full_nullspaces_over_extension_fields(self):
        rng = random.Random(20261007)
        for q in (2, 3, 4, 8, 9, 25):
            f = Field(q)
            for _ in range(12):
                space = row_basis(Matrix(f, [[rng.randrange(q) for _ in range(5)]
                                             for _ in range(4)], 5))
                row = tuple(rng.randrange(q) for _ in range(5))
                values = _hyperplane_values(space, row)
                actual = _restrict_hyperplane(space, values, unlimited())
                expected = intersection(space, nullspace(Matrix(f, [row], 5)))
                self.assertEqual(row_basis(actual), expected)
                self.assertEqual(actual.nrows, space.nrows - bool(any(values)))

    def test_incremental_dual_leaves_equal_complete_normal_oracle(self):
        for q in (2, 3, 4, 9):
            f, n = Field(q), (3 if q == 9 else 4)
            e = eye(f, n)
            sides = (Matrix(f, e.rows[:2], n), Matrix(f, e.rows[1:], n), e)
            demand_cases = ((zeros(f, 0, n),) * 3,
                            (Matrix(f, [e.rows[-1]], n), Matrix(f, [e.rows[0]], n),
                             zeros(f, 0, n)))
            for demands in demand_cases:
                task = Task(f, sides, demands)
                expected = []
                for normal in enumerate_subspaces(e, 2, unlimited()):
                    spaces = normal_relay_spaces(task.side, task.augmented, normal)
                    if spaces is not None:
                        expected.append(spaces[0].rows)
                budget = unlimited()
                actual = [relay.rows for relay, _, _ in
                          _normal_kernel_prefixes(task, 2, budget, lambda *_: True)]
                self.assertEqual(actual, expected, (q, demands))
                self.assertGreater(budget.counters.get('dual_kernel_rank_one_updates', 0), 0)

    def test_successful_scalar_candidate_does_not_request_later_recognizers(self):
        task = resonant_task(Field(2), 2)
        with patch('three_user_codes.compiler._resonant_choices',
                   side_effect=AssertionError('eager expensive recognition')):
            result = compile_task(task)
        self.assertEqual(result.certificate.blocklength, 1)
        self.assertTrue(result.verify(task))

    def test_streamed_two_instance_cross_pair_stops_before_unused_third_candidate(self):
        for q in (2, 3, 4):
            task = resonant_task(Field(q), 1)
            candidates = list(_scalar_choices(task, Fraction(4), unlimited()))

            def stream():
                yield from candidates[:2]
                raise AssertionError('unnecessary third relay requested')

            with patch('three_user_codes.compiler._scalar_choices', return_value=stream()):
                result = compile_task(task)
            self.assertEqual(result.certificate.blocklength, 2)
            self.assertEqual(result.strategy, 'constructive-scalar-relay-combination')
            self.assertTrue(result.verify(task))

    def test_failed_broadcast_construction_advances_stream(self):
        task = resonant_task(Field(3), 2)
        calls = []

        def broadcast(*args, **kwargs):
            calls.append(1)
            if len(calls) == 1:
                return None
            return _complete_broadcast(*args, **kwargs)

        with patch('three_user_codes.compiler._complete_broadcast', side_effect=broadcast):
            result = compile_task(task)
        self.assertEqual(len(calls), 2)
        self.assertTrue(result.verify(task))

    def test_full_relay_skips_scalar_candidate_generation(self):
        f = Field(2)
        side = tuple(Matrix(f, [row], 3) for row in eye(f, 3).rows)
        task = Task(f, side, (side[1], side[2], side[0]))
        with patch('three_user_codes.compiler._scalar_choices',
                   side_effect=AssertionError('unnecessary scalar candidates')):
            result = compile_task(task)
        self.assertEqual(result.strategy, 'full-relay')
        self.assertTrue(result.verify(task))

    def test_repeated_components_dispatch_before_scalar_and_probe_work(self):
        component = resonant_task(Field(3), 3)
        task = Task(component.field,
                    tuple(block_diag(a, a) for a in component.side),
                    tuple(block_diag(w, w) for w in component.demand))
        with patch('three_user_codes.compiler._scalar_choices',
                   side_effect=AssertionError('repeated components need no scalar warm menu')), \
             patch('three_user_codes.compiler._exact_relay_probe',
                   side_effect=AssertionError('repeated components need no ambient probe')):
            result = compile_task(task)
        self.assertEqual(result.strategy, 'constructive-structural-components')
        self.assertEqual(result.stats['search_counters']['early_structural_dispatches'], 1)
        self.assertEqual(result.stats['search_counters']['structural_constructor_attempts'], 1)
        self.assertTrue(result.verify(task))

    def test_unrecognized_early_structure_is_not_retried_before_exact_fallback(self):
        from three_user_codes.structural_compiler import structural_relay_candidates
        component = resonant_task(Field(3), 1)
        task = Task(component.field,
                    tuple(block_diag(a, a) for a in component.side),
                    tuple(block_diag(w, w) for w in component.demand))
        relay = next(structural_relay_candidates(task, 1, 8, 3, unlimited()))
        candidate = _accept(task, relay, 8, 3)

        def exact(current, upload, broadcast, budget, cache, accept):
            self.assertTrue(accept(candidate))
            return candidate

        with patch('three_user_codes.structural_compiler.structural_relay_candidates',
                   return_value=()) as structural, \
             patch('three_user_codes.compiler._scalar_choices', return_value=()), \
             patch('three_user_codes.compiler._exact_relay_probe', return_value=None), \
             patch('three_user_codes.active_relay.active_relay_uploads', return_value=None), \
             patch('three_user_codes.compiler._exact_relay_search', side_effect=exact):
            result = compile_task(task)
        structural.assert_called_once()
        self.assertEqual(result.strategy, 'exact-local-subspace-search')
        self.assertTrue(result.verify(task))

    def test_large_single_relation_keeps_lazy_scalar_priority(self):
        task = resonant_task(Field(2), 4)
        with patch('three_user_codes.structural_compiler.structural_relay_candidates',
                   side_effect=AssertionError('single relation should stay on its lazy path')):
            result = compile_task(task)
        self.assertEqual(result.strategy, 'constructive-scalar-relay-combination')
        self.assertNotIn('early_structural_dispatches', result.stats['search_counters'])
        self.assertTrue(result.verify(task))

    def test_unrecognized_early_structure_still_tries_scalar_candidate(self):
        from three_user_codes.structural_compiler import structural_relay_candidates
        component = resonant_task(Field(3), 1)
        task = Task(component.field,
                    tuple(block_diag(a, a) for a in component.side),
                    tuple(block_diag(w, w) for w in component.demand))
        relay = next(structural_relay_candidates(task, 1, 8, 3, unlimited()))
        order = []

        def unsupported(*args):
            order.append('structural')
            return ()

        def warm(*args):
            order.append('scalar')
            return (relay,)

        with patch('three_user_codes.structural_compiler.structural_relay_candidates',
                   side_effect=unsupported), \
             patch('three_user_codes.compiler._scalar_choices', side_effect=warm):
            result = compile_task(task)
        self.assertEqual(order, ['structural', 'scalar'])
        self.assertEqual(result.strategy, 'constructive-scalar-relay-combination')
        self.assertTrue(result.verify(task))


if __name__ == '__main__':
    unittest.main()
