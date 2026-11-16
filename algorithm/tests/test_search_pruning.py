"""Exact pruning checked against independent finite sets over GF(2)/GF(3)."""
import importlib.util
from itertools import product
from pathlib import Path
import unittest

from three_user_codes import Field, Matrix, Task
from three_user_codes.compiler import (
    _exact_dual_relay_search, _exact_local_relay_search, _exact_relay_search, _normal_prefixes,
    _residual_upload_spaces, enumerate_subspaces,
)
from three_user_codes.errors import SearchBudgetExceeded
from three_user_codes.linalg import eye, row_sum, zeros
from three_user_codes.progress import SearchBudget


PATH = Path(__file__).resolve().parents[1] / "benchmarks" / "independent_oracle.py"
SPEC = importlib.util.spec_from_file_location("search_pruning_oracle", PATH)
oracle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(oracle)


def unlimited():
    return SearchBudget(max_states=None, max_seconds=None)


def expected_relays(q, n, sides, demands, spaces, upload, download):
    result = set()
    for relay in spaces:
        if len(relay) != q ** upload:
            continue
        local = tuple(a & relay for a in sides)
        if oracle.sum_space(q, oracle.sum_space(q, local[0], local[1]), local[2]) != relay:
            continue
        if any(not w <= oracle.sum_space(q, a, relay) for a, w in zip(sides, demands)):
            continue
        if any(signal <= relay and len(signal) <= q ** download and
               all(w <= oracle.sum_space(q, a, signal) for a, w in zip(sides, demands))
               for signal in spaces):
            result.add(relay)
    return result


class SearchPruningTests(unittest.TestCase):
    def test_prefix_leaf_order_equals_complete_rref_enumeration(self):
        for q in (2, 3):
            for n in range(4):
                for codimension in range(n + 1):
                    expected = [a.rows for a in enumerate_subspaces(eye(Field(q), n), codimension, unlimited())]
                    actual = [a.rows for a in _normal_prefixes(Field(q), n, codimension,
                                                              unlimited(), lambda *_: True)]
                    self.assertEqual(actual, expected)

    def test_all_decodable_relays_survive_both_searches(self):
        # Every case is exhaustively checked; tasks include zero observations,
        # redundant source directions, binary scalar obstructions and q=3.
        comparisons = 0
        for task, sides, demands, spaces in oracle.oracle_cases(seed=20261006, samples=32):
            q, n = task.field.q, task.n
            for upload in range(n + 1):
                for download in {max(0, upload - 1), upload}:
                    expected = expected_relays(q, n, sides, demands, spaces, upload, download)
                    for search in (_exact_local_relay_search, _exact_dual_relay_search):
                        found = set()

                        def accept(uploads):
                            relay = oracle.vector_span(q, n, tuple(row for a in uploads for row in a.rows))
                            if relay in expected:
                                found.add(relay)
                            # Exhaust every candidate; no scalar-realizable
                            # completion may be lost by any pruning predicate.
                            return False

                        if search is _exact_dual_relay_search:
                            answer = search(task, upload, download, unlimited(), accept)
                        else:
                            answer = search(task, upload, download, unlimited(), accept=accept)
                        self.assertIsNone(answer)
                        self.assertEqual(found, expected, (q, n, upload, download, search.__name__))
                        comparisons += 1
        self.assertGreater(comparisons, 300)

    def test_tight_cut_forces_demand_line(self):
        f = Field(3)
        empty = zeros(f, 0, 3)
        demanded = Matrix(f, [(1, 1, 0)], 3)
        task = Task(f, (eye(f, 3), empty, empty), (empty, demanded, demanded))
        budget = unlimited()
        allowed = _residual_upload_spaces(task, empty, (0,), (1, 0, 0), budget)
        self.assertEqual(allowed[0], demanded)
        self.assertEqual(budget.counters["tight_cut_dimensions_removed"], 2)
        self.assertGreater(budget.counters["tight_cut_contractions"], 0)
        answer = _exact_local_relay_search(task, 1, 1, unlimited())
        self.assertEqual(row_sum(*answer), demanded)

    def test_residual_cut_rejects_insufficient_capacity(self):
        f = Field(2)
        e = eye(f, 3)
        empty = zeros(f, 0, 3)
        known = Matrix(f, [e.rows[1]], 3)
        demanded = Matrix(f, [e.rows[0], e.rows[2]], 3)
        task = Task(f, (e, known, empty), (empty, empty, demanded))
        budget = unlimited()
        self.assertIsNone(_residual_upload_spaces(task, known, (0,), (1, 1, 0), budget))
        self.assertEqual(budget.counters["pruned_residual_cut"], 1)

    def test_root_contraction_routes_to_unique_local_candidate(self):
        f = Field(2)
        empty = zeros(f, 0, 6)
        demanded = Matrix(f, [(0, 0, 0, 0, 0, 1)], 6)
        task = Task(f, (eye(f, 6), empty, empty), (empty, demanded, demanded))
        budget = unlimited()
        uploads = _exact_relay_search(task, 1, 1, budget)
        self.assertEqual(row_sum(*uploads), demanded)
        # Before contraction both primal and dual have [6 choose 1]_2=63
        # candidates. The tight cut leaves precisely one local candidate.
        self.assertEqual(budget.counters["local_relay_searches"], 1)
        self.assertEqual(budget.counters["root_cut_estimates"], 1)
        self.assertEqual(budget.counters["root_cut_estimate_reuses"], 1)
        self.assertNotIn("dual_relay_searches", budget.counters)
        self.assertEqual(budget.states, 1)

    def test_dual_prefix_pruning_and_counters_are_repeatable(self):
        f = Field(3)
        empty = zeros(f, 0, 3)
        demanded = Matrix(f, [(1, 0, 0)], 3)
        task = Task(f, (eye(f, 3), empty, empty), (empty, demanded, demanded))
        snapshots = []
        for _ in range(2):
            budget = unlimited()
            found = []
            _exact_dual_relay_search(task, 1, 1, budget,
                                     lambda uploads: found.append(row_sum(*uploads).rows) or False)
            self.assertEqual(found, [demanded.rows])
            self.assertGreater(budget.counters.get("dual_pruned_prefix_infeasible", 0), 0)
            snapshots.append((budget.states, budget.counters))
        self.assertEqual(*snapshots)

    def test_prefix_nodes_obey_state_budget(self):
        budget = SearchBudget(max_states=1, max_seconds=None)
        with self.assertRaises(SearchBudgetExceeded):
            list(_normal_prefixes(Field(2), 4, 2, budget, lambda *_: True))

    def test_optimistic_local_capacity_pruning_preserves_all_product_spaces(self):
        f = Field(2)
        e = eye(f, 6)
        side = tuple(Matrix(f, [e.rows[i], e.rows[i + 3]], 6) for i in range(3))
        task = Task(f, side, (zeros(f, 0, 6),) * 3)
        # The side spaces are a direct sum. A locally generated relay is
        # exactly a direct sum of three independently chosen local spaces.
        local_choices = []
        for i in range(3):
            choices = []
            for local in oracle.explicit_subspaces(2, 2):
                choices.append(frozenset(tuple(v[0] if j == i else v[1] if j == i + 3 else 0
                                               for j in range(6)) for v in local))
            local_choices.append(choices)
        expected = set()
        for local in product(*local_choices):
            relay = oracle.sum_space(2, oracle.sum_space(2, local[0], local[1]), local[2])
            if len(relay) == 8:
                expected.add(relay)
        found = set()
        budget = unlimited()

        def accept(uploads):
            found.add(oracle.vector_span(2, 6, tuple(row for a in uploads for row in a.rows)))
            return False

        _exact_dual_relay_search(task, 3, 3, budget, accept)
        self.assertEqual(len(expected), 45)
        self.assertEqual(found, expected)
        self.assertGreater(budget.counters.get("dual_pruned_prefix_capacity", 0), 0)

    def test_optimistic_profile_pruning_uses_feasible_super_relay(self):
        f = Field(2)
        e = eye(f, 6)
        side = tuple(Matrix(f, [e.rows[i], e.rows[i + 3]], 6) for i in range(3))
        demand = tuple(Matrix(f, [e.rows[(i + 1) % 3 + 3]], 6) for i in range(3))
        task = Task(f, side, demand)
        # A directed three-cycle of independent requested symbols needs two
        # broadcasts; the three extra private nuisance symbols cannot lower it.
        budget = unlimited()
        self.assertIsNone(_exact_dual_relay_search(task, 3, 1, budget, None))
        self.assertGreater(budget.counters.get("dual_pruned_prefix_profile", 0), 0)
        accepted = _exact_dual_relay_search(task, 3, 2, unlimited(), None)
        self.assertIsNotNone(accepted)


if __name__ == "__main__":
    unittest.main()
