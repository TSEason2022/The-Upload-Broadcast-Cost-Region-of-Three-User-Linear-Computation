"""A local warm-start stop must never swallow global resource controls."""
import threading
import unittest
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task, compile_task
from three_user_codes.compiler import _exact_relay_probe, _exact_relay_search
from three_user_codes.errors import CompilationCancelled, SearchBudgetExceeded
from three_user_codes.linalg import eye
from three_user_codes.progress import SearchBudget


class SameLengthProbeTests(unittest.TestCase):
    def test_private_stop_is_bounded_and_fallback_budget_stays_live(self):
        budget = SearchBudget(None, None)

        def run(task, r, s, limited, cache, accept):
            for _ in range(100):
                limited.tick()

        with patch('three_user_codes.compiler._exact_relay_search', side_effect=run):
            self.assertIsNone(_exact_relay_probe(None, 1, 1, budget, max_states=3))
        self.assertEqual(budget.states, 3)
        self.assertEqual(budget.counters['same_length_probe_stops'], 1)
        budget.tick()
        self.assertEqual(budget.states, 4)

    def test_global_state_limit_propagates_unchanged(self):
        budget = SearchBudget(1, None)

        def run(task, r, s, limited, cache, accept):
            limited.tick()
            limited.tick()

        with patch('three_user_codes.compiler._exact_relay_search', side_effect=run):
            with self.assertRaises(SearchBudgetExceeded):
                _exact_relay_probe(None, 1, 1, budget)
        self.assertNotIn('same_length_probe_stops', budget.counters)

    def test_global_time_exception_is_not_caught(self):
        budget = SearchBudget(None, None)
        error = SearchBudgetExceeded('global time limit', {})
        with patch('three_user_codes.compiler._exact_relay_search', side_effect=error):
            with self.assertRaises(SearchBudgetExceeded) as caught:
                _exact_relay_probe(None, 1, 1, budget)
        self.assertIs(caught.exception, error)

    def test_cancellation_is_forwarded_before_local_stop(self):
        event = threading.Event()
        budget = SearchBudget(None, None, cancel_event=event)

        def run(task, r, s, limited, cache, accept):
            limited.tick()
            event.set()
            limited.tick()

        with patch('three_user_codes.compiler._exact_relay_search', side_effect=run):
            with self.assertRaises(CompilationCancelled):
                _exact_relay_probe(None, 1, 1, budget, max_states=1)
        self.assertNotIn('same_length_probe_stops', budget.counters)

    def test_success_keeps_scalar_length_and_skips_active_setup(self):
        f = Field(2)
        e = eye(f, 3)
        side = tuple(Matrix(f, [row], 3) for row in e.rows)
        task = Task(f, side, (side[1], side[2], side[0]))
        # Disable sufficient fast candidates, preserving the genuine exact
        # search and broadcast construction inside the warm start.
        with patch('three_user_codes.compiler._scalar_choices', return_value=[]), \
             patch('three_user_codes.compiler._accept', return_value=None), \
             patch('three_user_codes.active_relay.active_relay_uploads') as active:
            result = compile_task(task)
        active.assert_not_called()
        self.assertEqual(result.strategy, 'exact-same-length-probe')
        self.assertEqual(result.certificate.blocklength, 1)
        self.assertEqual(result.stats['search_counters']['same_length_probe_successes'], 1)
        self.assertTrue(result.verify(task))

    def test_stopped_probe_keeps_scalar_length_for_complete_fallback(self):
        f = Field(2)
        side = tuple(Matrix(f, [row], 3) for row in eye(f, 3).rows)
        task = Task(f, side, (side[1], side[2], side[0]))
        calls = []

        def run(current, r, s, budget, cache, accept):
            calls.append(current.n)
            if len(calls) == 1:
                for _ in range(33):
                    budget.tick()
            return _exact_relay_search(current, r, s, budget, cache, accept)

        with patch('three_user_codes.compiler._scalar_choices', return_value=[]), \
             patch('three_user_codes.compiler._accept', return_value=None), \
             patch('three_user_codes.compiler._exact_relay_search', side_effect=run), \
             patch('three_user_codes.active_relay.active_relay_uploads', return_value=None):
            result = compile_task(task)
        self.assertEqual(calls, [3, 3])
        self.assertEqual(result.certificate.blocklength, 1)
        self.assertEqual(result.stats['search_counters']['same_length_probe_states'], 32)
        self.assertEqual(result.stats['search_counters']['same_length_probe_stops'], 1)
        self.assertTrue(result.verify(task))


if __name__ == '__main__':
    unittest.main()
