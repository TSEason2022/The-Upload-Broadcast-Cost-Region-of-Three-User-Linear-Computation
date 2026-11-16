"""Theorem-minimal scalar synthesis and independent relay-search oracles."""
import unittest
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task, compile_task
from three_user_codes.compiler import (_accept, _exact_relay_search,
                                       enumerate_subspaces)
from three_user_codes.errors import SearchBudgetExceeded
from three_user_codes.linalg import (eye, intersection, row_basis, row_sum,
                                     nullspace, zeros)
from three_user_codes.progress import SearchBudget
from three_user_codes.relay import normal_relay_spaces


class ScalarUpgradeTests(unittest.TestCase):
    @staticmethod
    def cycle(block=1):
        f=Field(2)
        identity=eye(f,3*block)
        side=tuple(Matrix(f,identity.rows[i*block:(i+1)*block],3*block)
                   for i in range(3))
        return Task(f,side,(side[1],side[2],side[0]))

    def test_exact_mode_preserves_scalar_length_beyond_old_dimension_cutoff(self):
        task=self.cycle(3)
        result=compile_task(task,fast_paths=False,max_states=10)
        self.assertEqual(result.certificate.blocklength,1)
        self.assertEqual(result.stats['minimum_linear_blocklength'],1)
        self.assertTrue(result.stats['blocklength_is_minimal'])
        self.assertEqual(result.stats['blocklength_policy'],'minimum')
        self.assertEqual(result.stats['search_counters']['dual_normal_candidates'],1)
        self.assertTrue(result.verify(task))

    def test_explicit_two_instances_reports_nonminimal_selection(self):
        task=self.cycle()
        result=compile_task(task,force_blocklength=2)
        self.assertEqual(result.certificate.blocklength,2)
        self.assertEqual(result.stats['minimum_linear_blocklength'],1)
        self.assertFalse(result.stats['blocklength_is_minimal'])
        self.assertEqual(result.stats['blocklength_policy'],'forced')
        self.assertTrue(result.verify(task))

    def test_global_budget_stop_never_silently_changes_blocklength(self):
        stages=[]
        with patch('three_user_codes.compiler._complete_broadcast',return_value=None):
            with self.assertRaises(SearchBudgetExceeded):
                compile_task(self.cycle(),fast_paths=False,max_states=1,
                             progress=lambda event: stages.append(event.stage))
        self.assertIn('relay-search-L1',stages)
        self.assertFalse(any('L2' in stage for stage in stages))

    def test_dual_image_reduction_matches_ambient_intersection_oracle(self):
        for q in (2,3,4):
            f=Field(q)
            identity=eye(f,3)
            side=(Matrix(f,identity.rows[:2],3),
                  Matrix(f,identity.rows[1:],3),
                  Matrix(f,[identity.rows[0]],3))
            augmented=(row_sum(side[0],side[1]),side[1],side[0])
            task=Task(f,side,augmented)
            for normal in enumerate_subspaces(identity,1,SearchBudget(None,None)):
                relay=row_basis(nullspace(normal))
                expected=_accept(task,relay,2,3)
                actual=normal_relay_spaces(task.side,task.augmented,normal)
                self.assertEqual(actual is None,expected is None)
                if actual is not None:
                    P,local,induced=actual
                    self.assertEqual(P,relay)
                    self.assertEqual(tuple(map(row_basis,local)),
                                     tuple(intersection(a,relay) for a in task.side))
                    self.assertEqual(tuple(map(row_basis,induced)),
                                     tuple(intersection(u,relay) for u in task.augmented))

    def test_quotient_enumeration_keeps_every_distinct_relay(self):
        f=Field(2)
        e=eye(f,4).rows
        side=(Matrix(f,[e[0],e[1]],4),Matrix(f,[e[1],e[2]],4),
              Matrix(f,[e[3]],4))
        task=Task(f,side,tuple(zeros(f,0,4) for _ in range(3)))
        expected={P.rows for P in enumerate_subspaces(eye(f,4),2,SearchBudget(None,None))
                  if _accept(task,P,2,0) is not None}
        actual=set()

        def collect(candidate):
            actual.add(row_sum(*candidate).rows)
            return False

        budget=SearchBudget(None,None)
        self.assertIsNone(_exact_relay_search(task,2,0,budget,accept=collect))
        self.assertEqual(actual,expected)
        self.assertGreater(budget.counters.get('quotient_local_enumerations',0),0)
        self.assertEqual(budget.counters['local_relay_searches'],1)


if __name__=='__main__':
    unittest.main()
