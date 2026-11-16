"""Independent exact-set scalar feasibility and arithmetic regression evidence."""
import importlib.util
from pathlib import Path
import unittest

from three_user_codes import Field, Matrix, Task, compile_task
from three_user_codes.lcbc import BinaryScalarRealizationUnavailable, build_lcbc
from three_user_codes.linalg import eye

PATH = Path(__file__).resolve().parents[1] / 'benchmarks' / 'independent_oracle.py'
SPEC = importlib.util.spec_from_file_location('independent_scalar_oracle', PATH)
oracle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(oracle)


class IndependentScalarUpgradeTests(unittest.TestCase):
    def test_explicit_subspace_enumeration_counts(self):
        for p, counts in ((2, (2, 5, 16)), (3, (2, 6, 28))):
            self.assertEqual([len(oracle.explicit_subspaces(p, n)) for n in (1,2,3)], list(counts))

    def test_sampled_joint_scalar_feasibility_matches_independent_oracle(self):
        report = oracle.run_oracle(seed=20261005, samples=96)
        self.assertTrue(report['all_comparisons_matched'])
        self.assertGreater(report['status_counts'].get('feasibility_matched', 0), 80)
        self.assertEqual({row['q'] for row in report['records']}, {2,3})

    def test_binary_broadcast_obstruction_still_rejected(self):
        # All three binary lines cover the plane. Every one-symbol signal is
        # already known to one receiver; the scalar LCBC obstruction is real.
        sides = tuple(oracle.vector_span(2, 2, (v,)) for v in ((1,0),(0,1),(1,1)))
        full = oracle.vector_span(2, 2, ((1,0),(0,1)))
        signals = [s for s in oracle.explicit_subspaces(2, 2) if len(s) == 2]
        self.assertFalse(any(all(full <= oracle.sum_space(2, side, signal) for side in sides)
                             for signal in signals))
        field = Field(2)
        A = tuple(Matrix(field, [vector], 2) for vector in ((1,0),(0,1),(1,1)))
        with self.assertRaises(BinaryScalarRealizationUnavailable):
            build_lcbc(A, (eye(field,2),)*3)

    def test_fast_paths_false_keeps_integral_instance_scalar(self):
        for q in (2,3,4,5,9):
            f = Field(q)
            side = tuple(Matrix(f, [row], 3) for row in eye(f,3).rows)
            task = Task(f, side, (side[1],side[2],side[0]))
            result = compile_task(task, fast_paths=False)
            self.assertEqual((result.upload_optimum, result.broadcast_optimum), (3,2))
            self.assertEqual(result.certificate.blocklength, 1)
            self.assertTrue(oracle.independent_code_check(result, task)['passed'])

    def test_round_up_fractional_profile_preserves_exact_decoding(self):
        # The two-instance optimum is 3/2. A valid two-symbol scalar code is
        # useful inside a relay whose allowed scalar target is already two.
        from three_user_codes import resonant_task
        task = resonant_task(Field(3), 1)
        with self.assertRaises(ValueError):
            build_lcbc(task.side, task.demand)
        code = build_lcbc(task.side, task.demand, round_up=True)
        self.assertEqual(code.broadcast.nrows, 2)
        signal = oracle.vector_span(3, task.n, code.broadcast.rows)
        for side, demand in zip(task.side, task.demand):
            a = oracle.vector_span(3, task.n, side.rows)
            w = oracle.vector_span(3, task.n, demand.rows)
            self.assertLessEqual(w, oracle.sum_space(3, a, signal))


if __name__ == '__main__':
    unittest.main()
