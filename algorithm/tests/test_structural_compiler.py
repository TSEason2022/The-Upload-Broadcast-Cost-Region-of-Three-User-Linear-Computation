"""Automatic structural discovery, rather than supplied component labels."""
from fractions import Fraction
from itertools import permutations
import random
from threading import Event
import unittest
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task, resonant_task
from three_user_codes.certificate import make_certificate
from three_user_codes.compiler import CompileResult, _accept, _complete_broadcast
from three_user_codes.errors import CompilationCancelled, SearchBudgetExceeded
from three_user_codes.linalg import block_diag, eye, rank
from three_user_codes.profile import broadcast_profile
from three_user_codes.progress import SearchBudget
from three_user_codes.provenance import task_fingerprint
from three_user_codes.structural_compiler import (
    _discover_split, _endomorphisms, _fitting_split, structural_relay_candidates,
)
from three_user_codes.upload_bound import upload_parameters


def direct_sum(*tasks):
    return Task(tasks[0].field,
                tuple(block_diag(*(t.side[i] for t in tasks)) for i in range(3)),
                tuple(block_diag(*(t.demand[i] for t in tasks)) for i in range(3)))


def cycle(field, positive=True):
    unit = eye(field, 3)
    side = tuple(Matrix(field, [unit.rows[i]], 3) for i in (2, 1, 0))
    order = (1, 2, 0) if positive else (2, 0, 1)
    return Task(field, side, tuple(side[i] for i in order))


def pair_omniscience(field):
    unit = eye(field, 3)
    side = tuple(Matrix(field, [unit.rows[j] for j in range(3) if j != i], 3)
                 for i in range(3))
    return Task(field, side, (unit, unit, unit))


def dense(task, seed=20261007):
    rng, f, n = random.Random(seed), task.field, task.n
    upper = Matrix(f, [[int(i == j) if j <= i else rng.randrange(f.q)
                        for j in range(n)] for i in range(n)], n)
    lower = Matrix(f, [[int(i == j) if j >= i else rng.randrange(f.q)
                        for j in range(n)] for i in range(n)], n)
    transform = upper @ lower
    return Task(f, tuple(a @ transform for a in task.side),
                tuple(w @ transform for w in task.demand))


class StructuralCompilerTests(unittest.TestCase):
    def build(self, task, forced_length=None):
        upload = upload_parameters(task).cost
        broadcast = broadcast_profile(task.side, task.augmented).cost
        length = forced_length or (1 if upload.denominator == broadcast.denominator == 1 else 2)
        budget = SearchBudget(10000, 15)
        candidates = list(structural_relay_candidates(
            task, length, int(length * upload), int(length * broadcast), budget))
        self.assertEqual(len(candidates), 1)
        lifted = task if length == 1 else task.lift(length)
        uploads = _accept(lifted, candidates[0], int(length * upload), int(length * broadcast))
        self.assertIsNotNone(uploads)
        code = _complete_broadcast(lifted, uploads, int(length * broadcast), budget=budget)
        self.assertIsNotNone(code)
        certificate = make_certificate(lifted, uploads, code, blocklength=length,
                                       base_field=task.field,
                                       expected_upload_count=int(length * upload),
                                       expected_broadcast_count=int(length * broadcast))
        result = CompileResult(certificate, upload, broadcast, "structural-test", {},
                               task_fingerprint(task))
        result.verify(task)
        self.assertEqual(certificate.base_field, task.field)
        return budget, result

    def test_repeated_and_heterogeneous_models_over_original_fields(self):
        for q, sizes in ((2, (1, 1, 1)), (2, (2, 2)), (3, (1, 2)),
                         (3, (3, 3)), (4, (1, 2)), (9, (2, 1))):
            with self.subTest(q=q, sizes=sizes):
                f = Field(q)
                task = dense(direct_sum(*(resonant_task(f, n) for n in sizes)))
                budget, _ = self.build(task)
                self.assertEqual(budget.counters["structural_resonant_components"], len(sizes))
                self.assertEqual(budget.counters["structural_verified_splits"], len(sizes) - 1)

    def test_multiple_cycle_repairs_both_orientations(self):
        for q in (2, 3, 4, 9):
            for positive in (False, True):
                with self.subTest(q=q, positive=positive):
                    f = Field(q)
                    bundle = direct_sum(resonant_task(f, 1), cycle(f, positive))
                    budget, result = self.build(dense(direct_sum(bundle, bundle)))
                    key = "structural_positive_cycle_repairs" if positive else "structural_negative_cycle_repairs"
                    self.assertEqual(budget.counters.get(key), 2)
                    self.assertEqual(result.upload_optimum, 14)
                    self.assertEqual(result.broadcast_optimum, 6)
                    self.assertEqual(result.certificate.blocklength, 1)

    def test_half_integral_target_and_active_omniscience(self):
        for q in (2, 4, 9):
            with self.subTest(q=q):
                f = Field(q)
                task = dense(direct_sum(resonant_task(f, 1), resonant_task(f, 2),
                                        pair_omniscience(f)))
                _, result = self.build(task)
                self.assertEqual(result.certificate.blocklength, 2)
                self.assertEqual(result.upload_optimum, Fraction(25, 2))

    def test_user_permutations_preserve_automatic_discovery(self):
        f = Field(3)
        bundle = direct_sum(resonant_task(f, 1), cycle(f))
        task = dense(direct_sum(bundle, bundle))
        for order in permutations(range(3)):
            with self.subTest(order=order):
                permuted = Task(f, tuple(task.side[i] for i in order),
                                tuple(task.demand[i] for i in order))
                self.build(permuted)

    def test_zero_excess_remainder_need_not_be_classified(self):
        f = Field(3)
        independent = Task.from_rows(f, [[[1, 0, 0]], [[0, 1, 0]], [[0, 0, 1]]],
                                     [[[0, 1, 1]], [[1, 0, 1]], [[1, 2, 0]]])
        self.build(dense(direct_sum(resonant_task(f, 1), independent)))

    def test_fitting_projectors_reconstruct_every_flag(self):
        f = Field(4)
        task = dense(direct_sum(resonant_task(f, 1), resonant_task(f, 2)))
        split = _discover_split(task, SearchBudget(None, None))
        self.assertIsNotNone(split)
        self.assertTrue(split.verify(task))
        self.assertEqual(sum(c.task.n for c in split.components), task.n)
        again = _discover_split(task, SearchBudget(None, None))
        self.assertEqual(split, again)

    def test_nonscalar_nilpotent_is_not_a_decomposition(self):
        task = dense(resonant_task(Field(3), 3))
        budget = SearchBudget(None, None)
        nilpotents = []
        for endomorphism in _endomorphisms(task, budget):
            if rank(endomorphism) == 0:
                continue
            power = endomorphism
            for _ in range(task.n.bit_length() + 1):
                power = power @ power
            if rank(power) == 0:
                nilpotents.append(endomorphism)
        self.assertTrue(nilpotents)
        for endomorphism in nilpotents:
            self.assertIsNone(_fitting_split(task, endomorphism, budget))

    def test_unrecognized_family_returns_to_complete_fallback(self):
        f = Field(2)
        a, b = Matrix(f, [[1, 0]], 2), Matrix(f, [[0, 1]], 2)
        task = Task(f, (a, b, a + b), (a, eye(f, 2), a + b))
        budget = SearchBudget(None, None)
        self.assertEqual(list(structural_relay_candidates(task, 1, 1, 1, budget)), [])
        self.assertIn("structural_unrecognized_remainders", budget.counters)

    def test_local_probe_stop_does_not_swallow_global_limits(self):
        task = direct_sum(resonant_task(Field(2), 1), resonant_task(Field(2), 1))
        def consume(*args):
            args[-1].tick(513)
        with patch("three_user_codes.structural_compiler._construct", side_effect=consume):
            budget = SearchBudget(None, None)
            self.assertEqual(list(structural_relay_candidates(task, 1, 8, 3, budget)), [])
            self.assertEqual(budget.counters["structural_probe_stops"], 1)
        with self.assertRaises(SearchBudgetExceeded):
            list(structural_relay_candidates(task, 1, 8, 3, SearchBudget(1, None)))
        token = Event()
        token.set()
        with self.assertRaises(CompilationCancelled):
            list(structural_relay_candidates(task, 1, 8, 3,
                                            SearchBudget(None, None, cancel_event=token)))

    def test_algebra_size_guard_precedes_dense_system_allocation(self):
        task = direct_sum(*(resonant_task(Field(2), 1) for _ in range(17)))
        budget = SearchBudget(None, None)
        with patch("three_user_codes.structural_compiler._task_normal_form",
                   side_effect=AssertionError("size guard must run first")):
            self.assertEqual(_endomorphisms(task, budget), ())
        self.assertEqual(budget.counters["structural_algebra_size_skips"], 1)


if __name__ == "__main__":
    unittest.main()
