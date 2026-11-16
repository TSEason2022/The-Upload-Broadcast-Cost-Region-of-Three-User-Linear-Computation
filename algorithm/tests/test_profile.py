"""Semantic cost checks, decomposition invariance, and exact small examples."""
import unittest
from fractions import Fraction
from random import Random

from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, block_diag, eye, rank, row_basis, row_sum
from three_user_codes.task import Task
from three_user_codes.profile import broadcast_profile
from three_user_codes.upload_bound import side_normal_form, upload_cost, upload_parameters


class CostTests(unittest.TestCase):
    def five_bit(self, q=2):
        f = Field(q)
        def m(rows):
            return Matrix(f, rows, ncols=5)
        a = (m([[1, 0, 0, 0, 0], [0, 0, 0, 1, 0]]),
             m([[0, 1, 0, 0, 0], [0, 0, 0, 0, 1]]),
             m([[0, 0, 1, 0, 0], [0, 0, 0, 1, 1]]))
        w = (m([[0, 1, 1, 0, 0]]), m([[1, 0, 1, 0, 0]]), m([[1, 1, 0, 1, 0]]))
        return Task(f, a, w)

    def test_five_bit(self):
        task = self.five_bit()
        p = upload_parameters(task)
        self.assertEqual((p.rho, p.r0, p.b, p.c, p.tau), (3, 0, 1, 0, (0, 0, 0)))
        self.assertEqual(p.cost, 4)
        profile = broadcast_profile(task.side, task.augmented)
        self.assertEqual(profile.first, (1,) * 6)
        self.assertEqual(profile.second, (Fraction(3, 2),) * 9)

    def test_tripod_omniscience(self):
        for q in (2, 3, 4, 5, 9):
            f = Field(q)
            side = (Matrix(f, [[1, 0]]), Matrix(f, [[0, 1]]), Matrix(f, [[f.neg(1), 1]]))
            task = Task(f, side, (eye(f, 2),) * 3)
            p = upload_parameters(task)
            self.assertEqual((p.rho, p.r0, p.b, p.c, p.tau), (0, 0, 0, 1, (0, 0, 0)))
            self.assertEqual(p.cost, Fraction(3, 2))
            self.assertEqual(broadcast_profile(side, task.augmented).cost, 1)

    def test_zero_and_common(self):
        f = Field(3)
        empty = Matrix(f, [], ncols=0)
        task = Task(f, (empty,) * 3, (empty,) * 3)
        self.assertEqual(upload_cost(task), 0)
        self.assertEqual(broadcast_profile(task.side, task.augmented).cost, 0)
        basis = eye(f, 3)
        task = Task(f, (basis,) * 3, (basis,) * 3)
        self.assertEqual(upload_cost(task), 0)
        self.assertEqual(broadcast_profile(task.side, task.augmented).cost, 0)

    def test_pair_only_omniscience(self):
        f = Field(3)
        side = (Matrix(f, [[0, 1, 0], [0, 0, 1]]),
                Matrix(f, [[1, 0, 0], [0, 0, 1]]),
                Matrix(f, [[1, 0, 0], [0, 1, 0]]))
        task = Task(f, side, (eye(f, 3),) * 3)
        p = upload_parameters(task)
        self.assertEqual((p.rho, p.r0, p.b, p.c, p.tau), (0, 0, 0, 0, (1, 1, 1)))
        self.assertEqual(p.cost, Fraction(3, 2))
        self.assertEqual(broadcast_profile(task.side, task.augmented).cost, 1)

    def test_private_cycle(self):
        f = Field(5)
        basis = eye(f, 3)
        side = tuple(Matrix(f, [row]) for row in basis.rows)
        demand = (side[1], side[2], side[0])
        task = Task(f, side, demand)
        self.assertEqual(upload_cost(task), 3)
        self.assertEqual(broadcast_profile(task.side, task.augmented).cost, 2)

    def test_lifts_scale_costs(self):
        task = self.five_bit()
        base = broadcast_profile(task.side, task.augmented)
        for length in (2, 3):
            lifted = task.lift(length)
            self.assertEqual(upload_cost(lifted), length * upload_cost(task))
            self.assertEqual(broadcast_profile(lifted.side, lifted.augmented).branches,
                             tuple(length * x for x in base.branches))

    def test_task_validates_inputs(self):
        f = Field(3)
        empty = Matrix(f, [], ncols=2)
        with self.assertRaises(ValueError):
            Task(f, (empty,) * 3, (eye(f, 2), empty, empty))
        task = Task(f, (eye(f, 2),) * 3, (empty,) * 3)
        with self.assertRaises(ValueError):
            task.lift(0)
        with self.assertRaises(ValueError):
            task.lift(True)

    def test_source_coordinate_and_row_basis_invariance(self):
        rng = Random(20260920)
        for q in (2, 3, 4, 5):
            f = Field(q)
            for n in range(1, 7):
                def mat(r, c):
                    return Matrix(f, [[rng.randrange(q) for _ in range(c)] for _ in range(r)], ncols=c)
                for repetition in range(5):
                    side = tuple(row_basis(mat(rng.randrange(n + 1), n)) for _ in range(3))
                    available = row_sum(*side)
                    demand = tuple(mat(rng.randrange(n + 1), available.nrows) @ available for _ in range(3))
                    task = Task(f, side, demand)
                    transform = mat(n, n)
                    while rank(transform) < n:
                        transform = mat(n, n)
                    transformed = Task(f, tuple(a @ transform for a in side), tuple(w @ transform for w in demand))
                    self.assertEqual(upload_parameters(task), upload_parameters(transformed), (q, n, repetition))
                    self.assertEqual(broadcast_profile(task.side, task.augmented),
                                     broadcast_profile(transformed.side, transformed.augmented))
                    self.assertEqual(side_normal_form(side).basis.nrows, available.nrows)


if __name__ == "__main__":
    unittest.main()
