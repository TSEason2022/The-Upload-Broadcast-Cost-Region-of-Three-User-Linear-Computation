import unittest
from fractions import Fraction
from random import Random

from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, eye, lift, zeros, vstack, rank
from three_user_codes.lcbc import build_lcbc, lcbc_parameters, _pair_basis


class LCBCTest(unittest.TestCase):
    def test_three_lines_one_symbol(self):
        for q in (3, 4, 5, 9):
            f = Field(q)
            A = [Matrix(f, [[1, 0]]), Matrix(f, [[0, 1]]), Matrix(f, [[1, 1]])]
            W = [eye(f, 2)] * 3
            code = build_lcbc(A, W)
            self.assertEqual(code.cost, 1)
            self.assertTrue(code.verify(A, W))
            self.assertEqual(code.broadcast, build_lcbc(A, W).broadcast)

    def test_aligned_cycle(self):
        f = Field(3)
        unit = eye(f, 3).rows
        A = [Matrix(f, [unit[i]]) for i in range(3)]
        W = [Matrix(f, [unit[(i + 1) % 3]]) for i in range(3)]
        code = build_lcbc(A, W)
        self.assertEqual(code.cost, 2)
        self.assertEqual(code.allocation['aligned'], 1)
        self.assertTrue(code.verify(A, W))

    def test_half_integral_requires_lift(self):
        for q in (3, 4, 5):
            f = Field(q)
            A = [Matrix(f, [[1, 1, 0]]), Matrix(f, [[1, 0, 1]]), Matrix(f, [[0, 1, 1]])]
            W = [Matrix(f, [[1, 0, 0]]), Matrix(f, [[0, 0, 1]]), Matrix(f, [[0, 1, 0]])]
            self.assertEqual(lcbc_parameters(A, W).cost, Fraction(3, 2))
            with self.assertRaises(ValueError):
                build_lcbc(A, W)
            AL, WL = [lift(a, 2) for a in A], [lift(w, 2) for w in W]
            code = build_lcbc(AL, WL)
            self.assertEqual(code.cost, 3)
            self.assertTrue(code.verify(AL, WL))

    def test_pair_basis_must_exchange(self):
        f = Field(3)
        # Greedily taking e1 from first blocks the second's only vector.
        first, second = eye(f, 2), Matrix(f, [[1, 0]])
        X, Y = _pair_basis(zeros(f, 0, 2), first, second, 1, 1)
        self.assertEqual(rank(vstack(X, Y)), 2)

    def test_redundant_rows_unused_source_and_empty_task(self):
        f = Field(3)
        A = [Matrix(f, [[1, 0, 0], [2, 0, 0], [0, 0, 0]])] * 3
        W = [Matrix(f, [[0, 1, 0], [0, 2, 0]])] * 3
        code = build_lcbc(A, W)
        self.assertTrue(code.verify(A, W))
        self.assertEqual(code.cost, 1)
        Z = zeros(f, 0, 0)
        self.assertTrue(build_lcbc([Z] * 3, [Z] * 3).verify([Z] * 3, [Z] * 3))

    def test_exact_random_regression(self):
        rng = Random(67401)
        for q in (3, 4, 5):
            f = Field(q)
            for d in range(1, 6):
                for case in range(5):
                    A = [Matrix(f, [[rng.randrange(q) for _ in range(d)]
                                    for _ in range(rng.randrange(d + 2))], ncols=d) for _ in range(3)]
                    W = [Matrix(f, [[rng.randrange(q) for _ in range(d)]
                                    for _ in range(rng.randrange(d + 2))], ncols=d) for _ in range(3)]
                    D = lcbc_parameters(A, W).cost
                    factor = D.denominator
                    AL, WL = [lift(a, factor) for a in A], [lift(w, factor) for w in W]
                    code = build_lcbc(AL, WL)
                    self.assertEqual(code.cost, D * factor)
                    self.assertTrue(code.verify(AL, WL))

    def test_binary_scalar_rejected(self):
        f = Field(2)
        # Integer LCBC optimum alone does not imply binary scalar achievability.
        sides = [Matrix(f, [[1, 0]]), Matrix(f, [[0, 1]]), Matrix(f, [[1, 1]])]
        with self.assertRaises(ValueError):
            build_lcbc(sides, [eye(f, 2)] * 3)


if __name__ == '__main__':
    unittest.main()
