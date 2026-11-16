"""Exact quotient-map invariants on prime fields and extension fields."""

import unittest
from random import Random
from unittest.mock import patch

from three_user_codes.field import Field
from three_user_codes.lcbc import _quotient_projection, build_lcbc
from three_user_codes.linalg import (Matrix, extend_basis, nullspace, rank,
                                     row_basis, row_sum, rref, zeros)


class QuotientProjectionTest(unittest.TestCase):
    def test_random_maps_match_annihilator_and_preserve_quotient(self):
        rng = Random(126891)
        for q in (2, 3, 4, 5, 8, 9):
            f = Field(q)
            for d in range(13):
                for case in range(8):
                    with self.subTest(q=q, dimension=d, case=case):
                        def random_matrix(n):
                            return Matrix(f, ([rng.randrange(q) for _ in range(d)]
                                              for _ in range(n)), ncols=d)

                        raw_side = random_matrix(rng.randrange(d + 3))
                        side = row_basis(raw_side)
                        augmented = row_sum(side, random_matrix(rng.randrange(d + 2)))
                        basis = extend_basis(side, augmented, augmented.nrows)
                        selected = Matrix(f, basis.rows[side.nrows:], ncols=d)
                        m = augmented.nrows - side.nrows
                        projection = _quotient_projection(raw_side, selected)

                        # An independent ambient-space annihilator is the old
                        # construction, including all unused source directions.
                        annihilator = nullspace(side)
                        _, columns = rref(selected @ annihilator.T)
                        reference = Matrix(f, (annihilator.rows[j] for j in columns),
                                           ncols=d).T
                        probes = random_matrix(d + 3)
                        self.assertEqual(projection.apply(probes), probes @ reference)
                        self.assertEqual(projection.apply(raw_side), zeros(f, raw_side.nrows, m))
                        self.assertEqual(rank(projection.apply(selected)), m)
                        self.assertEqual(rank(projection.apply(augmented)), m)
                        self.assertEqual(projection.coefficients.ncols, m)
                        self.assertLessEqual(projection.coefficients.nrows, side.nrows)

    def test_zero_demand_skips_factorization(self):
        f = Field(3)
        side = Matrix(f, [[1, 0, 2], [0, 1, 2]])
        with patch('three_user_codes.lcbc.row_basis', side_effect=AssertionError), \
                patch('three_user_codes.lcbc.rref', side_effect=AssertionError):
            projection = _quotient_projection(side, zeros(f, 0, 3))
            self.assertEqual(projection.apply(side), zeros(f, 2, 0))

    def test_dependent_conditional_rows_are_rejected(self):
        f = Field(3)
        side = Matrix(f, [[1, 0, 0]])
        with self.assertRaisesRegex(ArithmeticError, 'quotient lost rank'):
            _quotient_projection(side, Matrix(f, [[0, 1, 0], [1, 2, 0]]))

    def test_zero_coefficient_pivots_are_removed(self):
        f = Field(3)
        side = Matrix(f, [[1, 0, 0, 2, 0], [0, 1, 0, 0, 0]])
        selected = Matrix(f, [[0, 0, 0, 1, 0]])
        projection = _quotient_projection(side, selected)
        self.assertEqual(projection.pivots, (0,))
        self.assertEqual(projection.coefficients, Matrix(f, [[2]]))
        self.assertEqual(projection.apply(side), zeros(f, 2, 1))

        coordinate_side = Matrix(f, [[1, 0, 0], [0, 1, 0]])
        projection = _quotient_projection(coordinate_side, Matrix(f, [[0, 0, 1]]))
        self.assertEqual(projection.pivots, ())
        self.assertEqual(projection.coefficients.shape, (0, 1))
        probes = Matrix(f, [[1, 2, 1], [2, 1, 2]])
        with patch.object(Matrix, '__matmul__', side_effect=AssertionError):
            self.assertEqual(projection.apply(probes), Matrix(f, [[1], [2]]))

    def test_small_and_empty_decoder_quotients_with_unused_source(self):
        for q in (2, 3, 4, 9):
            f, d = Field(q), 48
            unit = lambda j: tuple(int(i == j) for i in range(d))
            side = Matrix(f, [unit(0), unit(1)])
            A = [side] * 3
            W = [side, Matrix(f, [unit(2)]), Matrix(f, [unit(2), unit(0)])]
            code = build_lcbc(A, W)
            self.assertEqual(code.cost, 1)
            self.assertEqual(code.stats['decoder_inverse_cells'], 2)
            self.assertTrue(code.verify(A, W))


if __name__ == '__main__':
    unittest.main()
