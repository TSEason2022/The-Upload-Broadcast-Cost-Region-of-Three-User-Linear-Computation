"""Scalar integer budgets and exact quotient-coordinate regressions."""
from fractions import Fraction
from random import Random
import unittest

from three_user_codes.coordination import (
    ColumnSpec, DecoderTemplate, avoid_linear_forms, coordinate_columns,
)
from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, eye, hstack, lift, rank, zeros
from three_user_codes.lcbc import (
    BinaryScalarRealizationUnavailable, build_lcbc, lcbc_parameters,
)


class ScalarBudgetUpgradeTest(unittest.TestCase):
    def test_half_integer_scalar_budget_over_original_fields(self):
        for q in (3, 4, 5, 9):
            f = Field(q)
            sides = [Matrix(f, [row]) for row in
                     ((1, 1, 0), (1, 0, 1), (0, 1, 1))]
            demands = [Matrix(f, [row]) for row in
                       ((1, 0, 0), (0, 0, 1), (0, 1, 0))]
            self.assertEqual(lcbc_parameters(sides, demands).cost, Fraction(3, 2))
            with self.assertRaisesRegex(ValueError, "two instances"):
                build_lcbc(sides, demands)
            code = build_lcbc(sides, demands, round_up=True)
            self.assertEqual(code.cost, 2)
            self.assertEqual(code.broadcast.shape, (2, 3))
            self.assertEqual(code.broadcast.field, f)
            self.assertEqual(code.stats["rounded_scalar_cost"], 1)
            self.assertTrue(code.verify(sides, demands))
            exact = build_lcbc([lift(a, 2) for a in sides],
                               [lift(w, 2) for w in demands])
            self.assertEqual(exact.cost, 3)

    def test_binary_separated_ceil_budget(self):
        f = Field(2)
        sides = [Matrix(f, rows, ncols=4) for rows in
                 (((1, 0, 0, 0), (0, 0, 0, 1)),
                  ((0, 1, 0, 0),), ((0, 0, 1, 0),))]
        demands = [Matrix(f, rows, ncols=4) for rows in
                   (((0, 1, 0, 0), (0, 1, 0, 1)),
                    ((0, 1, 1, 1), (1, 0, 0, 0)),
                    ((1, 1, 1, 1), (1, 0, 0, 0)))]
        self.assertEqual(lcbc_parameters(sides, demands).cost, Fraction(5, 2))
        code = build_lcbc(sides, demands, round_up=True)
        self.assertEqual(code.broadcast.shape, (3, 4))
        self.assertEqual(code.stats["binary_separation_guarantee"], 1)
        self.assertTrue(code.verify(sides, demands))

    def test_rounding_does_not_claim_to_fix_binary_scalar_obstruction(self):
        f = Field(2)
        sides = [Matrix(f, [row]) for row in ((1, 0), (0, 1), (1, 1))]
        with self.assertRaises(BinaryScalarRealizationUnavailable):
            build_lcbc(sides, [eye(f, 2)] * 3, round_up=True)
        with self.assertRaises(TypeError):
            build_lcbc(sides, [eye(f, 2)] * 3, round_up=1)


class QuotientDecoderUpgradeTest(unittest.TestCase):
    def test_small_conditional_demands_in_dense_large_ambient(self):
        rng = Random(670213)
        for q in (2, 3, 4, 9):
            f, d = Field(q), 12
            transform = list(eye(f, d).rows)
            for _ in range(8 * d):
                i, j = rng.sample(range(d), 2)
                transform[i] = f.axpy(rng.randrange(1, q), transform[j], transform[i])
            basis = hstack(Matrix(f, transform), zeros(f, d, 5))
            sides, demands = [], []
            for i in range(3):
                # Original redundant rows and demanded known functions must
                # survive reconstruction of the user-facing decoder maps.
                rows = [row for j, row in enumerate(basis.rows) if j != i]
                sides.append(Matrix(f, rows + [rows[0]], ncols=d + 5))
                demands.append(Matrix(f, [basis.rows[i], basis.rows[i], rows[0]],
                                      ncols=d + 5))
            code = build_lcbc(sides, demands)
            self.assertEqual(code.cost, 1)
            self.assertEqual(code.broadcast.ncols, 17)
            self.assertEqual(code.stats["max_decoder_dimension"], 1)
            self.assertEqual(code.stats["decoder_inverse_cells"], 3)
            self.assertTrue(code.verify(sides, demands))
            for (C, H), a, w in zip(code.decoders, sides, demands):
                self.assertEqual(C.nrows, w.nrows)
                self.assertEqual(H.ncols, a.nrows)

    def test_different_quotient_orders_including_zero(self):
        for q in (2, 3, 4, 9):
            f, d = Field(q), 8
            units = eye(f, d)
            sides = [Matrix(f, units.rows[:k], ncols=d) for k in (8, 7, 5)]
            demands = [units, Matrix(f, units.rows[7:], ncols=d),
                       Matrix(f, units.rows[5:], ncols=d)]
            code = build_lcbc(sides, demands)
            self.assertEqual(code.cost, 3)
            self.assertEqual(code.stats["max_decoder_dimension"], 3)
            self.assertEqual(code.stats["decoder_inverse_cells"], 10)
            self.assertTrue(code.verify(sides, demands))

    def test_random_rounded_codes_match_rank_lower_bound(self):
        rng = Random(38119)
        for q in (3, 4, 9):
            f = Field(q)
            for d in range(1, 6):
                for _ in range(8):
                    sides, demands = [], []
                    for target in (sides, demands):
                        target.extend(Matrix(f, [[rng.randrange(q) for _ in range(d)]
                                                 for _ in range(rng.randrange(d + 2))],
                                             ncols=d) for _ in range(3))
                    optimum = lcbc_parameters(sides, demands).cost
                    code = build_lcbc(sides, demands, round_up=True)
                    self.assertEqual(code.cost, -(-optimum.numerator // optimum.denominator))
                    self.assertEqual(rank(code.broadcast), code.cost)
                    self.assertTrue(code.verify(sides, demands))


class CoordinationUpgradeTest(unittest.TestCase):
    def test_binary_compatible_three_forms_and_many_decoders(self):
        f = Field(2)
        forms = eye(f, 3)
        self.assertEqual(avoid_linear_forms(forms), (1, 1, 1))
        templates = [DecoderTemplate(zeros(f, 1, 1),
                     (ColumnSpec(0, 0, Matrix(f, [row], ncols=3)),))
                     for row in forms.rows]
        templates += [DecoderTemplate(eye(f, 2), ())] * 4
        witnesses = [[row] for row in forms.rows] + [[(0, 0, 0)]] * 4
        result = coordinate_columns(templates, witnesses)
        self.assertEqual(result.assignment, ((1, 1, 1),))
        self.assertTrue(all(rank(M) == M.nrows for M in result.matrices))

    def test_projectively_repeated_constraints_do_not_raise_field_size_error(self):
        for q in (3, 4, 9):
            f = Field(q)
            originals = [(1, 0), (0, 1), (1, 1)]
            forms = Matrix(f, [tuple(f.mul(a, value) for value in row)
                               for row in originals for a in range(1, q)])
            x = avoid_linear_forms(forms)
            self.assertTrue(all(f.dot(row, x) for row in forms.rows))


if __name__ == "__main__":
    unittest.main()
