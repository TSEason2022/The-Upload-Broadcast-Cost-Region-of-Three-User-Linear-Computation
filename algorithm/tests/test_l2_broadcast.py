"""Original-field broadcast regressions for Lemmas 21--24 / Proposition 25."""
from fractions import Fraction
from itertools import permutations, product
from random import Random
import unittest

from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, block_diag, eye, lift, rank, vstack, zeros
from three_user_codes.lcbc import (
    BinaryScalarRealizationUnavailable, _pair_basis, build_lcbc, lcbc_parameters,
)


class OriginalFieldBroadcastTest(unittest.TestCase):
    def test_binary_aligned_cycle_uses_original_field(self):
        f = Field(2)
        unit = eye(f, 3).rows
        sides = [Matrix(f, [unit[i]]) for i in range(3)]
        demands = [Matrix(f, [unit[(i + 1) % 3]]) for i in range(3)]
        code = build_lcbc(sides, demands)
        self.assertEqual(code.broadcast.field, f)
        self.assertEqual(code.broadcast.ncols, 3)
        self.assertEqual(code.broadcast.nrows, 2)
        self.assertEqual(code.allocation['aligned'], 1)
        self.assertEqual(code.stats['binary_separation_guarantee'], 1)
        self.assertTrue(code.verify(sides, demands))

    def test_binary_maximum_disjoint_common_block(self):
        f = Field(2)
        unit = eye(f, 3)
        sides = [Matrix(f, [unit.rows[i]]) for i in range(3)]
        demands = [unit] * 3
        code = build_lcbc(sides, demands)
        self.assertEqual(code.cost, 2)
        self.assertEqual(code.stats['fixed_common_columns'], 2)
        self.assertEqual(code.stats['groups'], 0)
        self.assertTrue(code.verify(sides, demands))

    def test_common_and_aligned_blocks_share_one_binary_construction(self):
        f = Field(2)
        unit = eye(f, 3)
        own = [Matrix(f, [unit.rows[i]]) for i in range(3)]
        sides = [block_diag(side, side) for side in own]
        demands = [block_diag(unit, own[(i + 1) % 3]) for i in range(3)]
        code = build_lcbc(sides, demands)
        self.assertGreater(code.allocation['common'], 0)
        self.assertGreater(code.allocation['aligned'], 0)
        self.assertEqual(code.stats['binary_separation_guarantee'], 1)
        self.assertTrue(code.verify(sides, demands))

    def test_separated_user_can_have_any_label(self):
        f = Field(2)
        unit = eye(f, 4)
        sides = [Matrix(f, [unit.rows[0]]),
                 Matrix(f, [unit.rows[1], unit.rows[2]]),
                 Matrix(f, [unit.rows[1], unit.rows[3]])]
        demands = [unit] * 3
        for order in permutations(range(3)):
            reordered = [sides[i] for i in order]
            code = build_lcbc(reordered, demands)
            self.assertEqual(code.stats['binary_separation_guarantee'], 1)
            self.assertEqual(code.stats['fixed_common_columns'], 2)
            self.assertTrue(code.verify(reordered, demands))

    def test_true_binary_scalar_obstruction_is_reported_without_lifting(self):
        f = Field(2)
        sides = [Matrix(f, [[1, 0]]), Matrix(f, [[0, 1]]), Matrix(f, [[1, 1]])]
        demands = [eye(f, 2)] * 3
        self.assertEqual(lcbc_parameters(sides, demands).cost, 1)
        with self.assertRaises(BinaryScalarRealizationUnavailable):
            build_lcbc(sides, demands)

    def test_empty_and_unobserved_common_tasks(self):
        f = Field(2)
        for d in (0, 1, 3):
            sides, demands = [zeros(f, 0, d)] * 3, [eye(f, d)] * 3
            code = build_lcbc(sides, demands)
            self.assertEqual(code.cost, d)
            self.assertTrue(code.verify(sides, demands))

    def test_binary_half_integral_only_explicit_lift(self):
        f = Field(2)
        sides = [Matrix(f, [[1, 0, 0, 0, 0], [0, 0, 0, 1, 0]]),
                 Matrix(f, [[0, 1, 0, 0, 0], [0, 0, 0, 0, 1]]),
                 Matrix(f, [[0, 0, 1, 0, 0], [0, 0, 0, 1, 1]])]
        demands = [Matrix(f, [row]) for row in
                   ((0, 1, 1, 0, 0), (1, 0, 1, 0, 0), (1, 1, 0, 1, 0))]
        self.assertEqual(lcbc_parameters(sides, demands).cost, Fraction(3, 2))
        with self.assertRaisesRegex(ValueError, 'two instances'):
            build_lcbc(sides, demands)
        AL, WL = [lift(a, 2) for a in sides], [lift(w, 2) for w in demands]
        code = build_lcbc(AL, WL)
        self.assertEqual(code.broadcast.field, f)
        self.assertEqual(code.broadcast.ncols, 10)
        self.assertEqual(code.broadcast.nrows, 3)
        self.assertTrue(code.verify(AL, WL))

    def test_separated_binary_random_exact_identities(self):
        rng = Random(20260930)
        f = Field(2)
        for d in range(1, 7):
            for case in range(12):
                # Invertible row operations obscure the separated coordinates.
                transform = [list(row) for row in eye(f, d).rows]
                for _ in range(3 * d):
                    i, j = rng.randrange(d), rng.randrange(d)
                    if i != j:
                        transform[i] = [x ^ y for x, y in zip(transform[i], transform[j])]
                units = Matrix(f, transform).rows
                groups = [[], [], []]
                for row in units:
                    label = rng.randrange(4)
                    if label < 3:
                        groups[label].append(row)
                    else:
                        groups[1].append(row)
                        groups[2].append(row)
                sides = [Matrix(f, rows, ncols=d) for rows in groups]
                demands = [Matrix(f, [[rng.randrange(2) for _ in range(d)]
                                     for _ in range(rng.randrange(d + 2))], ncols=d)
                           for _ in range(3)]
                cost = lcbc_parameters(sides, demands).cost
                length = cost.denominator
                AL, WL = [lift(a, length) for a in sides], [lift(w, length) for w in demands]
                code = build_lcbc(AL, WL)
                self.assertLessEqual(length, 2)
                self.assertEqual(code.cost, cost * length)
                self.assertEqual(code.broadcast.ncols, d * length)
                self.assertEqual(code.stats['binary_separation_guarantee'], 1)
                self.assertTrue(code.verify(AL, WL))
                self.assertEqual(code.broadcast, build_lcbc(AL, WL).broadcast)

    def test_two_colour_quotas_against_every_binary_plane_subspace(self):
        f = Field(2)
        spaces = [zeros(f, 0, 2), eye(f, 2)]
        spaces += [Matrix(f, [row]) for row in ((1, 0), (0, 1), (1, 1))]
        for base, first, second in product(spaces, repeat=3):
            r0 = base.nrows
            c1, c2 = rank(vstack(base, first)) - r0, rank(vstack(base, second)) - r0
            union = rank(vstack(base, first, second)) - r0
            for n1 in range(c1 + 1):
                for n2 in range(c2 + 1):
                    if n1 + n2 > union:
                        continue
                    X, Y = _pair_basis(base, first, second, n1, n2)
                    self.assertEqual((X.nrows, Y.nrows), (n1, n2))
                    self.assertEqual(rank(vstack(base, X, Y)), r0 + n1 + n2)
                    self.assertEqual(rank(vstack(first, X)), first.nrows)
                    self.assertEqual(rank(vstack(second, Y)), second.nrows)


if __name__ == '__main__':
    unittest.main()
