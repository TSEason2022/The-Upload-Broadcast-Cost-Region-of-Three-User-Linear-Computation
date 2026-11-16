import unittest
from itertools import permutations

from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, contains, intersection, rank, row_basis, vstack
from three_user_codes.profile import broadcast_profile
from three_user_codes.relay import RelaySelectionError, corank_one, corank_two


def matrices(q, rows):
    return tuple(Matrix(Field(q), x) for x in rows)


class RelayTests(unittest.TestCase):
    def check_relay(self, side, augmented, relay, corank):
        self.assertEqual(relay.nrows, side[0].ncols - corank)
        local = tuple(intersection(a, relay) for a in side)
        induced = tuple(intersection(u, relay) for u in augmented)
        self.assertEqual(rank(vstack(*local)), relay.nrows)
        for a, u in zip(side, augmented):
            self.assertTrue(contains(row_basis(vstack(a, relay)), u))
        self.assertEqual(broadcast_profile(local, induced).second,
                         broadcast_profile(side, augmented).second)

    def test_corank_one_prime_and_extension(self):
        side_data = [[[0, 1, 0]], [[0, 0, 1]], [[1, 0, 0], [0, 1, 1]]]
        cases = [
            (3, [[[1, 0, 0], [0, 1, 0]], [[1, 2, 0], [0, 0, 1]], [[1, 0, 0], [0, 1, 1]]]),
            (4, [[[1, 0, 2], [0, 1, 0]], [[1, 0, 0], [0, 0, 1]], [[1, 0, 0], [0, 1, 1]]]),
            (5, [[[1, 0, 2], [0, 1, 0]], [[1, 3, 0], [0, 0, 1]], [[1, 0, 0], [0, 1, 1]]]),
        ]
        for q, aug in cases:
            side, augmented = matrices(q, side_data), matrices(q, aug)
            for arm in range(3):
                relay = corank_one(side, augmented, arm)
                self.check_relay(side, augmented, relay, 1)
                self.assertTrue(contains(relay, augmented[arm]))
                self.assertEqual(relay, corank_one(side, augmented, arm))

    def test_corank_two_all_arms_prime_and_extension(self):
        side_data = [[[1, 0, 0, 0], [0, 1, 0, 0]],
                     [[0, 0, 1, 0], [0, 0, 0, 1]],
                     [[1, 0, 1, 0], [0, 1, 0, 1]]]
        cases = [
            (3, [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1]],
                 [[1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
                 [[1, 0, 0, 1], [0, 1, 0, 1], [0, 0, 1, 2]]]),
            (4, [[[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 1]],
                 [[1, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]],
                 [[1, 0, 0, 2], [0, 1, 0, 1], [0, 0, 1, 2]]]),
        ]
        for q, aug in cases:
            side, augmented = matrices(q, side_data), matrices(q, aug)
            for arms in permutations(range(3), 2):
                self.check_relay(side, augmented, corank_two(side, augmented, arms), 2)

    def test_corank_two_longer_component(self):
        side = matrices(3, [
            [[1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]],
            [[0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]],
            [[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 1]],
        ])
        augmented = matrices(3, [
            [[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 2, 1], [0, 0, 1, 0, 0, 2, 2], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0]],
            [[1, 0, 2, 1, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]],
            [[1, 2, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 1], [0, 0, 0, 0, 0, 1, 0]],
        ])
        self.check_relay(side, augmented, corank_two(side, augmented), 2)

    def test_reject_invalid_hypotheses(self):
        side = matrices(3, [[[1, 0]], [[0, 1]], [[1, 1]]])
        with self.assertRaises(RelaySelectionError):
            corank_one(side, side, arm=3)
        with self.assertRaises(RelaySelectionError):
            corank_two(side, side)
        binary = matrices(2, [[[1, 0]], [[0, 1]], [[1, 1]]])
        with self.assertRaises(RelaySelectionError):
            corank_one(binary, binary)
        with self.assertRaises(RelaySelectionError):
            corank_one(side, (side[0], side[0], side[2]))


if __name__ == "__main__":
    unittest.main()
