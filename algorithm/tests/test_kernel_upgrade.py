"""Exact quotient-profile and batched coordinate regressions across fields."""
from fractions import Fraction
from itertools import permutations
from random import Random
import unittest

from three_user_codes import Field, Matrix, Task
from three_user_codes.linalg import (
    eye, intersection, rank, row_basis, row_sum, vstack,
)
from three_user_codes.profile import broadcast_profile
from three_user_codes.upload_bound import UploadParameters, upload_parameters


def intersection_profile(side, augmented):
    """Direct fifteen-branch definition, constructing every mixed subspace.

    Keep this independent of the production quotient-dimension identity and
    its shared joint rank, so an index or sign error changes the comparison.
    """
    side = tuple(row_basis(a) for a in side)
    augmented = tuple(row_basis(u) for u in augmented)
    deficit = sum(u.nrows - a.nrows for a, u in zip(side, augmented))
    conditional = lambda x, a: rank(vstack(x, a)) - rank(a)
    pairs = {(i, j): intersection(augmented[i], augmented[j])
             for i in range(3) for j in range(i + 1, 3)}
    pair = lambda i, j: pairs[tuple(sorted((i, j)))]
    mixed = tuple(intersection(augmented[i], row_sum(*(
        augmented[j] for j in range(3) if j != i))) for i in range(3))
    mr = tuple(conditional(mixed[i], side[i]) for i in range(3))
    first = tuple(Fraction(deficit - conditional(pair(i, j), side[j]) - mr[k])
                  for i, j, k in permutations(range(3)))
    triple = intersection(pair(0, 1), augmented[2])
    second = []
    for i in range(3):
        j, k = (h for h in range(3) if h != i)
        pair_sum = conditional(row_sum(pair(i, j), pair(i, k)), side[i])
        for ell in range(3):
            second.append(Fraction(2 * deficit - conditional(triple, side[ell])
                                   - pair_sum - mr[j] - mr[k], 2))
    return first + tuple(second)


class KernelUpgradeTests(unittest.TestCase):
    def test_quotient_profiles_against_direct_intersections(self):
        rng = Random(771906)
        for q in (2, 3, 4, 9, 343):
            field = Field(q)
            for n in range(9):
                for _ in range(3):
                    def matrix(m, width):
                        return Matrix(field, [[rng.randrange(q) for _ in range(width)]
                                              for _ in range(m)], ncols=width)
                    augmented = tuple(matrix(rng.randrange(n + 3), n) for _ in range(3))
                    # Arbitrary, possibly redundant side generators. This also
                    # includes fully informed servers whose demands lie outside
                    # the joint side span, and therefore have mixed rank < deficit.
                    side = tuple(matrix(rng.randrange(n + 2), u.nrows) @ u
                                 for u in augmented)
                    expected = intersection_profile(side, augmented)
                    actual = broadcast_profile(side, augmented)
                    with self.subTest(q=q, n=n):
                        self.assertEqual(actual.branches, expected)
                        self.assertEqual(actual.cost, max(expected))

    def test_batched_normal_coordinates_with_passive_source_columns(self):
        rng = Random(771907)
        for q in (2, 3, 4, 9, 343):
            field = Field(q)
            # Common + 3 pair + 3 private + 1 tripod components.
            unit = eye(field, 9)
            v, r = unit.rows[7], unit.rows[8]
            marked = (v, r, tuple(field.sub(y, x) for x, y in zip(v, r)))
            side = tuple(Matrix(field, (unit.rows[0],
                *(unit.rows[1 + j] for j in range(3) if j != i),
                unit.rows[4 + i], marked[i])) for i in range(3))
            expected = UploadParameters(3, 0, 0, 1, (1, 1, 1))
            self.assertEqual(upload_parameters(Task(field, side, (unit,) * 3)), expected)
            # Apply invertible elementary row operations to an embedding in 13
            # source coordinates. The normal basis is rectangular and generic.
            embedding = [list(row) + [rng.randrange(q) for _ in range(4)]
                         for row in unit.rows]
            for _ in range(30):
                i, j = rng.sample(range(9), 2)
                scale = rng.randrange(1, q)
                embedding[i] = [field.add(x, field.mul(scale, y))
                                for x, y in zip(embedding[i], embedding[j])]
            embedding = Matrix(field, embedding)
            transformed = Task(field, tuple(a @ embedding for a in side),
                               (embedding,) * 3)
            self.assertEqual(upload_parameters(transformed), expected)

    def test_batched_coordinates_keep_graph_relation_rank(self):
        for q in (2, 3, 4, 9):
            f = Field(q)
            side = tuple(Matrix(f, rows, ncols=8) for rows in (
                ((1, 0, 0, 1, 0, 0, 0, 0), (0, 0, 0, 1, 0, 0, 0, 0)),
                ((0, 1, 0, 0, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0, 0, 0)),
                ((0, 0, 1, 0, 0, 0, 0, 0), (0, 0, 0, 1, 1, 0, 0, 0)),
            ))
            demand = tuple(Matrix(f, [row]) for row in (
                (0, 1, 1, 0, 0, 0, 0, 0), (1, 0, 1, 0, 0, 0, 0, 0),
                (1, 1, 0, 1, 0, 0, 0, 0),
            ))
            self.assertEqual(upload_parameters(Task(f, side, demand)),
                             UploadParameters(3, 0, 1, 0, (0, 0, 0)))


if __name__ == '__main__':
    unittest.main()
