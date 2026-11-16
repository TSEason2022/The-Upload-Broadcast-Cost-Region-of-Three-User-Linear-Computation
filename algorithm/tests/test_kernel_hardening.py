"""Exact arithmetic regressions for cached bases and optimized field kernels."""
from concurrent.futures import ThreadPoolExecutor
import random
import unittest

from three_user_codes import Field, Matrix
from three_user_codes.linalg import (
    contains, determinant, extend_basis, eye, nullspace, quotient_rank,
    rank, row_basis, rref, solve, vstack, zeros,
)


def binary_polynomial_product(a, b, modulus):
    """Independent convolution followed by polynomial long division."""
    product = 0
    for i in range(a.bit_length()):
        for j in range(b.bit_length()):
            if ((a >> i) & 1) and ((b >> j) & 1):
                product ^= 1 << (i + j)
    divisor = sum(c << i for i, c in enumerate(modulus))
    while product.bit_length() >= divisor.bit_length():
        product ^= divisor << (product.bit_length() - divisor.bit_length())
    return product


class KernelHardeningTests(unittest.TestCase):
    def test_binary_table_and_polynomial_fallback_agree_with_convolution(self):
        rng = random.Random(94813)
        # Exercise byte tables, discrete-exponent tables, and the >65536
        # polynomial fallback, including zero and maximal encoded elements.
        for q in (4, 256, 512, 65536, 131072):
            field = Field(q)
            values = [(0, q - 1), (1, q - 1), (q - 1, q - 1)]
            values += [(rng.randrange(q), rng.randrange(q)) for _ in range(32)]
            for a, b in values:
                with self.subTest(q=q, a=a, b=b):
                    self.assertEqual(field.mul(a, b),
                                     binary_polynomial_product(a, b, field.modulus))

    def test_cached_reductions_do_not_change_original_rowspace_or_inputs(self):
        rng = random.Random(94814)
        for q in (2, 3, 4, 9, 343, 512):
            field = Field(q)
            original = Matrix(field, [[rng.randrange(q) for _ in range(11)]
                                      for _ in range(7)])
            candidate = Matrix(field, [[rng.randrange(q) for _ in range(11)]
                                       for _ in range(3)])
            before = original.rows, hash(original)
            expected = rank(vstack(original, candidate)) - rank(original)
            rref(original)  # cached reduced rows can differ from original.rows
            canonical = row_basis(original)
            for base in (original, canonical):
                self.assertEqual(quotient_rank(candidate, base), expected)
                self.assertEqual(contains(base, candidate), expected == 0)
                self.assertTrue(contains(base, canonical))
                # Mutating a fresh echelon for one query cannot contaminate
                # another query or the immutable source's cached RREF.
                self.assertEqual(quotient_rank(eye(field, 11), base), 11 - rank(base))
                self.assertEqual(quotient_rank(candidate, base), expected)
            self.assertEqual((original.rows, hash(original)), before)

    def test_out_of_order_binary_pivots_with_uncleared_right_coordinates(self):
        field = Field(2)
        rows = Matrix(field, [[0, 0, 0, 1, 1], [0, 1, 0, 1, 0],
                              [1, 1, 1, 0, 1], [0, 0, 1, 1, 0]])
        chosen = extend_basis(zeros(field, 0, 5), rows)
        self.assertEqual(chosen.rows, rows.rows)
        self.assertEqual(rank(chosen), 4)
        combinations = Matrix(field, [[1, 1, 0, 1], [1, 0, 1, 1],
                                      [1, 1, 1, 1]]) @ rows
        self.assertTrue(contains(chosen, combinations))
        self.assertEqual(quotient_rank(combinations, chosen), 0)
        self.assertEqual(rows @ nullspace(rows).T, zeros(field, 4, 1))

    def test_large_prime_power_and_unbounded_integer_accumulation(self):
        prime = 18446744073709551557
        field = Field(prime)
        exponent = 2 ** 257 + 17
        self.assertEqual(field.pow(prime - 2, exponent), pow(prime - 2, exponent, prime))
        self.assertEqual(field.pow(prime - 2, -17), pow(prime - 2, -17, prime))
        a = Matrix(field, [[prime - 1] * 97, [prime - 2] * 97])
        b = Matrix(field, [[prime - 1, prime - 3] for _ in range(97)])
        self.assertEqual((a @ b).rows, ((97, 291), (194, 582)))
        identity = eye(field, 3)
        self.assertEqual(solve(identity, identity), identity)

    def test_extension_determinant_row_operations(self):
        rng = random.Random(94815)
        for q in (343, 512, 65536, 131072):
            field = Field(q)
            # Upper triangular matrices give an independent determinant
            # formula, then row addition and swaps exercise elimination.
            rows = [[rng.randrange(q) if j >= i else 0 for j in range(6)]
                    for i in range(6)]
            for i in range(6):
                rows[i][i] = rng.randrange(1, q)
            expected = 1
            for i in range(6):
                expected = field.mul(expected, rows[i][i])
            for i in range(5, 0, -1):
                rows[i] = list(field.axpy(2, rows[i - 1], rows[i]))
            rows[0], rows[-1] = rows[-1], rows[0]
            self.assertEqual(determinant(Matrix(field, rows)), field.neg(expected))

    def test_concurrent_cached_quotient_reductions(self):
        for q in (2, 9):
            field = Field(q)
            base = row_basis(Matrix(field, [[1, 1, 0, 1], [0, 1, 1, 0]]))
            vectors = eye(field, 4)
            expected = rref(base), hash(base)
            with ThreadPoolExecutor(max_workers=4) as executor:
                actual = list(executor.map(lambda _: quotient_rank(vectors, base), range(32)))
            self.assertEqual(actual, [2] * 32)
            self.assertEqual((rref(base), hash(base)), expected)


if __name__ == '__main__':
    unittest.main()
