"""Independent finite-field laws and exact matrix certificates (stdlib only)."""
import itertools
import random
import unittest

from three_user_codes.field import Field
from three_user_codes.linalg import (
    Matrix, zeros, eye, from_columns, hstack, vstack, block_diag, lift,
    rref, row_basis, rank, nullspace, row_sum, intersection, contains,
    coordinates, solve, inverse, determinant, extend_basis, scalar_mul,
)


def enumerated_span(matrix):
    f = matrix.field
    return {
        tuple(f.dot(coefficients, column) for column in matrix.T)
        for coefficients in itertools.product(range(f.q), repeat=matrix.nrows)
    }


def permutation_determinant(matrix):
    f, n, result = matrix.field, matrix.nrows, 0
    for permutation in itertools.permutations(range(n)):
        term = 1
        for i, j in enumerate(permutation):
            term = f.mul(term, matrix[i][j])
        parity = sum(permutation[i] > permutation[j] for i in range(n) for j in range(i + 1, n)) % 2
        result = f.add(result, f.neg(term) if parity else term)
    return result


class FieldTests(unittest.TestCase):
    def test_exhaustive_small_field_axioms(self):
        for q in (2, 3, 4, 5, 7, 8, 9):
            f = Field(q)
            for a in range(q):
                self.assertEqual(f.add(a, f.neg(a)), 0)
                self.assertEqual(f.pow(a, q), a)
                self.assertEqual(f.from_coeffs(f.coeffs(a)), a)
                if a:
                    self.assertEqual(f.mul(a, f.inv(a)), 1)
                for b in range(q):
                    self.assertEqual(f.add(a, b), f.add(b, a))
                    self.assertEqual(f.mul(a, b), f.mul(b, a))
                    for c in range(q):
                        self.assertEqual(f.mul(f.mul(a, b), c), f.mul(a, f.mul(b, c)))
                        self.assertEqual(f.add(f.add(a, b), c), f.add(a, f.add(b, c)))
                        self.assertEqual(f.mul(a, f.add(b, c)), f.add(f.mul(a, b), f.mul(a, c)))

    def test_large_fields_and_big_integer_products(self):
        rng = random.Random(137)
        for q in (16, 25, 27, 81, 256, 257, 343, 65536, 2305843009213693951, 18446744073709551557):
            f = Field(q)
            for _ in range(30):
                a, b, c = (rng.randrange(q) for _ in range(3))
                self.assertEqual(f.mul(a, f.add(b, c)), f.add(f.mul(a, b), f.mul(a, c)))
                if a:
                    self.assertEqual(f.mul(a, f.inv(a)), 1)
            if f.degree == 1:
                self.assertEqual(f.mul(q - 1, q - 1), 1)

    def test_characteristic_and_encoding(self):
        f = Field(4)
        self.assertEqual(f.add(1, 1), 0)
        self.assertEqual(f.mul(2, 2), 3)
        self.assertEqual(f.pow(2, -1), 3)
        self.assertNotEqual(f.mul(2, 2), (2 * 2) % 4)
        self.assertEqual(f.to_dict(), {"q": 4, "modulus": [1, 1, 1]})
        self.assertEqual(Field.from_dict(f.to_dict()), f)

    def test_validation_and_irreducibility(self):
        for bad in (0, 1, 6, 12, 15, 341550071728321, 2 ** 64):
            with self.assertRaises(ValueError):
                Field(bad)
        for bad in (True, 4.0, "4"):
            with self.assertRaises(TypeError):
                Field(bad)
        for q, modulus in ((4, [1, 0, 1]), (16, [1, 0, 1, 0, 1]), (9, [0, 0, 1]), (9, [1, 0, 2])):
            with self.assertRaises(ValueError):
                Field(q, modulus)
        f = Field(3)
        for bad in (True, 1.0):
            with self.assertRaises(TypeError):
                f.add(0, bad)
        for bad in (-1, 3):
            with self.assertRaises(ValueError):
                f.mul(1, bad)
        with self.assertRaises(ZeroDivisionError):
            f.inv(0)
        with self.assertRaises(AttributeError):
            f.q = 7


class MatrixTests(unittest.TestCase):
    def test_all_small_binary_rowspaces(self):
        f = Field(2)
        matrices = [Matrix(f, rows, ncols=3) for rows in itertools.product(itertools.product(range(2), repeat=3), repeat=2)]
        for a in matrices:
            span = enumerated_span(a)
            self.assertEqual(len(span), 2 ** rank(a))
            kernel = nullspace(a)
            self.assertEqual(a @ kernel.T, zeros(f, a.nrows, kernel.nrows))
            self.assertEqual(rank(a) + kernel.nrows, a.ncols)
            self.assertEqual(enumerated_span(row_basis(a)), span)
        for a, b in zip(matrices, reversed(matrices)):
            self.assertEqual(enumerated_span(intersection(a, b)), enumerated_span(a) & enumerated_span(b))
            self.assertEqual(contains(a, b), enumerated_span(b) <= enumerated_span(a))
            self.assertEqual(rank(row_sum(a, b)) + rank(intersection(a, b)), rank(a) + rank(b))

    def test_random_systems_and_determinants(self):
        rng = random.Random(914)
        for q in (2, 3, 4, 8, 9, 257, 343):
            f = Field(q)
            for n in range(5):
                for _ in range(8):
                    a = Matrix(f, ([rng.randrange(q) for _ in range(n)] for _ in range(n)), ncols=n)
                    self.assertEqual(determinant(a), permutation_determinant(a))
                    x = Matrix(f, ([rng.randrange(q) for _ in range(2)] for _ in range(n)), ncols=2)
                    b = a @ x
                    self.assertEqual(a @ solve(a, b), b)
                    self.assertEqual(coordinates(b.T, a.T) @ a.T, b.T)
                    if determinant(a):
                        self.assertEqual(a @ inverse(a), eye(f, n))
                        self.assertEqual(inverse(a) @ a, eye(f, n))
                    else:
                        with self.assertRaises(ValueError):
                            inverse(a)

    def test_inconsistent_and_dependent_coordinates(self):
        f = Field(3)
        basis = Matrix(f, [[1, 0], [2, 0], [0, 1]])
        vectors = Matrix(f, [[2, 2], [1, 0]])
        self.assertEqual(coordinates(vectors, basis) @ basis, vectors)
        with self.assertRaises(ValueError):
            solve(Matrix(f, [[0]]), Matrix(f, [[1]]))
        with self.assertRaises(ValueError):
            coordinates(eye(f, 2), Matrix(f, [[1, 0]]))

    def test_zero_dimensional_shapes(self):
        f = Field(4)
        for r in range(4):
            for c in range(4):
                a = zeros(f, r, c)
                self.assertEqual(a.T.shape, (c, r))
                self.assertEqual(a.T.T, a)
                self.assertEqual(row_basis(a).shape, (0, c))
                self.assertEqual(nullspace(a), eye(f, c))
                self.assertEqual(solve(a, zeros(f, r, 2)).shape, (c, 2))
                self.assertEqual(a @ zeros(f, c, 0), zeros(f, r, 0))
        self.assertEqual(determinant(eye(f, 0)), 1)
        self.assertEqual(inverse(eye(f, 0)), eye(f, 0))
        self.assertEqual(intersection(zeros(f, 0, 3), eye(f, 3)), zeros(f, 0, 3))
        self.assertEqual(coordinates(zeros(f, 0, 3), zeros(f, 0, 3)).shape, (0, 0))
        self.assertEqual(from_columns(f, [], nrows=3).shape, (3, 0))

    def test_building_and_basis_selection(self):
        f = Field(5)
        a = Matrix(f, [[2, 0, 0], [4, 0, 0]])
        b = Matrix(f, [[0, 3, 0], [0, 0, 4]])
        extended = extend_basis(a, b)
        self.assertEqual(extended.rows, (a[0], b[0], b[1]))
        self.assertEqual(extend_basis(a, b, 2).rows, (a[0], b[0]))
        with self.assertRaises(ValueError):
            extend_basis(a, zeros(f, 0, 3), 2)
        self.assertEqual(lift(a, 2), block_diag(a, a))
        self.assertEqual(hstack(a, a).shape, (2, 6))
        self.assertEqual(vstack(a, b).shape, (4, 3))
        self.assertEqual(scalar_mul(a, 2)[0], (4, 0, 0))
        self.assertEqual(Matrix.from_dict(a.to_dict()), a)
        with self.assertRaises((AttributeError, TypeError)):
            a.ncols = 4
        with self.assertRaises(ValueError):
            Matrix(f, [[1], [1, 2]])
        with self.assertRaises(TypeError):
            Matrix(f, [[True]])
        with self.assertRaises(ValueError):
            Matrix(f, [[1]]) @ Matrix(Field(7), [[1]])


if __name__ == "__main__":
    unittest.main()
