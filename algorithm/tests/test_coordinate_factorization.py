"""Coordinate-factor reuse preserves the exact public linear-system contract."""
import random
import unittest
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import patch

from three_user_codes import Field, Matrix, Task
from three_user_codes.linalg import coordinates, coordinates_many, eye, zeros
from three_user_codes.upload_bound import upload_parameters
from test_optimized_linalg import Oracle


class CoordinateFactorizationTests(unittest.TestCase):
    def test_coordinates_match_independent_free_variable_oracle(self):
        rng = random.Random(150015)
        fields = [Field(q) for q in (2, 3, 4, 9, 257, 343, 18446744073709551557)]
        fields += [Field(9, [2, 1, 1])]
        for f in fields:
            oracle = Oracle(f.p, f.modulus)
            for _ in range(20):
                m, n, rhs = (rng.randrange(7) for _ in range(3))
                raw = [[rng.randrange(f.q) for _ in range(n)] for _ in range(m)]
                if m >= 2:
                    raw[-1] = list(raw[0])  # Include dependent/redundant representations.
                basis = Matrix(f, raw, n)
                values = [[rng.randrange(f.q) for _ in range(m)] for _ in range(rhs)]
                wanted = Matrix(f, oracle.product(values, raw, n), n)
                system = [tuple(basis[i][j] for i in range(m)) +
                          tuple(wanted[i][j] for i in range(rhs)) for j in range(n)]
                reduced, pivots = oracle.reduced(system, m + rhs)
                self.assertTrue(all(p < m for p in pivots))
                expected = [[0] * m for _ in range(rhs)]
                for row, pivot in enumerate(pivots):
                    for i in range(rhs):
                        expected[i][pivot] = reduced[row][m + i]
                for attempt in range(2):
                    with self.subTest(q=f.q, modulus=f.modulus, shape=basis.shape, attempt=attempt):
                        answer = coordinates(wanted, basis)
                        self.assertEqual(answer, Matrix(f, expected, m))
                        self.assertEqual(answer @ basis, wanted)

    def test_cached_factor_rejects_inconsistent_rhs_and_preserves_inputs(self):
        for q in (2, 3, 4, 9):
            f = Field(q)
            basis = Matrix(f, [[0, 1, 1], [1, 0, 0], [0, 1, 1]])
            before, hashed = basis.rows, hash(basis)
            wanted = Matrix(f, [[1, 1, 1]])
            expected = Matrix(f, [[1, 1, 0]])
            self.assertEqual(coordinates(wanted, basis), expected)
            factor = basis._coordinate_data
            self.assertIsNotNone(factor)
            with self.assertRaisesRegex(ValueError, 'inconsistent'):
                coordinates(Matrix(f, [[0, 0, 1]]), basis)
            self.assertEqual(coordinates(wanted, basis), expected)
            self.assertIs(factor, basis._coordinate_data)
            self.assertEqual(basis.rows, before)
            self.assertEqual(hash(basis), hashed)

    def test_batch_preserves_partition_empty_shapes_and_failures(self):
        f = Field(9, [2, 1, 1])
        basis = Matrix(f, [[0, 2, 1], [1, 0, 0], [0, 2, 1]])
        inputs = (zeros(f, 0, 3), basis, Matrix(f, [basis.rows[1]], 3))
        actual = coordinates_many(iter(inputs), basis)
        self.assertEqual(tuple(x.shape for x in actual), ((0, 3), (3, 3), (1, 3)))
        self.assertEqual(actual, tuple(coordinates(v, basis) for v in inputs))
        self.assertEqual(coordinates_many([], basis), ())
        with self.assertRaisesRegex(ValueError, 'inconsistent'):
            coordinates_many([inputs[1], Matrix(f, [[0, 0, 1]])], basis)
        with self.assertRaises(ValueError):
            coordinates_many([Matrix(Field(9), [[1, 0, 0]])], basis)
        with self.assertRaises(ValueError):
            coordinates_many([zeros(f, 0, 4)], basis)
        with self.assertRaises(TypeError):
            coordinates_many([[[1, 0, 0]]], basis)

    def test_empty_and_zero_bases_follow_free_variable_convention(self):
        f = Field(5)
        for m in (0, 3):
            for n in (0, 4):
                basis = zeros(f, m, n)
                answer = coordinates(zeros(f, 2, n), basis)
                self.assertEqual(answer, zeros(f, 2, m))
                self.assertEqual(coordinates(zeros(f, 0, n), basis).shape, (0, m))
        with self.assertRaises(ValueError):
            coordinates(eye(f, 1), zeros(f, 0, 1))

    def test_factorization_is_safe_for_concurrent_readers(self):
        f = Field(9)
        basis = Matrix(f, [[0, 2, 1], [1, 0, 0], [0, 2, 1]])
        wanted = Matrix(f, [[0, 2, 1], [1, 0, 0]])
        with ThreadPoolExecutor(max_workers=4) as executor:
            results = list(executor.map(lambda _: coordinates(wanted, basis), range(20)))
        self.assertTrue(all(x == results[0] and x @ basis == wanted for x in results))

    def test_task_bound_cache_is_local_and_avoids_duplicate_normal_form(self):
        f = Field(3)
        unit = eye(f, 3)
        side = tuple(Matrix(f, [unit.rows[i]], 3) for i in range(3))
        task = Task(f, side, (side[1], side[2], side[0]))
        import three_user_codes.upload_bound as module
        with patch.object(module, 'side_normal_form', wraps=module.side_normal_form) as normal:
            first = upload_parameters(task)
            self.assertIs(upload_parameters(task), first)
            self.assertEqual(normal.call_count, 1)
            other = Task(f, side, (side[0], side[1], side[2]))
            second = upload_parameters(other)
            self.assertNotEqual(second.cost, first.cost)
            self.assertEqual(normal.call_count, 2)

    def test_constructors_keep_public_validation(self):
        for constructor, args in ((zeros, ('bad', 2, 3)), (eye, ('bad', 3))):
            with self.assertRaises(TypeError):
                constructor(*args)
        with self.assertRaises(TypeError):
            zeros(Field(2), True, 2)
        with self.assertRaises(ValueError):
            eye(Field(2), -1)
