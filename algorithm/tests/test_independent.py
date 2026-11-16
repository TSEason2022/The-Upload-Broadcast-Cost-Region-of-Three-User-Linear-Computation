"""Independent finite-set oracles for exact small-field code construction.

The reference rowspace is the SET of all vector combinations.  It never calls
the package's rank, elimination, solve, or field arithmetic.  These tests are
deliberately small: they certify independent cases, not arbitrary input sizes.
"""
from __future__ import annotations

from itertools import product
import copy
import json
import random
import unittest
from fractions import Fraction
from math import ceil

from three_user_codes.field import Field


class ReferenceField:
    """Slow polynomial arithmetic, independent of production implementations."""

    def __init__(self, q, modulus):
        self.q = q
        self.modulus = tuple(modulus)
        self.degree = len(modulus) - 1
        self.p = next(p for p in range(2, q + 1) if p ** self.degree == q)

    def digits(self, a):
        result = []
        for _ in range(self.degree):
            result.append(a % self.p)
            a //= self.p
        return result

    def encode(self, coefficients):
        return sum((c % self.p) * self.p ** k for k, c in enumerate(coefficients))

    def add(self, a, b):
        return self.encode([x + y for x, y in zip(self.digits(a), self.digits(b))])

    def mul(self, a, b):
        left, right = self.digits(a), self.digits(b)
        out = [0] * (2 * self.degree - 1)
        for i, ai in enumerate(left):
            for j, bj in enumerate(right):
                out[i + j] += ai * bj
        for k in range(len(out) - 1, self.degree - 1, -1):
            lead = out[k] % self.p
            for j, coefficient in enumerate(self.modulus):
                out[k - self.degree + j] -= lead * coefficient
        return self.encode(out[:self.degree])

    def dot(self, a, b):
        value = 0
        for x, y in zip(a, b):
            value = self.add(value, self.mul(x, y))
        return value


def vector_add(a, b, field):
    return tuple(field.add(x, y) for x, y in zip(a, b))


def span_set(rows, width, field):
    """Enumerate a rowspace using repeated set addition, including duplicates."""
    result = {tuple([0] * width)}
    for row in rows:
        multiples = {tuple(field.mul(c, x) for x in row) for c in range(field.q)}
        result = {vector_add(u, v, field) for u in result for v in multiples}
    return frozenset(result)


def set_dimension(space, q):
    value, dimension = len(space), 0
    while value > 1:
        if value % q:
            raise AssertionError("reference rowspace cardinality is not a field power")
        value //= q
        dimension += 1
    return dimension


def all_subspaces_2d(field):
    """All subspaces in a two-dimensional vector space, from finite sets."""
    zero = ((0, 0),)
    spaces = {span_set(zero, 2, field): ()}
    for v in product(range(field.q), repeat=2):
        if v != (0, 0):
            spaces.setdefault(span_set([v], 2, field), (v,))
    spaces[span_set(((1, 0), (0, 1)), 2, field)] = ((1, 0), (0, 1))
    return tuple((space, basis) for space, basis in spaces.items())


def sum_sets(left, right, field):
    return frozenset(vector_add(a, b, field) for a in left for b in right)


def scalar_cost_oracle(sides, augmented, all_spaces, field, *, upload):
    """Exact scalar linear optimum via exhaustive subspace enumeration."""
    zero = frozenset({(0, 0)})
    if not upload:
        return min(set_dimension(space, field.q) for space, _ in all_spaces
                   if all(U <= sum_sets(A, space, field) for A, U in zip(sides, augmented)))
    choices = [[space for space, _ in all_spaces if space <= A] for A in sides]
    best = 7
    for selected in product(*choices):
        cost = sum(set_dimension(space, field.q) for space in selected)
        if cost >= best:
            continue
        relay = zero
        for space in selected:
            relay = sum_sets(relay, space, field)
        if all(U <= sum_sets(A, relay, field) for A, U in zip(sides, augmented)):
            best = cost
    return best


def check_decoder_identities(testcase, A, W, code, ref):
    """Check all coefficients with independent polynomial arithmetic."""
    for side, demand, (C, H) in zip(A, W, code.decoders):
        testcase.assertEqual(len(C.rows), len(demand.rows))
        testcase.assertEqual(len(H.rows), len(demand.rows))
        for row_index, target in enumerate(demand.rows):
            row = (0,) * demand.ncols
            for c, b in zip(C.rows[row_index], code.broadcast.rows):
                row = vector_add(row, tuple(ref.mul(c, v) for v in b), ref)
            for h, a in zip(H.rows[row_index], side.rows):
                row = vector_add(row, tuple(ref.mul(h, v) for v in a), ref)
            testcase.assertEqual(row, target)


class IndependentFieldTests(unittest.TestCase):
    def test_arithmetic_against_polynomial_reference(self):
        for q in (2, 3, 4, 5, 7, 8, 9, 16, 25, 27):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            for a, b in product(range(q), repeat=2):
                self.assertEqual(f.add(a, b), ref.add(a, b), (q, a, b))
                self.assertEqual(f.mul(a, b), ref.mul(a, b), (q, a, b))
            for a in range(1, q):
                self.assertEqual(ref.mul(a, f.inv(a)), 1)

    def test_gf4_is_not_integer_modulo_four(self):
        f = Field(4)
        self.assertEqual(f.add(1, 1), 0)
        self.assertEqual(f.mul(2, 2), 3)
        self.assertEqual(f.mul(2, 3), 1)

    def test_invalid_field_inputs_are_rejected(self):
        for value in (True, False, 3.0, "3", None):
            with self.subTest(value=value), self.assertRaises((TypeError, ValueError)):
                Field(value)
        for q in (0, 1, 6, 10, 12, 2 ** 64):
            with self.subTest(q=q), self.assertRaises(ValueError):
                Field(q)
        f = Field(4)
        for value in (True, False, 1.0, -1, 4):
            with self.subTest(value=value), self.assertRaises((TypeError, ValueError)):
                f.validate(value)
        with self.assertRaises(ZeroDivisionError):
            f.inv(0)
        with self.assertRaises(ValueError):
            Field(4, modulus=(1, 0, 1))


class IndependentLinearAlgebraTests(unittest.TestCase):
    def test_all_two_by_two_ranks_and_nullspaces(self):
        from three_user_codes.linalg import Matrix, nullspace, rank, row_basis
        for q in (2, 3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            vectors = tuple(product(range(q), repeat=2))
            for entries in product(range(q), repeat=4):
                rows = (entries[:2], entries[2:])
                matrix = Matrix(f, rows, ncols=2)
                expected = span_set(rows, 2, ref)
                self.assertEqual(rank(matrix), set_dimension(expected, q), (q, rows))
                self.assertEqual(span_set(row_basis(matrix).rows, 2, ref), expected)
                expected_kernel = frozenset(v for v in vectors if all(ref.dot(r, v) == 0 for r in rows))
                self.assertEqual(span_set(nullspace(matrix).rows, 2, ref), expected_kernel)

    def test_all_two_dimensional_intersections_and_containments(self):
        from three_user_codes.linalg import Matrix, contains, intersection
        for q in (2, 3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            spaces = all_subspaces_2d(ref)
            for (left, left_rows), (right, right_rows) in product(spaces, repeat=2):
                A, B = Matrix(f, left_rows, ncols=2), Matrix(f, right_rows, ncols=2)
                self.assertEqual(contains(A, B), right <= left)
                self.assertEqual(span_set(intersection(A, B).rows, 2, ref), left & right)

    def test_zero_dimensional_spaces(self):
        from three_user_codes.linalg import Matrix, eye, inverse, nullspace, rank
        for q in (2, 3, 4):
            f = Field(q)
            for width in range(4):
                empty = Matrix(f, (), ncols=width)
                self.assertEqual(rank(empty), 0)
                self.assertEqual(nullspace(empty), eye(f, width))
            self.assertEqual(inverse(eye(f, 0)), eye(f, 0))


class IndependentCoordinationTests(unittest.TestCase):
    def test_all_triples_of_nonzero_forms_in_two_dimensions(self):
        from three_user_codes.coordination import avoid_linear_forms
        from three_user_codes.linalg import Matrix
        for q in (3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            forms = tuple(v for v in product(range(q), repeat=2) if any(v))
            for rows in product(forms, repeat=3):
                x = avoid_linear_forms(Matrix(f, rows, ncols=2))
                self.assertTrue(all(ref.dot(r, x) for r in rows), (q, rows, x))

    def test_shared_columns_with_independent_witness_search(self):
        from three_user_codes.coordination import ColumnSpec, DecoderTemplate, coordinate_columns
        from three_user_codes.linalg import Matrix
        rng = random.Random(93041)
        for q in (3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            values = tuple(product(range(q), repeat=2))
            assignments = tuple(product(values, repeat=2))
            for _ in range(12):
                templates, witnesses = [], []
                for _ in range(3):
                    while True:
                        maps = tuple(tuple(tuple(rng.randrange(q) for _ in range(2)) for _ in range(2)) for _ in range(2))
                        def rows_at(x):
                            columns = tuple(tuple(ref.dot(r, x[g]) for r in maps[g]) for g in range(2))
                            return tuple(zip(*columns))
                        witness = next((x for x in assignments if len(span_set(rows_at(x), 2, ref)) == q ** 2), None)
                        if witness is not None:
                            break
                    slots = tuple(ColumnSpec(g, g, Matrix(f, maps[g], ncols=2)) for g in range(2))
                    templates.append(DecoderTemplate(Matrix(f, ((0, 0), (0, 0)), ncols=2), slots))
                    witnesses.append(witness)
                result = coordinate_columns(templates, witnesses)
                self.assertEqual(result.groups_processed, 2)
                for matrix in result.matrices:
                    self.assertEqual(len(span_set(matrix.rows, 2, ref)), q ** 2)


class IndependentTaskCostTests(unittest.TestCase):
    def test_small_tasks_against_exhaustive_scalar_subspaces(self):
        from three_user_codes.linalg import Matrix
        from three_user_codes.profile import broadcast_profile
        from three_user_codes.task import Task
        from three_user_codes.upload_bound import upload_cost
        rng = random.Random(912831)
        for q in (2, 3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            spaces = all_subspaces_2d(ref)
            valid_pairs = [(A, Ab, U, Ub) for A, Ab in spaces for U, Ub in spaces if A <= U]
            for _ in range(100):
                while True:
                    selected = tuple(rng.choice(valid_pairs) for _ in range(3))
                    sides = tuple(row[0] for row in selected)
                    augmented = tuple(row[2] for row in selected)
                    available = sum_sets(sum_sets(sides[0], sides[1], ref), sides[2], ref)
                    if all(U <= available for U in augmented):
                        break
                A = tuple(Matrix(f, row[1], ncols=2) for row in selected)
                U = tuple(Matrix(f, row[3], ncols=2) for row in selected)
                task = Task(f, A, U)
                scalar_U = scalar_cost_oracle(sides, augmented, spaces, ref, upload=True)
                scalar_D = scalar_cost_oracle(sides, augmented, spaces, ref, upload=False)
                computed_U = upload_cost(task)
                computed_D = broadcast_profile(A, U).cost
                self.assertIsInstance(computed_U, Fraction)
                self.assertLessEqual(computed_U, scalar_U, (q, selected))
                self.assertEqual(ceil(computed_U), scalar_U, (q, selected))
                self.assertLessEqual(computed_D, scalar_D, (q, selected))
                if q >= 3:
                    self.assertEqual(ceil(computed_D), scalar_D, (q, selected))

    def test_tripod_integer_broadcast_needs_nonbinary_coefficients(self):
        from three_user_codes.linalg import Matrix, eye
        from three_user_codes.profile import broadcast_profile
        from three_user_codes.task import Task
        from three_user_codes.upload_bound import upload_cost
        for q in (2, 3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            A = tuple(Matrix(f, [r], ncols=2) for r in ((1, 0), (0, 1), (1, 1)))
            U = (eye(f, 2),) * 3
            task = Task(f, A, U)
            self.assertEqual(upload_cost(task), Fraction(3, 2))
            self.assertEqual(broadcast_profile(A, U).cost, 1)
            sides = tuple(span_set(a.rows, 2, ref) for a in A)
            augmented = tuple(span_set(u.rows, 2, ref) for u in U)
            scalar = scalar_cost_oracle(sides, augmented, all_subspaces_2d(ref), ref, upload=False)
            self.assertEqual(scalar, 2 if q == 2 else 1)

    def test_source_basis_changes_and_duplicate_rows(self):
        from three_user_codes.linalg import Matrix, eye
        from three_user_codes.profile import broadcast_profile
        from three_user_codes.task import Task
        from three_user_codes.upload_bound import upload_cost
        for q in (3, 4, 5):
            f = Field(q)
            A = tuple(Matrix(f, [row], ncols=3) for row in ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
            W = tuple(Matrix(f, [row], ncols=3) for row in ((0, 1, 0), (0, 0, 1), (1, 0, 0)))
            original = Task(f, A, W)
            T = Matrix(f, ((1, 1, 0), (0, 1, 1), (0, 0, 1)), ncols=3)
            def duplicate(a):
                return Matrix(f, list(a.rows) + list(a.rows) + [(0,) * 3], ncols=3)
            transformed = Task(f, tuple(duplicate(a @ T) for a in A), tuple(duplicate(w @ T) for w in W))
            self.assertEqual(upload_cost(original), upload_cost(transformed))
            self.assertEqual(broadcast_profile(original.side, original.augmented),
                             broadcast_profile(transformed.side, transformed.augmented))
            self.assertEqual(upload_cost(original.lift(2)), 2 * upload_cost(original))


class IndependentLCBCTests(unittest.TestCase):
    def test_broadcast_against_exhaustive_scalar_oracle(self):
        from three_user_codes.lcbc import build_lcbc
        from three_user_codes.linalg import Matrix
        rng = random.Random(558101)
        for q in (3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            spaces = all_subspaces_2d(ref)
            valid_pairs = [(A, Ab, U, Ub) for A, Ab in spaces for U, Ub in spaces if A <= U]
            for _ in range(75):
                selected = tuple(rng.choice(valid_pairs) for _ in range(3))
                sides = tuple(row[0] for row in selected)
                augmented = tuple(row[2] for row in selected)
                A = tuple(Matrix(f, row[1], ncols=2) for row in selected)
                W = tuple(Matrix(f, row[3], ncols=2) for row in selected)
                code = build_lcbc(A, W)
                expected = scalar_cost_oracle(sides, augmented, spaces, ref, upload=False)
                self.assertEqual(code.cost, expected)
                self.assertEqual(code.broadcast.nrows, expected)
                self.assertEqual(len(span_set(code.broadcast.rows, 2, ref)), q ** expected)
                check_decoder_identities(self, A, W, code, ref)


    def test_random_dependent_inputs_and_two_instance_lifts(self):
        from three_user_codes.lcbc import build_lcbc, lcbc_parameters
        from three_user_codes.linalg import Matrix, lift
        from three_user_codes.profile import broadcast_profile
        from three_user_codes.linalg import row_sum
        rng = random.Random(915087)
        for q in (3, 4, 5, 9):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            for _ in range(30):
                def draw():
                    rows = [tuple(rng.randrange(q) for _ in range(4)) for _ in range(rng.randrange(5))]
                    if rows:
                        rows += [rows[0], (0, 0, 0, 0)]
                    return Matrix(f, rows, ncols=4)
                A, W = tuple(draw() for _ in range(3)), tuple(draw() for _ in range(3))
                cost = lcbc_parameters(A, W).cost
                expected = broadcast_profile(A, tuple(row_sum(a, w) for a, w in zip(A, W))).cost
                self.assertEqual(cost, expected)
                factor = cost.denominator
                A = tuple(lift(a, factor) for a in A)
                W = tuple(lift(w, factor) for w in W)
                code = build_lcbc(A, W)
                self.assertEqual(code.cost, factor * cost)
                check_decoder_identities(self, A, W, code, ref)

class IndependentCompilerTests(unittest.TestCase):
    def check_result(self, original, result):
        cert = result.certificate
        ref = ReferenceField(original.field.q, original.field.modulus)
        self.assertEqual(cert.task.field, original.field)
        self.assertEqual(cert.task, original.lift(cert.blocklength))
        report = cert.verify()
        self.assertEqual(report.upload_count, result.upload_optimum * cert.blocklength)
        self.assertEqual(report.upload_rank, report.upload_count)
        self.assertEqual(report.broadcast_count, result.broadcast_optimum * cert.blocklength)
        self.assertEqual(report.broadcast_rank, report.broadcast_count)
        class BroadcastView:
            pass
        view = BroadcastView()
        view.broadcast = cert.signal
        view.decoders = tuple(zip(cert.decoders, cert.side_decoders))
        check_decoder_identities(self, cert.task.side, cert.task.demand, view, ref)
        for E, T, A in zip(cert.uploads, cert.local_maps, cert.task.side):
            for target, coefficients in zip(E.rows, T.rows):
                row = (0,) * E.ncols
                for c, a in zip(coefficients, A.rows):
                    row = vector_add(row, tuple(ref.mul(c, x) for x in a), ref)
                self.assertEqual(row, target)

    def test_zero_task_and_directed_cycle(self):
        from three_user_codes.compiler import compile_task
        from three_user_codes.linalg import Matrix
        from three_user_codes.task import Task
        for q in (2, 3, 4, 5):
            f = Field(q)
            empty = Matrix(f, (), ncols=0)
            task = Task(f, (empty,) * 3, (empty,) * 3)
            self.check_result(task, compile_task(task))
            A = tuple(Matrix(f, [row], ncols=3) for row in ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
            W = (A[1], A[2], A[0])
            task = Task(f, A, W)
            result = compile_task(task)
            self.assertEqual(result.upload_optimum, 3)
            self.assertEqual(result.broadcast_optimum, 2)
            self.check_result(task, result)

    def test_resonant_five_source_symbols_and_changed_basis(self):
        from three_user_codes.compiler import compile_task, resonant_task
        from three_user_codes.linalg import Matrix
        from three_user_codes.task import Task
        for q in (2, 3, 4, 5):
            f = Field(q)
            original = resonant_task(f, 1)
            T = Matrix(f, tuple(tuple(int(i == j or j == i + 1) for j in range(5)) for i in range(5)), ncols=5)
            for task in (original, Task(f, tuple(a @ T for a in original.side), tuple(w @ T for w in original.demand))):
                result = compile_task(task, max_seconds=30)
                self.assertEqual(result.upload_optimum, 4)
                self.assertEqual(result.broadcast_optimum, Fraction(3, 2))
                self.assertEqual(result.certificate.blocklength, 2)
                self.check_result(task, result)

    def test_random_small_end_to_end(self):
        from three_user_codes.compiler import compile_task
        from three_user_codes.linalg import Matrix
        from three_user_codes.task import Task
        rng = random.Random(790173)
        for q in (2, 3, 4, 5):
            f = Field(q)
            ref = ReferenceField(q, f.modulus)
            spaces = all_subspaces_2d(ref)
            valid_pairs = [(A, Ab, U, Ub) for A, Ab in spaces for U, Ub in spaces if A <= U]
            for _ in range(15):
                while True:
                    selected = tuple(rng.choice(valid_pairs) for _ in range(3))
                    available = sum_sets(sum_sets(selected[0][0], selected[1][0], ref), selected[2][0], ref)
                    if all(row[2] <= available for row in selected):
                        break
                task = Task(f, tuple(Matrix(f, row[1], ncols=2) for row in selected),
                            tuple(Matrix(f, row[3], ncols=2) for row in selected))
                self.check_result(task, compile_task(task, max_states=10000, max_seconds=15))

    def test_serialized_certificate_roundtrip_and_tampering(self):
        from three_user_codes.certificate import CodeCertificate, VerificationError
        from three_user_codes.compiler import compile_task
        from three_user_codes.linalg import Matrix
        from three_user_codes.task import Task
        f = Field(3)
        A = tuple(Matrix(f, [row], ncols=3) for row in ((1, 0, 0), (0, 1, 0), (0, 0, 1)))
        task = Task(f, A, (A[1], A[2], A[0]))
        cert = compile_task(task).certificate
        data = json.loads(json.dumps(cert.to_dict()))
        reconstructed = CodeCertificate.from_dict(data)
        self.assertEqual(reconstructed.signal, cert.signal)
        self.assertEqual(reconstructed.verify(), cert.verify())
        mutations = []
        tampered = copy.deepcopy(data)
        tampered['decoders'][0]['rows'] = [[0] * tampered['decoders'][0]['ncols']]
        mutations.append(tampered)
        tampered = copy.deepcopy(data)
        tampered['uploads'][0]['rows'][0][0] = True
        mutations.append(tampered)
        tampered = copy.deepcopy(data)
        tampered['broadcast']['ncols'] += 1
        mutations.append(tampered)
        tampered = copy.deepcopy(data)
        tampered['schema'] = 'untrusted-format'
        mutations.append(tampered)
        for mutation in mutations:
            with self.assertRaises(VerificationError):
                CodeCertificate.from_dict(mutation)
        with self.assertRaises(VerificationError):
            cert.verify(expected_upload_count=4)

    def test_search_budget_does_not_claim_infeasibility(self):
        from three_user_codes.compiler import SearchBudgetExceeded, compile_task
        from three_user_codes.linalg import Matrix
        from three_user_codes.task import Task
        # A cycle now completes in one dual candidate. Use a task that really
        # needs more than one state so this tests exhaustion, not slow search.
        task = Task.from_rows(5,
            [[[1, 0, 0, 0], [0, 0, 0, 1], [1, 3, 0, 2]],
             [[0, 1, 0, 0]], [[0, 0, 1, 0]]],
            [[[0, 2, 2, 1]],
             [[1, 2, 3, 2], [4, 3, 1, 3], [1, 1, 2, 2]],
             [[4, 1, 1, 3], [0, 2, 0, 3]]])
        with self.assertRaises(SearchBudgetExceeded) as stopped:
            compile_task(task, fast_paths=False, max_states=1, max_seconds=None)
        self.assertIn("not an infeasibility", str(stopped.exception))
        self.check_result(task, compile_task(task, fast_paths=False, max_states=100, max_seconds=None))



if __name__ == "__main__":
    unittest.main()
