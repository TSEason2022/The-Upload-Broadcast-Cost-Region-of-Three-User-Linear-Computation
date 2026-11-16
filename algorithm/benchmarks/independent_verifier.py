"""Independent original-field certificate arithmetic for release validation.

Standard library only. No package rank, elimination, matrix multiplication,
lift, or field arithmetic is used by the polynomial oracle. The operating
adapter supplies the matrices; every original source basis vector is checked.
"""
from __future__ import annotations


class PolynomialOracle:
    """Small independent field implementation, without package arithmetic."""

    def __init__(self, field):
        self.p, self.degree = field.p, field.degree
        self.modulus = tuple(field.modulus)

    def digits(self, value):
        result = []
        for _ in range(self.degree):
            value, digit = divmod(value, self.p)
            result.append(digit)
        return result

    def encode(self, digits):
        result = 0
        for digit in reversed(digits):
            result = result * self.p + digit % self.p
        return result

    def add(self, left, right):
        if self.degree == 1:
            return (left + right) % self.p
        return self.encode([a + b for a, b in zip(self.digits(left), self.digits(right))])

    def mul(self, left, right):
        if not left or not right:
            return 0
        if self.degree == 1:
            return left * right % self.p
        a, b = self.digits(left), self.digits(right)
        product = [0] * (2 * self.degree - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                product[i + j] = (product[i + j] + x * y) % self.p
        for power in range(len(product) - 1, self.degree - 1, -1):
            coefficient = product[power]
            for j, value in enumerate(self.modulus):
                product[power - self.degree + j] = (
                    product[power - self.degree + j] - coefficient * value
                ) % self.p
        return self.encode(product[:self.degree])

    def dot(self, row, values):
        if len(row) != len(values):
            raise AssertionError("oracle matrix/vector shape mismatch")
        result = 0
        for coefficient, value in zip(row, values):
            result = self.add(result, self.mul(coefficient, value))
        return result

    def apply(self, matrix, values):
        return [self.dot(row, values) for row in matrix.rows]


def independently_check(result, task):
    """Verify all source basis vectors in the ORIGINAL row/instance convention."""
    adapter = result.operating_code(task)
    oracle = PolynomialOracle(task.field)
    length = result.certificate.blocklength
    # This explicitly constructs instance-major observations from original rows;
    # it does not call package lift(), matrix multiplication, or field arithmetic.
    for source in range(task.n * length):
        instance, column = divmod(source, task.n)
        side = [[row[column] if block == instance else 0
                 for block in range(length) for row in matrix.rows]
                for matrix in task.original_side]
        expected = [[row[column] if block == instance else 0
                     for block in range(length) for row in matrix.rows]
                    for matrix in task.original_demand]
        uploads = [oracle.apply(matrix, values)
                   for matrix, values in zip(adapter.original_local_maps, side)]
        signal = oracle.apply(result.certificate.broadcast,
                              [value for values in uploads for value in values])
        for user in range(3):
            from_signal = oracle.apply(adapter.original_decoders[user], signal)
            from_side = oracle.apply(adapter.original_side_decoders[user], side[user])
            actual = [oracle.add(a, b) for a, b in zip(from_signal, from_side)]
            if actual != expected[user]:
                raise AssertionError(f"independent decoding failed: source={source}, user={user}")
    return {"method": "all_original_source_basis_vectors_independent_polynomial_arithmetic",
            "basis_vectors": task.n * length, "users_checked": 3, "passed": True}
