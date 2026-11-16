"""Deterministic randomized differential tests against independent arithmetic.

The oracle below uses polynomial convolution/reduction written independently;
no production field operations, elimination, ranks or caches are reused.
"""
from __future__ import annotations

import random
import unittest
from concurrent.futures import ThreadPoolExecutor

from three_user_codes import Field, Matrix
from three_user_codes.linalg import contains, extend_basis, lift, quotient_rank, rank, rref, row_basis, zeros


class Oracle:
    def __init__(self, p, modulus):
        self.p, self.modulus = p, modulus
        self.m = len(modulus) - 1
        self.q = p ** self.m

    def digits(self, x):
        out = []
        for _ in range(self.m):
            x, digit = divmod(x, self.p)
            out.append(digit)
        return out

    def encode(self, values):
        return sum((x % self.p) * self.p**i for i, x in enumerate(values))

    def add(self, a, b):
        return self.encode([x+y for x, y in zip(self.digits(a), self.digits(b))])

    def neg(self, a):
        return self.encode([-x for x in self.digits(a)])

    def mul(self, a, b):
        aa, bb = self.digits(a), self.digits(b)
        out = [0] * (2*self.m-1)
        for i, x in enumerate(aa):
            for j, y in enumerate(bb):
                out[i+j] += x*y
        for k in range(len(out)-1, self.m-1, -1):
            coefficient = out[k] % self.p
            for j, v in enumerate(self.modulus):
                out[k-self.m+j] -= coefficient*v
        return self.encode(out[:self.m])

    def inv(self, a):
        assert a
        result, power = 1, self.q-2
        while power:
            if power & 1:
                result = self.mul(result, a)
            a = self.mul(a, a)
            power //= 2
        return result

    def reduced(self, rows, width):
        rows = [list(row) for row in rows]
        index, pivots = 0, []
        for c in range(width):
            chosen = next((i for i in range(index, len(rows)) if rows[i][c]), None)
            if chosen is None:
                continue
            rows[index], rows[chosen] = rows[chosen], rows[index]
            multiplier = self.inv(rows[index][c])
            rows[index] = [self.mul(multiplier, x) for x in rows[index]]
            for i in range(len(rows)):
                if i != index:
                    factor = rows[i][c]
                    rows[i] = [self.add(x, self.neg(self.mul(factor, y))) for x, y in zip(rows[i], rows[index])]
            pivots.append(c)
            index += 1
            if index == len(rows):
                break
        return tuple(tuple(row) for row in rows), tuple(pivots)

    def product(self, a, b, width):
        out = []
        for row in a:
            dest = []
            for j in range(width):
                value = 0
                for x, brow in zip(row, b):
                    value = self.add(value, self.mul(x, brow[j]))
                dest.append(value)
            out.append(tuple(dest))
        return tuple(out)


class OptimizedLinearAlgebraTests(unittest.TestCase):
    def fields(self):
        return [Field(q) for q in (2,3,4,5,8,9,16,25,257,343,18446744073709551557)] + [Field(9, [2,1,1]), Field(16,[1,0,0,1,1])]

    def test_independent_rref_and_forward_rank(self):
        rng = random.Random(2026091901)
        for f in self.fields():
            oracle = Oracle(f.p, f.modulus)
            for _ in range(24):
                m, n = rng.randrange(9), rng.randrange(11)
                a = Matrix(f, [[rng.randrange(f.q) for _ in range(n)] for _ in range(m)], ncols=n)
                with self.subTest(q=f.q, modulus=f.modulus, shape=a.shape):
                    expected, pivots = oracle.reduced(a.rows, n)
                    self.assertEqual(rank(a), len(pivots))  # before any RREF cache
                    actual, actual_pivots = rref(a)
                    self.assertEqual(actual.rows, expected)
                    self.assertEqual(actual_pivots, pivots)
                    self.assertEqual(row_basis(a).rows, expected[:len(pivots)])

    def test_independent_rectangular_products(self):
        rng = random.Random(2026091902)
        for f in self.fields():
            oracle = Oracle(f.p, f.modulus)
            for _ in range(18):
                m, k, n = (rng.randrange(9) for _ in range(3))
                a = Matrix(f, [[rng.randrange(f.q) for _ in range(k)] for _ in range(m)], ncols=k)
                b = Matrix(f, [[rng.randrange(f.q) for _ in range(n)] for _ in range(k)], ncols=n)
                expected = oracle.product(a.rows, b.rows, n)
                self.assertEqual((a @ b).rows, expected)
                self.assertEqual((a @ b).shape, (m,n))

    def test_independent_quotients_and_containment(self):
        rng = random.Random(2026091903)
        for f in self.fields()[:9]:
            oracle = Oracle(f.p, f.modulus)
            for _ in range(12):
                n = rng.randrange(8)
                a = Matrix(f, [[rng.randrange(f.q) for _ in range(n)] for _ in range(rng.randrange(6))], ncols=n)
                b = Matrix(f, [[rng.randrange(f.q) for _ in range(n)] for _ in range(rng.randrange(6))], ncols=n)
                ra = len(oracle.reduced(a.rows,n)[1])
                delta = len(oracle.reduced(a.rows+b.rows,n)[1])-ra
                self.assertEqual(quotient_rank(b,a),delta)
                self.assertEqual(contains(a,b),delta==0)

    def test_cache_does_not_affect_equality_hash_or_input(self):
        f=Field(3)
        a=Matrix(f,[[1,2,0],[0,1,2]])
        b=Matrix(f,a.rows)
        before=hash(a)
        rref(a);rank(a)
        self.assertEqual(a,b)
        self.assertEqual(hash(a),before)
        self.assertEqual(a.rows,((1,2,0),(0,1,2)))
        with self.assertRaises(AttributeError): a.rows=()

    def test_binary_cache_thread_readers(self):
        rng=random.Random(42)
        f=Field(2)
        a=Matrix(f,[[rng.randrange(2) for _ in range(75)] for _ in range(40)])
        def work(_): return rref(a),rank(a),a@a.T
        with ThreadPoolExecutor(max_workers=4) as executor:
            results=list(executor.map(work,range(16)))
        self.assertTrue(all(r==results[0] for r in results))

    def test_field_tables_shared_but_representations_separate(self):
        a,b=Field(256),Field(256)
        self.assertIs(a._muls,b._muls)
        self.assertIsInstance(a._muls[1],bytes)
        c,d=Field(9),Field(9,[2,1,1])
        self.assertNotEqual(c,d)
        self.assertIsNot(c._muls,d._muls)

    def test_out_of_order_pivots_preserve_original_rows(self):
        for q in (2,3,4,9,257):
            f=Field(q)
            base=Matrix(f,[[0,0,1],[1,0,1]])
            candidates=Matrix(f,[[1,0,0],[0,1,1],[0,1,0]])
            self.assertEqual(extend_basis(base,candidates).rows,base.rows+(candidates.rows[1],))

    def test_empty_lifts_do_not_materialize_block_count(self):
        f=Field(3)
        self.assertEqual(lift(zeros(f,0,0),10**9),zeros(f,0,0))
        self.assertEqual(lift(zeros(f,0,3),10**9).shape,(0,3*10**9))

    def test_public_validation_not_removed(self):
        f=Field(9)
        for invalid in (True,1.5,-1,9):
            with self.assertRaises((TypeError,ValueError)): Matrix(f,[[invalid]])
            with self.assertRaises((TypeError,ValueError)): f.mul(invalid,1)
        with self.assertRaises(ValueError): contains(Matrix(f,[[1]]),Matrix(f,[[1,0]]))
        with self.assertRaises(TypeError): rank([[1]])


if __name__ == '__main__': unittest.main()
