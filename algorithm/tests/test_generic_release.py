"""Release-path and generic-search differential checks, with fixed public fixtures."""
from __future__ import annotations
import json
import random
import unittest
from itertools import product
from pathlib import Path

from three_user_codes import Field,Matrix,compile_task
from three_user_codes.io import task_from_dict
from three_user_codes.linalg import intersection,rank,row_basis
from test_optimized_linalg import Oracle


class GenericReleaseTests(unittest.TestCase):
    def test_all_generic_fixtures_cache_on_off(self):
        root=Path(__file__).resolve().parents[1]
        hits=0
        for path in sorted((root/'benchmarks'/'fixtures').glob('*.json')):
            task=task_from_dict(json.loads(path.read_text()))
            a=compile_task(task,fast_paths=False,force_blocklength=1,max_cache_entries=0)
            b=compile_task(task,fast_paths=False,force_blocklength=1,max_cache_entries=2048)
            with self.subTest(fixture=path.name):
                self.assertEqual(a.certificate.to_dict(),b.certificate.to_dict())
                self.assertTrue(b.verify(task))
            hits+=b.stats['search_counters'].get('subspace_cache_hits',0)
        self.assertGreater(hits,0)

    def test_generic_fixture_all_sources_independent_runtime(self):
        root=Path(__file__).resolve().parents[1]
        path=next((root/'benchmarks'/'fixtures').glob('generic_00_*.json'))
        task=task_from_dict(json.loads(path.read_text()))
        result=compile_task(task,fast_paths=False,force_blocklength=1)
        code=result.operating_code(task)
        oracle=Oracle(task.field.p,task.field.modulus)
        # All q**n sources, not random samples. Expected outputs use independent
        # polynomial arithmetic rather than production Matrix multiplication.
        columns=tuple(product(range(task.field.q),repeat=task.n))
        source=tuple(zip(*columns))
        observations=tuple(Matrix(task.field,oracle.product(a.rows,source,len(columns))) for a in task.original_side)
        output=code.execute(observations)
        for w,decoded in zip(task.original_demand,output.decoded):
            self.assertEqual(decoded.rows,oracle.product(w.rows,source,len(columns)))

    def test_adaptive_intersection_against_relation_oracle(self):
        rng=random.Random(1800)
        for q in (2,3,4,9,25):
            f=Field(q);o=Oracle(f.p,f.modulus)
            for _ in range(3):
                n=8
                a=Matrix(f,[[rng.randrange(q) for _ in range(n)] for _ in range(7)])
                b=Matrix(f,[[rng.randrange(q) for _ in range(n)] for _ in range(6)])
                relation=tuple(tuple(a[i][j] for i in range(a.nrows))+tuple(o.neg(b[i][j]) for i in range(b.nrows)) for j in range(n))
                reduced,pivots=o.reduced(relation,a.nrows+b.nrows)
                relations=[]
                for free in range(a.nrows+b.nrows):
                    if free in pivots:continue
                    row=[0]*(a.nrows+b.nrows);row[free]=1
                    for i,p in enumerate(pivots):row[p]=o.neg(reduced[i][free])
                    relations.append(row[:a.nrows])
                expected=o.product(relations,a.rows,n)
                expected,p=o.reduced(expected,n)
                self.assertEqual(intersection(a,b).rows,expected[:len(p)])

    def test_medium_extension_log_tables_exact_and_readonly(self):
        rng=random.Random(550)
        for q in (343,512,729,6561,65536):
            f=Field(q);o=Oracle(f.p,f.modulus)
            for _ in range(32):
                a,b=rng.randrange(q),rng.randrange(q)
                self.assertEqual(f.mul(a,b),o.mul(a,b))
                if a:self.assertEqual(f.mul(a,f.inv(a)),1)
            self.assertIsNotNone(f._log_data)
            self.assertTrue(f._log_data[0].readonly)
            with self.assertRaises(TypeError):f._log_data[0][1]=7

    def test_binary_products_above_machine_word_size(self):
        rng=random.Random(650)
        f=Field(2);o=Oracle(f.p,f.modulus)
        a=Matrix(f,[[rng.randrange(2) for _ in range(17)] for _ in range(9)])
        b=Matrix(f,[[rng.randrange(2) for _ in range(139)] for _ in range(17)])
        self.assertEqual((a@b).rows,o.product(a.rows,b.rows,139))

    def test_singular_large_rank_cache_consistency(self):
        for q in (2,3,4,343):
            f=Field(q)
            a=Matrix(f,[[int(j%7==i%7) for j in range(41)] for i in range(29)])
            self.assertEqual(rank(a),7)
            self.assertEqual(row_basis(a).nrows,7)
            self.assertEqual(rank(a),7)


if __name__=='__main__':unittest.main()
