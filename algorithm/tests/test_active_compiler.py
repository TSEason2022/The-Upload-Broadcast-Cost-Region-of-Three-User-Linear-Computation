"""End-to-end regressions for the formerly unresolved fractional-upload tasks."""
import random
import unittest
from fractions import Fraction

from three_user_codes import Task, compile_task


class ActiveCompilerTests(unittest.TestCase):
    def test_six_fractional_upload_regressions(self):
        fixtures = ((5,9,20261013,Fraction(9,2),3),
                    (5,5,20261016,Fraction(5,2),2),
                    (3,7,20261018,Fraction(7,2),3),
                    (2,9,20261020,Fraction(9,2),3),
                    (3,9,20261021,Fraction(9,2),3),
                    (5,9,20261022,Fraction(9,2),3))
        for q,n,seed,upload,download in fixtures:
            with self.subTest(q=q,n=n,seed=seed):
                rng=random.Random(seed)
                side=[[[int(j==k) for j in range(n)]
                       for k in range(n) if k%3==i] for i in range(3)]
                for rows in side:
                    rows.extend([[rng.randrange(q) for _ in range(n)]
                                 for _ in range(1+n//6)])
                demand=[[[rng.randrange(q) for _ in range(n)]
                         for _ in range(1+n//4)] for _ in range(3)]
                task=Task.from_rows(q,side,demand)
                result=compile_task(task,max_states=1000,max_seconds=10)
                self.assertEqual(result.upload_optimum,upload)
                self.assertEqual(result.broadcast_optimum,download)
                self.assertEqual(result.certificate.blocklength,2)
                self.assertEqual(result.stats['working_field'],q)
                result.verify(task)


if __name__ == '__main__':
    unittest.main()
