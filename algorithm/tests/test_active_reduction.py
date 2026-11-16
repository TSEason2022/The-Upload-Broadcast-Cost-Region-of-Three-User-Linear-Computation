"""Source-map and rank-profile certificates for constructive active reduction."""
from itertools import permutations
import random
import unittest

from three_user_codes import Field, Matrix, Task, resonant_task
from three_user_codes.active_reduction import active_reduce
from three_user_codes.linalg import (block_diag, contains, eye, row_sum,
                                     vstack, zeros)
from three_user_codes.profile import broadcast_profile
from three_user_codes.structure import omniscience_relay
from three_user_codes.upload_bound import upload_cost, upload_parameters


def direct_sum(*tasks):
    return Task(tasks[0].field,
                tuple(block_diag(*(task.side[i] for task in tasks)) for i in range(3)),
                tuple(block_diag(*(task.demand[i] for task in tasks)) for i in range(3)))


def mix_coordinates(task, seed=4120):
    rng, f, n = random.Random(seed), task.field, task.n
    upper = Matrix(f, ((int(i == j) if j <= i else rng.randrange(f.q)
                        for j in range(n)) for i in range(n)), n)
    lower = Matrix(f, ((int(i == j) if j >= i else rng.randrange(f.q)
                        for j in range(n)) for i in range(n)), n)
    transform = upper @ lower
    return Task(f, tuple(a @ transform for a in task.side),
                tuple(w @ transform for w in task.demand))


class ActiveReductionTests(unittest.TestCase):
    def check_reduction(self, task):
        result = active_reduce(task)
        self.assertTrue(result.verify(task))
        original = broadcast_profile(task.side, task.augmented)
        profiles = [broadcast_profile(c.task.side, c.task.augmented)
                    for c in result.components]
        self.assertEqual(tuple(sum(p.branches[j] for p in profiles) for j in range(15)),
                         original.branches)
        self.assertEqual(sum(upload_cost(c.task) for c in result.components), upload_cost(task))
        p = result.parameters
        residual = upload_parameters(result.residual.task)
        self.assertEqual((residual.rho, residual.r0, residual.b, residual.c, residual.tau),
                         (p.rho, p.r0, p.b, 0, (0, 0, 0)))
        om = result.omniscience.task
        self.assertEqual(upload_cost(om), p.omega)
        self.assertEqual(upload_cost(result.residual.task), p.rho + p.r0 + p.b)
        return result

    def test_empty_common_and_unobserved_source_columns(self):
        for q in (2, 3, 4, 9):
            f = Field(q)
            for n in (0, 4):
                empty = zeros(f, 0, n)
                result = self.check_reduction(Task(f, (empty,) * 3, (empty,) * 3))
                self.assertEqual([c.task.n for c in result.components], [0, 0, 0])
            common = Matrix(f, [[1, 0, 1, 0]], 4)
            result = self.check_reduction(Task(f, (common,) * 3, (common,) * 3))
            self.assertEqual([c.task.n for c in result.components], [0, 0, 1])
            sides = tuple(Matrix(f, [row + (0, 0)], 5) for row in eye(f, 3).rows)
            result = self.check_reduction(Task(f, sides, (sides[1], sides[2], sides[0])))
            self.assertEqual(result.residual.task.n, 3)

    def test_all_side_only_normal_components_are_passive(self):
        for q in (2, 3, 4):
            f = Field(q)
            e = eye(f, 9).rows
            # Common, three pairs, three private rows, one tripod.
            side = tuple(Matrix(f, [e[0], *(e[1+j] for j in range(3) if j != i),
                                    e[4+i], e[7] if i == 0 else e[8] if i == 1 else
                                    tuple(f.sub(b, a) for a, b in zip(e[7], e[8]))], 9)
                         for i in range(3))
            result = self.check_reduction(mix_coordinates(Task(f, side, side)))
            self.assertEqual([c.task.n for c in result.components], [0, 0, 9])

    def test_nonzero_graph_obstruction_with_passive_shears(self):
        for q in (2, 3, 4, 5, 9):
            f = Field(q)
            core = resonant_task(f, 1)
            e = eye(f, 4).rows
            v, r = Matrix(f, e[:2], 4), Matrix(f, e[2:], 4)
            empty = zeros(f, 0, 4)
            passive_tripod = Task(f, (v, r, r-v), (empty,) * 3)
            unit = eye(f, 3).rows
            pairs = tuple(Matrix(f, [unit[j] for j in range(3) if j != i], 3)
                          for i in range(3))
            passive_pairs = Task(f, pairs, (zeros(f, 0, 3),) * 3)
            private = tuple(Matrix(f, [unit[i]], 3) for i in range(3))
            passive_private = Task(f, private, (zeros(f, 0, 3),) * 3)
            one = eye(f, 1)
            task = direct_sum(core, passive_tripod, passive_pairs, passive_private,
                              Task(f, (one,) * 3, (one,) * 3))
            # The resonant core orders a,b,c,v,r. Add passive tripod views
            # to each user's active private coordinate; this is an actual
            # nonzero graph canceled by Lemma 18, not a discarded zero row.
            graph = [[0] * task.n for _ in range(task.n)]
            graph[0][5] = 1
            graph[1][7] = 1
            graph[2][5], graph[2][7] = f.neg(1), 1
            transform = eye(f, task.n) + Matrix(f, graph, task.n)
            task = Task(f, tuple(a @ transform for a in task.side),
                        tuple(w @ transform for w in task.demand))
            # Add graphs into each passive pair space. The missing-view
            # functionals respectively kill v, r, and r-v.
            graph = [[0] * task.n for _ in range(task.n)]
            graph[4][9] = 1
            graph[3][10] = 1
            graph[3][11] = graph[4][11] = 1
            transform = eye(f, task.n) + Matrix(f, graph, task.n)
            task = Task(f, tuple(a @ transform for a in task.side),
                        tuple(w @ transform for w in task.demand))
            task = mix_coordinates(task, 1951 + q)
            result = self.check_reduction(task)
            self.assertEqual(result.parameters.b, 1)
            self.assertEqual([c.task.n for c in result.components], [0, 5, 11])
            if q in (2, 3, 4):
                for order in permutations(range(3)):
                    permuted = Task(f, tuple(task.side[i] for i in order),
                                    tuple(task.demand[i] for i in order))
                    reordered = self.check_reduction(permuted)
                    self.assertEqual(reordered.parameters.b, 1)
                    self.assertEqual([c.task.n for c in reordered.components], [0, 5, 11])

    def test_stress_fixtures_have_tiny_residuals(self):
        # Reconstruct the six previously unresolved random tasks directly,
        # independently of benchmark module import paths.
        fixtures = ((5, 9, 20261013, (6, 0, 3)),
                    (5, 5, 20261016, (2, 2, 1)),
                    (3, 7, 20261018, (5, 1, 1)),
                    (2, 9, 20261020, (4, 3, 2)),
                    (3, 9, 20261021, (4, 4, 1)),
                    (5, 9, 20261022, (4, 3, 2)))
        for q, n, seed, dimensions in fixtures:
            f, rng = Field(q), random.Random(seed)
            full = eye(f, n)
            side = [[list(full.rows[j]) for j in range(n) if j % 3 == i] for i in range(3)]
            for i in range(3):
                side[i].extend([[rng.randrange(q) for _ in range(n)] for _ in range(1 + n//6)])
            want = [[[rng.randrange(q) for _ in range(n)] for _ in range(1 + n//4)]
                    for _ in range(3)]
            result = self.check_reduction(Task.from_rows(f, side, want, n=n))
            self.assertEqual(tuple(c.task.n for c in result.components), dimensions)

    def test_omniscience_relay_embedding_preserves_the_fifteen_branches(self):
        for q in (2, 3, 4):
            f = Field(q)
            e = eye(f, 5).rows
            v, r = Matrix(f, e[:1], 5), Matrix(f, e[1:2], 5)
            sides = tuple(row_sum((v, r, r-v)[i],
                         Matrix(f, [e[2+j] for j in range(3) if j != i], 5)) for i in range(3))
            task = mix_coordinates(Task(f, sides, (eye(f, 5),) * 3))
            result = self.check_reduction(task)
            om = result.omniscience
            relay = omniscience_relay(om.task.lift(2))
            self.assertIsNotNone(relay)
            lifted = om.task.lift(2)
            from three_user_codes.linalg import intersection, lift
            induced = broadcast_profile(tuple(intersection(a, relay) for a in lifted.side),
                                        (relay,) * 3)
            self.assertEqual(induced.branches,
                             broadcast_profile(lifted.side, lifted.augmented).branches)
            original_relay = relay @ lift(om.embedding, 2)
            self.assertTrue(all(contains(row_sum(a, original_relay), u)
                                for a, u in zip(task.lift(2).side, task.lift(2).augmented)))

    def test_random_prime_and_extension_fields(self):
        rng = random.Random(19431006)
        for q in (2, 3, 4, 5, 9):
            f = Field(q)
            for trial in range(18):
                n = trial % 7
                side = tuple(Matrix(f, [[rng.randrange(q) for _ in range(n)]
                             for _ in range(rng.randrange(n + 2))], n) for _ in range(3))
                available = row_sum(*side)
                demand = tuple(Matrix(f, [[rng.randrange(q) for _ in range(available.nrows)]
                               for _ in range(rng.randrange(n + 2))], available.nrows) @ available
                               for _ in range(3))
                with self.subTest(q=q, trial=trial):
                    self.check_reduction(Task(f, side, demand))

    def test_bad_input_rejected(self):
        with self.assertRaises(TypeError):
            active_reduce(None)


if __name__ == "__main__":
    unittest.main()
