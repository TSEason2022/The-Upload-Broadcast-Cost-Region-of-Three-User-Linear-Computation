"""Structural fast paths checked against global costs and exact flag identities."""
from fractions import Fraction
import random
import unittest

from three_user_codes.field import Field
from three_user_codes.linalg import (Matrix, block_diag, contains, eye, intersection,
                                     row_sum, vstack, zeros)
from three_user_codes.profile import broadcast_profile
from three_user_codes.structure import (binary_corank_one_candidates, coordinate_components,
                                        independent_observation_relay, omniscience_relay,
                                        pure_tripod_relay)
from three_user_codes.task import Task
from three_user_codes.upload_bound import upload_cost


class IndependentObservationStructureTests(unittest.TestCase):
    def check_relay(self, task, relay, expected_upload):
        self.assertIsNotNone(relay)
        self.assertEqual(relay.nrows, expected_upload)
        self.assertEqual(upload_cost(task), expected_upload)
        local = tuple(intersection(a, relay) for a in task.side)
        induced = tuple(intersection(u, relay) for u in task.augmented)
        self.assertEqual(row_sum(*local), relay)
        for a, w in zip(task.side, task.demand):
            self.assertTrue(contains(row_sum(a, relay), w))
        self.assertEqual(broadcast_profile(local, induced).branches,
                         broadcast_profile(task.side, task.augmented).branches)

    def test_inactive_private_directions_in_dense_source_coordinates(self):
        rng = random.Random(33081)
        for q in (2, 3, 4, 9):
            f = Field(q)
            # Seven observed directions in a larger source; the upper
            # triangular change of basis hides their coordinate supports.
            transform = Matrix(f, [[int(i == j) if j <= i else rng.randrange(q)
                                    for j in range(9)] for i in range(9)], ncols=9)
            side = tuple(Matrix(f, eye(f, 7).rows[1 + 2*i:3 + 2*i], 7)
                         for i in range(3))
            common = Matrix(f, [eye(f, 7).rows[0]], 7)
            side = tuple(vstack(common, a) @ Matrix(f, transform.rows[:7], 9)
                         for a in side)
            # Every remote user needs only the first private coordinate
            # of each owner; their second coordinates occur only locally.
            demands = []
            for user in range(3):
                row = [0] * 7
                row[0] = 1
                row[2 + 2*user] = 1
                for owner in range(3):
                    if owner != user:
                        row[1 + 2*owner] = 1
                demands.append(Matrix(f, [row], 7) @ Matrix(f, transform.rows[:7], 9))
            task = Task(f, side, tuple(demands))
            self.check_relay(task, independent_observation_relay(task), 3)

    def test_independent_private_projection_may_be_a_linear_combination(self):
        for q in (2, 3, 4):
            f = Field(q)
            e = eye(f, 6)
            side = tuple(Matrix(f, e.rows[2*i:2*i+2], 6) for i in range(3))
            task = Task(f, side, (Matrix(f, [[0, 0, 1, 1, 1, 1]], 6),
                                  Matrix(f, [[1, 1, 0, 0, 1, 1]], 6),
                                  Matrix(f, [[1, 1, 1, 1, 0, 0]], 6)))
            relay = independent_observation_relay(task)
            self.check_relay(task, relay, 3)
            self.assertEqual(relay.rows, ((1, 1, 0, 0, 0, 0),
                                          (0, 0, 1, 1, 0, 0),
                                          (0, 0, 0, 0, 1, 1)))

    def test_tripod_is_not_misclassified_as_independent(self):
        f = Field(2)
        task = Task.from_rows(f, [[[1, 0]], [[0, 1]], [[1, 1]]],
                              [[[0, 1]], [[1, 0]], [[1, 0]]])
        self.assertIsNone(independent_observation_relay(task))

    def test_no_communication_needed_with_nonindependent_sides(self):
        task = Task.from_rows(2, [[[1, 0]], [[0, 1]], [[1, 1]]],
                              [[[1, 0]], [[0, 1]], [[1, 1]]])
        self.check_relay(task, independent_observation_relay(task), 0)
        empty = Task.from_rows(3, [[], [], []], [[], [], []], n=0)
        self.assertEqual(independent_observation_relay(empty), zeros(empty.field, 0, 0))

    def test_bad_input_rejected(self):
        with self.assertRaises(TypeError):
            independent_observation_relay(None)


class CoordinateComponentTests(unittest.TestCase):
    def assert_flag_reconstruction(self, task, components):
        for index in range(3):
            for attr in ("side", "augmented"):
                spaces = [getattr(c.task, attr)[index] @ c.embedding for c in components]
                reconstructed = row_sum(*spaces) if spaces else zeros(task.field, 0, task.n)
                self.assertEqual(reconstructed, getattr(task, attr)[index])

    def test_disconnected_flags_and_unused_ambient_columns(self):
        f = Field(3)
        task = Task.from_rows(f,
                             [[[1, 1, 0, 0, 0]], [[0, 0, 1, 1, 0]], []],
                             [[[0, 0, 1, 1, 0]], [[1, 1, 0, 0, 0]], []])
        components = coordinate_components(task)
        self.assertEqual(tuple(c.columns for c in components), ((0, 1), (2, 3)))
        self.assert_flag_reconstruction(task, components)
        for component in components:
            self.assertEqual(component.embedding.shape, (2, 5))
            self.assertIs(component.embedding, component.embedding)

    def test_coupled_demand_keeps_a_connected_component(self):
        task = Task.from_rows(2, [[[1, 0]], [[0, 1]], []],
                              [[], [], [[1, 1]]])
        components = coordinate_components(task)
        self.assertEqual(tuple(c.columns for c in components), ((0, 1),))
        self.assert_flag_reconstruction(task, components)

    def test_redundancy_and_measurement_order_do_not_change_partition(self):
        task = Task.from_rows(3, [[[1, 1, 0]], [[0, 0, 1]], []],
                              [[[0, 0, 1]], [[1, 1, 0]], []])
        redundant = Task(task.field,
                         tuple(vstack(a, a) for a in reversed(task.side)),
                         tuple(vstack(w, w) for w in reversed(task.demand)))
        self.assertEqual(tuple(c.columns for c in coordinate_components(task)),
                         tuple(c.columns for c in coordinate_components(redundant)))

    def test_component_broadcast_optima_are_not_additive(self):
        task = Task.from_rows(2, [[[1, 0]], [[0, 1]], []],
                              [[[0, 1]], [[1, 0]], []])
        components = coordinate_components(task)
        local_costs = sum(broadcast_profile(c.task.side, c.task.augmented).cost
                          for c in components)
        global_cost = broadcast_profile(task.side, task.augmented).cost
        self.assertEqual(local_costs, 2)
        self.assertEqual(global_cost, 1)
        summed_branches = tuple(sum(broadcast_profile(c.task.side, c.task.augmented).branches[j]
                                    for c in components) for j in range(15))
        self.assertEqual(max(summed_branches), global_cost)
        self.assert_flag_reconstruction(task, components)

    def test_component_upload_optima_also_need_global_validation(self):
        task = Task.from_rows(2, [[[0, 1, 0], [0, 0, 1]],
                                 [[1, 0, 0], [0, 0, 1]],
                                 [[1, 0, 0], [0, 1, 0]]],
                              [[[1, 0, 0]], [[0, 1, 0]], [[0, 0, 1]]])
        components = coordinate_components(task)
        self.assertEqual(len(components), 3)
        self.assertEqual(sum(upload_cost(c.task) for c in components), 3)
        self.assertEqual(upload_cost(task), Fraction(3, 2))
        self.assert_flag_reconstruction(task, components)

    def test_empty_and_invalid_inputs(self):
        task = Task.from_rows(2, [[], [], []], [[], [], []], n=7)
        self.assertEqual(coordinate_components(task), ())
        with self.assertRaises(TypeError):
            coordinate_components(None)


class BinaryCorankOneTests(unittest.TestCase):
    def test_binary_obstruction_is_solved_by_two_candidate_instances(self):
        from itertools import product
        from three_user_codes.compiler import resonant_task
        task = resonant_task(Field(2), 1)
        candidates = binary_corank_one_candidates(task)
        self.assertGreater(len(candidates), 0)
        self.assertLessEqual(len(candidates), 12)
        full = broadcast_profile(task.side, task.augmented).cost
        lifted = task.lift(2)
        best = min(broadcast_profile(
            tuple(intersection(a, block_diag(p, q)) for a in lifted.side),
            tuple(intersection(u, block_diag(p, q)) for u in lifted.augmented)).cost
            for p, q in product(candidates, repeat=2))
        self.assertEqual(best, 2 * full)

    def test_dense_large_binary_component_has_bounded_candidates(self):
        from three_user_codes.compiler import resonant_task
        rng = random.Random(5012)
        source = resonant_task(Field(2), 10)
        change = Matrix(source.field,
                        [[int(i == j) if j <= i else rng.randrange(2)
                          for j in range(source.n)] for i in range(source.n)], source.n)
        task = Task(source.field, tuple(a @ change for a in source.side),
                    tuple(w @ change for w in source.demand))
        candidates = binary_corank_one_candidates(task)
        self.assertGreater(len(candidates), 0)
        self.assertLessEqual(len(candidates), 12)
        for relay in candidates:
            self.assertEqual(relay.nrows, task.n - 1)
            self.assertEqual(row_sum(*(intersection(a, relay) for a in task.side)), relay)
            self.assertTrue(all(contains(row_sum(a, relay), w)
                                for a, w in zip(task.side, task.demand)))

    def test_unsupported_structures_are_not_called_infeasible(self):
        from three_user_codes.compiler import resonant_task
        self.assertEqual(binary_corank_one_candidates(resonant_task(Field(3), 1)), ())
        independent = Task.from_rows(2, [[[1, 0]], [[0, 1]], []],
                                     [[[0, 1]], [[1, 0]], []])
        self.assertEqual(binary_corank_one_candidates(independent), ())
        full_demand = Task.from_rows(2, [[[1, 0]], [[1, 0]], [[0, 1]]],
                                     [[[0, 1]], [[0, 1]], [[1, 0]]])
        self.assertEqual(binary_corank_one_candidates(full_demand), ())
        with self.assertRaises(TypeError):
            binary_corank_one_candidates(None)


class OmniscienceStructureTests(unittest.TestCase):
    @staticmethod
    def make_task(q, tripod, pairs=(0, 0, 0), private=(0, 0, 0), common=0,
                  change_coordinates=False):
        f = Field(q)
        n = common + sum(pairs) + sum(private) + 2 * tripod
        identity = eye(f, n)
        offset = common
        pair_spaces = []
        for count in pairs:
            pair_spaces.append(Matrix(f, identity.rows[offset:offset + count], n))
            offset += count
        private_spaces = []
        for count in private:
            private_spaces.append(Matrix(f, identity.rows[offset:offset + count], n))
            offset += count
        v = Matrix(f, identity.rows[offset:offset + tripod], n)
        r = Matrix(f, identity.rows[offset + tripod:offset + 2 * tripod], n)
        common_space = Matrix(f, identity.rows[:common], n)
        views = (v, r, r - v)
        side = tuple(vstack(common_space, private_spaces[user], views[user],
                            *(pair_spaces[other] for other in range(3) if other != user))
                     for user in range(3))
        if change_coordinates:
            rng = random.Random(83 + q + n)
            # Include two source directions outside the generated span.
            transform = Matrix(f, [[int(i == j) if j <= i else rng.randrange(q)
                                    for j in range(n + 2)] for i in range(n)], n + 2)
            return Task(f, tuple(a @ transform for a in side), (transform,) * 3)
        return Task(f, side, (identity,) * 3)

    def assert_optimal_relay(self, task):
        target = upload_cost(task)
        relay = omniscience_relay(task)
        if target.denominator != 1:
            self.assertIsNone(relay)
            task = task.lift(2)
            relay = omniscience_relay(task)
            target *= 2
        self.assertIsNotNone(relay)
        self.assertEqual(relay.nrows, target)
        local = tuple(intersection(a, relay) for a in task.side)
        induced = tuple(intersection(u, relay) for u in task.augmented)
        self.assertEqual(row_sum(*local), relay)
        self.assertTrue(all(contains(row_sum(a, relay), u)
                            for a, u in zip(task.side, task.augmented)))
        self.assertEqual(broadcast_profile(local, induced).branches,
                         broadcast_profile(task.side, task.augmented).branches)

    def test_original_field_mixed_components_and_coordinate_changes(self):
        for q in (2, 3, 4, 9):
            for tripod in (0, 1, 2):
                for pairs in ((0, 0, 0), (1, 0, 0), (1, 1, 1),
                              (3, 0, 1), (0, 5, 0), (2, 3, 4)):
                    with self.subTest(q=q, tripod=tripod, pairs=pairs):
                        task = self.make_task(q, tripod, pairs, private=(1, 0, 2),
                                              common=1, change_coordinates=True)
                        self.assert_optimal_relay(task)

    def test_large_tripods_do_not_enumerate_subspaces(self):
        for q in (2, 3):
            for tripod in (10, 30):
                self.assert_optimal_relay(self.make_task(q, tripod))

    def test_zero_information_and_all_common_information(self):
        self.assert_optimal_relay(self.make_task(2, 0))
        self.assert_optimal_relay(self.make_task(3, 0, common=4))

    def test_non_omniscience_and_bad_input(self):
        task = Task.from_rows(2, [[[1, 0]], [[0, 1]], []],
                              [[[0, 1]], [[1, 0]], []])
        self.assertIsNone(omniscience_relay(task))
        with self.assertRaises(TypeError):
            omniscience_relay(None)


class FunctionalTripodTests(unittest.TestCase):
    def check_candidate(self, task, *, require_broadcast_optimum=False):
        target = upload_cost(task)
        relay = pure_tripod_relay(task)
        if target.denominator != 1:
            self.assertIsNone(relay)
            task = task.lift(2)
            target *= 2
            relay = pure_tripod_relay(task)
        self.assertIsNotNone(relay)
        self.assertEqual(relay.nrows, target)
        local = tuple(intersection(a, relay) for a in task.side)
        induced = tuple(intersection(u, relay) for u in task.augmented)
        self.assertEqual(row_sum(*local), relay)
        self.assertTrue(all(contains(row_sum(a, relay), w)
                            for a, w in zip(task.side, task.demand)))
        selected_cost = broadcast_profile(local, induced).cost
        full_cost = broadcast_profile(task.side, task.augmented).cost
        if require_broadcast_optimum:
            self.assertEqual(selected_cost, full_cost)
        else:
            self.assertGreaterEqual(selected_cost, full_cost)
        if selected_cost > full_cost:
            # Upload optimality alone cannot justify returning a code. The
            # global acceptance gate must reject a worse broadcast profile.
            from three_user_codes.compiler import _accept
            self.assertIsNone(_accept(task, relay, int(target), full_cost))

    def test_random_dense_tasks_and_remeasured_demands(self):
        rng = random.Random(70193)
        for q in (2, 3, 4, 8, 9):
            for t in (1, 2, 3, 5):
                for trial in range(3):
                    f = Field(q)
                    source = OmniscienceStructureTests.make_task(q, t)
                    v, r = source.side[:2]
                    demands = []
                    for user in range(3):
                        count = t if trial == 0 else rng.randrange(t + 1)
                        missing = eye(f, t) if trial == 0 else Matrix(
                            f, [[rng.randrange(q) for _ in range(t)] for _ in range(count)], t)
                        known = Matrix(f, [[rng.randrange(q) for _ in range(t)]
                                           for _ in range(count)], t)
                        demand = missing @ (r if user == 0 else v) + known @ source.side[user]
                        measurement = Matrix(f,
                                             [[int(i == j) if j <= i else rng.randrange(q)
                                               for j in range(count)] for i in range(count)], count)
                        demands.append(vstack(measurement @ demand, demand))
                    change = Matrix(f, [[int(i == j) if j <= i else rng.randrange(q)
                                         for j in range(2*t + 1)] for i in range(2*t)], 2*t + 1)
                    task = Task(f, tuple(a @ change for a in source.side),
                                tuple(w @ change for w in demands))
                    with self.subTest(q=q, t=t, trial=trial):
                        self.check_candidate(task)

    def test_two_dimensional_demand_tripod_with_common_half_rate(self):
        for q in (2, 3, 8):
            f = Field(q)
            source = OmniscienceStructureTests.make_task(q, 3)
            v, r = source.side[:2]
            d0 = Matrix(f, [[1, 0, 0], [0, 1, 0]], 3)
            d1 = Matrix(f, [[1, 0, 0], [0, 0, 1]], 3)
            d2 = Matrix(f, [[1, 0, 0], [0, f.neg(1), 1]], 3)
            task = Task(f, source.side, (d0 @ r, d1 @ v, d2 @ v))
            self.assertEqual(upload_cost(task), Fraction(7, 2))
            self.check_candidate(task, require_broadcast_optimum=True)

    def test_reported_gf8_fractional_stress_regression(self):
        f = Field(8, modulus=(1, 1, 0, 1))
        task = Task.from_rows(f,
            [[(1, 0, 0, 0), (0, 0, 0, 1)],
             [(1, 0, 4, 7), (0, 1, 0, 0)],
             [(0, 1, 0, 5), (0, 0, 1, 0)]],
            [[(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)],
             [(1, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 4)],
             [(1, 0, 0, 1), (0, 1, 0, 5), (0, 0, 1, 0)]])
        self.assertEqual(upload_cost(task), Fraction(5, 2))
        self.check_candidate(task, require_broadcast_optimum=True)

    def test_side_private_pair_and_common_summands_are_not_generalized(self):
        for kwargs in ({"pairs": (1, 0, 0)}, {"private": (1, 0, 0)}, {"common": 1}):
            task = OmniscienceStructureTests.make_task(2, 1, **kwargs)
            self.assertIsNone(pure_tripod_relay(task))
        with self.assertRaises(TypeError):
            pure_tripod_relay(None)


if __name__ == "__main__":
    unittest.main()
