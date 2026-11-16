import unittest
from itertools import product

from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, eye, zeros, determinant, contains
from three_user_codes.coordination import (ColumnSpec, DecoderTemplate, avoid_linear_forms,
                                            avoid_subspaces, coordinate_columns)


class CoordinationTest(unittest.TestCase):
    def test_exhaustive_three_forms_dimension_two(self):
        for q in (3, 4):
            f = Field(q)
            # Exhaust all triples of projective linear forms, including repeats.
            forms = [(1, a) for a in range(q)] + [(0, 1)]
            for choice in product(forms, repeat=3):
                M = Matrix(f, choice)
                x = avoid_linear_forms(M)
                self.assertTrue(all(f.dot(row, x) for row in choice))
                self.assertEqual(x, avoid_linear_forms(M))

    def test_bad_forms_rejected(self):
        with self.assertRaises(ValueError):
            avoid_linear_forms(Matrix(Field(3), [[0, 0]]))
        with self.assertRaises(ValueError):
            avoid_linear_forms(Matrix(Field(2), [[1, 0], [0, 1], [1, 1]]))
        with self.assertRaises(ValueError):
            avoid_subspaces([eye(Field(3), 2)])

    def test_subspace_avoidance(self):
        f = Field(3)
        spaces = [Matrix(f, [[1, 0, 0]]), Matrix(f, [[0, 1, 0]]), Matrix(f, [[1, 1, 0]])]
        x = avoid_subspaces(spaces)
        for S in spaces:
            self.assertFalse(contains(S, Matrix(f, [x])))

    def test_column_updates_and_absent_groups(self):
        for q in (3, 4, 7):
            f = Field(q)
            I = eye(f, 3)
            templates = [DecoderTemplate(zeros(f, 3, 3),
                         tuple(ColumnSpec(g, g, I) for g in range(3))) for _ in range(3)]
            # Individually valid but deliberately different permutations.
            witnesses = [[I.rows[(g + i) % 3] for g in range(3)] for i in range(3)]
            result = coordinate_columns(templates, witnesses)
            self.assertTrue(all(determinant(M) for M in result.matrices))
            self.assertEqual(result.inverse_updates, 9)
            self.assertEqual(result.assignment, coordinate_columns(templates, witnesses).assignment)
            # A group can be absent in a decoder, with different matrix orders.
            templates2 = [DecoderTemplate(zeros(f, 1, 1), (ColumnSpec(0, 0, Matrix(f, [[1, 0]])),)),
                          DecoderTemplate(zeros(f, 1, 1), (ColumnSpec(0, 0, Matrix(f, [[0, 1]])),)),
                          DecoderTemplate(eye(f, 2), ())]
            result2 = coordinate_columns(templates2, [[(1, 0)], [(0, 1)], [(0, 0)]])
            self.assertTrue(all(determinant(M) for M in result2.matrices))

    def test_template_validation(self):
        f = Field(3)
        bad = DecoderTemplate(zeros(f, 2, 2), (ColumnSpec(0, 0, eye(f, 2)), ColumnSpec(0, 1, eye(f, 2))))
        with self.assertRaises(ValueError):
            coordinate_columns([bad], [[(1, 0)]])
        template = DecoderTemplate(zeros(f, 2, 2), (ColumnSpec(0, 0, eye(f, 2)),))
        with self.assertRaises(ValueError):
            coordinate_columns([template], [[(1, 0)]])


if __name__ == '__main__':
    unittest.main()
