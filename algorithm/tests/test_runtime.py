import unittest

from three_user_codes.certificate import VerificationError, make_certificate
from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, lift, zeros
from three_user_codes.runtime import OperatingCode
from three_user_codes.task import Task


def original_task(q=3):
    f = Field(q)
    side = tuple(Matrix(f, rows) for rows in (
        [[0, 2], [0, 1], [0, 0]], [[1, 0], [2, 0]], [[1, 1], [2, 2], [0, 0]],
    ))
    demand = tuple(Matrix(f, rows) for rows in (
        [[0, 1], [1, 0], [1, 1], [0, 0]], [[2, 1], [1, 0]], [[2, 2], [1, 0], [0, 1]],
    ))
    return Task(f, side, demand)


def operating_code(q=3, length=1):
    task = original_task(q)
    f = task.field
    uploads = (Matrix(f, [[0, 1]]), Matrix(f, [[1, 0]]), zeros(f, 0, 2))
    b = Matrix(f, [[2, 1]])
    # B for L>1 must account for stacked-user rather than stacked-instance uploads.
    if length > 1:
        rows = []
        for instance in range(length):
            row = [0] * (2 * length)
            row[instance], row[length + instance] = 2, 1
            rows.append(row)
        b = Matrix(f, rows)
    certificate = make_certificate(task.lift(length), tuple(lift(e, length) for e in uploads),
                                    b, blocklength=length)
    return OperatingCode(certificate, task)


class RuntimeTests(unittest.TestCase):
    def execute(self, runtime, source):
        observations = tuple(a @ source for a in runtime.original_side)
        uploads = runtime.encode_uploads(observations)
        for i in range(3):
            self.assertEqual(runtime.encode_upload(i, observations[i]), uploads[i])
            self.assertEqual(uploads[i], runtime.certificate.uploads[i] @ source)
        message = runtime.broadcast(uploads)
        self.assertEqual(message, runtime.certificate.signal @ source)
        for i in range(3):
            self.assertEqual(runtime.decode(i, observations[i], message), runtime.original_demand[i] @ source)

    def test_original_row_order_and_redundancy(self):
        for q in (3, 4, 5):
            runtime = operating_code(q)
            source = Matrix(Field(q), [[a for a in range(q) for b in range(q)],
                                       [b for a in range(q) for b in range(q)]])
            self.execute(runtime, source)
            self.assertEqual(runtime.original_local_maps[0].ncols, 3)
            self.assertEqual(runtime.original_decoders[0].nrows, 4)
            self.assertTrue(runtime.verify())

    def test_instance_major_two_blocks(self):
        runtime = operating_code(3, 2)
        source = Matrix(Field(3), [[0, 1, 2], [1, 1, 0], [2, 0, 1], [0, 2, 1]])
        self.execute(runtime, source)

    def test_empty_sample_batch(self):
        runtime = operating_code()
        self.execute(runtime, zeros(Field(3), 2, 0))

    def test_reject_shape_field_and_index_errors(self):
        runtime = operating_code()
        with self.assertRaises(ValueError):
            runtime.encode_upload(0, zeros(Field(3), 1, 1))
        with self.assertRaises(ValueError):
            runtime.encode_upload(0, zeros(Field(4), 3, 1))
        with self.assertRaises(ValueError):
            runtime.encode_upload(True, zeros(Field(3), 3, 1))
        with self.assertRaises(TypeError):
            runtime.encode_upload(0, [0, 0, 0])
        with self.assertRaises(ValueError):
            runtime.broadcast((zeros(Field(3), 1, 1), zeros(Field(3), 1, 2), zeros(Field(3), 0, 1)))
        with self.assertRaises(ValueError):
            runtime.decode(0, zeros(Field(3), 3, 1), zeros(Field(3), 1, 2))

    def test_reject_mismatched_original_task(self):
        runtime = operating_code()
        f = Field(3)
        other = Task(f, (Matrix(f, [[1, 0], [0, 1]]),) * 3, runtime.original_task.demand)
        with self.assertRaises(VerificationError):
            OperatingCode(runtime.certificate, other)


if __name__ == "__main__":
    unittest.main()
