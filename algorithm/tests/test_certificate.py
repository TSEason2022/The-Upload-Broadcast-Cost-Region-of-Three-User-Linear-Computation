import json
import unittest

from three_user_codes.certificate import (
    CodeCertificate, VerificationError, make_certificate,
    restrict_certificate_to_prime, restrict_matrix_to_prime,
)
from three_user_codes.field import Field
from three_user_codes.linalg import Matrix, eye, zeros
from three_user_codes.task import Task


def tripod_certificate(q=4):
    field = Field(q)
    side = tuple(Matrix(field, rows) for rows in ([[1, 0]], [[0, 1]], [[1, 1]]))
    task = Task(field, side, (eye(field, 2),) * 3)
    uploads = (side[0], side[1], zeros(field, 0, 2))
    return make_certificate(task, uploads, Matrix(field, [[1, 2]]),
                            expected_upload_count=2, expected_broadcast_count=1)


class CertificateTests(unittest.TestCase):
    def test_exact_identities_and_json(self):
        for q in (3, 4, 5, 9):
            certificate = tripod_certificate(q)
            report = certificate.verify(2, 1)
            self.assertEqual(report.upload_rank, 2)
            self.assertEqual(report.broadcast_rank, 1)
            recovered = CodeCertificate.from_dict(json.loads(json.dumps(certificate.to_dict())))
            self.assertEqual(recovered.signal, certificate.signal)
            self.assertEqual(recovered.verify(), report)

    def test_gf4_restriction_and_basis_multiplication(self):
        certificate = tripod_certificate()
        binary = restrict_certificate_to_prime(certificate)
        self.assertEqual(binary.task.field, Field(2))
        self.assertEqual(binary.blocklength, 2)
        self.assertEqual(binary.verify(4, 2).source_dimension, 4)
        f = Field(4)
        for a in range(4):
            for b in range(4):
                aa, bb = Matrix(f, [[a]]), Matrix(f, [[b]])
                self.assertEqual(restrict_matrix_to_prime(aa @ bb),
                                 restrict_matrix_to_prime(aa) @ restrict_matrix_to_prime(bb))
                self.assertEqual(restrict_matrix_to_prime(aa + bb),
                                 restrict_matrix_to_prime(aa) + restrict_matrix_to_prime(bb))

    def test_extension_restriction_for_odd_characteristic(self):
        f = Field(9)
        for a in range(9):
            for b in range(9):
                aa, bb = Matrix(f, [[a]]), Matrix(f, [[b]])
                self.assertEqual(restrict_matrix_to_prime(aa @ bb),
                                 restrict_matrix_to_prime(aa) @ restrict_matrix_to_prime(bb))
        restricted = restrict_certificate_to_prime(tripod_certificate(9))
        self.assertEqual(restricted.task.field, Field(3))
        restricted.verify(4, 2)

    def test_reject_wrong_broadcast_and_tampering(self):
        certificate = tripod_certificate()
        with self.assertRaises(VerificationError):
            make_certificate(certificate.task, certificate.uploads, Matrix(Field(4), [[1, 0]]))
        data = certificate.to_dict()
        data["decoders"][0]["rows"][0][0] ^= 1
        with self.assertRaises(VerificationError):
            CodeCertificate.from_dict(data)
        data = certificate.to_dict()
        data["local_maps"][0]["rows"][0][0] = 0
        with self.assertRaises(VerificationError):
            CodeCertificate.from_dict(data)
        with self.assertRaises(VerificationError):
            certificate.verify(expected_upload_count=1)
        with self.assertRaises(VerificationError):
            certificate.verify(expected_broadcast_count=2)

    def test_reject_binary_scalar_tripod(self):
        f = Field(2)
        side = tuple(Matrix(f, rows) for rows in ([[1, 0]], [[0, 1]], [[1, 1]]))
        task = Task(f, side, (eye(f, 2),) * 3)
        uploads = (side[0], side[1], zeros(f, 0, 2))
        for coefficients in ([0, 0], [1, 0], [0, 1], [1, 1]):
            with self.assertRaises(VerificationError):
                make_certificate(task, uploads, Matrix(f, [coefficients]))

    def test_zero_source_and_zero_communication(self):
        f = Field(3)
        empty = zeros(f, 0, 0)
        task = Task(f, (empty,) * 3, (empty,) * 3)
        certificate = make_certificate(task, (empty,) * 3, empty)
        self.assertEqual(certificate.verify(0, 0).upload_count, 0)
        whole = eye(f, 2)
        task = Task(f, (whole,) * 3, (whole,) * 3)
        certificate = make_certificate(task, (zeros(f, 0, 2),) * 3, empty)
        self.assertEqual(certificate.verify(0, 0).broadcast_rank, 0)

    def test_duplicate_transmission_reported_and_cost_rejected(self):
        cert = tripod_certificate(3)
        f = cert.task.field
        uploads = (Matrix(f, [[1, 0], [1, 0]]), cert.uploads[1], cert.uploads[2])
        duplicate = make_certificate(cert.task, uploads, Matrix(f, [[1, 0, 2]]))
        self.assertEqual(duplicate.verify().upload_count, 3)
        self.assertEqual(duplicate.verify().upload_rank, 2)
        with self.assertRaises(VerificationError):
            duplicate.verify(expected_upload_count=3)


if __name__ == "__main__":
    unittest.main()
