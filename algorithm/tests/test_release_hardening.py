"""Interchange trust-boundary and original-field blocklength regressions."""
from __future__ import annotations

import copy
import sys
import unittest
from unittest.mock import patch

from three_user_codes import (
    Field, InputFormatError, ReadLimits, Task, VerificationError, compile_task,
)
from three_user_codes.io import loads_json, result_from_dict, result_to_dict


class InterchangeHardeningTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.task = Task.from_rows(
            Field(3), [[[1, 0, 0, 0, 0, 0, 0]]] * 3, [[], [], []], n=7)
        cls.result = compile_task(cls.task)
        cls.data = result_to_dict(cls.result, cls.task)

    def test_invalid_unicode_is_normalized(self):
        for value in ('"\ud800"', '"\udfff"', b'"\xff"'):
            with self.subTest(value=repr(value)):
                with self.assertRaises(InputFormatError):
                    loads_json(value)

    def test_integer_conversion_error_is_normalized(self):
        # CPython's configurable integer-string bound exists on supported
        # patched 3.10 releases and all newer versions; do not alter global state.
        get_limit = getattr(sys, "get_int_max_str_digits", None)
        if get_limit is None or not get_limit():
            self.skipTest("runtime does not impose an integer-string digit limit")
        with self.assertRaises(InputFormatError):
            loads_json('{"integer":' + '1' * (get_limit() + 1) + '}')

    def test_compiled_input_uses_one_aggregate_cell_budget(self):
        # The input and certificate each store 21 cells; the whole code stores 42.
        with patch('three_user_codes.io.CodeCertificate.from_dict') as reconstruct:
            with self.assertRaisesRegex(InputFormatError, "total max_cells"):
                result_from_dict(self.data, limits=ReadLimits(max_cells=41))
            reconstruct.assert_not_called()
        result, task = result_from_dict(self.data, limits=ReadLimits(max_cells=42))
        self.assertTrue(result.verify(task))

    def test_broadcast_product_is_bounded_before_reconstruction(self):
        data = copy.deepcopy(self.data)
        # A 10x0 broadcast costs no stored scalar cells, but multiplying it by
        # the 0x7 upload creates 70 signal cells. Stored input remains 42 cells.
        data['certificate']['broadcast'] = {'rows': [[] for _ in range(10)], 'ncols': 0}
        for decoder in data['certificate']['decoders']:
            decoder['ncols'] = 10
        with patch('three_user_codes.io.CodeCertificate.from_dict') as reconstruct:
            with self.assertRaisesRegex(InputFormatError, "signal exceeds max_cells"):
                result_from_dict(data, limits=ReadLimits(max_cells=50))
            reconstruct.assert_not_called()

    def test_metadata_is_bound_before_certificate_algebra(self):
        for name, update in (
                ('blocklength', lambda c: c.update(blocklength=2)),
                ('field', lambda c: c.update(field=Field(5).to_dict())),
                ('base field', lambda c: c.update(base_field=Field(5).to_dict())),
                ('broadcast width', lambda c: c['broadcast'].update(ncols=1)),
                ('local map', lambda c: c['local_maps'][0].update(ncols=2))):
            data = copy.deepcopy(self.data)
            update(data['certificate'])
            with self.subTest(name=name):
                with patch('three_user_codes.io.CodeCertificate.from_dict') as reconstruct:
                    with self.assertRaises(VerificationError):
                        result_from_dict(data)
                    reconstruct.assert_not_called()

    def test_unknown_verification_summary_never_authorizes_code(self):
        data = copy.deepcopy(self.data)
        data['verification'] = {'verified': True}
        data['upload_optimum']['numerator'] = 1
        with self.assertRaises(VerificationError):
            result_from_dict(data)


if __name__ == '__main__':
    unittest.main()
