import copy
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from three_user_codes import Field, Matrix, Task, compile_task, resonant_task
from three_user_codes.compiler import SearchBudget, enumerate_subspaces
from three_user_codes.linalg import eye
from three_user_codes.io import (task_from_dict, task_to_dict, result_to_dict,
                                result_from_dict, read_json, write_json)
from three_user_codes.cli import main


class InterchangeTests(unittest.TestCase):
    def test_result_binding_and_claims(self):
        task = resonant_task(Field(3), 1)
        result = compile_task(task)
        data = result_to_dict(result, task)
        restored, original = result_from_dict(data)
        self.assertEqual(original, task)
        self.assertEqual(restored.certificate.signal, result.certificate.signal)
        for key in ("upload_optimum", "broadcast_optimum"):
            modified = copy.deepcopy(data)
            modified[key]["numerator"] += 1
            with self.assertRaises(ValueError): result_from_dict(modified)
        modified = copy.deepcopy(data)
        modified["input_task"]["demand"][0] = [[1, 0, 0, 0, 0]]
        with self.assertRaises(ValueError): result_from_dict(modified)

    def test_json_atomic_and_strict(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp)/"task.json"
            task = resonant_task(Field(4), 1)
            write_json(path, task_to_dict(task))
            self.assertEqual(task_from_dict(read_json(path)), task)
            for invalid in ('{"q":3,"q":4}', '{"x":NaN}', '{"x":Infinity}'):
                path.write_text(invalid, encoding="utf-8")
                with self.assertRaises(ValueError): read_json(path)

    def test_budget_validation_and_large_field_lazy_enumeration(self):
        for invalid in (True, float("nan"), float("inf"), "1", 0, -1):
            with self.assertRaises(ValueError): SearchBudget(max_seconds=invalid)
        task = resonant_task(Field(3), 1)
        for invalid in (True, 1.0, "1", 0, 3):
            with self.assertRaises(ValueError): compile_task(task, force_blocklength=invalid)
        field = Field(18446744073709551557)
        iterator = enumerate_subspaces(eye(field, 2), 1, SearchBudget(2, None))
        self.assertEqual(next(iterator).rows, ((1, 0),))
        self.assertEqual(next(iterator).rows, ((1, 1),))

    def test_cli_workflow(self):
        with tempfile.TemporaryDirectory() as tmp:
            task = str(Path(tmp)/"task.json")
            code = str(Path(tmp)/"code.json")
            def run(args):
                out = io.StringIO()
                with contextlib.redirect_stdout(out): status = main(args)
                self.assertEqual(status, 0, out.getvalue())
                return json.loads(out.getvalue())
            data = run(["demo", "--q", "2", "--output", code, "--task-output", task])
            self.assertEqual(data["blocklength"], 2)
            self.assertTrue(data["execution"]["decoded_exactly"])
            self.assertEqual(run(["inspect", task])["broadcast_optimum"], {"numerator":3,"denominator":2})
            self.assertEqual(run(["verify", code])["status"], "verified")
            self.assertTrue(run(["simulate", code])["execution"]["decoded_exactly"])
            self.assertEqual(run(["compile", task, "-o", code])["status"], "verified")


if __name__ == "__main__": unittest.main()
