"""The command line counts instances over the caller's original field."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest

from three_user_codes.cli import main
from three_user_codes import Field, resonant_task, save_task


class OriginalFieldCLITests(unittest.TestCase):
    def test_inspect_reports_minimal_length_without_synthesis(self):
        with tempfile.TemporaryDirectory() as directory:
            path = str(Path(directory) / 'task.json')
            for n, minimum in ((1, 2), (2, 1)):
                save_task(resonant_task(Field(2), n), path)
                stream = io.StringIO()
                with contextlib.redirect_stdout(stream):
                    status = main(['inspect', path])
                self.assertEqual(status, 0)
                self.assertEqual(json.loads(stream.getvalue())['minimum_linear_blocklength'], minimum)

    def test_binary_two_instance_alias_and_scalar_rejection(self):
        with tempfile.TemporaryDirectory() as directory:
            output = str(Path(directory) / "code.json")
            for flag in ("--blocklength", "--force-working-blocklength"):
                stream = io.StringIO()
                with contextlib.redirect_stdout(stream):
                    status = main(["demo", "--q", "2", flag, "2", "--output", output])
                self.assertEqual(status, 0)
                result = json.loads(stream.getvalue())
                self.assertEqual(result["q"], 2)
                self.assertEqual(result["blocklength"], 2)
                self.assertEqual(result["upload_symbols"], 8)
                self.assertEqual(result["broadcast_symbols"], 3)
                self.assertTrue(result["execution"]["decoded_exactly"])
            old = Path(output).read_bytes()
            errors = io.StringIO()
            with contextlib.redirect_stderr(errors):
                status = main(["demo", "--q", "2", "--blocklength", "1", "--output", output])
            self.assertEqual(status, 2)
            self.assertEqual(json.loads(errors.getvalue())["status"], "error")
            self.assertEqual(Path(output).read_bytes(), old)


if __name__ == "__main__":
    unittest.main()
