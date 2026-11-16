#!/usr/bin/env python3
"""Regression tests for the lexical gate, using text fixtures only.

No fixture is passed to Lean or installed in the project library.
"""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


class SourceAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'scripts').mkdir()
        shutil.copy2(Path(__file__).with_name('audit_source.py'), self.root / 'scripts/audit_source.py')
        (self.root / 'UploadBroadcast.lean').write_text('-- Minimal lexical fixture.\n')

    def tearDown(self):
        self.temp.cleanup()

    def check_text(self, relative, text, rejected):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        result = subprocess.run([sys.executable, str(self.root / 'scripts/audit_source.py')],
                                text=True, capture_output=True)
        self.assertEqual(result.returncode != 0, rejected, result.stdout + result.stderr)

    def test_nested_comments_and_strings_are_masked(self):
        self.check_text('UploadBroadcast/A.lean',
                        '/- axiom /- unsafe -/ sorry -/\n'
                        '-- native_decide\n'
                        'def text := "admit \\\" unsafe"\n', False)

    def test_placeholder_is_rejected(self):
        self.check_text('UploadBroadcast/A.lean', 'sorry\n', True)

    def test_axiom_command_token_is_rejected(self):
        self.check_text('UploadBroadcast/A.lean', 'axiom\n', True)

    def test_plural_axioms_command_is_rejected(self):
        self.check_text('UploadBroadcast/A.lean', 'axioms marker\n', True)

    def test_unsafe_token_is_rejected(self):
        self.check_text('UploadBroadcast/A.lean', 'unsafe\n', True)

    def test_native_reduction_is_rejected_in_verification(self):
        self.check_text('verification/A.lean', 'Lean.ofReduceBool\n', True)

    def test_native_decide_is_rejected_in_scripts(self):
        self.check_text('scripts/A.lean', 'native_decide\n', True)

    def test_kernel_skip_option_is_rejected(self):
        self.check_text('UploadBroadcast/A.lean', 'set_option debug.skipKernelTC true\n', True)

    def test_library_command_metaprogram_requires_review(self):
        self.check_text('UploadBroadcast/A.lean', 'run_cmd pure ()\n', True)

    def test_umbrella_command_metaprogram_requires_review(self):
        self.check_text('UploadBroadcast.lean', 'run_cmd pure ()\n', True)

    def test_read_only_audit_syntax_is_allowed(self):
        self.check_text('scripts/A.lean',
                        'run_cmd do\n  let axioms := #[]\n  pure ()\n#print axioms marker\n', False)

    def test_environment_mutation_is_rejected(self):
        self.check_text('scripts/A.lean', 'modifyEnv\n', True)


if __name__ == '__main__':
    unittest.main()
