#!/usr/bin/env python3
"""Fast regression tests for release selection and identity; no Lean cache needed."""
from pathlib import Path
import os, subprocess, sys, tempfile, unittest
from unittest import mock
from release_support import project_files, source_manifest, module_inventory, copy_dependency_cache, validate_axiom_reports, normalize_distributed_log

class ReleaseIdentityTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory()
        self.root=Path(self.temp.name)
        (self.root/'UploadBroadcast').mkdir()
        (self.root/'UploadBroadcast.lean').write_text('import UploadBroadcast.A\n')
        (self.root/'UploadBroadcast/A.lean').write_text('def value := 1\n')
        (self.root/'UploadBroadcast/B.lean').write_text('def other := 2\n')
        (self.root/'coverage.json').write_text('{}\n')
    def tearDown(self):
        self.temp.cleanup()
    def test_deterministic_manifest(self):
        self.assertEqual(source_manifest(self.root),source_manifest(self.root))
    def test_supplementary_verification_script_included(self):
        folder=self.root/'verification'
        folder.mkdir()
        path=folder/'finite_diagnostic.py'
        path.write_text('print("Supplementary diagnostic only")\n')
        self.assertIn(path,list(project_files(self.root)))
    def test_source_edit_changes_identity(self):
        before=source_manifest(self.root)
        (self.root/'UploadBroadcast/A.lean').write_text('def value := 3\n')
        self.assertNotEqual(before,source_manifest(self.root))
    def test_build_outputs_are_excluded(self):
        before=source_manifest(self.root)
        for name in ['.lake/build/lib/lean/A.olean','.tooling/cache/file','logs/run.log',
                     'scripts/__pycache__/x.pyc','.verification-results/report.json','UploadBroadcast/A.olean.hash',
                     'UploadBroadcast/A.ilean','UploadBroadcast/A.trace','UploadBroadcast/A.lean.bak']:
            path=self.root/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text('cached\n')
        self.assertEqual(before,source_manifest(self.root))
    def test_unimported_source_is_present(self):
        inventory=module_inventory(self.root)
        self.assertEqual(inventory['module_count'],3)
        self.assertEqual(inventory['outside_umbrella'],['UploadBroadcast.B'])
    def test_topological_dependency_order(self):
        (self.root/'UploadBroadcast/B.lean').write_text('import UploadBroadcast.A\n')
        order=module_inventory(self.root)['topological_modules']
        self.assertLess(order.index('UploadBroadcast.A'),order.index('UploadBroadcast.B'))
        self.assertLess(order.index('UploadBroadcast.A'),order.index('UploadBroadcast'))
    def test_import_override_rejected_before_tool_invocation(self):
        script=Path(__file__).with_name('verify_toolchain.py')
        result=subprocess.run([sys.executable,str(script)],env=dict(os.environ,LEAN_PATH='test-only-shadow-path'),
                              capture_output=True,text=True)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('Inherited LEAN_PATH',result.stdout+result.stderr)
    def test_portable_dependency_copy(self):
        source=self.root/'dependency-cache'
        source.mkdir()
        (source/'module.lean').write_text('def value := 1\n')
        (source/'module.olean').write_bytes(b'test-only-cache')
        (source/'link').symlink_to('module.lean')
        destination=self.root/'copied-cache'
        with mock.patch('release_support.shutil.which',return_value=None):
            method=copy_dependency_cache(source,destination)
        self.assertEqual(method,'python-copytree')
        self.assertEqual((destination/'module.olean').read_bytes(),b'test-only-cache')
        self.assertEqual((destination/'module.lean').read_bytes(),(source/'module.lean').read_bytes())
        self.assertTrue((destination/'link').is_symlink())
    def test_axiom_report_validation(self):
        source='#print axioms Public.example\n#print axioms Public.empty\n'
        output="'Public.example' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'Public.empty' does not depend on any axioms\n"
        result=validate_axiom_reports(source,output)
        self.assertEqual(result['declaration_count'],2)
        self.assertEqual(set(result['axioms']),{'propext','Classical.choice','Quot.sound'})
    def test_unapproved_axiom_rejected(self):
        with self.assertRaises(ValueError):
            validate_axiom_reports('#print axioms Public.example\n',
                                   "'Public.example' depends on axioms: [unapprovedTestAxiom]\n")
    def test_missing_axiom_report_rejected(self):
        with self.assertRaises(ValueError):
            validate_axiom_reports('#print axioms Public.example\n','')
    def test_private_log_path_normalization(self):
        temporary='/'+'tmp'+'/sample-recheck.olean'
        source=f'output {temporary}; source /fixture/project/Example.lean\n'
        normalized=normalize_distributed_log(source,Path('/fixture/project'))
        self.assertNotIn(temporary,normalized)
        self.assertIn('<temporary-path>',normalized)
        self.assertIn('<verification-root>/Example.lean',normalized)
    def test_source_symlink_rejected(self):
        (self.root/'UploadBroadcast/Link.lean').symlink_to('A.lean')
        with self.assertRaises(ValueError):
            list(project_files(self.root))

if __name__=='__main__':
    unittest.main()
