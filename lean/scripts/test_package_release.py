#!/usr/bin/env python3
"""End-to-end packaging tests using synthetic fixtures and mocked check evidence.

These tests validate archive logic only. They never certify a manuscript, compile
Lean, or create a real release. Every fixture and output is deleted afterward.
"""
from pathlib import Path
import io, json, shutil, subprocess, sys, tarfile, tempfile, unittest, zipfile
from release_support import dump_json, source_manifest, sha256

class SyntheticPackagingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='synthetic-packaging-test-')
        self.base = Path(self.temp.name)
        self.root = self.base / 'synthetic-project'
        (self.root / 'scripts').mkdir(parents=True)
        self.inputs = self.base / 'synthetic-inputs'
        self.inputs.mkdir()
        for name in ('release_support.py', 'package_release.py', 'check_coverage.py'):
            shutil.copy2(Path(__file__).with_name(name), self.root / 'scripts' / name)
        (self.root / 'README.md').write_text('SYNTHETIC TEST FIXTURE. This is not a verified manuscript or real release.\n')
        (self.root / 'UploadBroadcast.lean').write_text('-- Synthetic packaging input; not compiled by this test.\n')
        (self.root / 'lake-manifest.json').write_text('{"packages": []}\n')
        paper = b'SYNTHETIC INPUT FOR A PACKAGING SOFTWARE TEST ONLY.\n'
        (self.inputs / 'TIT_LCBC_optimized.tex').write_bytes(paper)
        claims = [{'id':f'fixture:{i}', 'title':'Synthetic fixture', 'status':'reviewed_complete',
                   'lean_declarations':['Synthetic.fixture'], 'remaining_obligations':[]} for i in range(28)]
        dump_json(self.root / 'coverage.json', {'paper_title':'SYNTHETIC PACKAGING TEST',
                  'source_sha256':sha256(paper), 'claims':claims,
                  'unnumbered_and_external_dependencies_reviewed':True})
        inventory = [{'labels':[c['id']], 'kind':'test-only', 'line':i+1,
                      'statement':'Synthetic fixture; no real mathematical claim.'} for i,c in enumerate(claims)]
        dump_json(self.inputs / 'claims_inventory.json', inventory)
        for name in ('label_locations.json', 'displayed_equations.json', 'proof_blocks.json'):
            dump_json(self.inputs / name, [])
        self.evidence = self.root / '.verification-results'
        self.evidence.mkdir()
        manifest = source_manifest(self.root)
        dump_json(self.evidence / 'source-manifest.json', manifest)
        self.report = {'simulation_only':True,
                       'notice':'Mock evidence solely for testing the packaging software; no Lean build was run.',
                       'passed':True, 'whole_paper_release_gate_passed':True,
                       'project_compiled_artifacts_reused':False, 'source_unchanged_during_checks':True,
                       'project_source_sha256':manifest['project_source_sha256'],
                       'checks':[{'name':name,'exit_code':0} for name in
                                 ('toolchain','dependency-pins','release-regressions','source-preflight','all-modules','integrated-check','complete-coverage')]}
        dump_json(self.evidence / 'report.json', self.report)
        self.dependencies = self.base / 'synthetic-dependencies.tar.gz'
        dep = {'files':[], 'dependencies':[], 'lockfile_sha256':sha256((self.root / 'lake-manifest.json').read_bytes())}
        content = json.dumps(dep).encode()
        with tarfile.open(self.dependencies, 'w:gz') as archive:
            member = tarfile.TarInfo('DEPENDENCY_MANIFEST.json')
            member.size = len(content)
            archive.addfile(member, io.BytesIO(content))
        self.output = self.base / 'synthetic-output'
    def tearDown(self):
        self.temp.cleanup()
    def run_packager(self):
        return subprocess.run([sys.executable,str(self.root/'scripts/package_release.py'),
            '--source-dir',str(self.inputs),'--dependencies',str(self.dependencies),'--output-dir',str(self.output)],
            text=True,capture_output=True)
    def test_synthetic_archive_round_trip(self):
        result=self.run_packager()
        self.assertEqual(result.returncode,0,result.stderr)
        with zipfile.ZipFile(self.output/'upload-broadcast-lean.zip') as archive:
            names=archive.namelist()
            self.assertIn('upload-broadcast-lean/source-ledger/named-claims.json',names)
            self.assertIn('upload-broadcast-lean/verification-results/DISTRIBUTED_EVIDENCE_MANIFEST.json',names)
            self.assertFalse(any('/.lake/' in name for name in names))
            unpacked=self.base/'unpacked'
            archive.extractall(unpacked)
        extracted=unpacked/'upload-broadcast-lean'
        self.assertEqual(source_manifest(extracted),json.loads((extracted/'SOURCE_MANIFEST.json').read_text()))
        for line in (self.output/'SHA256SUMS').read_text().splitlines():
            digest,name=line.split('  ',1)
            self.assertEqual(sha256((self.output/name).read_bytes()),digest)
    def test_changed_source_refused(self):
        (self.root/'README.md').write_text('Changed synthetic fixture.\n')
        result=self.run_packager()
        self.assertNotEqual(result.returncode,0)
        self.assertIn('no longer matches',result.stderr)
        self.assertFalse(self.output.exists())
    def test_missing_release_check_refused(self):
        self.report['checks']=[c for c in self.report['checks'] if c['name']!='all-modules']
        dump_json(self.evidence/'report.json',self.report)
        result=self.run_packager()
        self.assertNotEqual(result.returncode,0)
        self.assertFalse(self.output.exists())

if __name__=='__main__':
    unittest.main()
