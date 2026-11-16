#!/usr/bin/env python3
"""Package only a source-identical, complete, independently checked snapshot.

No uploading, Git publication, license grant, or payment is performed.
"""
from pathlib import Path, PurePosixPath
import argparse, io, json, posixpath, re, subprocess, tarfile, zipfile
from release_support import project_files, source_manifest, sha256, dump_json, referenced_historical_logs, normalize_distributed_log

parser = argparse.ArgumentParser()
parser.add_argument('--source-dir', type=Path, required=True, help='Frozen manuscript and inventories directory')
parser.add_argument('--dependencies', type=Path, required=True, help='Verified dependency-sources.tar.gz')
parser.add_argument('--output-dir', type=Path, required=True, help='Fresh output directory')
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
evidence = root / '.verification-results'
if not (evidence / 'report.json').is_file() or not (evidence / 'source-manifest.json').is_file():
    raise SystemExit('No independent clean-build evidence found. Run clean_rebuild.py --require-complete and package from that verified snapshot.')
report = json.loads((evidence / 'report.json').read_text())
saved = json.loads((evidence / 'source-manifest.json').read_text())
assert report.get('passed') and report.get('whole_paper_release_gate_passed'), 'Full clean release gate has not passed'
assert report.get('project_compiled_artifacts_reused') is False, 'Clean project rebuild is not established'
assert report.get('source_unchanged_during_checks'), 'Sources changed during verification'
assert source_manifest(root) == saved, 'Project source no longer matches the verified snapshot'
assert report['project_source_sha256'] == saved['project_source_sha256']
assert {c['name'] for c in report['checks'] if c['exit_code'] == 0} >= {
    'toolchain', 'dependency-pins', 'release-regressions', 'source-preflight', 'all-modules', 'integrated-check', 'complete-coverage'}
subprocess.run(['python3', 'scripts/check_coverage.py'], cwd=root, check=True)
coverage = json.loads((root / 'coverage.json').read_text())
source_dir = args.source_dir.resolve()
tex = source_dir / 'TIT_LCBC_optimized.tex'
assert sha256(tex.read_bytes()) == coverage['source_sha256'], 'Manuscript hash does not match the coverage review'
# Verify all archive members against the embedded source manifest before copying it.
dep_path = args.dependencies.resolve()
with tarfile.open(dep_path) as archive:
    dep_manifest = json.load(archive.extractfile('DEPENDENCY_MANIFEST.json'))
    archive_members = archive.getmembers()
    assert len(archive_members) == len({m.name for m in archive_members}), 'Duplicate dependency archive paths'
    assert all(m.isfile() or m.issym() for m in archive_members), 'Unexpected dependency archive member type'
    members = {m.name:m for m in archive_members}
    expected = {f['path']:f for f in dep_manifest['files']}
    assert set(members) == set(expected) | {'DEPENDENCY_MANIFEST.json'}, 'Unexpected dependency archive members'
    for name, f in expected.items():
        m = members[name]
        assert not PurePosixPath(name).is_absolute() and '..' not in PurePosixPath(name).parts
        assert (m.issym() if f['kind'] == 'symlink_target' else m.isfile()), f'Dependency member type mismatch: {name}'
        if m.issym():
            target = posixpath.normpath(str(PurePosixPath(name).parent / m.linkname))
            assert not PurePosixPath(m.linkname).is_absolute() and target.startswith(name.split('/')[0] + '/'), f'Unsafe dependency symlink: {name}'
        data = m.linkname.encode() if m.issym() else archive.extractfile(m).read()
        assert sha256(data) == f['sha256'] and len(data) == f['size'], f'Dependency hash mismatch: {name}'
lock = json.loads((root / 'lake-manifest.json').read_text())
assert dep_manifest['lockfile_sha256'] == sha256((root / 'lake-manifest.json').read_bytes())
assert {(d['name'],d['url'],d['revision']) for d in dep_manifest['dependencies']} == {
    (d['name'],d['url'],d['rev']) for d in lock['packages']}
output = args.output_dir.resolve()
if root == output or root in output.parents:
    raise SystemExit('Release output must be outside the verified source repository.')
if output.exists():
    raise SystemExit('Output directory already exists; choose a fresh release output directory.')
records = {}
for p in project_files(root):
    records[p.relative_to(root).as_posix()] = p.read_bytes()
records['SOURCE_MANIFEST.json'] = (json.dumps(saved, indent=2, sort_keys=True) + '\n').encode()
evidence_records = []
for p in sorted(evidence.iterdir()):
    if p.suffix in {'.json', '.log', '.lean'}:
        original = p.read_bytes()
        normalized = normalize_distributed_log(original.decode(), root).encode()
        records['verification-results/' + p.name] = normalized
        evidence_records.append({'path': p.name, 'original_sha256': sha256(original),
                                 'distributed_sha256': sha256(normalized), 'paths_normalized': original != normalized})
records['verification-results/DISTRIBUTED_EVIDENCE_MANIFEST.json'] = (json.dumps(evidence_records, indent=2, sort_keys=True) + '\n').encode()
historical = []
for relative in referenced_historical_logs(root):
    p = root / relative
    entry = {'path': relative, 'available': p.is_file()}
    if p.is_file():
        original = p.read_bytes()
        normalized = normalize_distributed_log(original.decode(), root).encode()
        records[relative] = normalized
        entry.update({'original_sha256': sha256(original), 'distributed_sha256': sha256(normalized),
                      'path_prefixes_normalized': original != normalized})
    historical.append(entry)
records['logs/HISTORICAL_LOG_MANIFEST.json'] = (json.dumps(historical, indent=2, sort_keys=True) + '\n').encode()
records['logs/README.md'] = (
    '# Historical focused checks\n\n'
    'These logs are retained because source-review documents explicitly refer to them. '
    'They concern their original focused development checks, which may predate the frozen release. '
    'They are not certification that the entire final source tree passed.\n\n'
    'The authoritative fresh all-module and integrated checks for this release are in '
    '`verification-results/`, bound to the exact `SOURCE_MANIFEST.json` identity. '
    '`HISTORICAL_LOG_MANIFEST.json` records availability and both original and distributed hashes; '
    'executor-only prefixes and temporary paths are normalized in distributed copies. Missing historical logs '
    'are reported explicitly rather than recreated.\n').encode()
source_files = sorted([*source_dir.glob('*.tex'), *source_dir.glob('*.bib'), *source_dir.glob('*.zip')])
source_identity = {'paper_title': coverage['paper_title'], 'authors': ['Shuo Tan', 'Syed A. Jafar'],
                   'files': [{'filename': p.name, 'sha256':sha256(p.read_bytes()), 'size':p.stat().st_size}
                             for p in source_files],
                   'note': 'Original input identities only; no manuscript publication or license grant is made.'}
records['source-ledger/source-identity.json'] = (json.dumps(source_identity, indent=2, ensure_ascii=False) + '\n').encode()
inventory = json.loads((source_dir / 'claims_inventory.json').read_text())
lookup = {label:c for c in inventory for label in c.get('labels', [])}
ledger = []
for c in coverage['claims']:
    assert c['id'] in lookup, f"Named claim missing from frozen source inventory: {c['id']}"
    original = lookup[c['id']]
    ledger.append({'id':c['id'], 'title': c['title'], 'source_line':original['line'],
                   'source_kind':original['kind'], 'source_labels':original['labels'],
                   'source_statement':original['statement'],
                   'source_references':original.get('dependencies', []),
                   'lean_declarations':c['lean_declarations'], 'review_status':c['status'],
                   'remaining_obligations':c['remaining_obligations']})
records['source-ledger/named-claims.json'] = (json.dumps(ledger, indent=2, ensure_ascii=False) + '\n').encode()
# Include the review inventory, not identity metadata carrying private Library identifiers.
for name in ('claims_inventory.json', 'label_locations.json', 'displayed_equations.json', 'proof_blocks.json'):
    records['source-ledger/' + name] = (source_dir / name).read_bytes()
private_patterns = [r'/workspace/(?:scratch|shared)/[A-Za-z0-9]', r'/home/agent/[A-Za-z0-9]', r'/tmp/[A-Za-z0-9]', r'libfile_[A-Za-z0-9_]+',
                    r'sk-proj-[A-Za-z0-9_-]+', r'-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----']
for name, data in records.items():
    text = data.decode('utf-8')
    for pattern in private_patterns:
        assert not re.search(pattern, text), f'Private local path or credential-like data in {name}'
output.mkdir(parents=True)
archive_path = output / 'upload-broadcast-lean.zip'
with zipfile.ZipFile(archive_path, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
    for name, data in sorted(records.items()):
        info = zipfile.ZipInfo('upload-broadcast-lean/' + name, date_time=(1980,1,1,0,0,0))
        info.compress_type = zipfile.ZIP_DEFLATED
        info.external_attr = (0o100755 if name.startswith('scripts/') and name.endswith('.sh') else 0o100644) << 16
        archive.writestr(info, data)
(output / 'dependency-sources.tar.gz').write_bytes(dep_path.read_bytes())
dump_json(output / 'RELEASE.json', {
    'schema_version':1, 'project_source_sha256':saved['project_source_sha256'],
    'manuscript_source_sha256':coverage['source_sha256'],
    'whole_paper_release_gate_passed':True, 'publication_performed':False,
    'license_for_new_project_material':'Not selected; rights-holder decision required',
    'dependency_source_bundle_sha256':sha256(dep_path.read_bytes()),
    'proof_archive_sha256':sha256(archive_path.read_bytes()),
    'evidence':'upload-broadcast-lean/verification-results/report.json'})
paths = sorted(p for p in output.iterdir() if p.is_file())
(output / 'SHA256SUMS').write_text(''.join(f'{sha256(p.read_bytes())}  {p.name}\n' for p in paths))
print('Verified release files prepared locally; nothing has been published:')
for p in sorted(output.iterdir()):
    print(f'{p.name}: {p.stat().st_size} bytes')
