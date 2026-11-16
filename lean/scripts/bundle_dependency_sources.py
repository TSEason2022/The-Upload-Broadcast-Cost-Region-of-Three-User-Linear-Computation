#!/usr/bin/env python3
"""Deterministically bundle exact Git-tracked dependency sources and notices."""
from pathlib import Path, PurePosixPath
import argparse, gzip, io, json, os, posixpath, subprocess, tarfile, tempfile
from release_support import dump_json, sha256

parser = argparse.ArgumentParser()
parser.add_argument('output', type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
args.output = args.output.resolve()
args.output.parent.mkdir(parents=True, exist_ok=True)
with tempfile.TemporaryDirectory() as work:
    metadata = Path(work) / 'pins.json'
    subprocess.run(['python3', 'scripts/verify_dependency_pins.py', '--output', str(metadata)], cwd=root, check=True)
    manifest = json.loads(metadata.read_text())
    entries = []
    # Only Git-tracked bytes at the recorded commit are read; no build/cache tree is packed.
    for dep in manifest['dependencies']:
        folder = root / '.lake/packages' / dep['name']
        archive = subprocess.check_output(['git', '-C', str(folder), 'archive', '--format=tar', dep['revision']])
        tracked = set(subprocess.check_output(['git', '-C', str(folder), 'ls-tree', '-r', '--name-only', dep['revision']]).decode().splitlines())
        archived = set()
        with tarfile.open(fileobj=io.BytesIO(archive)) as src:
            for item in src:
                if item.isdir():
                    continue
                archived.add(item.name)
                path = PurePosixPath(dep['name']) / item.name
                assert not path.is_absolute() and '..' not in path.parts
                assert item.isfile() or item.issym(), f'Unsupported archive member: {path}'
                if item.issym():
                    target = posixpath.normpath(str(path.parent / item.linkname))
                    assert not PurePosixPath(item.linkname).is_absolute() and target.startswith(dep['name'] + '/'), f'Unsafe symlink: {path}'
                payload = item.linkname.encode() if item.issym() else src.extractfile(item).read()
                entries.append((path.as_posix(), payload, item.mode, item.linkname if item.issym() else None))
        assert tracked == archived, f"Git archive omitted tracked files or submodules: {dep['name']}"
    manifest['files'] = [{'path': name, 'sha256': sha256(data), 'size': len(data),
                          'kind': 'symlink_target' if link is not None else 'file'}
                         for name, data, mode, link in sorted(entries)]
    manifest['note'] = ('Exact tracked upstream trees; symlink digests hash link-target UTF-8 bytes. '
                        'Tracked upstream fixtures are retained, including mathlib\'s empty fake shared-library fixture. '
                        'No installed Lean toolchain, build output, Git history, or downloaded caches are included.')
    manifest_bytes = (json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + '\n').encode()
    temporary = args.output.with_name(args.output.name + '.tmp')
    with temporary.open('wb') as raw, gzip.GzipFile(filename='', mode='wb', fileobj=raw, mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode='w', format=tarfile.PAX_FORMAT) as dst:
            for name, data, mode, link in [('DEPENDENCY_MANIFEST.json', manifest_bytes, 0o644, None), *sorted(entries)]:
                item = tarfile.TarInfo(name)
                item.mode = mode
                item.mtime = 0
                if link is not None:
                    item.type = tarfile.SYMTYPE
                    item.linkname = link
                else:
                    item.size = len(data)
                dst.addfile(item, None if link is not None else io.BytesIO(data))
    os.replace(temporary, args.output)
    dump_json(args.output.with_name('dependency-pins.json'), {k:v for k,v in manifest.items() if k != 'files'})
print(f'{sha256(args.output.read_bytes())}  {args.output.name}')
