"""Build a deterministic final handover ZIP and executable ZIP application.

Only project-owned source/documentation paths are collected; caches, local
build environments and output archives are excluded. ZIP metadata is fixed.
Run from any directory: python /path/to/build_release.py --output /path/to/release
"""
from __future__ import annotations

import argparse
import hashlib
import io
import json
import runpy
import zipfile
from pathlib import Path


ROOT_FILES = {
    'README.md','LICENSING.md','SECURITY.md',
    'pyproject.toml','build_release.py','MANIFEST.in','.gitignore',
}
ROOT_DIRS = {'three_user_codes','tests','examples','benchmarks','docs','validation','tools','.github','typing_examples'}
SKIP_PARTS = {'__pycache__','.git','.pytest_cache','.mypy_cache','.ruff_cache','.venv','build','dist'}


def _write_entry(archive, name, data):
    info=zipfile.ZipInfo(name,date_time=(2026,1,1,0,0,0))
    info.compress_type=zipfile.ZIP_DEFLATED
    info.create_system=3
    info.external_attr=0o100644 << 16
    archive.writestr(info,data)


def _project_files(root,output):
    for path in sorted(root.rglob('*')):
        if not path.is_file() or path.is_symlink() or output in path.parents:
            continue
        relative=path.relative_to(root)
        if any(part in SKIP_PARTS or part.endswith('.egg-info') for part in relative.parts):
            continue
        if path.suffix in ('.pyc','.pyo','.tmp') or path.name in ('.coverage','.DS_Store','MANIFEST.sha256'):
            continue
        if relative.as_posix() in ROOT_FILES or relative.parts[0] in ROOT_DIRS:
            yield path


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path('../release'))
    args=parser.parse_args()
    root=Path(__file__).resolve().parent
    version=runpy.run_path(str(root/'three_user_codes'/'_version.py'))['__version__']
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=True)
    files=tuple(_project_files(root,output))
    executable=output/f'three_user_codes-{version}.pyz'
    source=output/f'three_user_codes-{version}-final.zip'
    executable_data=io.BytesIO()
    with zipfile.ZipFile(executable_data,'w') as archive:
        _write_entry(archive,'__main__.py',b'from three_user_codes.cli import main\nraise SystemExit(main())\n')
        for path in files:
            relative=path.relative_to(root)
            if relative.parts[0]=='three_user_codes' and path.suffix=='.py':
                _write_entry(archive,relative.as_posix(),path.read_bytes())
    executable.with_suffix('.tmp').write_bytes(executable_data.getvalue())
    executable.with_suffix('.tmp').replace(executable)
    manifest=[]
    with zipfile.ZipFile(source.with_suffix('.tmp'),'w') as archive:
        for path in files:
            relative=path.relative_to(root).as_posix();data=path.read_bytes()
            manifest.append(hashlib.sha256(data).hexdigest()+'  '+relative)
            _write_entry(archive,f'three_user_codes-{version}/'+relative,data)
        data=executable_data.getvalue()
        manifest.append(hashlib.sha256(data).hexdigest()+'  three_user_codes.pyz')
        _write_entry(archive,f'three_user_codes-{version}/three_user_codes.pyz',data)
        _write_entry(archive,f'three_user_codes-{version}/MANIFEST.sha256',('\n'.join(manifest)+'\n').encode())
    source.with_suffix('.tmp').replace(source)
    records=[]
    for path in (source,executable):
        with zipfile.ZipFile(path) as archive:
            if archive.testzip() is not None:raise RuntimeError('archive CRC validation failed')
        records.append({'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    print(json.dumps({'version':version,'files':len(files),'artifacts':records},indent=2))


if __name__=='__main__':main()
