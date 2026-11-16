#!/usr/bin/env python3
"""Shared deterministic release selection and content identity (Python 3.11+)."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess

if not __debug__:
    raise SystemExit("Release verification must run without Python optimization (-O / PYTHONOPTIMIZE).")

ROOT_FILES = {'README.md', 'TOOLCHAIN.md', 'RIGHTS.md', 'lean-toolchain',
              'lakefile.toml', 'lake-manifest.json', 'toolchain-lock.json', 'coverage.json', '.gitignore', 'LICENSE', 'LICENSE.md', 'CITATION.cff'}
ROOT_DIRS = {'UploadBroadcast', 'scripts', 'docs', 'third_party_notices', '.github', 'examples'}
GENERATED = {'SOURCE_MANIFEST.json', 'DEPENDENCY_MANIFEST.json'}


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def project_files(root):
    """Release allowlist; generated reports are added separately after checking."""
    root = Path(root)
    for path in sorted(root.rglob('*')):
        rel = path.relative_to(root)
        if any(x in {'.git', '.lake', '.tooling', '__pycache__', '.verification-results'} for x in rel.parts):
            continue
        if path.is_symlink():
            if rel.parts[0] in ROOT_DIRS:
                raise ValueError(f'Project symlink is not allowed: {rel}')
            continue
        if not path.is_file():
            continue
        allowed = ((len(rel.parts) == 1 and (rel.name in ROOT_FILES or path.suffix == '.lean'))
                   or rel.parts[0] in ROOT_DIRS
                   or (rel.parts[0] == 'verification' and path.suffix in {'.lean', '.json', '.py'}
                       and path.name != 'current_snapshot.json'))
        generated_suffixes = {'.pyc', '.olean', '.ilean', '.o', '.so', '.a', '.dll',
                              '.dylib', '.bc', '.trace', '.hash', '.tmp', '.bak', '.swp'}
        if (allowed and not generated_suffixes.intersection(path.suffixes)
                and path.name != '.DS_Store' and not path.name.endswith('~')):
            yield path


def source_manifest(root):
    root = Path(root)
    files = [{'path': p.relative_to(root).as_posix(), 'sha256': sha256(p.read_bytes()),
              'size': p.stat().st_size} for p in project_files(root)]
    identity = sha256(''.join(f"{f['sha256']}  {f['path']}\n" for f in files).encode())
    return {'schema_version': 1, 'identity_algorithm': 'SHA-256 of sorted sha256-double-space-path-newline records',
            'project_source_sha256': identity, 'file_count': len(files), 'files': files}


def dump_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + '\n')


def imports(path):
    # Project import headers are plain single-line Lean imports.
    return sum((m.split() for m in re.findall(r'^\s*import\s+(.+?)(?:\s*--.*)?$', path.read_text(), re.M)), [])


def module_inventory(root):
    root = Path(root)
    paths = [root / 'UploadBroadcast.lean', *sorted((root / 'UploadBroadcast').rglob('*.lean'))]
    modules = {'.'.join(p.relative_to(root).with_suffix('').parts): p for p in paths}
    reached = set()
    def visit(name):
        if name in reached or name not in modules:
            return
        reached.add(name)
        for child in imports(modules[name]):
            visit(child)
    visit('UploadBroadcast')
    ordered, done, active = [], set(), set()
    def order(name):
        if name not in modules or name in done:
            return
        if name in active:
            raise ValueError(f'Project import cycle: {name}')
        active.add(name)
        for child in imports(modules[name]):
            order(child)
        active.remove(name)
        done.add(name)
        ordered.append(name)
    for name in sorted(modules):
        order(name)
    return {'module_count': len(modules), 'umbrella_reachable_count': len(reached),
            'modules': sorted(modules), 'topological_modules': ordered,
            'outside_umbrella': sorted(set(modules) - reached)}


def referenced_historical_logs(root):
    """Return only local focused logs explicitly referenced by audit documents."""
    root = Path(root)
    names = set()
    for directory in ('docs', 'verification'):
        for path in (root / directory).rglob('*'):
            if path.is_file() and path.suffix in {'.md', '.json'}:
                names.update(re.findall(r'(?<![\w/])(?:logs|verification)/[A-Za-z0-9_.-]+\.log', path.read_text()))
    return sorted(names)


def copy_dependency_cache(source, destination):
    """Preserve dependency sources, Git data and caches, with a portable fallback."""
    source, destination = Path(source), Path(destination)
    if destination.exists():
        raise ValueError('Dependency-cache destination must not exist')
    cp = shutil.which('cp')
    if cp:
        help_result = subprocess.run([cp, '--help'], capture_output=True, text=True, check=False)
        if '--reflink' in help_result.stdout:
            subprocess.run([cp, '-a', '--reflink=auto', str(source), str(destination)], check=True)
            return 'cp-reflink-auto'
    shutil.copytree(source, destination, symlinks=True, copy_function=shutil.copy2)
    return 'python-copytree'


def validate_axiom_reports(source, output):
    expected = re.findall(r'^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$', source, re.M)
    if not expected or len(set(expected)) != len(expected):
        raise ValueError('Example axiom roots must be nonempty and distinct')
    reports = {}
    for match in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]|'([^']+)' does not depend on any axioms", output, re.S):
        name = match.group(1) or match.group(3)
        if name in reports:
            raise ValueError(f'Duplicate axiom report: {name}')
        reports[name] = sorted(x.strip() for x in (match.group(2) or '').split(',') if x.strip())
    if set(expected) != set(reports):
        raise ValueError('Missing or unexpected public-example axiom reports')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in reports.items():
        if not set(axioms) <= allowed:
            raise ValueError(f'Unapproved axiom in {name}: {axioms}')
    return {'declaration_count': len(reports), 'declarations': reports,
            'axioms': sorted({a for values in reports.values() for a in values})}


def normalize_distributed_log(text, root):
    """Remove executor-only locations while preserving original hashes separately."""
    root = Path(root).resolve()
    text = text.replace(str(root), '<verification-root>')
    if root.parent != root.parent.parent:
        text = text.replace(str(root.parent), '<verification-parent>')
    # Do not retain transient filenames/coordinates from private scratch probes.
    return re.sub(r"(?<![A-Za-z0-9])/(?:tmp|var/tmp|private/tmp|private/var/tmp|private/var/folders)/[^\s\"'<>]+",
                  '<temporary-path>', text)
