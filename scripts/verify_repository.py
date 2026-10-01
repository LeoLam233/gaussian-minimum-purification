"""Standard-library integrity and repository-structure checks."""
from pathlib import Path, PurePosixPath
from urllib.parse import unquote
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
IGNORED_DIRS = {'.git', '.local', '.venv', '__pycache__', '.lake', 'build-evidence'}


def inventory(root=ROOT):
    return {
        p.relative_to(root).as_posix(): p
        for p in root.rglob('*')
        if p.is_file()
        and not (set(p.relative_to(root).parts) & IGNORED_DIRS)
        and p.suffix not in {'.pyc', '.pyo'}
        and p.name not in {'.DS_Store', 'Thumbs.db'}
    }


def verify():
    expected = {}
    errors = []
    for line in (ROOT/'MANIFEST.sha256').read_text(encoding='utf-8').splitlines():
        if not line.strip():
            continue
        digest, name = line.split('  ', 1)
        rel = PurePosixPath(name)
        if not re.fullmatch('[0-9a-f]{64}', digest) or rel.is_absolute() or '..' in rel.parts or ':' in name or '\\' in name:
            errors.append('Invalid manifest entry: '+name)
            continue
        if name in expected:
            errors.append('Duplicate entry: '+name)
        expected[name] = digest
    actual = inventory()
    for name, digest in expected.items():
        p = actual.get(name)
        if p is None:
            errors.append('Missing: '+name)
        elif not p.resolve().is_relative_to(ROOT):
            errors.append('External link: '+name)
        elif hashlib.sha256(p.read_bytes()).hexdigest() != digest:
            errors.append('Hash mismatch: '+name)
    errors.extend('Unlisted: '+name for name in sorted(set(actual)-set(expected)-{'MANIFEST.sha256'}))

    metadata = json.loads((ROOT/'RELEASE_METADATA.json').read_text(encoding='utf-8'))
    for name, digest in metadata['manuscript_sha256'].items():
        if expected.get(name) != digest:
            errors.append('Manuscript release-metadata disagreement: '+name)
    sources = json.loads((ROOT/'provenance/SOURCE_MAP.json').read_text(encoding='utf-8'))
    for row in sources['files']:
        if expected.get(row['repository_path']) != row['distributed_sha256']:
            errors.append('Source map disagreement: '+row['repository_path'])
        if row['transformation']=='none' and row['source_sha256'] != row['distributed_sha256']:
            errors.append('Non-identical frozen source: '+row['repository_path'])
    citation = json.loads((ROOT/'CITATION.cff').read_text(encoding='utf-8'))
    if citation.get('cff-version') != '1.2.0' or citation.get('version') != metadata['repository_candidate'].removeprefix('v'):
        errors.append('Citation version mismatch')
    if citation.get('title') != metadata['title'] or citation['authors'][0]['family-names'] != 'Lin':
        errors.append('Citation identity mismatch')

    from verify_lean_source import verify as verify_lean_source
    errors.extend('Lean source identity: ' + error for error in verify_lean_source()['errors'])

    links_checked = 0
    for name, p in actual.items():
        if p.suffix.lower() != '.md':
            continue
        for target in re.findall(r'(?<!!)\[[^\]\n]+\]\(([^)]+)\)', p.read_text(encoding='utf-8')):
            target = target.strip('<>').split('#', 1)[0]
            if not target or re.match(r'[a-zA-Z][a-zA-Z0-9+.-]*:', target):
                continue
            links_checked += 1
            dest = (p.parent/unquote(target)).resolve()
            if not dest.is_relative_to(ROOT) or not dest.is_file():
                errors.append('Broken local link in '+name+': '+target)
    return {
        'status':'PASS' if not errors else 'FAIL',
        'files_checked':len(expected),
        'source_map_entries':len(sources['files']),
        'local_links_checked':links_checked,
        'errors':errors,
    }


if __name__ == '__main__':
    result = verify()
    print(json.dumps(result, indent=2))
    raise SystemExit(result['status'] != 'PASS')
