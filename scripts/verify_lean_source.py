"""Fail closed on the frozen 313-file Lean-project identity and proof holes."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'formalization'
GENERATED_DIRS = {'.lake', 'build-evidence', '__pycache__'}


def lean_tokens(text):
    """Discard nested Lean comments and string literals before token inspection."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            result.append(' ')
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
            result.append(' ')
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            result.append(' ')
        else:
            result.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return re.findall(r'[A-Za-z_][A-Za-z_0-9\'!?.]*', ''.join(result))


def verify(check_tracked=False):
    provenance = json.loads((ROOT / 'provenance/LEAN_FORMALIZATION_SOURCE.json').read_text())
    rows = provenance['protected_files']
    errors = []
    expected = {row['path']: row for row in rows}
    if len(rows) != 313 or len(expected) != 313:
        errors.append('Expected exactly 313 distinct protected files')
    if sum(name.endswith('.lean') for name in expected) != 308:
        errors.append('Expected exactly 308 Lean sources')
    for name, row in expected.items():
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts or '\\' in name or ':' in name:
            errors.append('Invalid protected path: ' + name)
            continue
        path = PROJECT / name
        if not path.is_file() or path.is_symlink():
            errors.append('Missing or linked protected file: ' + name)
            continue
        payload = path.read_bytes()
        if len(payload) != row['size'] or hashlib.sha256(payload).hexdigest() != row['sha256']:
            errors.append('Protected byte mismatch: ' + name)
        if name.endswith('.lean'):
            forbidden = set(lean_tokens(payload.decode('utf-8'))) & {'sorry', 'admit', 'axiom'}
            if forbidden:
                errors.append('Forbidden proof token in ' + name + ': ' + ', '.join(sorted(forbidden)))
    actual = {
        p.relative_to(PROJECT).as_posix()
        for p in PROJECT.rglob('*') if p.is_file()
        and not set(p.relative_to(PROJECT).parts) & GENERATED_DIRS
        and p.suffix not in {'.pyc', '.pyo'}
    }
    errors.extend('Unexpected protected-project file: ' + p for p in sorted(actual - expected.keys()))
    if check_tracked:
        tracked = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
        protected_tracked = {p.removeprefix('formalization/') for p in tracked if p.startswith('formalization/')}
        if protected_tracked != set(expected):
            errors.append('Git tracked formalization inventory is not exactly the frozen 313 files')
        for name in tracked:
            parts = PurePosixPath(name).parts
            if '.lake' in parts or name.endswith(('.olean', '.ilean', '.olean.private', '.olean.server')):
                errors.append('Committed proof product: ' + name)
    return {'status': 'PASS' if not errors else 'FAIL', 'protected_files': 313,
            'lean_sources': 308, 'errors': errors}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-tracked', action='store_true')
    args = parser.parse_args()
    result = verify(args.check_tracked)
    print(json.dumps(result, indent=2))
    raise SystemExit(result['status'] != 'PASS')
