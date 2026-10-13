"""Verify appendix source locators and excerpts, without claiming Lean compilation."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / 'docs/formal-verification'

def verify():
    errors = []
    data = json.loads((DOCS / 'declarations.json').read_text())
    statements = (DOCS / 'STATEMENTS.md').read_text()
    appendix = (DOCS / 'APPENDIX.md').read_text()
    seen = set()
    for e in data['declarations']:
        key = e['id']
        if key in seen:
            errors.append('duplicate ID: ' + key)
        seen.add(key)
        path = ROOT / e['path']
        if not path.is_file():
            errors.append('missing source: ' + e['path'])
            continue
        if hashlib.sha256(path.read_bytes()).hexdigest() != e['source_sha256']:
            errors.append('source hash: ' + key)
        source = path.read_text().splitlines()
        excerpt = '\n'.join(source[e['start_line']-1:e['end_line']])
        # The last line also holds the proof assignment; only its header is recorded.
        if not excerpt.startswith(e['signature']):
            errors.append('statement excerpt: ' + key)
        remainder = excerpt[len(e['signature']):].strip()
        if not remainder.startswith(':='):
            errors.append('missing proof boundary: ' + key)
        if e['signature'] not in statements:
            errors.append('dossier mismatch: ' + key)
        expected = ('https://github.com/LeoLam233/gaussian-minimum-purification/blob/'
                    + data['lean_source_commit'] + '/' + e['path']
                    + f"#L{e['start_line']}-L{e['end_line']}")
        if e['url'] != expected or expected not in appendix or expected not in statements:
            errors.append('source link: ' + key)
        if '## ' + key + '\n' not in statements or '(STATEMENTS.md#' + key.lower() + ')' not in appendix:
            errors.append('crosswalk anchor: ' + key)
        namespace = []
        for line in source[:e['start_line']-1]:
            match = re.match(r'^namespace\s+(\S+)', line)
            if match:
                namespace.append(match[1])
            match = re.match(r'^end\s+(\S+)', line)
            if match and namespace and match[1] == namespace[-1]:
                namespace.pop()
        if '.'.join(namespace + [e['name']]) != e['qualified_name']:
            errors.append('namespace locator: ' + key)
    receipt = json.loads((DOCS / 'INPUTS.json').read_text())
    for e in receipt['current_checkout_input_files']:
        if hashlib.sha256((ROOT / e['path']).read_bytes()).hexdigest() != e['sha256']:
            errors.append('input file hash: ' + e['path'])
    return {'status': 'PASS' if not errors else 'FAIL',
            'declarations_checked': len(seen), 'errors': errors,
            'scope': 'Source/documentation consistency only; no Lean elaboration or kernel replay.'}

if __name__ == '__main__':
    result = verify()
    print(json.dumps(result, indent=2))
    raise SystemExit(result['status'] != 'PASS')
