"""Check the appendix's pinned declaration locators and verbatim source excerpts.

This is a documentation check, not a Lean type checker or semantic certification.
--write refreshes generated excerpts only after checking the frozen source hashes.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'docs/formalization-appendix'
REGISTRY = DIRECTORY / 'declarations.json'
CATALOG = DIRECTORY / 'DECLARATIONS.md'
PIN = '62820a0afff79559be7c3af99cc23a8c7550ac5c'
BASE = 'https://github.com/LeoLam233/gaussian-minimum-purification/blob/' + PIN + '/'


def excerpt(row):
    path = ROOT / row['path']
    lines = path.read_text(encoding='utf-8').splitlines()
    pattern = re.compile(r'^(?:@\[[^\n]*\]\s*)?(theorem|lemma|def|abbrev|structure) '
                         + re.escape(row['local_name']) + r'(?=\s|\{|\(|$)')
    found = [i for i, line in enumerate(lines) if pattern.match(line)]
    if len(found) != 1:
        raise ValueError('Expected one declaration: ' + row['id'])
    start = found[0]
    scopes = []
    variables = []
    opens = []
    universes = []
    i = 0
    while i < start:
        line = lines[i]
        if line.startswith('namespace '):
            scopes.append(line.split()[1])
        elif line.startswith('end ') and scopes:
            scopes.pop()
        elif line.startswith('open '):
            opens.append((tuple(scopes), line))
        elif line.startswith('universe '):
            universes.append(line)
        elif line.startswith('variable '):
            block = [line]
            while i + 1 < start and lines[i+1].startswith('  '):
                i += 1
                block.append(lines[i])
            variables.append((tuple(scopes), '\n'.join(block)))
        i += 1
    name = '.'.join(scopes + [row['local_name']])
    if name != row['name']:
        raise ValueError('Namespace mismatch: ' + row['id'] + ': ' + name)
    kind = pattern.match(lines[start]).group(1)
    end = start
    if kind in {'theorem', 'lemma'}:
        while ':=' not in lines[end]:
            end += 1
        statement = '\n'.join(lines[start:end+1]).split(':=', 1)[0].rstrip()
    else:
        while end + 1 < len(lines) and lines[end+1].strip():
            end += 1
        statement = '\n'.join(lines[start:end+1])
    def active(items):
        return [value for scope, value in items if tuple(scopes[:len(scope)]) == scope]
    context = '\n'.join(dict.fromkeys(universes + active(opens) + ['namespace ' + s for s in scopes] + active(variables)))
    return {'start_line': start+1, 'end_line': end+1, 'context': context,
            'statement': statement, 'source_sha256': hashlib.sha256(path.read_bytes()).hexdigest()}


def render(data):
    output = ['# Verbatim declaration register', '',
              'Companion to the [formalization verification appendix](README.md), version 1.0, 13 October 2026.', '',
              'The excerpts below are copied from the frozen v0.1.3 sources. Each entry includes the file-scoped '
              '`variable` blocks and namespace/open context preceding the declaration, followed by the exact '
              'theorem type or definition. Context is a reading aid, not a standalone Lean file. The source link '
              'also exposes the proof and imports; imported definitions and instances remain part of the type. '
              'Some context variables do not occur in a particular declaration and are not its hypotheses. '
              'No proof body is reproduced for theorems. The register is intentionally selective, not an index '
              'of every lemma in all 308 source files.', '',
              'The machine-readable [registry](declarations.json) pins names, complete-file hashes and line ranges. '
              'Run `python scripts/verify_formalization_appendix.py` from the repository root to check the excerpts. '
              'That command checks documentation identity; the separate Lean workflow checks compilation and root axioms.', '']
    for row in data['declarations']:
        output += ['## ' + row['id'], '', '`' + row['name'] + '`', '',
                   '**Paper node:** ' + row['paper_node'] + '.', '',
                   '**Reading and coverage:** ' + row['reading'], '',
                   '**Limits / premises to retain:** ' + row['limits'], '',
                   '[Frozen source, lines ' + str(row['start_line']) + '–' + str(row['end_line']) + ']('
                   + BASE + row['path'] + '#L' + str(row['start_line']) + '-L' + str(row['end_line']) + ')', '',
                   '```lean', row['context'], '', row['statement'], '```', '']
    return '\n'.join(output)


def verify(write=False):
    data = json.loads(REGISTRY.read_text(encoding='utf-8'))
    errors = []
    if data['lean_commit'] != PIN or data['manuscript_commit'] != '313c3e8ac67463388c36a4094a42f40aec8a3aa6':
        errors.append('Incorrect source revision pins')
    inventory = json.loads((ROOT / 'provenance/LEAN_FORMALIZATION_SOURCE.json').read_text(encoding='utf-8'))
    hashes = {'formalization/' + r['path']: r['sha256'] for r in inventory['protected_files']}
    seen = set()
    for row in data['declarations']:
        if row['id'] in seen or not re.fullmatch('[BFDGS][0-9]{2}', row['id']):
            errors.append('Invalid/duplicate ID: ' + row['id'])
        seen.add(row['id'])
        if row['path'] not in hashes:
            errors.append('Declaration outside frozen inventory: ' + row['id'])
            continue
        try:
            actual = excerpt(row)
        except (ValueError, IndexError, OSError) as error:
            errors.append(str(error))
            continue
        if actual['source_sha256'] != hashes[row['path']]:
            errors.append('Source differs from frozen inventory: ' + row['id'])
            continue
        if write:
            row.update(actual)
        elif any(row.get(key) != value for key, value in actual.items()):
            errors.append('Stale declaration excerpt/locator: ' + row['id'])
    appendix = (DIRECTORY / 'README.md').read_text(encoding='utf-8')
    referenced = set(re.findall(r'DECLARATIONS\.md#([bfdgs][0-9]{2})', appendix))
    if referenced != {r.lower() for r in seen}:
        errors.append('Appendix and declaration register IDs disagree')
    if not errors:
        rendered = render(data)
        if write:
            REGISTRY.write_text(json.dumps(data, ensure_ascii=False, indent=2) + '\n', encoding='utf-8', newline='\n')
            CATALOG.write_text(rendered, encoding='utf-8', newline='\n')
        elif CATALOG.read_text(encoding='utf-8') != rendered:
            errors.append('Generated declaration register differs')
    return {'status': 'FAIL' if errors else 'PASS', 'declarations_checked': len(seen), 'errors': errors}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    result = verify(parser.parse_args().write)
    print(json.dumps(result, indent=2))
    raise SystemExit(bool(result['errors']))
