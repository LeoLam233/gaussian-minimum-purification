"""Build frozen public Gaussian sources and check both named roots and their axioms.

Run from any directory with the exact Lean toolchain's lake on PATH. No Gaussian
build cache is accepted. Upstream official pinned mathlib caches are optional.
All generated evidence is outside the protected project, in .local/lean-ci/.
"""
from pathlib import Path
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

from verify_lean_source import ROOT, PROJECT, verify

ROOTS = [
    'Gaussian.Physical.Boson.exists_matched_global_gaussian_purification',
    'Gaussian.Physical.Fermion.exists_matched_global_gaussian_purification',
]
STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def make_build_environment(runtime, inherited=None):
    """Isolate Lake configuration/cache and remove inherited compiler/cache overrides."""
    env = dict(os.environ if inherited is None else inherited)
    for name in list(env):
        if name.startswith(('LAKE_', 'LEAN_', 'MATHLIB_')) or name == 'ELAN_TOOLCHAIN':
            env.pop(name)
    runtime = Path(runtime).resolve()
    runtime.mkdir(parents=True, exist_ok=True)
    config = runtime / 'lake-config.toml'
    config.write_text('# Isolated default Lake configuration for source-only CI.\n')
    env.update(LEAN_NUM_THREADS='2', LAKE_NO_CACHE='true', LAKE_ARTIFACT_CACHE='false',
               LAKE_RESTORE_ARTIFACTS='false', LAKE_CACHE_DIR='',
               LAKE_CONFIG=str(config), XDG_CACHE_HOME=str(runtime / 'cache'),
               MATHLIB_CACHE_DIR=str(runtime / 'mathlib-cache'))
    return env


def check_gaussian_build_coverage(output, expected=None):
    """Require actual Built jobs for every frozen source, not replay/fetch messages."""
    if expected is None:
        provenance = json.loads((ROOT / 'provenance/LEAN_FORMALIZATION_SOURCE.json').read_text())
        expected = {row['path'][:-5].replace('/', '.') for row in provenance['protected_files']
                    if row['path'].endswith('.lean')}
    built = set(re.findall(r"(?m)^[^\n]*\[\d+/\d+\] Built (Gaussian(?:\.[A-Za-z0-9_']+)*)(?= \(|$)", output))
    missing = set(expected) - built
    unexpected = built - set(expected)
    if missing or unexpected:
        raise RuntimeError('Gaussian source-build coverage mismatch: ' + json.dumps(
            {'missing': sorted(missing), 'unexpected': sorted(unexpected)}))
    return sorted(built)


def parse_root_axioms(output):
    entries = re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", output, re.S)
    if len(entries) != 2 or {name for name, _ in entries} != set(ROOTS):
        raise RuntimeError('Expected exactly one axiom report for each exact root: ' + output)
    result = {name: sorted(a.strip() for a in axioms.split(',') if a.strip()) for name, axioms in entries}
    for name, axioms in result.items():
        if set(axioms) != STANDARD_AXIOMS:
            raise RuntimeError('Unexpected trusted base for ' + name + ': ' + repr(axioms))
    if re.search(r'\b(?:sorryAx|error|warning)\b', output):
        raise RuntimeError('Root probe produced an error, warning, or proof hole: ' + output)
    return result


def verify_dependencies():
    lock = json.loads((PROJECT / 'lake-manifest.json').read_text())
    result = []
    for package in lock['packages']:
        name = package['name'].strip('«»')
        path = PROJECT / lock['packagesDir'] / name
        revision = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
        if not re.fullmatch('[0-9a-f]{40}', package['rev']) or revision != package['rev']:
            raise RuntimeError('Dependency revision mismatch: ' + name)
        subprocess.run(['git', '-C', str(path), 'diff', '--exit-code', 'HEAD', '--'], check=True)
        untracked = subprocess.check_output(['git', '-C', str(path), 'ls-files', '--others', '--exclude-standard'], text=True)
        if untracked.strip():
            raise RuntimeError('Untracked dependency source: ' + name + '\n' + untracked)
        result.append({'name': name, 'revision': revision})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--use-official-cache', action='store_true')
    parser.add_argument('--check-tracked', action='store_true')
    args = parser.parse_args()
    output = ROOT / '.local/lean-ci'
    output.mkdir(parents=True, exist_ok=True)
    runtime = Path(tempfile.mkdtemp(prefix='runtime-', dir=output))
    env = make_build_environment(runtime)
    records = []

    def run(command, name):
        proc = subprocess.run(command, cwd=PROJECT, env=env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (output / name).write_text(proc.stdout)
        print(proc.stdout, end='', flush=True)
        records.append({'command': command, 'exit_code': proc.returncode, 'log': name})
        (output / 'commands.json').write_text(json.dumps(records, indent=2) + '\n')
        if proc.returncode:
            raise RuntimeError('Command failed: ' + ' '.join(command))
        return proc.stdout

    identity = verify(args.check_tracked)
    if identity['status'] != 'PASS':
        raise RuntimeError(json.dumps(identity))
    if (PROJECT / '.lake/build').exists():
        raise RuntimeError('Project .lake/build already exists; use a fresh source-only checkout')
    lean_version = run(['lake', 'env', 'lean', '--version'], 'lean-version.log')
    lake_version = run(['lake', '--version'], 'lake-version.log')
    if not re.search(r'\bversion 4\.34\.1,', lean_version):
        raise RuntimeError('Wrong Lean version: ' + lean_version)
    if not re.search(r'\bversion 5\.0\.0-src\+5045d00\b', lake_version):
        raise RuntimeError('Wrong Lake version: ' + lake_version)
    pins = verify_dependencies()
    if args.use_official_cache:
        run(['lake', 'exe', 'cache', 'get'], 'official-cache.log')
    if (PROJECT / '.lake/build').exists():
        raise RuntimeError('Unexpected project build products before source compilation')
    verify_dependencies()
    if verify()['status'] != 'PASS':
        raise RuntimeError('Protected project changed during dependency materialization')
    build_log = run(['lake', 'build'], 'lake-build.log')
    built_modules = check_gaussian_build_coverage(build_log)
    (output / 'gaussian-built-modules.json').write_text(json.dumps(built_modules, indent=2) + '\n')
    probe = output / 'RootAxioms.lean'
    probe.write_text('import Gaussian\n' + ''.join('#check ' + name + '\n#print axioms ' + name + '\n' for name in ROOTS))
    axioms = parse_root_axioms(run(['lake', 'env', 'lean', '-Dwarn.sorry=true', str(probe)], 'root-axioms.log'))
    if verify(args.check_tracked)['status'] != 'PASS':
        raise RuntimeError('Protected project changed during build')
    verify_dependencies()
    result = {'status': 'LEAN_CI_PASS', 'source_identity': '313 / 313 byte-identical',
              'lean_version': lean_version.strip(), 'lake_version': lake_version.strip(),
              'dependencies': pins, 'root_axioms': axioms, 'local_lake_build_exit_code': 0,
              'official_upstream_cache_requested': args.use_official_cache,
              'gaussian_build_cache_used': False,
              'gaussian_source_modules_built': len(built_modules),
              'cache_controls': {name: env[name] for name in
                  ['LEAN_NUM_THREADS', 'LAKE_NO_CACHE', 'LAKE_ARTIFACT_CACHE', 'LAKE_RESTORE_ARTIFACTS', 'LAKE_CACHE_DIR']},
              'isolated_cache_and_config': True}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, subprocess.SubprocessError) as exc:
        print('LEAN_CI_FAIL: ' + str(exc), file=sys.stderr)
        raise SystemExit(1)
