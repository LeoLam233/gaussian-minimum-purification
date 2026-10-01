"""Negative controls for the repository-level Lean identity and root gates."""
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import verify_lean_source as identity
from lean_ci import ROOTS, parse_root_axioms, make_build_environment, check_gaussian_build_coverage


def report(name, axioms='propext, Classical.choice, Quot.sound'):
    return "'" + name + "' depends on axioms: [" + axioms + "]\n"


class LeanGateTests(unittest.TestCase):
    def test_inherited_cache_and_compiler_overrides_are_removed(self):
        inherited = {'PATH': '/toolchain/bin', 'LAKE_ARTIFACT_CACHE': 'true',
                     'LAKE_NO_CACHE': 'false', 'LAKE_CACHE_DIR': '/stale',
                     'LAKE_CACHE_ARTIFACT_ENDPOINT': 'https://unapproved.invalid',
                     'LAKE_PKG_URL_MAP': '{}', 'LEAN_GITHASH': 'untrusted',
                     'LEAN_PATH': '/stale/proofs', 'LEAN_NUM_THREADS': '128', 'ELAN_TOOLCHAIN': 'wrong',
                     'MATHLIB_CACHE_GET_URL': 'https://unapproved.invalid',
                     'XDG_CACHE_HOME': '/stale'}
        with tempfile.TemporaryDirectory(prefix='gaussian-cache-gate-') as folder:
            env = make_build_environment(Path(folder), inherited)
            self.assertEqual(env['PATH'], inherited['PATH'])
            self.assertEqual(env['LEAN_NUM_THREADS'], '2')
            self.assertEqual(env['LAKE_ARTIFACT_CACHE'], 'false')
            self.assertEqual(env['LAKE_NO_CACHE'], 'true')
            self.assertEqual(env['LAKE_CACHE_DIR'], '')
            self.assertEqual(env['LAKE_RESTORE_ARTIFACTS'], 'false')
            for name in ['LEAN_PATH', 'LEAN_GITHASH', 'ELAN_TOOLCHAIN',
                         'LAKE_CACHE_ARTIFACT_ENDPOINT', 'LAKE_PKG_URL_MAP', 'MATHLIB_CACHE_GET_URL']:
                self.assertNotIn(name, env)
            self.assertTrue(Path(env['LAKE_CONFIG']).is_file())
            self.assertTrue(Path(env['XDG_CACHE_HOME']).is_relative_to(folder))

    def test_actual_source_build_coverage_required(self):
        expected = {'Gaussian', 'Gaussian.Physical.Boson.GlobalMinimum'}
        built = '✔ [1/2] Built Gaussian.Physical.Boson.GlobalMinimum (12s)\n✔ [2/2] Built Gaussian (1s)\n'
        self.assertEqual(set(check_gaussian_build_coverage(built, expected)), expected)
        for output in ['', built.replace('Built Gaussian (', 'Replayed Gaussian ('),
                       built.replace('Built', 'Fetched'), built.splitlines()[0],
                       built + '✔ [3/3] Built Gaussian.Unexpected (1s)\n']:
            with self.subTest(output=output), self.assertRaises(RuntimeError):
                check_gaussian_build_coverage(output, expected)

    def test_exact_two_roots_pass(self):
        result = parse_root_axioms(''.join(report(name) for name in ROOTS))
        self.assertEqual(set(result), set(ROOTS))

    def test_missing_duplicated_or_wrong_roots_fail(self):
        for value in ['', report(ROOTS[0]), report(ROOTS[0]) * 2,
                      report(ROOTS[0]) + report('Unrelated.root'),
                      ''.join(report(name) for name in ROOTS) + report(ROOTS[0])]:
            with self.subTest(value=value), self.assertRaises(RuntimeError):
                parse_root_axioms(value)

    def test_hole_extra_or_missing_axioms_fail(self):
        for axioms in ['sorryAx', 'propext, Classical.choice, Quot.sound, Private.axiom',
                       'propext, Classical.choice', '']:
            with self.subTest(axioms=axioms), self.assertRaises(RuntimeError):
                parse_root_axioms(report(ROOTS[0], axioms) + report(ROOTS[1]))

    def test_warning_fails(self):
        with self.assertRaises(RuntimeError):
            parse_root_axioms('warning: declaration uses sorry\n' + ''.join(report(name) for name in ROOTS))

    def test_nested_comments_and_strings_are_not_proof_tokens(self):
        self.assertEqual(identity.lean_tokens('/- sorry /- axiom -/ admit -/ "sorry" -- axiom\ntheorem good'),
                         ['theorem', 'good'])
        for token in ['sorry', 'admit', 'axiom']:
            self.assertIn(token, identity.lean_tokens('example : True := by ' + token))

    def test_protected_byte_change_and_extra_source_fail(self):
        with tempfile.TemporaryDirectory(prefix='gaussian-identity-gate-') as folder:
            project = Path(folder) / 'formalization'
            shutil.copytree(identity.PROJECT, project, ignore=shutil.ignore_patterns('.lake', 'build-evidence', '__pycache__'))
            with patch.object(identity, 'PROJECT', project):
                self.assertEqual(identity.verify()['status'], 'PASS')
                target = project / 'README.md'
                original = target.read_bytes()
                target.write_bytes(original + b'\n')
                self.assertEqual(identity.verify()['status'], 'FAIL')
                target.write_bytes(original)
                (project / 'Unexpected.lean').write_text('example : True := by trivial\n')
                self.assertEqual(identity.verify()['status'], 'FAIL')


if __name__ == '__main__':
    unittest.main(verbosity=2)
