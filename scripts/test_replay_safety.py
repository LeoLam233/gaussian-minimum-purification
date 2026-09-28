"""Regression tests for assertion-preserving diagnostic replay."""
from pathlib import Path
import os
import subprocess
import sys
import unittest
from unittest.mock import patch

from reproduce import diagnostic_environment


ROOT = Path(__file__).resolve().parents[1]
FAULT_PROBE = r'''
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, sys.argv[1])
import verify_fock_compression as checker

original_entropy = checker.sf
checker.sf = lambda gamma: original_entropy(gamma) + 1.0
with tempfile.TemporaryDirectory(prefix='gaussian-replay-test-') as output:
    checker.ROOT = Path(output)
    print('Injected entropy offset: +1 nat', flush=True)
    checker.run()
'''


class ReplaySafetyTests(unittest.TestCase):
    def run_python(self, args, env):
        return subprocess.run(
            [sys.executable, '-B', *args], cwd=ROOT, env=env,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding='utf-8', errors='replace', timeout=60,
            check=False,
        )

    def test_optimized_entry_point_is_rejected(self):
        cases = [(['-O'], None), (['-OO'], None), ([], '1'), ([], '2')]
        for flags, level in cases:
            with self.subTest(flags=flags, environment_level=level):
                env = diagnostic_environment()
                if level is not None:
                    env['PYTHONOPTIMIZE'] = level
                # --help avoids running the suites if the guard regresses.
                run = self.run_python(
                    [*flags, 'scripts/reproduce.py', '--help'], env,
                )
                self.assertEqual(run.returncode, 2, run.stdout)
                self.assertIn('Diagnostic replay requires Python assertions.', run.stdout)

    def test_entropy_fault_is_detected_in_child_process(self):
        # A variable set after interpreter startup does not change this process's
        # optimize flag, but would disable assertions in unsanitized children.
        for level in [None, '1', '2']:
            with self.subTest(inherited_environment_level=level):
                with patch.dict(os.environ):
                    os.environ.pop('PYTHONOPTIMIZE', None)
                    if level is not None:
                        os.environ['PYTHONOPTIMIZE'] = level
                    env = diagnostic_environment()
                run = self.run_python(
                    ['-c', FAULT_PROBE, str(ROOT/'verification/original')], env,
                )
                self.assertNotEqual(run.returncode, 0, run.stdout)
                self.assertIn('Injected entropy offset: +1 nat', run.stdout)
                self.assertIn('assert abs(bef-cov_bef)', run.stdout)
                self.assertIn('AssertionError', run.stdout)
                self.assertNotIn('FOCK-SPACE CHECK PASS', run.stdout)


if __name__ == '__main__':
    unittest.main(verbosity=2)
