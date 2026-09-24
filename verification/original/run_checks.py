#!/usr/bin/env python3
"""Replay the internal falsification/regression suite, not a formal proof checker.

Usage: python run_checks.py
Runs in this directory, creates replay_logs/ and REPLAY_SUMMARY.json, and returns
nonzero if any test fails. Floating-point output can vary across BLAS platforms;
the assertions, not byte identity of regenerated logs, are the replay criterion.
"""
from __future__ import annotations
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
SCRIPTS = (
    "verify_polar_compression.py",
    "verify_fock_compression.py",
    "verify_exact_geometry.py",
    "verify_orbit_and_boundary.py",
    "verify_failed_shortcut.py",
    "verify_mutations.py",
)

def main() -> int:
    logdir = ROOT / "replay_logs"
    logdir.mkdir(exist_ok=True)
    env = os.environ.copy()
    env.update(OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", MKL_NUM_THREADS="1")
    results = []
    for script in SCRIPTS:
        path = ROOT / script
        if not path.is_file():
            print(f"Missing required verifier: {path}", file=sys.stderr)
            return 2
        start = time.monotonic()
        run = subprocess.run([sys.executable, str(path)], cwd=ROOT, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             text=True, check=False)
        log = logdir / (path.stem + ".log")
        log.write_text(run.stdout, encoding="utf-8")
        result = {"script": script, "exit_code": run.returncode,
                  "elapsed_seconds": round(time.monotonic() - start, 3),
                  "script_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                  "log": str(log.relative_to(ROOT)),
                  "status": "PASS" if run.returncode == 0 else "FAIL"}
        results.append(result)
        print(f"{result['status']} {script} ({result['elapsed_seconds']} s)", flush=True)
        if run.returncode:
            print(run.stdout, file=sys.stderr)
    summary = {
        "interpretation": "Same-agent internal replay; not independent external audit or formal certification",
        "python": sys.version,
        "platform": platform.platform(),
        "packages": {name: importlib.metadata.version(name)
                     for name in ("numpy", "scipy", "sympy", "mpmath")},
        "tests": results,
        "overall": "PASS" if all(x["exit_code"] == 0 for x in results) else "FAIL",
    }
    (ROOT / "REPLAY_SUMMARY.json").write_text(json.dumps(summary, indent=2), encoding="utf-8")
    return 0 if summary["overall"] == "PASS" else 1

if __name__ == "__main__":
    raise SystemExit(main())
