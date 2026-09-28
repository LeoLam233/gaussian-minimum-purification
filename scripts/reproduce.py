"""Replay unchanged scientific scripts in a fresh, untracked working directory."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import importlib.metadata
import json
import os
import platform
import shutil
import subprocess
import sys
import time
import uuid

from verify_repository import ROOT, verify


def diagnostic_environment():
    env = os.environ.copy()
    # A parent started with -E may still carry this variable into its children.
    env.pop('PYTHONOPTIMIZE', None)
    env.update(OPENBLAS_NUM_THREADS='1', OMP_NUM_THREADS='1', MKL_NUM_THREADS='1',
               PYTHONDONTWRITEBYTECODE='1', PYTHONUTF8='1')
    return env


def main():
    if sys.flags.optimize:
        print('Diagnostic replay requires Python assertions. '
              'Remove -O/-OO and unset PYTHONOPTIMIZE before running this command.',
              file=sys.stderr)
        return 2
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', choices=['all','original','independent'], default='all')
    args = parser.parse_args()
    integrity = verify()
    if integrity['status'] != 'PASS':
        print(json.dumps(integrity, indent=2))
        return 2
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    output = ROOT/'.local/runs'/(stamp+'-'+uuid.uuid4().hex[:8])
    output.mkdir(parents=True)
    env = diagnostic_environment()
    selected = ['original','independent'] if args.suite=='all' else [args.suite]
    records = []
    for name in selected:
        destination = output/name
        destination.mkdir()
        for source in (ROOT/'verification'/name).iterdir():
            if source.is_file():
                shutil.copyfile(source,destination/source.name)
        entry = 'run_checks.py' if name=='original' else 'independent_density_checks.py'
        print('Running '+name+' diagnostics...',flush=True)
        start = time.monotonic()
        run = subprocess.run([sys.executable,'-B',entry],cwd=destination,env=env,
                             stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                             text=True,encoding='utf-8',errors='replace',check=False)
        (destination/'stdout.log').write_text(run.stdout,encoding='utf-8')
        print(run.stdout,flush=True)
        summary_name = 'REPLAY_SUMMARY.json' if name=='original' else 'independent_density_checks.json'
        check_error = None
        try:
            result = json.loads((destination/summary_name).read_text(encoding='utf-8'))
            if result.get('overall') != 'PASS':
                raise ValueError('Result summary did not report PASS')
            if name=='original':
                if len(result['tests'])!=6 or any(t['exit_code']!=0 for t in result['tests']):
                    raise ValueError('Expected six successful original verifiers')
                for test in result['tests']:
                    if test['script_sha256'] != hashlib.sha256((destination/test['script']).read_bytes()).hexdigest():
                        raise ValueError('Executed-source hash disagreement')
                counts = {'original_verifiers':6}
            else:
                counts = {key:len(result[key]) for key in ['boson_kernel','fermion_density','fermion_graded_parity']}
                if list(counts.values()) != [4,32,12]:
                    raise ValueError('Unexpected independent case counts')
        except (OSError,KeyError,ValueError) as exc:
            check_error = str(exc)
            counts = {}
        records.append({'suite':name,'exit_code':run.returncode,'summary_error':check_error,
                        'status':'PASS' if run.returncode==0 and check_error is None else 'FAIL',
                        'elapsed_seconds':round(time.monotonic()-start,3),'counts':counts,
                        'log':name+'/stdout.log'})
    summary = {
        'timestamp_utc':datetime.now(timezone.utc).isoformat(),
        'interpretation':'Repository-entry-point replay of existing diagnostic implementations; not a new independent proof audit.',
        'python_version':platform.python_version(),'system':platform.system(),
        'python_optimization':sys.flags.optimize,
        'packages':{n:importlib.metadata.version(n) for n in ['numpy','scipy','sympy','mpmath']},
        'integrity_before_run':integrity,'jobs':records,
        'overall':'PASS' if all(r['status']=='PASS' for r in records) else 'FAIL',
    }
    (output/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    print('Results: '+str(output.relative_to(ROOT)))
    print('Overall: '+summary['overall'])
    return 0 if summary['overall']=='PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
