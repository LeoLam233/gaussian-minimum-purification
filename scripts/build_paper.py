"""Compile a working copy, keeping the versioned paper bytes unchanged."""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import sys
import uuid

from verify_repository import ROOT, verify


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine',choices=['tectonic','pdflatex'],default='tectonic')
    parser.add_argument('--engine-path',help='Optional path to the selected engine executable')
    parser.add_argument('--only-cached',action='store_true',help='Tectonic: use only cached TeX resources')
    args = parser.parse_args()
    result = verify()
    if result['status']!='PASS':
        print(json.dumps(result,indent=2))
        return 2
    executable = args.engine_path or shutil.which(args.engine)
    if not executable:
        parser.error('Selected TeX engine is not installed or not on PATH')
    if args.only_cached and args.engine!='tectonic':
        parser.error('--only-cached applies to Tectonic')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    output = ROOT/'.local/builds'/(stamp+'-'+uuid.uuid4().hex[:8])
    output.mkdir(parents=True)
    shutil.copyfile(ROOT/'paper/manuscript.tex',output/'manuscript.tex')
    if args.engine=='tectonic':
        command = [executable,'--keep-logs','--keep-intermediates']
        if args.only_cached: command.append('--only-cached')
        command.append('manuscript.tex')
        passes = 1
    else:
        command = [executable,'-interaction=nonstopmode','-halt-on-error','manuscript.tex']
        passes = 2
    logs = []
    for _ in range(passes):
        run = subprocess.run(command,cwd=output,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                             text=True,encoding='utf-8',errors='replace',check=False)
        logs.append(run.stdout)
        (output/'build_stdout.log').write_text('\n'.join(logs),encoding='utf-8')
        if run.returncode:
            print(run.stdout)
            return run.returncode
    if not (output/'manuscript.pdf').is_file():
        raise RuntimeError('Build reported success without producing a PDF')
    print('Built working-copy PDF: '+str((output/'manuscript.pdf').relative_to(ROOT)))
    print('The frozen manuscript files were not modified.')
    return 0


if __name__=='__main__':
    sys.exit(main())
