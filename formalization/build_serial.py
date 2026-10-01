#!/usr/bin/env python3
"""Build this pinned Gaussian project with one requested module at a time.

Run from this script's directory. Requires Python3, Git, and elan/Lean4.34.1.
No campaign paths, proof caches, generated theorem stubs, or local patches are used.
"""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, subprocess, sys, time
root=Path(__file__).resolve().parent
args=argparse.ArgumentParser();args.add_argument('--log-dir',default='build-evidence');opt=args.parse_args()
logs=(root/opt.log_dir).resolve();logs.mkdir(parents=True,exist_ok=True)
env=dict(os.environ,LEAN_NUM_THREADS='1');env.pop('LEAN_PATH',None)
commands=[]
def run(cmd,log):
    start=time.time()
    with (logs/log).open('w') as stream:
        code=subprocess.call(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT)
    commands.append({'command':cmd,'exit_code':code,'seconds':time.time()-start,'log':log})
    (logs/'commands.json').write_text(json.dumps(commands,indent=2)+'\n')
    if code:
        print((logs/log).read_text()[-12000:],file=sys.stderr);raise SystemExit(code)
run(['lake','--version'],'lake-version.log')
# Lake uses lake-manifest.json to materialize exactly the locked dependency set.
run(['lake','env','lean','--version'],'lean-version.log')
assert re.search(r'\bversion 4\.34\.1,', (logs/'lean-version.log').read_text()),'wrong Lean toolchain'
lock=json.loads((root/'lake-manifest.json').read_text());pins=[]
for item in lock['packages']:
    name=item['name'].strip('«»');path=root/lock.get('packagesDir','.lake/packages')/name
    rev=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
    assert rev==item['rev'],(name,rev,item['rev'])
    subprocess.run(['git','-C',str(path),'diff','--exit-code','HEAD','--'],check=True,stdout=subprocess.DEVNULL)
    untracked=subprocess.check_output(['git','-C',str(path),'ls-files','--others','--exclude-standard'],text=True).splitlines()
    assert not untracked,(name,'untracked dependency files',untracked)
    pins.append({'name':name,'url':item['url'],'revision':rev})
(logs/'dependency-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
seen=set();order=[];sources={}
def visit(module):
    if module in seen:return
    seen.add(module)
    relative=Path(*module.split('.')).with_suffix('.lean')
    source=root/relative
    if not source.exists():source=root/'.lake/packages/Physlib'/relative
    if not source.exists():return # Official dependencies are resolved by Lake itself.
    sources[str(source.relative_to(root))]=hashlib.sha256(source.read_bytes()).hexdigest()
    for dependency in re.findall(r'^(?:public )?import ([\w.]+)',source.read_text(),re.M):visit(dependency)
    order.append(module)
visit('Gaussian')
(logs/'source-hashes-before.json').write_text(json.dumps(sources,indent=2)+'\n')
(logs/'module-order.json').write_text(json.dumps(order,indent=2)+'\n')
for index,module in enumerate(order,1):
    print(f'[{index}/{len(order)}] {module}',flush=True)
    run(['lake','build','+'+module],module+'.log')
run(['lake','build'],'ordinary-lake-build.log')
probe=logs/'RootAxioms.lean'
probe.write_text('import Gaussian\n#print axioms Gaussian.Physical.Boson.exists_matched_global_gaussian_purification\n#print axioms Gaussian.Physical.Fermion.exists_matched_global_gaussian_purification\n')
run(['lake','env','lean','-Dwarn.sorry=true',str(probe)],'root-axioms.log')
text=(logs/'root-axioms.log').read_text();groups=re.findall(r'depends on axioms:\s*\[([^\]]*)\]',text,re.S)
axioms={name.strip() for group in groups for name in group.split(',') if name.strip()}
assert len(groups)==2 and axioms<={'propext','Classical.choice','Quot.sound'},text
changed=[path for path,digest in sources.items() if hashlib.sha256((root/path).read_bytes()).hexdigest()!=digest]
assert not changed,changed
(logs/'completion.json').write_text(json.dumps({'status':'PINNED_PROJECT_BUILD_PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_modules':len(order),'source_hashes_unchanged':True,'root_axioms':sorted(axioms),'ordinary_lake_exit_code':0,'note':'This script does not certify an independent audit or a clean starting directory; record cache provenance separately for a clean-room run.'},indent=2)+'\n')
print('PINNED_PROJECT_BUILD_PASS',flush=True)
