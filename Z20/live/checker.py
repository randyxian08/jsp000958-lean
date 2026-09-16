#!/usr/bin/env python3
"""Bounded incremental verifier for this isolated proof branch.

Only explicit module-build/audit requests are accepted. This is build tooling,
not part of any mathematical trusted base. Compiler output and its exact source
commit are recorded; no success is inferred from the absence of source markers.
The GitHub token is not passed to Lean, generators, or other proof subprocesses.
"""
from __future__ import annotations
import base64
import json
import os
import re
import shutil
import signal
import subprocess
import time
import urllib.error
import urllib.request
from pathlib import Path

ROOT = Path.cwd()
PROJECT = ROOT / '.z20/project'
BRANCH = 'work/jsp000622-z20-verification'
REPO = 'randyxian08/jsp000958-lean'
TOKEN = os.environ['GH_TOKEN']
API = 'https://api.github.com/repos/' + REPO
OUT = ROOT / 'live-output'
OUT.mkdir(exist_ok=True)
ENV = {k:v for k,v in os.environ.items() if k not in ('GH_TOKEN','GITHUB_TOKEN')}
ENV['PATH'] = str(ROOT/'.z20/lean/bin') + os.pathsep + ENV['PATH']
ENV['LEAN_NUM_THREADS'] = '2'
PIN = '8822f7ddef30fadbd92e1c6ab4ed897af356af5e'
NAME = re.compile(r'^(?:JSP000622|ErdosProblems|Util)(?:\.[A-Za-z_][A-Za-z0-9_]*)+$')


def api(path, data=None):
    request=urllib.request.Request(API+path, data=None if data is None else json.dumps(data).encode(),
        headers={'Authorization':'Bearer '+TOKEN,'Accept':'application/vnd.github+json','X-GitHub-Api-Version':'2022-11-28','Content-Type':'application/json'},
        method='GET' if data is None else 'PUT')
    with urllib.request.urlopen(request,timeout=60) as response:
        return json.load(response)


def publish(result):
    text=json.dumps(result,ensure_ascii=False,indent=2)+'\n'
    (OUT/'result.json').write_text(text)
    path='/contents/Z20/live/result.json'
    for attempt in range(4):
        try:
            try: previous=api(path+'?ref='+urllib.parse.quote(BRANCH,safe=''))
            except urllib.error.HTTPError as e:
                if e.code!=404: raise
                previous={}
            payload={'message':f"ci(z20): incremental check {result.get('id')} {result['status']} [skip ci]",
                     'branch':BRANCH,'content':base64.b64encode(text.encode()).decode()}
            if 'sha' in previous: payload['sha']=previous['sha']
            api(path,payload)
            return
        except urllib.error.HTTPError as e:
            if e.code not in (409,422) or attempt==3: raise
            time.sleep(1)


def command(args,cwd=PROJECT,timeout=600,token=False):
    env=dict(ENV)
    if token: env['GH_TOKEN']=TOKEN
    start=time.monotonic()
    p=subprocess.Popen(args,cwd=cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                       text=True,start_new_session=True)
    try: text,_=p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGTERM)
        try: text,_=p.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL); text,_=p.communicate()
        text+='\nCHECKER_TIMEOUT: no successful verification is claimed.\n'
        p.returncode=124
    return {'command':args,'returncode':p.returncode,'seconds':round(time.monotonic()-start,2),'output':text}


def require(args,cwd=ROOT,timeout=300,token=False):
    result=command(args,cwd,timeout,token)
    if result['returncode']:
        raise RuntimeError(json.dumps(result))
    return result


def upstream():
    path=ROOT/'.z20/upstream'
    if not (path/'.git').exists():
        require(['git','init',str(path)])
        require(['git','-C',str(path),'remote','add','origin','https://github.com/plby/lean-proofs.git'])
        require(['git','-C',str(path),'config','core.sparseCheckout','true'])
        (path/'.git/info/sparse-checkout').write_text('/README.md\n/LICENSE\n/src/latest/lean-toolchain\n/src/latest/lake-manifest.json\n/src/latest/ErdosProblems/Erdos758.lean\n/src/latest/ErdosProblems/Erdos758/\n/src/latest/Util/\n')
        require(['git','-C',str(path),'fetch','--depth','1','--filter=blob:none','origin',PIN])
        require(['git','-C',str(path),'checkout','--detach','FETCH_HEAD'])
    actual=require(['git','-C',str(path),'rev-parse','HEAD'])['output'].strip()
    assert actual==PIN
    (PROJECT/'ErdosProblems').mkdir(exist_ok=True)
    shutil.copy2(path/'src/latest/ErdosProblems/Erdos758.lean',PROJECT/'ErdosProblems/Erdos758.lean')
    shutil.copytree(path/'src/latest/ErdosProblems/Erdos758',PROJECT/'ErdosProblems/Erdos758',dirs_exist_ok=True)
    shutil.copytree(path/'src/latest/Util',PROJECT/'Util',dirs_exist_ok=True)


def artifact(item):
    run=int(item['run_id']); pattern=item['pattern']
    assert pattern.startswith('z20-') and '/' not in pattern
    directory=ROOT/'.z20/imports'/f'{run}-{pattern.replace("*","all")}'
    marker=directory/'.downloaded'
    if not marker.exists():
        directory.mkdir(parents=True,exist_ok=True)
        require(['gh','run','download',str(run),'-R',REPO,'--pattern',pattern,'--dir',str(directory)],timeout=300,token=True)
        marker.touch()
    for sources in directory.rglob('project/JSP000622'):
        shutil.copytree(sources,PROJECT/'JSP000622',dirs_exist_ok=True)
    if item.get('builds',False):
        for tar in directory.rglob('*.tar.zst'):
            listing=require(['tar','--zstd','-tf',str(tar)])['output'].splitlines()
            assert all(not p.startswith('/') and '..' not in Path(p).parts and p.startswith('.lake/build') for p in listing), str(tar)
            require(['tar','--zstd','-xf',str(tar)],cwd=PROJECT)
    return {'run_id':run,'pattern':pattern,'files':sum(1 for p in directory.rglob('*') if p.is_file())}


def execute(request,source):
    ident=request['id']; result={'id':ident,'status':'running','source_commit':source,
        'worker_run_id':os.environ['GITHUB_RUN_ID'],'builds':[]}
    publish(result)
    snapshot=ROOT/'.z20/current-sources'
    if snapshot.exists(): shutil.rmtree(snapshot)
    snapshot.mkdir()
    archive=ROOT/'.z20/current-sources.tar'
    require(['git','archive','--format=tar','-o',str(archive),source,'Z20'])
    require(['tar','-xf',str(archive),'-C',str(snapshot)])
    sources=snapshot/'Z20'
    if request.get('upstream'): upstream()
    result['artifacts']=[artifact(item) for item in request.get('artifacts',[])]
    shutil.copytree(sources/'JSP000622',PROJECT/'JSP000622',dirs_exist_ok=True)
    timeout=max(10,min(900,int(request.get('timeout',300))))
    if request.get('core_data'):
        result['builds'].append(command(['python3',str(sources/'generate_core_certificates.py'),str(PROJECT),str(OUT/'core')],cwd=ROOT,timeout=300))
        for p in (PROJECT/'JSP000622').glob('Core[01].lean'):
            p.write_text(p.read_text().replace('(rules.map PairRule.clause).proof []','Sat.Fmla.proof (rules.map PairRule.clause) []'))
    for name in request.get('targets',[]):
        assert NAME.fullmatch(name),name
        r=command(['lake','build',name],timeout=timeout)
        result['builds'].append(r)
        if r['returncode']: break
    if request.get('probe') and not any(r['returncode'] for r in result['builds']):
        (PROJECT/'LiveProbe.lean').write_text(request['probe'])
        result['builds'].append(command(['lake','env','lean','LiveProbe.lean'],timeout=timeout))
    reads=[]
    for item in request.get('read_files',[]):
        p=(PROJECT/item['path']).resolve()
        assert p.is_relative_to(PROJECT.resolve()) and p.suffix in ('.lean','.json','.txt','.toml','.md'),str(p)
        lines=p.read_text().splitlines()
        start=max(1,int(item.get('start',1))); end=min(len(lines),int(item.get('end',start+160)))
        reads.append({'path':item['path'],'text':'\n'.join(f'{i+1}: {line}' for i,line in enumerate(lines) if start<=i+1<=end)})
    result['reads']=reads
    result['status']='passed' if all(r['returncode']==0 for r in result['builds']) else 'failed'
    full=json.dumps(result,ensure_ascii=False,indent=2)
    (OUT/f'check-{ident}.json').write_text(full)
    for r in result['builds']:
        if len(r['output'])>30000: r['output']='[earlier output retained in the workflow artifact]\n'+r['output'][-30000:]
    publish(result)


def main():
    PROJECT.mkdir(parents=True,exist_ok=True)
    publish({'id':None,'status':'ready','worker_run_id':os.environ['GITHUB_RUN_ID'],
             'scope':'Incremental checking only; no mathematical success or prize is claimed.'})
    start=last=time.monotonic(); handled=None
    while time.monotonic()-start<2400 and time.monotonic()-last<600:
        try:
            require(['git','fetch','--depth','1','origin',BRANCH],timeout=60)
            source=require(['git','rev-parse','FETCH_HEAD'])['output'].strip()
            blob=command(['git','show',source+':Z20/live/request.json'],cwd=ROOT,timeout=30)
            if blob['returncode']:
                time.sleep(5); continue
            request=json.loads(blob['output'])
            if request.get('stop'):
                publish({'id':request.get('id'),'status':'stopped','source_commit':source}); break
            if request['id']!=handled:
                handled=request['id']; last=time.monotonic()
                try: execute(request,source)
                except Exception as e:
                    publish({'id':handled,'status':'tooling_error','source_commit':source,'error':str(e)[-30000:]})
                last=time.monotonic()
        except Exception as e:
            print(type(e).__name__,str(e)[:300],flush=True)
        time.sleep(5)
    if (PROJECT/'JSP000622').exists(): shutil.copytree(PROJECT/'JSP000622',OUT/'JSP000622',dirs_exist_ok=True)
    if (PROJECT/'.lake/build').exists():
        require(['tar','--zstd','-cf',str(OUT/'incremental-build.tar.zst'),'.lake/build'],cwd=PROJECT,timeout=120)
    print('Bounded checker stopped.',flush=True)

if __name__=='__main__':
    import urllib.parse
    main()
