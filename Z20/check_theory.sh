#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
export PATH="$root/.z20/lean/bin:$PATH"
export LEAN_NUM_THREADS=2
mkdir -p theory-output .z20/project/JSP000622
cp -a classification-data/project/JSP000622/. .z20/project/JSP000622/
cp -a Z20/JSP000622/. .z20/project/JSP000622/
python3 - "$root" <<'PY'
import json, os, signal, subprocess, sys, time
from pathlib import Path
root=Path(sys.argv[1]); project=root/'.z20/project'; out=root/'theory-output'
sys.path.insert(0,str(root/'Z20'))
from audit_axioms import audit
checks=[
 ('JSP000622.Foundations',['JSP000622.z_twenty_ge_six','JSP000622.z_twenty_eq_six_of_two_fours']),
 ('JSP000622.ExtensionKernel',['JSP000622.Certificate.classified_step']),
 ('JSP000622.Templates',['JSP000622.Certificate.realizes_template16','JSP000622.Certificate.realizes_template20']),
 ('JSP000622.RamseyAux',['JSP000622.Certificate.degree_seven_or_eight','JSP000622.Certificate.exists_homogeneous_four_twenty']),
 ('JSP000622.R34Steps.Level0Case0',['JSP000622.R34Steps.Level0Case0.classify']),
 ('JSP000622.R34Steps.Level3Case0',['JSP000622.R34Steps.Level3Case0.classify']),
]
results=[]
for module,theorems in checks:
    start=time.monotonic(); p=subprocess.Popen(['lake','build',module],cwd=project,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
    try: text,_=p.communicate(timeout=480)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGTERM)
        try: text,_=p.communicate(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL); text,_=p.communicate()
        text+='\nCHECK_TIMEOUT: no successful proof check is claimed.\n'; p.returncode=124
    name=module.replace('.','_'); (out/f'{name}.txt').write_text(text)
    result={'module':module,'returncode':p.returncode,'seconds':round(time.monotonic()-start,2)}
    print(f'=== {module}: returncode {p.returncode} ===\n{text}',flush=True)
    if p.returncode==0:
        f=project/'TheoryAudit.lean'
        f.write_text(f'import {module}\n'+''.join(f'#print axioms {n}\n' for n in theorems))
        q=subprocess.run(['lake','env','lean',str(f)],cwd=project,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=180)
        logfile=out/f'{name}_axioms.txt'; logfile.write_text(q.stdout); print(q.stdout,flush=True)
        if q.returncode: result['audit_error']=q.stdout
        else:
            try: result['axiom_audit']=audit(logfile,theorems)
            except ValueError as e: result['audit_error']=str(e)
    results.append(result)
    (out/'results.json').write_text(json.dumps({'source_commit':os.environ['GITHUB_SHA'],'checks':results},indent=2))
if any(x['returncode'] or 'audit_error' in x for x in results): raise SystemExit(1)
PY
