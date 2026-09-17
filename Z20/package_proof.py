#!/usr/bin/env python3
"""Package checked source and evidence; never turn a source scan into proof success.

The package includes no precompiled proof objects and no credentials. Rebuilding
uses the exact dependency lock; the upstream auxiliary source is fetched at its
recorded commit with its original headers. All generated finite data are included.
"""
from __future__ import annotations
import hashlib
import json
import os
import shutil
import sys
import zipfile
from pathlib import Path
from audit_axioms import audit

ROOT = Path.cwd()
OUT = ROOT/'delivery'
PACKAGE = OUT/'JSP000622-z20'
EXPECTED = ['JSP000622.R34Seven.complete', 'JSP000622.R34Eight.complete',
    'JSP000622.FiniteEvidence.complete_sixteen', 'JSP000622.FiniteEvidence.packing_twenty',
    'JSP000622.z_twenty_eq_six', 'JSP000622.maximum_cochromatic_twenty_eq_six',
    'JSP000622.colorable_six_of_card_twenty', 'JSP000622.JSP_000622']

BOOTSTRAP = '''#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
mkdir -p logs ErdosProblems
pin=8822f7ddef30fadbd92e1c6ab4ed897af356af5e
if [ ! -d upstream/.git ]; then
  git init upstream
  git -C upstream remote add origin https://github.com/plby/lean-proofs.git
  git -C upstream config core.sparseCheckout true
  printf '%s\\n' /README.md /src/latest/lean-toolchain /src/latest/lake-manifest.json /src/latest/ErdosProblems/Erdos758.lean /src/latest/ErdosProblems/Erdos758/ /src/latest/Util/ > upstream/.git/info/sparse-checkout
fi
git -C upstream fetch --depth 1 --filter=blob:none origin "$pin"
git -C upstream checkout --detach "$pin"
test "$(git -C upstream rev-parse HEAD)" = "$pin"
cp upstream/src/latest/ErdosProblems/Erdos758.lean ErdosProblems/
cp -a upstream/src/latest/ErdosProblems/Erdos758 ErdosProblems/
cp -a upstream/src/latest/Util .
# Do not run lake update: lake-manifest.json is the exact checked dependency lock.
lake exe cache get 2>&1 | tee logs/dependency-cache.txt
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = db584cd6d46c92f209a44c0f1c829460d327499d
lake env lean --version | tee logs/lean-version.txt
'''

VERIFY = '''#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
python3 verify_manifest.py
bash bootstrap.sh
lake build JSP000622.Main 2>&1 | tee logs/complete-build.txt
lake env lean Audit.lean 2>&1 | tee logs/axioms.txt
python3 audit_axioms.py logs/axioms.txt JSP000622.R34Seven.complete JSP000622.R34Eight.complete JSP000622.FiniteEvidence.complete_sixteen JSP000622.FiniteEvidence.packing_twenty JSP000622.z_twenty_eq_six JSP000622.maximum_cochromatic_twenty_eq_six JSP000622.colorable_six_of_card_twenty JSP000622.JSP_000622 | tee logs/axiom-audit.json
if [ "${1:-}" = "--fresh" ]; then
  lake env leanchecker --fresh JSP000622.Main 2>&1 | tee logs/fresh-kernel.txt
  printf '%s\\n' 'Closed theorem compiled, exact axiom audit passed, fresh kernel replay passed.'
else
  printf '%s\\n' 'Closed theorem compiled and exact axiom audit passed. Fresh replay was not requested in this run.'
fi
'''

MANIFEST_CHECK = '''from pathlib import Path
import hashlib
root=Path(__file__).resolve().parent
for line in (root/'MANIFEST.sha256').read_text().splitlines():
    digest,name=line.split('  ',1)
    p=root/name
    if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
        raise SystemExit('Integrity check failed: '+name)
print('All source and evidence hashes matched. This checks integrity, not mathematical correctness.')
'''

README = '''# Complete Lean formalization of z(20) = 6

The closed theorem `JSP000622.z_twenty_eq_six : Erdos758.z 20 = 6` and the direct upper-bound/sharpness theorem `JSP000622.JSP_000622` compiled successfully and passed exact transitive axiom auditing in GitHub Actions run 35174067645, at source commit `3773abab463d0c58d92bdf200d5397a826385988`. All eight audited declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This is the **twenty-vertex sub-question associated with Erdős 758 / JSP-000622**, not a formula for z(n) at every n. The theorem has no unproved classification, packing, or certificate hypotheses. Its generated finite evidence, universal reductions, and imported small-order lemmas are included in the checked dependency chain.

## Reproduce

Install Git, Python 3, and elan/Lake, then run:

```bash
bash verify.sh
```

For a fresh Lean-kernel replay of all imported constants as well:

```bash
bash verify.sh --fresh
```

Lean is pinned to `v4.33.0`; Mathlib and all direct/transitive dependency revisions are recorded in `lake-manifest.json`. The script fetches the separate small-order formalization at exactly `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, retaining its source headers. Internet access is needed to retrieve that source and toolchain/dependency packages. The supplied finite proof files need no SAT solver to compile. Optional regeneration tools are in `generators/`; those programs are not mathematical axioms.

## Evidence and attribution

`evidence/closed/` contains the actual closed theorem receipt, compiler logs, exact axiom output, and recorded finite-shard provenance. The closed-stage receipt explicitly does not claim a fresh replay; consult any separately supplied fresh-replay receipt for that additional check. Hashes establish file integrity, not proof correctness.

The mathematical two-core reduction and original core SAT certificates come from the credited `ipitchford/z20-cochromatic` candidate. The twelve-vertex upper bound, lower-bound inputs and Ramsey facts reuse the credited `plby/lean-proofs` development. See `STATEMENT_AND_PROVENANCE.md` for exact contributions, source revisions and trusted-boundary details.

This source package contains no cached `.olean` proof objects. A successful build or this package does not constitute independent human review, first-formalization priority, prize eligibility, an award decision, or a right to payment. Another public submission for the same twenty-vertex target is PR #332; no priority entitlement is asserted here.
'''


def prepare() -> None:
    receipt = ROOT/'closed-evidence'
    status = json.loads((receipt/'CLOSED_STATUS.json').read_text())
    if status.get('closed_theorem_compiled_and_axiom_audited') is not True:
        raise RuntimeError('No successful closed-theorem receipt')
    if status['source_commit'] != '3773abab463d0c58d92bdf200d5397a826385988':
        raise RuntimeError('Unexpected source snapshot')
    audit(receipt/'ClosedAudit.txt', EXPECTED)
    if PACKAGE.exists():
        raise RuntimeError('Refusing to overwrite an existing delivery package')
    PACKAGE.mkdir(parents=True)
    shutil.copytree(receipt/'project/JSP000622', PACKAGE/'JSP000622')
    shutil.copy2(ROOT/'Z20/standalone/lakefile.toml', PACKAGE/'lakefile.toml')
    manifest = ROOT/'.z20/project/lake-manifest.json'
    lock = json.loads(manifest.read_text())
    assert next(p['rev'] for p in lock['packages'] if p['name']=='mathlib') == 'db584cd6d46c92f209a44c0f1c829460d327499d'
    shutil.copy2(manifest, PACKAGE/'lake-manifest.json')
    (PACKAGE/'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
    (PACKAGE/'bootstrap.sh').write_text(BOOTSTRAP)
    (PACKAGE/'verify.sh').write_text(VERIFY)
    (PACKAGE/'verify_manifest.py').write_text(MANIFEST_CHECK)
    shutil.copy2(ROOT/'Z20/audit_axioms.py', PACKAGE/'audit_axioms.py')
    (PACKAGE/'Audit.lean').write_text('import JSP000622.Main\n'
        + ''.join(f'#print axioms {n}\n#check {n}\n' for n in EXPECTED)
        + '#print JSP000622.z_twenty_eq_six\n#print JSP000622.JSP_000622\n')
    evidence = PACKAGE/'evidence/closed'
    evidence.mkdir(parents=True)
    for p in receipt.iterdir():
        if p.is_file() and p.suffix in ('.json','.txt'):
            shutil.copy2(p,evidence/p.name)
    shutil.copy2(ROOT/'Z20/STATEMENT_AND_PROVENANCE.md', PACKAGE/'STATEMENT_AND_PROVENANCE.md')
    (PACKAGE/'README.md').write_text(README)
    gen = PACKAGE/'generators'
    gen.mkdir()
    for name in ['generate_classification.py','generate_classification_v2.py',
                 'generate_core_certificates.py','prepare_core_v2.py','generate_bridges.py',
                 'finish_generated.py','rup_to_lrat.cpp']:
        shutil.copy2(ROOT/'Z20'/name,gen/name)
    generation = ROOT/'complete-data/logs'
    if generation.is_dir():
        target = PACKAGE/'evidence/generation'
        target.mkdir(parents=True)
        for p in generation.iterdir():
            if p.is_file() and p.suffix == '.json':
                shutil.copy2(p,target/p.name)
    for path in [PACKAGE/'bootstrap.sh',PACKAGE/'verify.sh']:
        path.chmod(0o755)
    hashes=[]
    for p in sorted(PACKAGE.rglob('*')):
        if p.is_file():
            hashes.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(PACKAGE)))
    (PACKAGE/'MANIFEST.sha256').write_text('\n'.join(hashes)+'\n')
    print(json.dumps({'packaged_files':len(hashes)+1,'closed_proof_verified':True,
                      'fresh_replay_in_this_stage':False}),flush=True)


def archive() -> None:
    files=[]
    for p in sorted(PACKAGE.rglob('*')):
        if p.is_file() and not any(x in ('.lake','upstream','__pycache__') for x in p.relative_to(PACKAGE).parts):
            files.append(p)
    path=OUT/'JSP000622_z20_complete_source.zip'
    with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in files:
            z.write(p,str(p.relative_to(OUT)))
    with zipfile.ZipFile(path) as z:
        if z.testzip() is not None:
            raise RuntimeError('ZIP CRC check failed')
    report={'name':path.name,'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'files':len(files),'lean_sources':sum(p.suffix=='.lean' for p in files),
        'closed_build_source_commit':'3773abab463d0c58d92bdf200d5397a826385988',
        'package_commit':os.environ.get('GITHUB_SHA'),'prize_awarded':False}
    (OUT/'PACKAGE.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report),flush=True)

if __name__=='__main__':
    if len(sys.argv)!=2 or sys.argv[1] not in ('prepare','archive'):
        raise SystemExit('usage: package_proof.py prepare|archive')
    OUT.mkdir(exist_ok=True)
    if sys.argv[1]=='prepare': prepare()
    else: archive()
