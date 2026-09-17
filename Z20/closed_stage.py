#!/usr/bin/env python3
"""Explicit, separate receipts for a closed theorem build and fresh kernel replay.

A successful build-stage receipt never claims that the fresh replay ran.
A replay-stage receipt requires a previously successful closed-theorem audit.
"""
from __future__ import annotations
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from complete_build import ROOT, PROJECT, OUT, ENV, run, generated_sources, verify_runtime, archive_local, audit_modules


def build() -> None:
    generated_sources()
    verify_runtime()
    parts = ROOT/'complete-parts'
    provenance = []
    for i in range(8):
        manifests = list(parts.rglob(f'shard-{i}.json'))
        archives = list(parts.rglob(f'finite-{i}.tar.zst'))
        if len(manifests) != 1 or len(archives) != 1:
            raise RuntimeError(f'Missing or duplicated finite shard {i}')
        manifest = json.loads(manifests[0].read_text())
        if not manifest['passed']:
            raise RuntimeError(f'Finite shard {i} did not pass')
        provenance.append(manifest)
        subprocess.run(['tar', '--zstd', '-xf', str(archives[0])], cwd=PROJECT, check=True)
    checks = []
    for module in ('JSP000622.R34Nine', 'JSP000622.FiniteEvidence', 'JSP000622.Main'):
        result = run(['lake', 'build', module], OUT/(module+'.txt'), timeout=1200)
        checks.append(result)
        (OUT/'build-progress.json').write_text(json.dumps(checks, indent=2))
        if result['returncode']:
            break
    passed = len(checks) == 3 and all(x['returncode'] == 0 for x in checks)
    if passed:
        declarations = ['JSP000622.R34Seven.complete', 'JSP000622.R34Eight.complete',
            'JSP000622.FiniteEvidence.complete_sixteen', 'JSP000622.FiniteEvidence.packing_twenty',
            'JSP000622.z_twenty_eq_six', 'JSP000622.maximum_cochromatic_twenty_eq_six',
            'JSP000622.colorable_six_of_card_twenty', 'JSP000622.JSP_000622']
        result = audit_modules(['JSP000622.Main'], declarations, 'ClosedAudit')
        checks.append(result)
        passed = result['returncode'] == 0
    status = {'source_commit': os.environ.get('GITHUB_SHA'),
        'workflow_run_id': os.environ.get('GITHUB_RUN_ID'),
        'closed_theorem_compiled_and_axiom_audited': passed,
        'fresh_kernel_replay': None, 'fresh_replay_status': 'NOT_RUN_IN_THIS_STAGE',
        'checks': checks, 'finite_shard_provenance': provenance, 'prize_awarded': False}
    (OUT/'CLOSED_STATUS.json').write_text(json.dumps(status, indent=2))
    shutil.copytree(PROJECT/'JSP000622', OUT/'project/JSP000622', dirs_exist_ok=True)
    shutil.copytree(ROOT/'Z20', OUT/'source', dirs_exist_ok=True)
    archive_local('closed-build.tar.zst')
    print(json.dumps(status), flush=True)
    if not passed:
        raise SystemExit(1)


def fresh() -> None:
    source = ROOT/'closed-evidence'
    status = json.loads((source/'CLOSED_STATUS.json').read_text())
    if not status['closed_theorem_compiled_and_axiom_audited']:
        raise RuntimeError('Fresh replay requires a successful closed-theorem receipt')
    shutil.copytree(source/'project/JSP000622', PROJECT/'JSP000622', dirs_exist_ok=True)
    verify_runtime()
    subprocess.run(['tar', '--zstd', '-xf', str(source/'closed-build.tar.zst')], cwd=PROJECT, check=True)
    result = run(['lake', 'env', 'leanchecker', '--fresh', 'JSP000622.Main'],
                 OUT/'fresh-kernel.txt', timeout=1800)
    status['fresh_kernel_replay'] = result
    status['fresh_replay_status'] = 'PASSED' if result['returncode'] == 0 else 'FAILED'
    (OUT/'FINAL_STATUS.json').write_text(json.dumps(status, indent=2))
    print(json.dumps(status), flush=True)
    if result['returncode']:
        raise SystemExit(1)


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    if len(sys.argv) != 2 or sys.argv[1] not in ('build', 'fresh'):
        raise SystemExit('usage: closed_stage.py build|fresh')
    if sys.argv[1] == 'build':
        build()
    else:
        fresh()
