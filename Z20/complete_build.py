#!/usr/bin/env python3
"""Reproduce finite certificates and verify the complete z(20)=6 import closure.

The generators are untrusted. Success requires actual Lean compilation and an
exact standard-axiom audit. The final stage also requests fresh kernel replay.
No credentials, dynamic remote commands or background request loop are used.
"""
from __future__ import annotations
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path.cwd()
PROJECT = ROOT / '.z20/project'
OUT = ROOT / 'complete-output'
PIN = 'db584cd6d46c92f209a44c0f1c829460d327499d'
ENV = dict(os.environ)
ENV['LEAN_NUM_THREADS'] = '2'
ENV['PATH'] = str(ROOT / '.z20/lean/bin') + os.pathsep + ENV.get('PATH', '')


def run(args: list[str], log: Path, timeout: int = 600, cwd: Path = PROJECT) -> dict:
    log.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    with log.open('w') as stream:
        p = subprocess.Popen(args, cwd=cwd, env=ENV, stdout=stream,
                             stderr=subprocess.STDOUT, start_new_session=True)
        try:
            p.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGTERM)
            try:
                p.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                p.wait()
            p.returncode = 124
            stream.write('\nCHECK_TIMEOUT: this command did not verify successfully.\n')
    result = {'command': args, 'returncode': p.returncode,
              'seconds': round(time.monotonic() - start, 2), 'log': log.name}
    print(json.dumps(result), flush=True)
    if p.returncode:
        lines = log.read_text(errors='replace').splitlines()
        blocks = [i for i, s in enumerate(lines) if s.startswith('error:') or 'unsolved goals' in s]
        if blocks:
            for i in blocks[:8]:
                print('\n'.join(lines[i:i+24]), flush=True)
        else:
            print('\n'.join(lines[-25:]), flush=True)
    return result


def verify_runtime() -> None:
    actual = subprocess.check_output(['git', '-C', str(PROJECT/'.lake/packages/mathlib'),
                                      'rev-parse', 'HEAD'], env=ENV, text=True).strip()
    if actual != PIN:
        raise RuntimeError(f'Mathlib pin mismatch: {actual}')
    version = subprocess.check_output(['lean', '--version'], env=ENV, text=True).strip()
    if 'version 4.33.0,' not in version:
        raise RuntimeError(f'Lean pin mismatch: {version}')
    (OUT/'runtime.json').write_text(json.dumps({'lean': version, 'mathlib': actual,
        'source_commit': os.environ.get('GITHUB_SHA')}, indent=2))


def generated_sources() -> None:
    source = ROOT/'complete-data/project/JSP000622'
    if not source.is_dir():
        raise FileNotFoundError(source)
    shutil.copytree(source, PROJECT/'JSP000622', dirs_exist_ok=True)
    # Analytic source may be repaired independently of the finite data snapshot.
    shutil.copytree(ROOT/'Z20/JSP000622', PROJECT/'JSP000622', dirs_exist_ok=True)
    from finish_generated import finish
    finish(PROJECT)


def archive_local(name: str) -> None:
    directories = ['.lake/build/lib/lean/JSP000622', '.lake/build/ir/JSP000622']
    present = [d for d in directories if (PROJECT/d).exists()]
    if present:
        subprocess.run(['tar', '--zstd', '-cf', str(OUT/name), *present], cwd=PROJECT,
                       env=ENV, check=True)


def audit_modules(modules: list[str], declarations: list[str], name: str) -> dict:
    from audit_axioms import audit
    path = PROJECT/f'{name}.lean'
    path.write_text(''.join(f'import {m}\n' for m in modules)
                    + ''.join(f'#print axioms {n}\n' for n in declarations)
                    + ''.join(f'#check {n}\n' for n in declarations))
    result = run(['lake', 'env', 'lean', str(path)], OUT/f'{name}.txt', timeout=600)
    if result['returncode']:
        return result
    try:
        result['axioms'] = audit(OUT/f'{name}.txt', declarations)
    except (ValueError, OSError) as e:
        result['returncode'] = 1
        result['audit_error'] = str(e)
    (OUT/f'{name}.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    return result


def generate() -> None:
    from generate_classification_v2 import main as classify
    from prepare_core_v2 import main as cores
    from generate_bridges import generate as bridges
    from finish_generated import finish
    project = OUT/'project'
    logs = OUT/'logs'
    logs.mkdir(parents=True, exist_ok=True)
    shutil.copytree(ROOT/'Z20/JSP000622', project/'JSP000622', dirs_exist_ok=True)
    converter = OUT/'rup_to_lrat'
    subprocess.run(['g++', '-O2', '-std=c++17', str(ROOT/'Z20/rup_to_lrat.cpp'),
                    '-o', str(converter)], check=True)
    classify(project, logs, converter)
    cores(project, logs)
    bridges(project, logs/'classification-generation.json')
    for p in (project/'JSP000622').rglob('Data.lean'):
        text = p.read_text()
        if '![' in text and 'import Mathlib.Data.Fin.VecNotation' not in text:
            p.write_text('import Mathlib.Data.Fin.VecNotation\n'+text)
    finish(project)
    shutil.copytree(ROOT/'Z20', OUT/'source', dirs_exist_ok=True)
    (OUT/'SOURCE_COMMIT').write_text(os.environ.get('GITHUB_SHA', 'local')+'\n')


def finite(shard: int) -> None:
    if not 0 <= shard < 8:
        raise ValueError('Finite shard must be between zero and seven')
    generated_sources()
    verify_runtime()
    report = json.loads((ROOT/'complete-data/logs/classification-generation.json').read_text())
    if report['version'] != 2 or len(report['cases']) != 76:
        raise ValueError('Incomplete generated classification inventory')
    if shard < 6:
        names = [c['name'] for c in report['cases']][shard::6]
        modules = ['JSP000622.'+n for n in names]
        declarations = [m+'.classify' for m in modules]
    else:
        core = shard-6
        modules = [f'JSP000622.Core{core}']
        declarations = [f'JSP000622.Core{core}.{n}' for n in ('refutation', 'formula_eq', 'packing')]
    results = []
    try:
        for module in modules:
            results.append(run(['lake', 'build', module], OUT/(module+'.txt'), timeout=900))
        if all(r['returncode'] == 0 for r in results):
            results.append(audit_modules(modules, declarations, f'AuditShard{shard}'))
    finally:
        status = {'shard': shard, 'source_commit': os.environ.get('GITHUB_SHA'),
                  'modules': modules, 'results': results,
                  'passed': bool(results) and len(results) == len(modules)+1 and
                            all(r['returncode'] == 0 for r in results)}
        (OUT/f'shard-{shard}.json').write_text(json.dumps(status, indent=2))
        archive_local(f'finite-{shard}.tar.zst')
    if not status['passed']:
        raise SystemExit(1)


def join() -> None:
    generated_sources()
    verify_runtime()
    parts = ROOT/'complete-parts'
    for i in range(8):
        manifests = list(parts.rglob(f'shard-{i}.json'))
        archives = list(parts.rglob(f'finite-{i}.tar.zst'))
        if len(manifests) != 1 or len(archives) != 1:
            raise RuntimeError(f'Missing or duplicated shard {i}')
        if not json.loads(manifests[0].read_text())['passed']:
            raise RuntimeError(f'Unverified finite shard {i}')
        subprocess.run(['tar', '--zstd', '-xf', str(archives[0])], cwd=PROJECT, check=True)
    results = []
    for module in ['JSP000622.R34Nine', 'JSP000622.FiniteEvidence', 'JSP000622.Main']:
        result = run(['lake', 'build', module], OUT/(module+'.txt'), timeout=1200)
        results.append(result)
        if result['returncode']:
            break
    proof_passed = all(r['returncode'] == 0 for r in results) and len(results) == 3
    if proof_passed:
        declarations = ['JSP000622.R34Seven.complete', 'JSP000622.R34Eight.complete',
            'JSP000622.FiniteEvidence.complete_sixteen', 'JSP000622.FiniteEvidence.packing_twenty',
            'JSP000622.z_twenty_eq_six', 'JSP000622.maximum_cochromatic_twenty_eq_six',
            'JSP000622.colorable_six_of_card_twenty', 'JSP000622.JSP_000622']
        result = audit_modules(['JSP000622.Main'], declarations, 'FinalAudit')
        results.append(result)
        proof_passed = result['returncode'] == 0
    fresh = None
    if proof_passed:
        # Replays all imported constants in a fresh kernel environment.
        fresh = run(['lake', 'env', 'leanchecker', '--fresh', 'JSP000622.Main'],
                    OUT/'fresh-kernel.txt', timeout=1800)
    status = {'source_commit': os.environ.get('GITHUB_SHA'), 'results': results,
              'closed_theorem_compiled_and_axiom_audited': proof_passed,
              'fresh_kernel_replay': fresh,
              'prize_awarded': False}
    (OUT/'FINAL_STATUS.json').write_text(json.dumps(status, indent=2))
    shutil.copytree(PROJECT/'JSP000622', OUT/'project/JSP000622', dirs_exist_ok=True)
    shutil.copytree(ROOT/'Z20', OUT/'source', dirs_exist_ok=True)
    archive_local('joined-local-build.tar.zst')
    print(json.dumps(status), flush=True)
    if not proof_passed or not fresh or fresh['returncode']:
        raise SystemExit(1)


if __name__ == '__main__':
    OUT.mkdir(parents=True, exist_ok=True)
    if len(sys.argv) < 2:
        raise SystemExit('usage: complete_build.py generate | finite SHARD | join')
    mode = sys.argv[1]
    if mode == 'generate':
        generate()
    elif mode == 'finite' and len(sys.argv) == 3:
        finite(int(sys.argv[2]))
    elif mode == 'join':
        join()
    else:
        raise SystemExit('Invalid stage')
