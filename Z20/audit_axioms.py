#!/usr/bin/env python3
"""Check actual Lean '#print axioms' output, not source-level keyword guesses."""
from __future__ import annotations
import json
import re
import sys
from pathlib import Path

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def audit(path: Path, expected: list[str]) -> dict:
    text=path.read_text(encoding='utf-8-sig')
    found={}
    for name, names in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
        axioms={n.strip() for n in names.split(',') if n.strip()}
        if name in found and found[name]!=axioms:
            raise ValueError(f'Conflicting reports for {name}')
        found[name]=axioms
    for name in re.findall(r"'([^']+)' does not depend on any axioms",text):
        found[name]=set()
    missing=set(expected)-found.keys()
    if missing: raise ValueError(f'Missing actual Lean axiom output: {sorted(missing)}')
    bad={n:sorted(a-ALLOWED) for n,a in found.items() if a-ALLOWED}
    if bad: raise ValueError(f'Nonstandard axioms: {bad}')
    if re.search(r'\berror:',text): raise ValueError('Lean reported an error in the audit output')
    return {'status':'PASSED','allowed':sorted(ALLOWED),
            'expected_theorems':expected,'actual_axioms':{n:sorted(found[n]) for n in expected}}

if __name__=='__main__':
    if len(sys.argv)<3: raise SystemExit('usage: audit_axioms.py LOG_FILE THEOREM...')
    try: result=audit(Path(sys.argv[1]),sys.argv[2:])
    except (ValueError,OSError) as e:
        print('AXIOM_AUDIT_REJECTED:',e,file=sys.stderr); raise SystemExit(1)
    print(json.dumps(result,indent=2))
