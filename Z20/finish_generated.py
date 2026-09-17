#!/usr/bin/env python3
"""Finish generated Lean source layout. This is not a proof checker.

All mathematical claims remain Lean declarations to be checked by the kernel.
The transformation preserves rule order, changes only append association and
its validity proof, and closes the empty-tail membership simplification.
It is idempotent and records exactly which source files it changed.
"""
from __future__ import annotations
import json
import re
import sys
from pathlib import Path

RULES = re.compile(r'^def rules : (List \((?:ClassRule|PairRule) \d+\)) := ([^\n]+)$', re.M)
VALID = re.compile(r'^(theorem valid : [^\n]+?) :=(?: by)?\n.*?(?=^theorem |^end )', re.M | re.S)


def balanced(names: list[str]) -> tuple[str, str]:
    if not names:
        raise ValueError('A certificate must have at least one nonempty rule chunk')
    if len(names) == 1:
        return names[0], names[0] + '_valid'
    i = len(names) // 2
    left, left_proof = balanced(names[:i])
    right, right_proof = balanced(names[i:])
    return f'({left} ++ {right})', f'(valid_append {left_proof} {right_proof})'


def finish(project: Path) -> list[str]:
    base = project / 'JSP000622'
    if not base.is_dir():
        raise FileNotFoundError(base)
    changed = []
    for p in sorted(base.rglob('*.lean')):
        original = p.read_text()
        text = original.replace('List.mem_cons, List.mem_singleton',
                                'List.mem_cons, List.not_mem_nil, or_false')
        # Sat.Fmla and Sat.Clause are semireducible definitions, not abbreviations.
        # Keep the representation explicit so ordinary list DecidableEq applies.
        text = text.replace('def formula : Sat.Fmla :=',
                            'def formula : List (List Sat.Literal) :=')
        text = text.replace('  rw [formula_eq]\n  exact refutation',
            '  exact Eq.mp\n'
            '    (congrArg (fun f : List (List Sat.Literal) => Sat.Fmla.proof f [])\n'
            '      formula_eq.symm) refutation')
        match = RULES.search(text)
        if match:
            names = re.findall(r'\brules\d+\b', match.group(2))
            if len(names) != len(set(names)):
                raise ValueError(f'Duplicate chunk name in {p}')
            expr, proof = balanced(names)
            text = RULES.sub(lambda m: f'def rules : {m.group(1)} := {expr}', text, count=1)
            if len(VALID.findall(text)) != 1:
                raise ValueError(f'Expected one validity theorem in {p}')
            text = VALID.sub(lambda m: f'{m.group(1)} :=\n  {proof}\n', text, count=1)
            if 'import JSP000622.ListEvidence\n' not in text:
                text = 'import JSP000622.ListEvidence\n' + text
        if text != original:
            p.write_text(text)
            changed.append(str(p.relative_to(project)))
    print(json.dumps({'source_layout_updates': len(changed), 'files': changed,
                      'proof_status': 'REQUIRES_LEAN_CHECK'}, indent=2), flush=True)
    return changed

if __name__ == '__main__':
    if len(sys.argv) != 2:
        raise SystemExit('usage: finish_generated.py PROJECT')
    finish(Path(sys.argv[1]))
