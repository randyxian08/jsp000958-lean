#!/usr/bin/env python3
"""Untrusted layout transform for independently kernel-checked proof modules."""
from pathlib import Path
import sys
from generate_core_certificates import generate, read_cnf, lean_list, literal


def main(project: Path, logs: Path):
    generate(project, logs)
    for core in range(2):
        ns = f'JSP000622.Core{core}'
        directory = project / 'JSP000622' / f'Core{core}'
        symbols = directory/'Symbols.lean'
        symbols.write_text('import Mathlib.Data.Fin.VecNotation\n'+symbols.read_text())
        parent = project/'JSP000622'/f'Core{core}.lean'
        old = parent.read_text()
        prefix = old.split('theorem unsat :', 1)[0]
        (directory/'Rules.lean').write_text(prefix+f'end {ns}\n')
        _, clauses = read_cnf((directory/'core.cnf').read_bytes())
        text = 'import JSP000622.CertificateKernel\n'
        text += f'namespace {ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
        text += 'def formula : Sat.Fmla := [\n'
        text += ',\n'.join('  '+lean_list([literal(l) for l in c]) for c in clauses)+'\n]\n'
        text += 'theorem refutation : Sat.Fmla.proof formula [] :=\n'
        text += '  checked_from_lrat (include_str "core.cnf") (include_str "core.lrat")\n'
        text += f'#print axioms refutation\nend {ns}\n'
        (directory/'Refutation.lean').write_text(text)
        text = f'import JSP000622.Core{core}.Rules\nimport JSP000622.Core{core}.Refutation\n'
        text += f'namespace {ns}\nopen JSP000622.Certificate\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
        text += 'theorem formula_eq : rules.map PairRule.clause = formula := by decide\n'
        text += 'theorem unsat : Sat.Fmla.proof (rules.map PairRule.clause) [] := by\n'
        text += '  rw [formula_eq]\n  exact refutation\n'
        text += 'theorem packing (G : SimpleGraph (Fin 20)) (v : Sat.Valuation)\n'
        text += '    (h : Realizes G symbols v) : TwoFours G :=\n'
        text += '  twoFours_of_refutation symbols rules valid unsat G v h\n'
        text += '#print axioms packing\n#print axioms formula_eq\n'
        text += f'end {ns}\n'
        parent.write_text(text)

if __name__ == '__main__':
    if len(sys.argv)!=3: raise SystemExit('usage: prepare_core_v2.py PROJECT LOGS')
    main(Path(sys.argv[1]),Path(sys.argv[2]))
