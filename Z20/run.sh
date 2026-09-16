#!/usr/bin/env bash
set -euo pipefail
project="$1"
logs="$2"
mkdir -p "$project/JSP000622" "$logs"
cp -a Z20/JSP000622/. "$project/JSP000622/"
python3 Z20/generate_core_certificates.py "$project" "$logs" 2>&1 | tee "$logs/core-generation.txt"
python3 - "$project" <<'PY'
from pathlib import Path
import sys
for p in (Path(sys.argv[1])/'JSP000622').glob('Core[01].lean'):
    t = p.read_text()
    t = t.replace('(rules.map PairRule.clause).proof []', 'Sat.Fmla.proof (rules.map PairRule.clause) []')
    p.write_text(t)
PY
cd "$project"
lake build JSP000622.CertificateKernel 2>&1 | tee "$logs/certificate-kernel.txt"
cat > KernelAudit.lean <<'EOF'
import JSP000622.CertificateKernel
#print axioms JSP000622.Certificate.twoFours_of_refutation
#check Finite.surjective_of_injective
#check SimpleGraph.Iso
#check SimpleGraph.isNClique_iff
#check SimpleGraph.isNIndepSet_iff
#check finSumFinEquiv
#check Sat.Fmla.proof
EOF
lake env lean KernelAudit.lean > "$logs/kernel-audit.txt" 2>&1 || true
cat "$logs/kernel-audit.txt"
lake build JSP000622.Core0 JSP000622.Core1 2>&1 | tee "$logs/core-build.txt"
cat > CoreAudit.lean <<'EOF'
import JSP000622.Core0
import JSP000622.Core1
#print axioms JSP000622.Core0.packing
#print axioms JSP000622.Core1.packing
#print JSP000622.Core0.packing
#print JSP000622.Core1.packing
EOF
lake env lean CoreAudit.lean 2>&1 | tee "$logs/core-audit.txt"
if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' "$logs/core-audit.txt"; then
  echo 'Rejected: an inadmissible axiom was detected.' >&2
  exit 1
fi
printf '%s\n' 'Scope: two fixed-core graph theorems only. Full z(20)=6 still requires universal reduction and twelve-vertex input.' | tee "$logs/SCOPE.txt"
