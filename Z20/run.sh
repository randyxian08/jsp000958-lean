#!/usr/bin/env bash
set -euo pipefail
project="$1"
logs="$2"
mkdir -p "$project/JSP000622" "$logs"
cp -a Z20/JSP000622/. "$project/JSP000622/"
cd "$project"
lake build JSP000622.CertificateKernel 2>&1 | tee "$logs/certificate-kernel.txt"
cat > KernelAudit.lean <<'EOF'
import JSP000622.CertificateKernel
#print axioms JSP000622.Certificate.twoFours_of_refutation
#check Finset.card_image_of_injective
#check Equiv.ofBijective
#check Fintype.bijective_iff_injective_and_card
#check Finset.exists_subset_card_eq
#check Fintype.exists_lt_card_fiber_of_mul_lt_card
#check List.nodup_iff_injective_get
#check SimpleGraph.Iso
#check SimpleGraph.isNClique_iff
#check SimpleGraph.isNIndepSet_iff
#check finSumFinEquiv
#check Fintype.bijective_iff_injective
#check Sat.Fmla.proof
EOF
lake env lean KernelAudit.lean 2>&1 | tee "$logs/kernel-audit.txt"
printf '%s\n' 'Scope: semantic bridge only. Full z(20)=6 not yet established.' | tee "$logs/SCOPE.txt"
