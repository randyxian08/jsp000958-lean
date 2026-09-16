#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
project="$1"
out="$2"
core="${3:?core number}"
[[ "$core" = 0 || "$core" = 1 ]]
export PATH="$root/.z20/lean/bin:$PATH"
export LEAN_NUM_THREADS=2
mkdir -p "$project/JSP000622" "$out/logs" "$out/project"
cp -a Z20/JSP000622/. "$project/JSP000622/"
trap 'cp -a "$project/JSP000622" "$out/project/"; cp -a "$root/Z20" "$out/source"' EXIT
python3 Z20/prepare_core_v2.py "$project" "$out/logs" 2>&1 | tee "$out/generation.txt"
cd "$project"
lean --version | tee "$out/lean-version.txt"
git -C .lake/packages/mathlib rev-parse HEAD | tee "$out/mathlib-pin.txt"
lake build JSP000622.CertificateKernel 2>&1 | tee "$out/kernel.txt"
lake build "JSP000622.Core$core.Refutation" 2>&1 | tee "$out/refutation.txt"
lake build "JSP000622.Core$core.Symbols" 2>&1 | tee "$out/symbols.txt"
for chunk in JSP000622/Core"$core"/Chunk*.lean; do
  target="${chunk%.lean}"; target="${target//\//.}"
  lake build "$target" 2>&1 | tee -a "$out/clauses.txt"
done
lake build "JSP000622.Core$core.Rules" 2>&1 | tee "$out/rules.txt"
lake build "JSP000622.Core$core" 2>&1 | tee "$out/graph-theorem.txt"
cat > CoreAudit.lean <<EOF
import JSP000622.Core$core
#print axioms JSP000622.Core$core.refutation
#print axioms JSP000622.Core$core.formula_eq
#print axioms JSP000622.Core$core.packing
#print JSP000622.Core$core.packing
EOF
lake env lean CoreAudit.lean 2>&1 | tee "$out/axioms.txt"
python3 "$root/Z20/audit_axioms.py" "$out/axioms.txt" \
  "JSP000622.Core$core.refutation" "JSP000622.Core$core.formula_eq" "JSP000622.Core$core.packing" \
  | tee "$out/axiom-audit.json"
tar --zstd -cf "$out/checked-core-$core.tar.zst" .lake/build
sha256sum "$out/checked-core-$core.tar.zst" > "$out/checked-core-$core.sha256"
printf '%s\n' 'Verified scope: one fixed-core graph packing theorem. Universal twenty-vertex normalization remains a separate obligation.' > "$out/SCOPE.txt"
