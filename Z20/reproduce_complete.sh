#!/usr/bin/env bash
# Run from any directory using: bash /path/to/repo/Z20/reproduce_complete.sh
# Requires git, Python 3 with venv, a C++17 compiler, and elan/lake.
# The compiler and Mathlib are pinned; no GitHub Actions cache is required.
set -euo pipefail
src="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
work="${Z20_WORKSPACE:-$src/standalone-work}"
mkdir -p "$work/logs" "$work/JSP000622" "$work/ErdosProblems"
work="$(cd "$work" && pwd)"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"
for command in git python3 lake; do
  command -v "$command" >/dev/null || { echo "Missing prerequisite: $command" >&2; exit 2; }
done
cxx="${CXX:-c++}"
command -v "$cxx" >/dev/null || { echo "Missing C++17 compiler: $cxx" >&2; exit 2; }
printf '%s\n' leanprover/lean4:v4.33.0 > "$work/lean-toolchain"
cp "$src/standalone/lakefile.toml" "$work/lakefile.toml"
cp -a "$src/JSP000622/." "$work/JSP000622/"
upstream="$work/upstream"
pin=8822f7ddef30fadbd92e1c6ab4ed897af356af5e
if [ ! -d "$upstream/.git" ]; then
  git init "$upstream"
  git -C "$upstream" remote add origin https://github.com/plby/lean-proofs.git
  git -C "$upstream" config core.sparseCheckout true
  printf '%s\n' /README.md /src/latest/lean-toolchain /src/latest/lake-manifest.json \
    /src/latest/ErdosProblems/Erdos758.lean /src/latest/ErdosProblems/Erdos758/ \
    /src/latest/Util/ > "$upstream/.git/info/sparse-checkout"
fi
git -C "$upstream" fetch --depth 1 --filter=blob:none origin "$pin"
git -C "$upstream" checkout --detach "$pin"
test "$(git -C "$upstream" rev-parse HEAD)" = "$pin"
printf '%s\n' "$pin" > "$work/logs/upstream-commit.txt"
cp "$upstream/src/latest/ErdosProblems/Erdos758.lean" "$work/ErdosProblems/"
cp -a "$upstream/src/latest/ErdosProblems/Erdos758" "$work/ErdosProblems/"
cp -a "$upstream/src/latest/Util" "$work/"
python3 -m venv "$work/.venv"
py="$work/.venv/bin/python"
"$py" -m pip install networkx==3.4.2 python-sat==1.8.dev24
"$py" -m pip freeze > "$work/logs/python-packages.txt"
"$cxx" -O2 -std=c++17 "$src/rup_to_lrat.cpp" -o "$work/rup_to_lrat"
"$py" "$src/generate_classification_v2.py" "$work" "$work/logs" "$work/rup_to_lrat" \
  2>&1 | tee "$work/logs/classification-generation.txt"
"$py" "$src/prepare_core_v2.py" "$work" "$work/logs" \
  2>&1 | tee "$work/logs/core-generation.txt"
"$py" "$src/generate_bridges.py" "$work" "$work/logs/classification-generation.json" \
  2>&1 | tee "$work/logs/bridge-generation.txt"
"$py" - "$work" <<'PY'
from pathlib import Path
import sys
for p in (Path(sys.argv[1])/'JSP000622').rglob('Data.lean'):
    text=p.read_text()
    if '![' in text and 'import Mathlib.Data.Fin.VecNotation' not in text:
        p.write_text('import Mathlib.Data.Fin.VecNotation\n'+text)
PY
"$py" "$src/finish_generated.py" "$work" > "$work/logs/source-layout.json"
cd "$work"
lake update 2>&1 | tee logs/lake-update.txt
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = db584cd6d46c92f209a44c0f1c829460d327499d
lake env lean --version | tee logs/lean-version.txt
lake exe cache get 2>&1 | tee logs/mathlib-cache.txt
lake build JSP000622.Main 2>&1 | tee logs/complete-build.txt
cat > ReproductionAudit.lean <<'EOF'
import JSP000622.Main
#print JSP000622.z_twenty_eq_six
#print JSP000622.JSP_000622
#print axioms JSP000622.FiniteEvidence.complete_sixteen
#print axioms JSP000622.FiniteEvidence.packing_twenty
#print axioms JSP000622.z_twenty_eq_six
#print axioms JSP000622.maximum_cochromatic_twenty_eq_six
#print axioms JSP000622.JSP_000622
EOF
lake env lean ReproductionAudit.lean 2>&1 | tee logs/axioms.txt
"$py" "$src/audit_axioms.py" logs/axioms.txt \
  JSP000622.FiniteEvidence.complete_sixteen JSP000622.FiniteEvidence.packing_twenty \
  JSP000622.z_twenty_eq_six JSP000622.maximum_cochromatic_twenty_eq_six \
  JSP000622.JSP_000622 | tee logs/axiom-audit.json
lake env leanchecker --fresh JSP000622.Main 2>&1 | tee logs/fresh-kernel.txt
printf '%s\n' 'Closed theorem compiled, exact axiom audit passed, and fresh kernel replay completed.' \
  | tee logs/VERIFIED.txt
# This message certifies only this script run; it does not claim a prize decision.
