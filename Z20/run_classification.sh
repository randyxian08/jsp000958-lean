#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
mode="${1:?generate, kernel, or replay}"
out="$root/classification-output"
mkdir -p "$out"
export LEAN_NUM_THREADS=2
case "$mode" in
generate)
  python3 -m venv .classification-venv
  .classification-venv/bin/pip install networkx==3.4.2 python-sat==1.8.dev24
  .classification-venv/bin/pip freeze > "$out/python-packages.txt"
  g++ -O2 -std=c++17 -Wall -Wextra Z20/rup_to_lrat.cpp -o "$out/rup_to_lrat"
  mkdir -p "$out/project/JSP000622" "$out/logs"
  cp -a Z20/JSP000622/. "$out/project/JSP000622/"
  .classification-venv/bin/python Z20/generate_classification.py "$out/project" "$out/logs" "$out/rup_to_lrat" 2>&1 | tee "$out/generation.txt"
  cp -a Z20 "$out/source"
  ;;
kernel)
  export PATH="$root/.z20/lean/bin:$PATH"
  project="$root/.z20/project"
  mkdir -p "$project/JSP000622"
  cp -a Z20/JSP000622/. "$project/JSP000622/"
  cd "$project"
  lake build JSP000622.ClassificationKernel 2>&1 | tee "$out/kernel-build.txt"
  cat > ClassKernelAudit.lean <<'EOF'
import JSP000622.ClassificationKernel
#print axioms JSP000622.Certificate.classified_of_refutation
#print JSP000622.Certificate.classified_of_refutation
EOF
  lake env lean ClassKernelAudit.lean 2>&1 | tee "$out/kernel-audit.txt"
  if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' "$out/kernel-audit.txt"; then exit 1; fi
  ;;
replay)
  export PATH="$root/.z20/lean/bin:$PATH"
  shard="${2:?shard number}"
  project="$root/.z20/project"
  cp -a classification-data/project/JSP000622 "$project/"
  python3 - "$shard" "$out" <<'PY'
import json, sys
from pathlib import Path
shard, out = int(sys.argv[1]), Path(sys.argv[2])
report=json.loads(Path('classification-data/logs/classification-generation.json').read_text())
names=[x['name'] for x in report['cases']]
assert len(names)==29
(out/f'targets-{shard}.txt').write_text('\n'.join(names[shard::6])+'\n')
PY
  cd "$project"
  lake build JSP000622.ClassificationKernel 2>&1 | tee "$out/replay-$shard.txt"
  while IFS= read -r name; do
    path="JSP000622/${name//./\/}"
    lake build "JSP000622.$name.Data" 2>&1 | tee -a "$out/replay-$shard.txt"
    for chunk in "$path"/Chunk*.lean; do
      target="${chunk%.lean}"; target="${target//\//.}"
      lake build "$target" 2>&1 | tee -a "$out/replay-$shard.txt"
    done
    lake build "JSP000622.$name" 2>&1 | tee -a "$out/replay-$shard.txt"
    printf '%s\n' "$name" >> "$out/checked-$shard.txt"
  done < "$out/targets-$shard.txt"
  python3 - "$out" "$shard" <<'PY'
from pathlib import Path
import sys
out, shard=Path(sys.argv[1]),sys.argv[2]
names=(out/f'checked-{shard}.txt').read_text().splitlines()
t=''.join(f'import JSP000622.{name}\n' for name in names)
t+=''.join(f'#print axioms JSP000622.{name}.classify\n' for name in names)
for name in names:
    if name in ('R34Seven','R34Eight'): t+=f'#print axioms JSP000622.{name}.complete\n'
Path('ClassificationAudit.lean').write_text(t)
PY
  lake env lean ClassificationAudit.lean 2>&1 | tee "$out/audit-$shard.txt"
  if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' "$out/audit-$shard.txt"; then exit 1; fi
  tar --zstd -cf "$out/checked-classification-$shard.tar.zst" .lake/build
  sha256sum "$out/checked-classification-$shard.tar.zst" > "$out/checked-classification-$shard.sha256"
  ;;
*) exit 2 ;;
esac
