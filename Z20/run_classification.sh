#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
mode="${1:?generate, kernel, replay, or join}"
out="$root/classification-output"
project="$root/.z20/project"
mkdir -p "$out"
export LEAN_NUM_THREADS=2
export PATH="$root/.z20/lean/bin:$PATH"
case "$mode" in
generate)
  python3 -m venv .classification-venv
  .classification-venv/bin/pip install networkx==3.4.2 python-sat==1.8.dev24
  .classification-venv/bin/pip freeze > "$out/python-packages.txt"
  g++ -O2 -std=c++17 -Wall -Wextra Z20/rup_to_lrat.cpp -o "$out/rup_to_lrat"
  mkdir -p "$out/project/JSP000622" "$out/logs"
  cp -a Z20/JSP000622/. "$out/project/JSP000622/"
  .classification-venv/bin/python Z20/generate_classification_v2.py "$out/project" "$out/logs" "$out/rup_to_lrat" 2>&1 | tee "$out/generation.txt"
  python3 - "$out/project" <<'PY'
from pathlib import Path
import sys
for p in (Path(sys.argv[1])/'JSP000622').rglob('Data.lean'):
    t=p.read_text()
    if '![' in t and 'import Mathlib.Data.Fin.VecNotation' not in t:
        p.write_text('import Mathlib.Data.Fin.VecNotation\n'+t)
PY
  cp -a Z20 "$out/source"
  ;;
kernel)
  mkdir -p "$project/JSP000622"
  cp -a Z20/JSP000622/. "$project/JSP000622/"
  cd "$project"
  lake build JSP000622.ExtensionKernel 2>&1 | tee "$out/kernel-build.txt"
  cat > ClassKernelAudit.lean <<'EOF'
import JSP000622.ExtensionKernel
#print axioms JSP000622.Certificate.twoFours_of_refutation
#print axioms JSP000622.Certificate.classified_of_refutation
#print axioms JSP000622.Certificate.classified_step
#print JSP000622.Certificate.classified_step
EOF
  lake env lean ClassKernelAudit.lean 2>&1 | tee "$out/kernel-audit.txt"
  python3 "$root/Z20/audit_axioms.py" "$out/kernel-audit.txt" JSP000622.Certificate.twoFours_of_refutation JSP000622.Certificate.classified_of_refutation JSP000622.Certificate.classified_step > "$out/kernel-axioms.json"
  ;;
replay)
  shard="${2:?shard number}"
  cp -a classification-data/project/JSP000622 "$project/"
  cp -a Z20/JSP000622/. "$project/JSP000622/"
  python3 - "$shard" "$out" <<'PY'
import json, sys
from pathlib import Path
shard, out = int(sys.argv[1]), Path(sys.argv[2])
report=json.loads(Path('classification-data/logs/classification-generation.json').read_text())
names=[x['name'] for x in report['cases']]
assert report['version']==2 and len(names)==76
(out/f'targets-{shard}.txt').write_text('\n'.join(names[shard::6])+'\n')
PY
  cd "$project"
  lake build JSP000622.ExtensionKernel 2>&1 | tee "$out/replay-$shard.txt"
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
Path('ClassificationAudit.lean').write_text(t)
(out/f'audit-names-{shard}.txt').write_text('\n'.join(f'JSP000622.{n}.classify' for n in names)+'\n')
PY
  lake env lean ClassificationAudit.lean 2>&1 | tee "$out/audit-$shard.txt"
  mapfile -t expected < "$out/audit-names-$shard.txt"
  python3 "$root/Z20/audit_axioms.py" "$out/audit-$shard.txt" "${expected[@]}" > "$out/axioms-$shard.json"
  tar --zstd -cf "$out/checked-classification-$shard.tar.zst" .lake/build
  sha256sum "$out/checked-classification-$shard.tar.zst" > "$out/checked-classification-$shard.sha256"
  ;;
join)
  cp -a classification-data/project/JSP000622 "$project/"
  cp -a Z20/JSP000622/. "$project/JSP000622/"
  cd "$project"
  count=0
  for p in "$root"/classification-parts/checked-classification-*.tar.zst; do
    tar --zstd -xf "$p"
    count=$((count+1))
  done
  test "$count" = 6
  lake build JSP000622.R34Nine 2>&1 | tee "$out/join-build.txt"
  lake build JSP000622.R34Seven JSP000622.R34Eight 2>&1 | tee -a "$out/join-build.txt"
  cat > CompleteCatalogAudit.lean <<'EOF'
import JSP000622.R34Seven
import JSP000622.R34Eight
import JSP000622.R34Nine
#print axioms JSP000622.R34Seven.complete
#print axioms JSP000622.R34Eight.complete
#print axioms JSP000622.R34Nine.complete
#print JSP000622.R34Nine.complete
EOF
  lake env lean CompleteCatalogAudit.lean 2>&1 | tee "$out/complete-catalog-audit.txt"
  python3 "$root/Z20/audit_axioms.py" "$out/complete-catalog-audit.txt" JSP000622.R34Seven.complete JSP000622.R34Eight.complete JSP000622.R34Nine.complete > "$out/complete-catalog-axioms.json"
  tar --zstd -cf "$out/checked-classification-full.tar.zst" .lake/build
  sha256sum "$out/checked-classification-full.tar.zst" > "$out/checked-classification-full.sha256"
  cp -a JSP000622 "$out/"
  printf '%s\n' 'Complete small catalogs and all normalized sixteen-vertex cases checked. Universal normalization is a separate theorem.' > "$out/SCOPE.txt"
  ;;
*) exit 2 ;;
esac
