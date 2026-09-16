#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
export PATH="$root/.z20/lean/bin:$PATH"
export LEAN_NUM_THREADS=2
project="$root/.z20/project"
out="$root/foundation-output"
mkdir -p "$out"
mode="${1:?prepare, shard, or join}"
case "$mode" in
prepare)
  test -x .z20/lean/bin/lean
  lean --version | tee "$out/lean-version.txt"
  if [ ! -d .z20/upstream/.git ]; then
    git init .z20/upstream
    git -C .z20/upstream remote add origin https://github.com/plby/lean-proofs.git
    git -C .z20/upstream config core.sparseCheckout true
    printf '%s\n' /README.md /LICENSE /src/latest/lean-toolchain /src/latest/lake-manifest.json /src/latest/ErdosProblems/Erdos758.lean /src/latest/ErdosProblems/Erdos758/ /src/latest/Util/ > .z20/upstream/.git/info/sparse-checkout
    git -C .z20/upstream fetch --depth 1 --filter=blob:none origin 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
    git -C .z20/upstream checkout --detach FETCH_HEAD
  fi
  test "$(git -C .z20/upstream rev-parse HEAD)" = 8822f7ddef30fadbd92e1c6ab4ed897af356af5e
  mkdir -p "$project/ErdosProblems" "$project/JSP000622"
  cp -a .z20/upstream/src/latest/ErdosProblems/Erdos758.lean "$project/ErdosProblems/"
  cp -a .z20/upstream/src/latest/ErdosProblems/Erdos758 "$project/ErdosProblems/"
  cp -a .z20/upstream/src/latest/Util "$project/"
  cp -a Z20/JSP000622/. "$project/JSP000622/"
  git -C .z20/upstream rev-parse HEAD > "$out/upstream-commit.txt"
  git -C "$project/.lake/packages/mathlib" rev-parse HEAD > "$out/mathlib-commit.txt"
  ;;
shard)
  shard="${2:?shard number}"
  python3 - "$project" "$shard" "$out" <<'PY'
import json, sys
from pathlib import Path
project, shard, out = Path(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3])
base = project/'ErdosProblems/Erdos758/D12'
modules = [line.split()[1] for line in (base/'Certificates.lean').read_text().splitlines() if line.startswith('import ')]
assert len(modules) == len(set(modules))
weighted = []
for module in modules:
    name = module.split('.')[-1]
    weight = (base/'reduced'/f'{name}.lrat').stat().st_size
    weighted.append((weight,module))
bins, weights = [[] for _ in range(16)], [0]*16
for weight,module in sorted(weighted,reverse=True):
    i = min(range(16), key=lambda j: weights[j])
    bins[i].append(module); weights[i] += weight
(out/f'assignment-{shard}.json').write_text(json.dumps({'shard':shard,'all_cases':len(modules),'weights':weights,'modules':bins[shard]},indent=2))
(out/f'targets-{shard}.txt').write_text('\n'.join(bins[shard])+'\n')
PY
  cd "$project"
  while IFS= read -r target; do
    printf '%s\n' "$target" | tee -a "$out/build-$shard.txt"
    lake build "$target" 2>&1 | tee -a "$out/build-$shard.txt"
  done < "$out/targets-$shard.txt"
  tar --zstd -cf "$out/chunk-$shard.tar.zst" .lake/build
  sha256sum "$out/chunk-$shard.tar.zst" > "$out/chunk-$shard.sha256"
  ;;
join)
  cd "$project"
  count=0
  for part in "$root"/foundation-parts/chunk-*.tar.zst; do
    tar --zstd -xf "$part"
    count=$((count+1))
  done
  test "$count" = 16
  lake build ErdosProblems.Erdos758.SmallValues 2>&1 | tee "$out/small-values-build.txt"
  cat > FoundationAudit.lean <<'EOF'
import ErdosProblems.Erdos758.SmallValues
#print axioms Erdos758.small_values_exact
#print axioms Erdos758.small_values_sequence
#print axioms Erdos758.ramseyProperty_four_four_eighteen
#print Erdos758.small_values_exact
EOF
  lake env lean FoundationAudit.lean 2>&1 | tee "$out/foundation-audit.txt"
  if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' "$out/foundation-audit.txt"; then exit 1; fi
  tar --zstd -cf "$out/checked-auxiliary-build.tar.zst" .lake/build
  sha256sum "$out/checked-auxiliary-build.tar.zst" > "$out/checked-auxiliary-build.sha256"
  lake build JSP000622.Foundations 2>&1 | tee "$out/z20-foundations-build.txt"
  cat > Z20FoundationAudit.lean <<'EOF'
import JSP000622.Foundations
#print axioms JSP000622.z_twenty_ge_six
#print axioms JSP000622.z_twenty_eq_six_of_two_fours
#print JSP000622.z_twenty_eq_six_of_two_fours
EOF
  lake env lean Z20FoundationAudit.lean 2>&1 | tee "$out/z20-foundation-audit.txt"
  if grep -E 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler' "$out/z20-foundation-audit.txt"; then exit 1; fi
  printf '%s\n' 'Auxiliary result and conditional reduction only: the universal two-four-set obligation is NOT assumed solved.' > "$out/SCOPE.txt"
  ;;
*) exit 2 ;;
esac
