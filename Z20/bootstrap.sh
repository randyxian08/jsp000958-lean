#!/usr/bin/env bash
set -euo pipefail
root="$(pwd)"
mkdir -p .z20 logs .z20/project
if [ ! -x .z20/lean/bin/lean ]; then
  curl --fail --location --retry 3 https://github.com/leanprover/lean4/releases/download/v4.33.0/lean-4.33.0-linux.tar.zst -o .z20/lean.tar.zst
  echo '4b3fb03c29a1e0a253fb1d11f9bae3725f19a0dc6fc09b3ea16d2c9df3349e2c  .z20/lean.tar.zst' | sha256sum --check
  tar --zstd -xf .z20/lean.tar.zst -C .z20
  mv .z20/lean-4.33.0-linux .z20/lean
  rm .z20/lean.tar.zst
fi
export PATH="$root/.z20/lean/bin:$PATH"
echo "$root/.z20/lean/bin" >> "$GITHUB_PATH"
lean --version | tee logs/lean-version.txt
cat > .z20/project/lakefile.toml <<'EOF'
name = "jsp000622"
version = "0.1.0"
[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "db584cd6d46c92f209a44c0f1c829460d327499d"
[[lean_lib]]
name = "JSP000622"
[[lean_lib]]
name = "ErdosProblems"
[[lean_lib]]
name = "Util"
EOF
printf '%s\n' leanprover/lean4:v4.33.0 > .z20/project/lean-toolchain
cd .z20/project
if [ ! -d .lake/packages/mathlib/.git ]; then
  mkdir -p .lake/packages/mathlib
  git -C .lake/packages/mathlib init
  git -C .lake/packages/mathlib remote add origin https://github.com/leanprover-community/mathlib4.git
  git -C .lake/packages/mathlib fetch --depth 1 origin db584cd6d46c92f209a44c0f1c829460d327499d
  git -C .lake/packages/mathlib checkout --detach FETCH_HEAD
fi
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update 2>&1 | tee ../../logs/lake-update.txt
lake exe cache get 2>&1 | tee ../../logs/mathlib-cache.txt
git -C .lake/packages/mathlib rev-parse HEAD | tee ../../logs/mathlib-pin.txt
df -h . | tee ../../logs/disk.txt
