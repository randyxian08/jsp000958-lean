#!/usr/bin/env bash
# Compile the upstream Randy 1153 proof and the three JSP adapters.
# Usage:  bash run.sh            (log written next to this script)
#         bash run.sh my.log     (custom log path)
set -euo pipefail

ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$ROOT"
LOG="${1:-$ROOT/JSP-verification.log}"

export PATH="$HOME/.elan/bin:$PATH"

if ! command -v lake >/dev/null 2>&1; then
  echo "lake not found. Install elan first:" >&2
  echo "  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y" >&2
  exit 1
fi

run() { echo "### $*"; "$@"; }

{
  echo "===== JSP-000936 / JSP-000937 / JSP-000958 verification ====="
  echo "date: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo

  echo "===== [1/6] toolchain ====="
  lake env lean --version
  echo

  echo "===== [2/6] mathlib cache ====="
  lake exe cache get
  echo

  echo "===== [3/6] build the upstream proof (26k lines) ====="
  lake build
  echo

  echo "===== [4/6] upstream audits ====="
  lake env lean AxiomAudit.lean
  lake env lean StatementAudit.lean
  echo

  echo "===== [5/6] JSP adapters ====="
  lake env lean jsp936/JSP000936.lean
  lake env lean jsp937/JSP000937.lean
  lake env lean jsp958/JSP000958.lean
  echo

  echo "===== [6/6] placeholder / axiom scan ====="
  if grep -R -n -E --include='*.lean' \
      '(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe|opaque)[[:space:]]' \
      Randy1153 Randy1153.lean AxiomAudit.lean StatementAudit.lean jsp936 jsp937 jsp958; then
    echo "Trust scan FAILED" >&2
    exit 1
  fi
  echo "placeholder scan clean"

  echo
  echo "===== ALL PASSED ====="
} 2>&1 | tee "$LOG"
