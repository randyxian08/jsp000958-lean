#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "$0")"

echo "Building the complete proof..."
lake build

echo "Checking the final theorem directly..."
lake env lean Randy1153/Main.lean

echo "Compiling the statement correspondence audit..."
lake env lean StatementAudit.lean

echo "Scanning for proof placeholders and project-defined axioms..."
if grep -R -n -E \
  '(^|[^[:alnum:]_])(sorry|admit|sorryAx)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|unsafe|opaque)[[:space:]]' \
  Randy1153 Randy1153.lean StatementAudit.lean AxiomAudit.lean
then
  echo "Trust scan failed." >&2
  exit 1
fi

echo "Checking the independent import boundary..."
if grep -R -n -E '^import[[:space:]]+FormalConjectures' \
  Randy1153 Randy1153.lean StatementAudit.lean AxiomAudit.lean
then
  echo "The independent proof imports the benchmark repository." >&2
  exit 1
fi

echo "Printing the kernel axiom report..."
axiom_report="$(lake env lean AxiomAudit.lean 2>&1)"
printf '%s\n' "$axiom_report"

if grep -q 'sorryAx' <<<"$axiom_report"
then
  echo "Kernel audit found sorryAx." >&2
  exit 1
fi

expected_axioms="[propext, Classical.choice, Quot.sound]"
if ! grep -F -q "$expected_axioms" <<<"$axiom_report"
then
  echo "Kernel axiom surface differs from the expected list." >&2
  exit 1
fi

echo "Verification passed."
