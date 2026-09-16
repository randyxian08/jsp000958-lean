# JSP-000958 — Lean formalization

Author: [randyxian08](https://github.com/randyxian08).

I completed the Lean 4 formalization of the following statement of
[Erdős problem 1153](https://www.erdosproblems.com/1153), catalogued as
JSP-000958: for every fixed non-degenerate interval `[a,b]` contained in
`[-1,1]` and every `ε > 0`, there is a threshold `N` such that, for every
`n ≥ N` and every family of `n` distinct interpolation nodes in `[-1,1]`,
the maximum of the Lebesgue function on `[a,b]` is greater than
`(2/π − ε) log n`.

The threshold is uniform over all node configurations. This is the
epsilon formulation of the coefficient `2/π − o(1)`; it does not assert
the stronger additive `O(1)` remainder.

## Authorship

The core formal proof in `Randy1153` and the JSP entry point are my own
development. The earlier attribution “Ethan Yang” refers to me; I now use
my GitHub identity `randyxian08`. This identity clarification is supplied
by the author. The fact that the JSP entry point imports the core proof
does not make it a different person's formalization.

This is an authorship statement about the Lean formalization, not a claim
to have originated the historical mathematical problem or every
mathematical result used in the proof.

## Proof and verification

- Core theorem: `Randy1153.randy1153_main : Randy1153.Target`.
- JSP theorem: `JSP000958.jsp_000958`.
- Equivalent maximum formulation: `JSP000958.jsp_000958_maximum`.
- Toolchain: Lean 4.27.0, Mathlib v4.27.0.
- Reproduction: run `bash run.sh` from the project root.

The complete project verification passed on 2026-09-16. The reported
axiom dependencies of the JSP theorems were `propext`, `Classical.choice`
and `Quot.sound`. Statement correspondence is documented in
`../STATEMENT-CORRESPONDENCE.md` and checked by `../StatementAudit.lean`.

This statement concerns JSP-000958 only. The included JSP-000936 and
JSP-000937 adapters prove restricted endpoint-fixed results and are not
presented here as complete solutions of those original problems.
