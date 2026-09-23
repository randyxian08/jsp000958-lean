# JSP-000958: Lean formalization of Erdős problem 1153

Author: [randyxian08](https://github.com/randyxian08).

This repository contains my Lean 4 formal proof that the Lebesgue function
of any interpolation node family has a logarithmic lower bound on every
fixed non-degenerate subinterval of `[-1,1]`.

For every `-1 ≤ a < b ≤ 1` and every `ε > 0`, there is `N ≥ 2` such that,
for every `n ≥ N` and every family of `n` distinct nodes in `[-1,1]`,

```text
max_{t ∈ [a,b]} ∑_k |ℓ_k(t)| > (2/π − ε) log n.
```

`N` is uniform over all node configurations. This is the original
`(2/π − o(1)) log n` lower bound, not the stronger additive `O(1)` remainder.

## Proof and correspondence

- Original problem: https://www.erdosproblems.com/1153
- Prize catalog: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0901-1000.md#JSP-000958
- Core proof: [Randy1153/Main.lean](Randy1153/Main.lean), `Randy1153.randy1153_main`.
- JSP entry: [jsp958/JSP000958.lean](jsp958/JSP000958.lean), `JSP000958.jsp_000958` and `JSP000958.jsp_000958_maximum`.
- Definitions and quantifiers: [Randy1153/Statement.lean](Randy1153/Statement.lean).
- [Statement correspondence](STATEMENT-CORRESPONDENCE.md), [executable statement audit](StatementAudit.lean), and [proof exposition](PROOF.md).

## Authorship and scope

I am the author of both the core Lean formalization and its JSP adapter.
The earlier author label “Ethan Yang” refers to me; my GitHub identity is
`randyxian08`. This is my public authorship clarification and consent to
attribute this formalization to that GitHub identity. It does not claim
new priority for the historical mathematical result or independent review.

The directory name `Randy1153` is a Lean namespace; the mathematical source
is Erdős problem 1153. The included JSP-000936 and JSP-000937 adapters only
prove restricted endpoint-fixed statements. They are not submitted here as
complete solutions of those original problems.

## Reproduce

Install elan and run:

```sh
bash run.sh
```

The project pins Lean 4.33.0 and Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`, including the exact
Mathlib revision in `lake-manifest.json`. The script builds the core proof,
checks the statement and axiom audits, compiles the JSP entry points, and
scans the project source for proof placeholders and added axioms. It also
replays the core final module with `leanchecker`.

The earlier 4.27.0 verification passed on 2026-09-16. It is historical
evidence, not a check of this upgraded snapshot. The reported dependencies of the
final theorems are `propext`, `Classical.choice`, and `Quot.sound`.
The upgraded snapshot has a separate [Lean 4.33.0 local verification record](evidence/lean433-local-verification.md).
Local checks reuse dependency/build artifacts and are not represented as
independent review. GitHub Actions provides a separate Linux reproduction;
its actual status must be read from the workflow run.

Submission to The Justin Sun Prize requests review of the formalization
and eligibility. It is not an announced award or confirmation of payment.
