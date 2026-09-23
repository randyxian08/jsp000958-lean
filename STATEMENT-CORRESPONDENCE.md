# Statement correspondence for Erdős problem 1153

This document makes the proposition-selection boundary independently
reviewable.  Unlike Erdős 825, problem 1153 did not have a public Google
DeepMind Formal Conjectures declaration to use as an externally accepted Lean
adapter when this proof was completed.  The table below therefore maps every
mathematically significant clause of the displayed problem to the precise Lean
surface used by this repository.

The formal statement lives in
[`Randy1153/Statement.lean`](Randy1153/Statement.lean).  The executable audit
[`StatementAudit.lean`](StatementAudit.lean) checks the named interfaces and
proves that its maximum formulation and the public witness formulation are
logically equivalent.  `./run.sh` compiles that audit on every run.

## Expanded proposition

The displayed problem is read as follows:

```text
for every a b with -1 <= a < b <= 1,
  for every real epsilon > 0,
    there is N >= 2 such that
      for every natural n >= N,
        for every injectively indexed family of n nodes in [-1,1],
          there is t in [a,b] such that
            (2 / pi - epsilon) * log n < lambda(t).
```

In symbols, the node-dependent functions are

```text
ell_k(t) = product over i != k of (t - x_i) / (x_k - x_i)
lambda(t) = sum over k of |ell_k(t)|.
```

The placement of `N` before the node family is essential: the threshold is
uniform over every configuration of `n` nodes.  It may depend on the fixed
interval and on `epsilon`.

## Clause-by-clause correspondence

| Problem clause | Lean encoding | Checked correspondence |
|---|---|---|
| `x_1, ..., x_n` | `NodeFamily n` has `point : Fin n -> Real` | `Fin n` has exactly `n` indices; this is not `n + 1` nodes. `NodeFamily.card_nodeFinset` also proves the underlying finite set has cardinality `n`. |
| Nodes are distinct | `NodeFamily.injective : Function.Injective point` | Distinctness makes every displayed denominator nonzero and matches the cardinal interpolation problem. |
| `x_i in [-1,1]` | `NodeFamily.mem_Icc : forall i, point i in Set.Icc (-1) 1` | `Set.Icc` includes both endpoints. No stronger hypothesis puts the nodes inside `[a,b]`. |
| Product over `i != k` | `lagrangeFundamental nodes k t := product i in univ.erase k, (t - point i) / (point k - point i)` | This is the literal finite product, with the source numerator and denominator in the same orientation. |
| The product is the Lagrange basis | `lagrangeBasis_eq_product` and `lagrangeBasis_eval` | These theorems connect Mathlib's polynomial basis to the literal displayed product after evaluation; the proof does not rely on a suggestive name. |
| `ell_k(x_k) = 1` | `lagrangeBasis_eval_self` plus `lagrangeBasis_eval` | `StatementAudit.lean` derives the corresponding fact directly for `lagrangeFundamental`. |
| `ell_k(x_i) = 0` for `i != k` | `lagrangeBasis_eval_of_ne` plus `lagrangeBasis_eval` | `StatementAudit.lean` derives the corresponding fact directly for `lagrangeFundamental`. |
| `lambda(t) = sum_k |ell_k(t)|` | `lebesgueFunction nodes t := sum k : Fin n, abs (lagrangeFundamental nodes k t)` | The absolute value is inside the finite sum, exactly as displayed. |
| “for any fixed `-1 <= a < b <= 1`” | The first binders of `Target` are `forall a b`, followed by `-1 <= a`, `a < b`, and `b <= 1` | The interval is closed, nondegenerate, and fixed before all asymptotic and node choices. Endpoints `a = -1` and `b = 1` are allowed. |
| `max` over `[a,b]` | The public target returns `exists t in Set.Icc a b`; `lebesgueOn` is the interval supremum | `continuous_lebesgueFunction` and compactness yield `exists_lebesgueOn_eq_and_ge`; `lt_lebesgueOn_iff` proves strict maximum-above-bound iff an explicit witness is above it. `StatementAudit.sourceMaximumTarget_iff_target` lifts this equivalence through every quantifier. |
| `(2/pi - o(1)) log n` | `forall epsilon > 0, exists N, forall n >= N, (2 / Real.pi - epsilon) * Real.log (n : Real) < ...` | This is the standard epsilon/eventual reading of a subtractive `o(1)` in the coefficient. It does not claim Tao's stronger additive `O(1)` remainder. |
| Uniformity over node choices | `N` is introduced before `forall n ... forall nodes : NodeFamily n` | A node-dependent threshold is not expressible by this binder order. |
| Natural logarithm | `Real.log (n : Real)` | The cardinality is explicitly coerced to a real and Mathlib's natural logarithm is used. |
| Strict `>` | Lean writes the same relation as `threshold < lebesgueFunction nodes t` | No weakening to `<=` or `>=` occurs. |
| Arbitrary node enumeration | The public theorem quantifies over every `NodeFamily n` | `NodeFamily.sorted`, `sortingPerm`, and `lebesgueFunction_sorted` justify the internal use of increasing nodes without restricting the public proposition. |
| Final affirmative answer | `Randy1153.randy1153_main : Randy1153.Target` | `Main.lean` proves the frozen target; `StatementAudit.statementAudit_final` rechecks the exact exported type. |

## Interpretive choices that Lean alone cannot certify

Kernel checking can prove that the implementation has the type written in
`Target`; it cannot prove that a human-language web page intended that type.
The following source judgments are therefore stated rather than hidden:

1. The displayed fractions require distinct nodes, and the resolving paper
   uses a strictly ordered list of distinct nodes.
2. The phrase “for any fixed” and the resolving theorem support a threshold
   uniform over all node configurations.  Consequently `N` precedes `nodes`.
3. Analytic `log` is read as the natural logarithm.
4. Requiring `N >= 2` is threshold hygiene, not extra asymptotic content: any
   valid eventual threshold can be enlarged to at least two.
5. The existential witness is used instead of putting a maximum operator in
   `Target`; the checked compactness equivalence proves that this changes no
   mathematical content.

These are the source-language judgments that cannot be reduced to kernel
checking. They are exposed directly here so that the public theorem can be
reviewed without relying on any development-history record.

## What the statement audit establishes

Running

```bash
lake env lean StatementAudit.lean
```

checks all declarations named in the table and proves:

- the literal fundamental product has the required cardinal values;
- the interval supremum is an attained maximum;
- the full maximum formulation is equivalent to `Target`; and
- the final theorem inhabits exactly `Target`.

This closes every correspondence that Lean can close internally.  It is not
presented as an external benchmark-statement certification: no such public
1153 formal statement was available to import.
