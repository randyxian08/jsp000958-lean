import Randy1153.Main

/-!
# JSP-000958 — logarithmic lower bound on every fixed subinterval

JSP-000958 (Erdős–Turán 1961; Erdős Problem **1153**) asks: for every choice of
interpolation nodes, must the error amplification on each fixed subinterval
grow at least logarithmically?

The frozen statement, `Randy1153.Target`, is: for every fixed non-degenerate
`[a,b] ⊆ [-1,1]` and every `ε > 0`, one threshold `N` works simultaneously for
every sufficiently large cardinality `n` and every choice of distinct nodes,

  `(2/π − ε) log n < max_{t ∈ [a,b]} Σ_k |ℓ_k(t)|`.

The author's core theorem `Randy1153.randy1153_main : Target` proves exactly this.
This file re-exports it under a JSP name and records the equivalent form with
the interval maximum written as the explicit `lebesgueOn` supremum.
AUTHORSHIP AND SCOPE:

* Lean formalization author: **randyxian08** (GitHub).
  The author has clarified that the earlier attribution "Ethan Yang" and
  the current GitHub identity refer to the same person. The core proof and
  this JSP entry point belong to the same author's development.
* The complete formal proof is in `Randy1153`; this file exposes that proof
  under its JSP identifier. The short adapter is not the whole proof.
* `jsp_000958_maximum` converts the pointwise witness in `Target` to the
  interval-maximum formulation using `lt_lebesgueOn_iff`.
* This attribution concerns the Lean formalization, not priority for the
  historical mathematical problem or all mathematical results it uses.
* Run `run.sh` to check the proof, statement correspondence and axiom audit.
-/

namespace JSP000958

open Randy1153

/-- The author's core result, re-exported under its JSP identifier. -/
theorem jsp_000958 : Randy1153.Target :=
  Randy1153.randy1153_main

/-- The same result with the interval maximum written explicitly.
The threshold `N` is chosen BEFORE `n` and BEFORE the node family. -/
theorem jsp_000958_maximum :
    ∀ a b : ℝ,
      -1 ≤ a → a < b → b ≤ 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, 2 ≤ N ∧
          ∀ n : ℕ, N ≤ n → ∀ nodes : Randy1153.NodeFamily n,
            (2 / Real.pi - ε) * Real.log (n : ℝ) <
              Randy1153.lebesgueOn nodes a b := by
  intro a b ha hab hb ε hε
  obtain ⟨N, hN, hproof⟩ := jsp_000958 a b ha hab hb ε hε
  refine ⟨N, hN, ?_⟩
  intro n hn nodes
  exact (Randy1153.lt_lebesgueOn_iff nodes hab.le).mpr
    (hproof n hn nodes)

end JSP000958

#print axioms JSP000958.jsp_000958
#print axioms JSP000958.jsp_000958_maximum
