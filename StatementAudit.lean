import Randy1153.Main
import Randy1153.NodeOrder

/-!
# Executable audit of the Randy 1153 statement boundary

This file makes the mechanically checkable claims in
`STATEMENT-CORRESPONDENCE.md` part of the verifier.  It does not replace the
source-reading judgment recorded there.
-/

namespace Randy1153

noncomputable section

#check NodeFamily
#check NodeFamily.card_nodeFinset
#check lagrangeFundamental
#check lagrangeBasis_eq_product
#check lagrangeBasis_eval
#check lebesgueFunction
#check continuous_lebesgueFunction
#check exists_lebesgueOn_eq_and_ge
#check lt_lebesgueOn_iff
#check NodeFamily.sorted
#check NodeFamily.lebesgueFunction_sorted
#check Target
#check randy1153_main

/-- The literal fundamental product is one at its own node. -/
example {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeFundamental nodes k (nodes.point k) = 1 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_self nodes k

/-- The literal fundamental product vanishes at every other node. -/
example {n : ℕ} (nodes : NodeFamily n) {j k : Fin n} (hjk : j ≠ k) :
    lagrangeFundamental nodes k (nodes.point j) = 0 := by
  rw [← lagrangeBasis_eval]
  exact lagrangeBasis_eval_of_ne nodes hjk

/-- A formulation using the maximum value on `[a,b]`, matching the displayed
`max` in the source problem.  `lebesgueOn` is proved to be attained below. -/
def SourceMaximumTarget : Prop :=
  ∀ a b : ℝ,
    -1 ≤ a → a < b → b ≤ 1 →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
          (2 / Real.pi - ε) * Real.log (n : ℝ) < lebesgueOn nodes a b

/-- The source-style maximum formulation is exactly equivalent to the public
explicit-witness target, including all outer quantifiers and their order. -/
theorem sourceMaximumTarget_iff_target : SourceMaximumTarget ↔ Target := by
  constructor
  · intro h a b ha hab hb ε hε
    obtain ⟨N, hN, hEventual⟩ := h a b ha hab hb ε hε
    refine ⟨N, hN, ?_⟩
    intro n hn nodes
    exact (lt_lebesgueOn_iff nodes hab.le).mp (hEventual n hn nodes)
  · intro h a b ha hab hb ε hε
    obtain ⟨N, hN, hEventual⟩ := h a b ha hab hb ε hε
    refine ⟨N, hN, ?_⟩
    intro n hn nodes
    exact (lt_lebesgueOn_iff nodes hab.le).mpr (hEventual n hn nodes)

/-- The exported proof inhabits exactly the frozen public proposition. -/
theorem statementAudit_final : Target :=
  randy1153_main

#print axioms sourceMaximumTarget_iff_target
#print axioms statementAudit_final

end

end Randy1153
