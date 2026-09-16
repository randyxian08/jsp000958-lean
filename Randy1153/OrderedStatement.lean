import Randy1153.NodeOrder

/-!
# Ordered form of the public Randy 1153 statement

The proof architecture works with strictly increasing node families.  This
file records the exact ordered analogue of the frozen public `Target` and the
permutation-invariant transport back to arbitrary node enumerations.
-/

namespace Randy1153

noncomputable section

/-- The exact ordered analogue of `Target`.

The interval, epsilon, and threshold quantifiers are unchanged; only the
uniform node-family quantifier is restricted to the canonical internal type
`OrderedNodes`.
-/
def OrderedTarget : Prop :=
  ∀ a b : ℝ,
    -1 ≤ a → a < b → b ≤ 1 →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ nodes : OrderedNodes n,
          ∃ t ∈ Set.Icc a b,
            (2 / Real.pi - ε) * Real.log (n : ℝ) <
              lebesgueFunction nodes.toNodeFamily t

/-- Sorting transports the ordered statement to the frozen public target.

No quantitative loss occurs: sorting preserves the entire Lebesgue function
pointwise, and the threshold (including `2 ≤ N`) is reused verbatim.
-/
theorem target_of_orderedTarget (hordered : OrderedTarget) : Target := by
  intro a b ha hab hb ε hε
  obtain ⟨N, hN2, hN⟩ := hordered a b ha hab hb ε hε
  refine ⟨N, hN2, fun n hn nodes ↦ ?_⟩
  obtain ⟨t, ht, hlt⟩ := hN n hn nodes.sorted
  refine ⟨t, ht, ?_⟩
  rw [← nodes.lebesgueFunction_sorted t]
  exact hlt

end

end Randy1153
