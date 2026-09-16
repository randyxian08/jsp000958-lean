import Randy1153.Interpolation

/-!
# Compact-interval maximum conveniences

The frozen statement module already proves continuity, compact attainment,
and the strict-bound witness equivalence.  This file adds the order-theoretic
consequences and interpolation estimates that later proof modules consume.
-/

namespace Randy1153

open Polynomial

noncomputable section

/-- Every value on a nonempty closed interval is bounded by `lebesgueOn`. -/
lemma lebesgueFunction_le_lebesgueOn {n : ℕ} (nodes : NodeFamily n)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) :
    lebesgueFunction nodes t ≤ lebesgueOn nodes a b := by
  obtain ⟨u, hu, hsup, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [hsup]
  exact hmax t ht

/-- A compact interval supremum of the Lebesgue function is nonnegative. -/
lemma lebesgueOn_nonneg {n : ℕ} (nodes : NodeFamily n) {a b : ℝ}
    (hab : a ≤ b) : 0 ≤ lebesgueOn nodes a b := by
  exact (lebesgueFunction_nonneg nodes a).trans
    (lebesgueFunction_le_lebesgueOn nodes hab ⟨le_rfl, hab⟩)

/-- A universal upper bound on the interval bounds its compact supremum. -/
lemma lebesgueOn_le_iff {n : ℕ} (nodes : NodeFamily n) {a b C : ℝ}
    (hab : a ≤ b) :
    lebesgueOn nodes a b ≤ C ↔
      ∀ t ∈ Set.Icc a b, lebesgueFunction nodes t ≤ C := by
  constructor
  · intro h t ht
    exact (lebesgueFunction_le_lebesgueOn nodes hab ht).trans h
  · intro h
    obtain ⟨t, ht, hsup, _⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    rw [hsup]
    exact h t ht

/-- Enlarging a nonempty closed interval can only increase its Lebesgue
supremum. -/
lemma lebesgueOn_mono_Icc {n : ℕ} (nodes : NodeFamily n)
    {a b c d : ℝ} (hab : a ≤ b) (hca : c ≤ a) (hbd : b ≤ d) :
    lebesgueOn nodes a b ≤ lebesgueOn nodes c d := by
  obtain ⟨t, ht, hsup, _⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  rw [hsup]
  exact lebesgueFunction_le_lebesgueOn nodes (hca.trans (hab.trans hbd))
    ⟨hca.trans ht.1, ht.2.trans hbd⟩

/-- If an interpolation node lies in the interval, the interval supremum is
at least one. -/
lemma one_le_lebesgueOn_of_node_mem {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {a b : ℝ} (hab : a ≤ b) (hk : nodes.point k ∈ Set.Icc a b) :
    1 ≤ lebesgueOn nodes a b := by
  simpa only [lebesgueFunction_at_node] using
    lebesgueFunction_le_lebesgueOn nodes hab hk

/-- On the full source interval, every nonempty node family has Lebesgue
supremum at least one. -/
lemma one_le_lebesgueOn {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    1 ≤ lebesgueOn nodes (-1) 1 :=
  one_le_lebesgueOn_of_node_mem nodes k (by norm_num) (nodes.mem_Icc k)

/-- The finite nodal maximum is nonnegative. -/
lemma nodalMax_nonneg {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hn : 0 < n) : 0 ≤ nodalMax nodes p hn := by
  let k : Fin n := ⟨0, hn⟩
  exact (abs_nonneg (p.eval (nodes.point k))).trans
    (abs_eval_node_le_nodalMax nodes p hn k)

/-- The Lagrange inequality with a common nodal bound, uniformly over a
closed interval. -/
lemma abs_eval_le_mul_lebesgueOn {n : ℕ} (nodes : NodeFamily n)
    (p : ℝ[X]) (hp : p.degree < n) (M : ℝ) (hM0 : 0 ≤ M)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (hM : ∀ k : Fin n, |p.eval (nodes.point k)| ≤ M) :
    |p.eval t| ≤ M * lebesgueOn nodes a b := by
  exact (abs_eval_le_mul_lebesgueFunction nodes p hp M t hM).trans
    (mul_le_mul_of_nonneg_left
      (lebesgueFunction_le_lebesgueOn nodes hab ht) hM0)

/-- Conventional maximum-norm interpolation inequality, uniformly over a
closed interval. -/
lemma abs_eval_le_nodalMax_mul_lebesgueOn {n : ℕ}
    (nodes : NodeFamily n) (p : ℝ[X]) (hp : p.degree < n)
    (hn : 0 < n) {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) :
    |p.eval t| ≤ nodalMax nodes p hn * lebesgueOn nodes a b := by
  exact (abs_eval_le_nodalMax_mul_lebesgueFunction nodes p hp hn t).trans
    (mul_le_mul_of_nonneg_left
      (lebesgueFunction_le_lebesgueOn nodes hab ht)
      (nodalMax_nonneg nodes p hn))

end

end Randy1153
