import Randy1153.ClassicalBound.Mesoscopic
import Randy1153.GapPolynomial

/-!
# Checked reductions for the sharp classical full-interval bound

This file proves all asymptotic bookkeeping needed after a genuine classical
finite estimate is available.  In particular, a uniform additive-constant
bound with leading coefficient `2 / π` implies the exact epsilon/eventual
Phase 4 statement.

It does **not** manufacture that finite estimate: the remaining input is
displayed explicitly either as a uniform additive bound, a harmonic
polynomial certificate, or a lower bound for one of the checked gap
polynomials.
-/

namespace Randy1153
namespace ClassicalBound

open Filter Polynomial

noncomputable section

/-- Natural logarithms of natural numbers tend to infinity. -/
lemma tendsto_log_nat_atTop :
    Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- A fixed additive loss is eventually smaller than `ε log n`. -/
lemma eventually_const_lt_epsilon_mul_log_nat (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, C < ε * Real.log (n : ℝ) := by
  filter_upwards [(tendsto_log_nat_atTop.eventually_gt_atTop (C / ε))] with n hn
  have := (div_lt_iff₀ hε).mp hn
  nlinarith

/-- The honest finite `2/π log n - C` estimate implies the exact uniform
epsilon/eventual statement. -/
theorem fullIntervalEventual_of_uniform_additive_bound
    (C : ℝ) (N₀ : ℕ)
    (hclassical : ∀ n : ℕ, N₀ ≤ n → ∀ nodes : NodeFamily n,
      (2 / Real.pi) * Real.log (n : ℝ) - C ≤
        lebesgueOn nodes (-1) 1) :
    FullIntervalEventual := by
  intro ε hε
  have heventual := eventually_const_lt_epsilon_mul_log_nat C ε hε
  rw [Filter.eventually_atTop] at heventual
  obtain ⟨N₁, hN₁⟩ := heventual
  refine ⟨max N₀ N₁, fun n hn nodes ↦ ?_⟩
  have hn₀ : N₀ ≤ n := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans hn
  unfold FullIntervalAt
  calc
    (2 / Real.pi - ε) * Real.log (n : ℝ) <
        (2 / Real.pi) * Real.log (n : ℝ) - C := by
      have hloss := hN₁ n hn₁
      nlinarith
    _ ≤ lebesgueOn nodes (-1) 1 := hclassical n hn₀ nodes

/-- A uniform harmonic-size polynomial certificate implies the complete
sharp classical epsilon/eventual bound.  The only analytic estimate used in
the reduction is `log n ≤ H_(n-1)`.
-/
theorem fullIntervalEventual_of_uniform_harmonic_certificates
    (C : ℝ) (N₀ : ℕ)
    (hcert : ∀ n : ℕ, N₀ ≤ n → 1 ≤ n → ∀ nodes : NodeFamily n,
      HarmonicCertificate nodes C) :
    FullIntervalEventual := by
  apply fullIntervalEventual_of_uniform_additive_bound C (max N₀ 1)
  intro n hn nodes
  have hn₀ : N₀ ≤ n := (le_max_left N₀ 1).trans hn
  have hnpos : 1 ≤ n := (le_max_right N₀ 1).trans hn
  have hpi : 0 ≤ 2 / Real.pi := (div_pos two_pos Real.pi_pos).le
  calc
    (2 / Real.pi) * Real.log (n : ℝ) - C ≤
        (2 / Real.pi) * realHarmonic (n - 1) - C := by
      exact sub_le_sub_right
        (mul_le_mul_of_nonneg_left (log_nat_le_realHarmonic_pred hnpos) hpi) C
    _ ≤ lebesgueOn nodes (-1) 1 :=
      (lt_lebesgueOn_of_polynomialCertificate (hcert n hn₀ hnpos nodes)).le

/-- A strict lower bound for one ordered nodal gap is also a strict lower
bound for the full-interval Lebesgue constant. -/
lemma lt_lebesgueOn_of_lt_gapHeight {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {A : ℝ} (hA : A < gapHeight nodes g) :
    A < lebesgueOn nodes.toNodeFamily (-1) 1 := by
  obtain ⟨t, htgap, hheight, _⟩ :=
    exists_gapHeight_eq_eval_gapPolynomial nodes g
  apply (lt_lebesgueOn_iff nodes.toNodeFamily (by norm_num)).2
  have htfull : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · exact (nodes.neg_one_le (gapLeftIndex g)).trans htgap.1
    · exact htgap.2.trans (nodes.le_one (gapRightIndex g))
  refine ⟨t, htfull, ?_⟩
  rw [lebesgueFunction_eq_eval_gapPolynomial nodes g htgap]
  rwa [hheight] at hA

/-- It is enough to prove a harmonic lower bound on one gap of the sorted
node family.  This is the most concrete checked interface for an independent
Randy--Turán/Randy mesoscopic argument.
-/
theorem fullIntervalEventual_of_uniform_harmonic_gap_bound
    (C : ℝ) (N₀ : ℕ)
    (hgap : ∀ n : ℕ, N₀ ≤ n → 2 ≤ n → ∀ nodes : NodeFamily n,
      ∃ g : Fin (n - 1),
        (2 / Real.pi) * realHarmonic (n - 1) - C <
          gapHeight nodes.sorted g) :
    FullIntervalEventual := by
  apply fullIntervalEventual_of_uniform_additive_bound C (max N₀ 2)
  intro n hn nodes
  have hn₀ : N₀ ≤ n := (le_max_left N₀ 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N₀ 2).trans hn
  obtain ⟨g, hg⟩ := hgap n hn₀ hn2 nodes
  have hpi : 0 ≤ 2 / Real.pi := (div_pos two_pos Real.pi_pos).le
  have hnpos : 1 ≤ n := by omega
  have hlogharm :
      (2 / Real.pi) * Real.log (n : ℝ) - C ≤
        (2 / Real.pi) * realHarmonic (n - 1) - C := by
    exact sub_le_sub_right
      (mul_le_mul_of_nonneg_left
        (log_nat_le_realHarmonic_pred hnpos) hpi) C
  rw [← nodes.lebesgueOn_sorted (-1) 1]
  exact hlogharm.trans (lt_lebesgueOn_of_lt_gapHeight nodes.sorted g hg).le

end

end ClassicalBound
end Randy1153
