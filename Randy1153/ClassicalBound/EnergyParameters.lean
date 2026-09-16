import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Finite parameter selection for the sharp energy constant

The normalized energy coefficient tends to one when the geometric ratio
`q` tends down to one, the two integer divisors tend to infinity, and the
harmonic loss `eta` tends down to zero.  This file makes that selection
fully explicit, with no asymptotic or node-theoretic input.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- For every positive error, the four elementary losses in the energy
argument can be chosen so that the resulting coefficient is strictly above
`2 / pi - eps`.

The witnesses in the proof are `q = 1 + delta`, `eta = delta`, and equal
natural divisors larger than `delta⁻¹`, where
`delta = min (1/4) (eps*pi/12)`.
-/
theorem exists_energy_parameters (eps : ℝ) (heps : 0 < eps) :
    ∃ (q : ℝ) (R L : ℕ) (eta : ℝ),
      1 < q ∧ 1 ≤ R ∧ 1 < L ∧ 0 < eta ∧ eta < 1 ∧
      2 * ((1 - (R : ℝ)⁻¹) ^ 2 / (q * Real.pi)) *
          (1 - (L : ℝ)⁻¹) ^ 2 * (1 - eta) >
        2 / Real.pi - eps := by
  let delta : ℝ := min (1 / 4 : ℝ) (eps * Real.pi / 12)
  have hepspi : 0 < eps * Real.pi := mul_pos heps Real.pi_pos
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (by positivity)
  have hdelta_quarter : delta ≤ (1 / 4 : ℝ) := by
    exact min_le_left _ _
  have hdelta_budget : delta ≤ eps * Real.pi / 12 := by
    exact min_le_right _ _
  have hdelta_one : delta < 1 := hdelta_quarter.trans_lt (by norm_num)
  obtain ⟨M : ℕ, hM⟩ := exists_nat_gt delta⁻¹
  let N : ℕ := M + 2
  have hN : delta⁻¹ < (N : ℝ) := by
    dsimp [N]
    norm_num only [Nat.cast_add, Nat.cast_ofNat]
    linarith
  have hNpos : 0 < (N : ℝ) := by
    dsimp [N]
    positivity
  have hNone : 1 ≤ N := by
    dsimp [N]
    omega
  have hNtwo : 1 < N := by
    dsimp [N]
    omega
  let a : ℝ := (N : ℝ)⁻¹
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha_delta : a < delta := by
    dsimp [a]
    exact (inv_lt_comm₀ hdelta hNpos).1 hN
  have ha_quarter : a < (1 / 4 : ℝ) :=
    ha_delta.trans_le hdelta_quarter

  let A : ℝ := (1 - a) ^ 2
  let w : ℝ := 1 - 2 * delta
  let ratio : ℝ := (1 - delta) / (1 + delta)
  have hu : 0 ≤ 1 - 2 * a := by nlinarith
  have hw : 0 ≤ w := by
    dsimp [w]
    nlinarith
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have huA : 1 - 2 * a ≤ A := by
    dsimp [A]
    nlinarith [sq_nonneg a]
  have hratio : w ≤ ratio := by
    dsimp [w, ratio]
    apply (le_div_iff₀ (by linarith : 0 < 1 + delta)).2
    nlinarith [sq_nonneg delta]
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    exact div_nonneg (sub_nonneg.mpr hdelta_one.le)
      (by linarith : 0 ≤ 1 + delta)

  have hfirst :
      1 - 4 * a ≤ (1 - 2 * a) * (1 - 2 * a) := by
    nlinarith [sq_nonneg a]
  have hsecond :
      1 - 4 * a - 2 * delta ≤ (1 - 4 * a) * w := by
    dsimp [w]
    nlinarith [mul_nonneg ha.le hdelta.le]
  have hproduct_loss :
      1 - 4 * a - 2 * delta ≤
        (1 - 2 * a) * (1 - 2 * a) * w := by
    exact hsecond.trans (mul_le_mul_of_nonneg_right hfirst hw)
  have hsquares :
      (1 - 2 * a) * (1 - 2 * a) ≤ A * A := by
    calc
      (1 - 2 * a) * (1 - 2 * a) ≤ A * (1 - 2 * a) :=
        mul_le_mul_of_nonneg_right huA hu
      _ ≤ A * A := mul_le_mul_of_nonneg_left huA hA
  have hnormalized :
      1 - 4 * a - 2 * delta ≤ A * A * ratio := by
    calc
      1 - 4 * a - 2 * delta ≤
          (1 - 2 * a) * (1 - 2 * a) * w := hproduct_loss
      _ ≤ A * A * w := mul_le_mul_of_nonneg_right hsquares hw
      _ ≤ A * A * ratio :=
        mul_le_mul_of_nonneg_left hratio (mul_nonneg hA hA)
  have hloss : 4 * a + 2 * delta < eps * Real.pi / 2 := by
    have hsmall : 4 * a + 2 * delta < 6 * delta := by
      nlinarith
    have hbudget : 6 * delta ≤ eps * Real.pi / 2 := by
      nlinarith
    exact hsmall.trans_le hbudget
  have hnormalized_strict :
      1 - eps * Real.pi / 2 < A * A * ratio := by
    nlinarith

  refine ⟨1 + delta, N, N, delta, by linarith, hNone, hNtwo,
    hdelta, hdelta_one, ?_⟩
  have hexpression :
      2 * ((1 - ((N : ℝ))⁻¹) ^ 2 / ((1 + delta) * Real.pi)) *
          (1 - ((N : ℝ))⁻¹) ^ 2 * (1 - delta) =
        (2 / Real.pi) * (A * A * ratio) := by
    dsimp [A, a, ratio]
    have hdeltaDen : (1 + delta) ≠ 0 := by linarith
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp [hdeltaDen, hNne, Real.pi_ne_zero]
  rw [hexpression]
  have hcoefficient : 0 < 2 / Real.pi := div_pos (by norm_num) Real.pi_pos
  have hmul := mul_lt_mul_of_pos_left hnormalized_strict hcoefficient
  have hbaseline :
      (2 / Real.pi) * (1 - eps * Real.pi / 2) =
        2 / Real.pi - eps := by
    field_simp [Real.pi_ne_zero]
  rwa [hbaseline] at hmul

end

end ClassicalBound
end Randy1153
