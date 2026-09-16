import Randy1153.ClassicalBound.EnergyGeometry
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Truncated energy inside a dense bin

This file extracts the exact finite harmonic gain from the fixed-step
geometry.  For a truncation level R < m, every retained step satisfies

    m - r ≥ m - R,

so the fixed-step kernels sum to at least (m-R)^2 H_R.  The final section
specializes this statement to R = m / L, retaining all floor loss.

No geometric partition or asymptotic estimate is asserted here.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Expand the existing real-valued harmonic number as a one-based real
finite sum. -/
lemma realHarmonic_eq_sum_Icc (R : ℕ) :
    realHarmonic R = ∑ r ∈ Finset.Icc 1 R, (r : ℝ)⁻¹ := by
  rw [realHarmonic, harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

lemma realHarmonic_nonneg (R : ℕ) :
    0 ≤ realHarmonic R := by
  rw [realHarmonic_eq_sum_Icc]
  exact Finset.sum_nonneg fun r _ ↦ inv_nonneg.mpr (Nat.cast_nonneg r)

/-- The unscaled spacing kernel retained through index step R. -/
def truncatedSpacingKernel (m R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    (((m - r : ℕ) : ℝ) ^ 2) / (r : ℝ)

/-- The spacing kernel with the bin-length denominator kept explicit. -/
def truncatedLengthKernel (m R : ℕ) (h : ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R,
    (((m - r : ℕ) : ℝ) ^ 2) / ((r : ℝ) * h)

/-- The portion of the local pair energy whose index separation is at most
R. -/
def truncatedLocalPairEnergy {m : ℕ} (R : ℕ)
    (x scale : Fin m → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R, stepPairEnergy (r := r) x scale

/-- Exact finite harmonic lower bound for the truncated spacing kernel. -/
theorem sq_sub_mul_realHarmonic_le_truncatedSpacingKernel
    (m R : ℕ) :
    (((m - R : ℕ) : ℝ) ^ 2) * realHarmonic R ≤
      truncatedSpacingKernel m R := by
  rw [realHarmonic_eq_sum_Icc, truncatedSpacingKernel, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hrmem
  have hrR : r ≤ R := (Finset.mem_Icc.mp hrmem).2
  have hsub : m - R ≤ m - r := Nat.sub_le_sub_left hrR m
  have hcast :
      (((m - R : ℕ) : ℝ) : ℝ) ≤ ((m - r : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hsquares :
      (((m - R : ℕ) : ℝ) ^ 2) ≤ (((m - r : ℕ) : ℝ) ^ 2) := by
    have hleft : (0 : ℝ) ≤ ((m - R : ℕ) : ℝ) := Nat.cast_nonneg _
    have hright : (0 : ℝ) ≤ ((m - r : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_right hsquares
      (inv_nonneg.mpr (Nat.cast_nonneg r)))

/-- Algebraic form of the truncation loss used in asymptotic estimates. -/
lemma sq_natSub_eq_sq_mul_one_sub_div {m R : ℕ} (hRm : R < m) :
    (((m - R : ℕ) : ℝ) ^ 2) =
      (m : ℝ) ^ 2 * (1 - (R : ℝ) / (m : ℝ)) ^ 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le R) hRm))
  rw [Nat.cast_sub hRm.le]
  field_simp

/-- Requested normalized form:

sum from r=1 to R of (m-r)^2/r is at least m^2 (1-R/m)^2 H_R.
-/
theorem sq_mul_one_sub_div_mul_realHarmonic_le_truncatedSpacingKernel
    {m R : ℕ} (hRm : R < m) :
    (m : ℝ) ^ 2 * (1 - (R : ℝ) / (m : ℝ)) ^ 2 *
        realHarmonic R ≤ truncatedSpacingKernel m R := by
  rw [← sq_natSub_eq_sq_mul_one_sub_div hRm]
  exact sq_sub_mul_realHarmonic_le_truncatedSpacingKernel m R

lemma truncatedLengthKernel_eq_div {m R : ℕ} {h : ℝ} (hh : h ≠ 0) :
    truncatedLengthKernel m R h = truncatedSpacingKernel m R / h := by
  rw [truncatedLengthKernel, truncatedSpacingKernel, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hrmem
  have hr : 0 < r := (Finset.mem_Icc.mp hrmem).1
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  field_simp

/-- Harmonic lower bound after inserting the positive bin length. -/
theorem sq_sub_mul_realHarmonic_div_le_truncatedLengthKernel
    (m R : ℕ) {h : ℝ} (hh : 0 < h) :
    ((((m - R : ℕ) : ℝ) ^ 2) * realHarmonic R) / h ≤
      truncatedLengthKernel m R h := by
  rw [truncatedLengthKernel_eq_div hh.ne']
  exact div_le_div_of_nonneg_right
    (sq_sub_mul_realHarmonic_le_truncatedSpacingKernel m R) hh.le

/-- Each fixed-step weighted energy is nonnegative when the points are
strictly ordered and the step is positive. -/
lemma stepPairEnergy_nonneg {m r : ℕ} (x scale : Fin m → ℝ)
    (hx : StrictMono x) (hr : 0 < r) :
    0 ≤ stepPairEnergy (r := r) x scale := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (Real.sqrt_nonneg _)
    (inv_nonneg.mpr (stepSpan_pos x hx hr i).le)

/-- The truncated energy is literally a sub-sum of the complete local
energy. -/
lemma truncatedLocalPairEnergy_le_localPairEnergy {m R : ℕ}
    (x scale : Fin m → ℝ) (hx : StrictMono x) (hRm : R < m) :
    truncatedLocalPairEnergy R x scale ≤ localPairEnergy x scale := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hrmem
    have hr := Finset.mem_Icc.mp hrmem
    exact Finset.mem_Ico.mpr ⟨hr.1, hr.2.trans_lt hRm⟩
  · intro r hrfull _
    have hr := Finset.mem_Ico.mp hrfull
    exact stepPairEnergy_nonneg x scale hx hr.1

/-- Exact finite lower bound obtained by summing the checked fixed-step
energy estimates only through R. -/
theorem mul_truncatedLengthKernel_le_truncatedLocalPairEnergy
    {m R : ℕ} (x scale : Fin m → ℝ) (hx : StrictMono x) (hRm : R < m)
    {A B h a : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) (ha : 0 ≤ a)
    (hscale : ∀ i, a ≤ scale i) :
    a * truncatedLengthKernel m R h ≤
      truncatedLocalPairEnergy R x scale := by
  rw [truncatedLengthKernel, Finset.mul_sum]
  exact Finset.sum_le_sum fun r hrmem ↦
    mul_sq_sub_div_mul_length_le_stepPairEnergy x scale hx
      (Finset.mem_Icc.mp hrmem).1
      ((Finset.mem_Icc.mp hrmem).2.trans_lt hRm)
      hxIcc hh hinterval ha hscale

/-- Dense-bin harmonic lower bound, still with an arbitrary finite
truncation R < m. -/
theorem mul_sq_sub_mul_realHarmonic_div_le_localPairEnergy
    {m R : ℕ} (x scale : Fin m → ℝ) (hx : StrictMono x) (hRm : R < m)
    {A B h a : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) (ha : 0 ≤ a)
    (hscale : ∀ i, a ≤ scale i) :
    a * (((((m - R : ℕ) : ℝ) ^ 2) * realHarmonic R) / h) ≤
      localPairEnergy x scale := by
  calc
    a * (((((m - R : ℕ) : ℝ) ^ 2) * realHarmonic R) / h) ≤
        a * truncatedLengthKernel m R h := by
      exact mul_le_mul_of_nonneg_left
        (sq_sub_mul_realHarmonic_div_le_truncatedLengthKernel m R hh) ha
    _ ≤ truncatedLocalPairEnergy R x scale :=
      mul_truncatedLengthKernel_le_truncatedLocalPairEnergy
        x scale hx hRm hxIcc hh hinterval ha hscale
    _ ≤ localPairEnergy x scale :=
      truncatedLocalPairEnergy_le_localPairEnergy x scale hx hRm

/-- The same dense-bin bound in the normalized m^2 (1-R/m)^2 form. -/
theorem mul_sq_mul_one_sub_div_mul_realHarmonic_div_le_localPairEnergy
    {m R : ℕ} (x scale : Fin m → ℝ) (hx : StrictMono x) (hRm : R < m)
    {A B h a : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) (ha : 0 ≤ a)
    (hscale : ∀ i, a ≤ scale i) :
    a * (((m : ℝ) ^ 2 * (1 - (R : ℝ) / (m : ℝ)) ^ 2 *
      realHarmonic R) / h) ≤ localPairEnergy x scale := by
  rw [← sq_natSub_eq_sq_mul_one_sub_div hRm]
  exact mul_sq_sub_mul_realHarmonic_div_le_localPairEnergy
    x scale hx hRm hxIcc hh hinterval ha hscale

/-- Exact R = floor(m/L) specialization.  The assumptions 1 < L ≤ m
make the retained range nonempty and ensure m/L < m; no rounding loss is
hidden. -/
theorem denseBin_divisor_lower {m L : ℕ} (x scale : Fin m → ℝ)
    (hx : StrictMono x) (hL : 1 < L) (hLm : L ≤ m)
    {A B h a : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) (ha : 0 ≤ a)
    (hscale : ∀ i, a ≤ scale i) :
    a * (((((m - m / L : ℕ) : ℝ) ^ 2) * realHarmonic (m / L)) / h) ≤
      localPairEnergy x scale := by
  have hm : 0 < m := lt_of_lt_of_le (Nat.zero_lt_of_lt hL) hLm
  have hdiv : m / L < m := Nat.div_lt_self hm hL
  exact mul_sq_sub_mul_realHarmonic_div_le_localPairEnergy
    x scale hx hdiv hxIcc hh hinterval ha hscale

end

end ClassicalBound
end Randy1153
