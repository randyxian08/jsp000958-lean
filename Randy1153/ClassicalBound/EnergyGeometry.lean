import Randy1153.ClassicalBound.Clock

/-!
# Finite spacing energy on an interval

This file isolates the elementary geometry behind a clipped pair-energy
argument.  For a fixed step r, every elementary adjacent gap occurs in at
most r of the spans x (i + r) - x i.  The exact boundary-sum identity below
records that overlap count.  Engel's form of Cauchy--Schwarz then gives the
sharp reciprocal-span lower bound

    (m - r)^2 / (r * h)

for m strictly ordered points in an interval of length at most h.

No asymptotic energy estimate is asserted here.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Left endpoint of an r-step pair among m indexed points. -/
def stepLeftIndex {m r : ℕ} (i : Fin (m - r)) : Fin m :=
  ⟨i.val, by omega⟩

/-- Right endpoint of an r-step pair among m indexed points. -/
def stepRightIndex {m r : ℕ} (i : Fin (m - r)) : Fin m :=
  ⟨i.val + r, by omega⟩

@[simp]
lemma stepLeftIndex_val {m r : ℕ} (i : Fin (m - r)) :
    (stepLeftIndex i).val = i.val :=
  rfl

@[simp]
lemma stepRightIndex_val {m r : ℕ} (i : Fin (m - r)) :
    (stepRightIndex i).val = i.val + r :=
  rfl

lemma stepLeftIndex_lt_stepRightIndex {m r : ℕ} (hr : 0 < r)
    (i : Fin (m - r)) :
    stepLeftIndex i < stepRightIndex i := by
  simp [Fin.lt_def, hr]

/-- The span between two points whose indices differ by r. -/
def stepSpan {m r : ℕ} (x : Fin m → ℝ) (i : Fin (m - r)) : ℝ :=
  x (stepRightIndex i) - x (stepLeftIndex i)

lemma stepSpan_pos {m r : ℕ} (x : Fin m → ℝ) (hx : StrictMono x)
    (hr : 0 < r) (i : Fin (m - r)) :
    0 < stepSpan x i := by
  exact sub_pos.mpr (hx (stepLeftIndex_lt_stepRightIndex hr i))

/-- Pure finite-sum form of the fixed-step overlap count. -/
private lemma sum_range_step_eq_boundary (f : ℕ → ℝ) {m r : ℕ}
    (hrm : r ≤ m) :
    (∑ i ∈ Finset.range (m - r), (f (i + r) - f i)) =
      ∑ j ∈ Finset.range r, (f (m - r + j) - f j) := by
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hsub : m - r + r = m := Nat.sub_add_cancel hrm
  have hright :
      (∑ i ∈ Finset.range (m - r), f (i + r)) =
        ∑ j ∈ Finset.Ico r m, f j := by
    rw [← Nat.Ico_zero_eq_range]
    simpa [Nat.add_comm, hsub] using Finset.sum_Ico_add f 0 (m - r) r
  have htop :
      (∑ j ∈ Finset.range r, f (m - r + j)) =
        ∑ j ∈ Finset.Ico (m - r) m, f j := by
    rw [← Nat.Ico_zero_eq_range]
    have hsub' : r + (m - r) = m := by omega
    simpa [Nat.add_comm, hsub, hsub'] using Finset.sum_Ico_add f 0 r (m - r)
  rw [hright, htop, ← Nat.Ico_zero_eq_range]
  rw [Finset.sum_Ico_eq_sub _ hrm]
  rw [Finset.sum_Ico_eq_sub _ (Nat.sub_le m r)]
  rw [Finset.sum_Ico_eq_sub _ (Nat.zero_le (m - r))]
  rw [Finset.sum_Ico_eq_sub _ (Nat.zero_le r)]
  ring

/-- Exact boundary form of the fixed-step overlap count.

The sum of all r-step spans is the sum of the last r point values minus
the sum of the first r point values.  This identity does not require the
points to be ordered.
-/
lemma sum_stepSpan_eq_boundary {m r : ℕ} (x : Fin m → ℝ)
    (hrm : r ≤ m) :
    (∑ i : Fin (m - r), stepSpan x i) =
      ∑ j : Fin r,
        (x ⟨m - r + j.val, by omega⟩ - x ⟨j.val, by omega⟩) := by
  by_cases hm : m = 0
  · subst m
    have : r = 0 := Nat.eq_zero_of_le_zero hrm
    subst r
    simp
  let f : ℕ → ℝ := fun j ↦ x ⟨min j (m - 1), by omega⟩
  rw [Finset.sum_fin_eq_sum_range, Finset.sum_fin_eq_sum_range]
  calc
    (∑ i ∈ Finset.range (m - r),
        if hi : i < m - r then stepSpan x ⟨i, hi⟩ else 0) =
        ∑ i ∈ Finset.range (m - r), (f (i + r) - f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < m - r := Finset.mem_range.mp hi
      rw [dif_pos hi']
      simp only [stepSpan, stepRightIndex, stepLeftIndex, f]
      congr 2
      · apply Fin.ext
        simp only
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        simp only
        exact (Nat.min_eq_left (by omega)).symm
    _ = ∑ j ∈ Finset.range r, (f (m - r + j) - f j) :=
      sum_range_step_eq_boundary f hrm
    _ = ∑ j ∈ Finset.range r,
        if hj : j < r then
          (x ⟨m - r + j, by omega⟩ - x ⟨j, by omega⟩)
        else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < r := Finset.mem_range.mp hj
      rw [dif_pos hj']
      simp only [f]
      congr 2
      · apply Fin.ext
        simp only
        exact Nat.min_eq_left (by omega)
      · apply Fin.ext
        simp only
        exact Nat.min_eq_left (by omega)

/-- Fixed-step overlap bound.  If every point lies in [A,B], the total
length of all r-step spans is at most r * (B-A). -/
lemma sum_stepSpan_le_mul_intervalLength {m r : ℕ} (x : Fin m → ℝ)
    (hrm : r ≤ m) {A B : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B) :
    (∑ i : Fin (m - r), stepSpan x i) ≤ (r : ℝ) * (B - A) := by
  rw [sum_stepSpan_eq_boundary x hrm]
  calc
    (∑ j : Fin r,
        (x ⟨m - r + j.val, by omega⟩ - x ⟨j.val, by omega⟩)) ≤
        ∑ _j : Fin r, (B - A) := by
      apply Finset.sum_le_sum
      intro j _
      exact sub_le_sub (hxIcc _).2 (hxIcc _).1
    _ = (r : ℝ) * (B - A) := by
      simp
      ring

/-- The sharp finite fixed-step reciprocal-spacing inequality.

For m strictly ordered real points in an interval of length at most h,
and 0 < r < m, the reciprocal mass of the m-r spans of step r is at
least (m-r)^2 / (r*h).
-/
theorem sq_sub_div_mul_length_le_sum_stepSpan_inv {m r : ℕ}
    (x : Fin m → ℝ) (hx : StrictMono x) (hr : 0 < r) (hrm : r < m)
    {A B h : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) :
    (((m - r : ℕ) : ℝ) ^ 2) / ((r : ℝ) * h) ≤
      ∑ i : Fin (m - r), (stepSpan x i)⁻¹ := by
  have hspan : ∀ i : Fin (m - r), 0 < stepSpan x i := stepSpan_pos x hx hr
  have hsumpos : 0 < ∑ i : Fin (m - r), stepSpan x i := by
    exact Finset.sum_pos' (fun i _ ↦ (hspan i).le)
      ⟨⟨0, by omega⟩, Finset.mem_univ _, hspan _⟩
  have hsumle : (∑ i : Fin (m - r), stepSpan x i) ≤ (r : ℝ) * h := by
    calc
      (∑ i : Fin (m - r), stepSpan x i) ≤ (r : ℝ) * (B - A) :=
        sum_stepSpan_le_mul_intervalLength x hrm.le hxIcc
      _ ≤ (r : ℝ) * h := by
        exact mul_le_mul_of_nonneg_left hinterval (Nat.cast_nonneg r)
  have hrh : 0 < (r : ℝ) * h := mul_pos (Nat.cast_pos.mpr hr) hh
  have htitu := Finset.sq_sum_div_le_sum_sq_div
    (Finset.univ : Finset (Fin (m - r))) (fun _ ↦ (1 : ℝ))
      (g := fun i ↦ stepSpan x i) (fun i _ ↦ hspan i)
  have hcard : (∑ _i : Fin (m - r), (1 : ℝ)) = ((m - r : ℕ) : ℝ) := by
    simp
  have hone :
      (∑ i : Fin (m - r), (1 : ℝ) ^ 2 / stepSpan x i) =
        ∑ i : Fin (m - r), (stepSpan x i)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i _
    simp [div_eq_mul_inv]
  rw [hcard, hone] at htitu
  calc
    (((m - r : ℕ) : ℝ) ^ 2) / ((r : ℝ) * h) ≤
        (((m - r : ℕ) : ℝ) ^ 2) /
          (∑ i : Fin (m - r), stepSpan x i) := by
      apply (div_le_div_iff₀ hrh hsumpos).2
      exact mul_le_mul_of_nonneg_left hsumle
        (sq_nonneg (((m - r : ℕ) : ℝ)))
    _ ≤ ∑ i : Fin (m - r), (stepSpan x i)⁻¹ := htitu

/-- The geometric-mean weight assigned to an r-step pair. -/
def stepGeometricWeight {m r : ℕ} (scale : Fin m → ℝ)
    (i : Fin (m - r)) : ℝ :=
  Real.sqrt (scale (stepLeftIndex i) * scale (stepRightIndex i))

/-- Fixed-step portion of the scale-weighted pair energy. -/
def stepPairEnergy {m r : ℕ} (x scale : Fin m → ℝ) : ℝ :=
  ∑ i : Fin (m - r), stepGeometricWeight scale i * (stepSpan x i)⁻¹

lemma le_stepGeometricWeight_of_le_scale {m r : ℕ} (scale : Fin m → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hscale : ∀ i, a ≤ scale i)
    (i : Fin (m - r)) :
    a ≤ stepGeometricWeight scale i := by
  have hleft : 0 ≤ scale (stepLeftIndex i) := ha.trans (hscale _)
  have hsq : a ^ 2 ≤ scale (stepLeftIndex i) * scale (stepRightIndex i) := by
    simpa [pow_two] using
      (mul_le_mul (hscale (stepLeftIndex i)) (hscale (stepRightIndex i))
        ha hleft)
  calc
    a = Real.sqrt (a ^ 2) := by simp [Real.sqrt_sq_eq_abs, abs_of_nonneg ha]
    _ ≤ Real.sqrt (scale (stepLeftIndex i) * scale (stepRightIndex i)) :=
      Real.sqrt_le_sqrt hsq
    _ = stepGeometricWeight scale i := rfl

/-- Local fixed-step energy bound for a bin on which every clipped scale is
bounded below by a.

This is deliberately a finite single-step statement: summing it over a
chosen set of steps, or embedding those pairs into a global unordered-pair
energy, is separate bookkeeping.
-/
theorem mul_sq_sub_div_mul_length_le_stepPairEnergy {m r : ℕ}
    (x scale : Fin m → ℝ) (hx : StrictMono x) (hr : 0 < r) (hrm : r < m)
    {A B h a : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) (ha : 0 ≤ a)
    (hscale : ∀ i, a ≤ scale i) :
    a * ((((m - r : ℕ) : ℝ) ^ 2) / ((r : ℝ) * h)) ≤
      stepPairEnergy (r := r) x scale := by
  have hspacing := sq_sub_div_mul_length_le_sum_stepSpan_inv
    x hx hr hrm hxIcc hh hinterval
  calc
    a * ((((m - r : ℕ) : ℝ) ^ 2) / ((r : ℝ) * h)) ≤
        a * ∑ i : Fin (m - r), (stepSpan x i)⁻¹ :=
      mul_le_mul_of_nonneg_left hspacing ha
    _ = ∑ i : Fin (m - r), a * (stepSpan x i)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin (m - r),
        stepGeometricWeight scale i * (stepSpan x i)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (le_stepGeometricWeight_of_le_scale scale ha hscale i)
        (inv_nonneg.mpr (stepSpan_pos x hx hr i).le)
    _ = stepPairEnergy (r := r) x scale := rfl

/-- The complete weighted pair energy inside one ordered bin, decomposed
uniquely by positive index separation.  Thus every pair of distinct indices
with the smaller index first occurs once. -/
def localPairEnergy {m : ℕ} (x scale : Fin m → ℝ) : ℝ :=
  ∑ r ∈ Finset.Ico 1 m, stepPairEnergy (r := r) x scale

/-- Summing the sharp fixed-step estimates gives the finite local-bin
energy bound.  The right side of the lower bound is left as an exact finite
sum; extracting its harmonic asymptotics is a separate analytic step. -/
theorem mul_sum_sq_sub_div_mul_length_le_localPairEnergy {m : ℕ}
    (x scale : Fin m → ℝ) (hx : StrictMono x)
    {A B h a : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B)
    (hh : 0 < h) (hinterval : B - A ≤ h) (ha : 0 ≤ a)
    (hscale : ∀ i, a ≤ scale i) :
    a * (∑ r ∈ Finset.Ico 1 m,
      (((m - r : ℕ) : ℝ) ^ 2) / ((r : ℝ) * h)) ≤
        localPairEnergy x scale := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun r hrmem ↦
    mul_sq_sub_div_mul_length_le_stepPairEnergy x scale hx
      (Finset.mem_Ico.mp hrmem).1 (Finset.mem_Ico.mp hrmem).2
      hxIcc hh hinterval ha hscale

end

end ClassicalBound
end Randy1153
