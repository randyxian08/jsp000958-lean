import Randy1153.ClassicalBound.RieszWeights
import Randy1153.ClassicalBound.ChebyshevDerivative
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Finite Riesz interpolation for algebraic trigonometric polynomials

This file develops the exact midpoint Fourier calculation behind the sharp
weighted Bernstein inequality.  No analytic Bernstein inequality is assumed.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- The `j`-th midpoint angle in the `2d`-point Riesz formula. -/
def rieszAngle (d j : ℕ) : ℝ :=
  ((2 * (j : ℝ) + 1) * Real.pi) / (2 * (d : ℝ))

/-- Its point on the complex unit circle. -/
def rieszPhase (d j : ℕ) : ℂ :=
  Complex.exp ((rieszAngle d j : ℂ) * Complex.I)

/-- The primitive `2d`-th root which advances one midpoint to the next. -/
def rieszStep (d : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (2 * (d : ℂ)))

private lemma rieszPhase_eq_first_mul_step_pow (d j : ℕ) (hd : 0 < d) :
    rieszPhase d j = rieszPhase d 0 * rieszStep d ^ j := by
  rw [rieszPhase, rieszPhase, rieszStep]
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  apply congr_arg Complex.exp
  dsimp [rieszAngle]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  push_cast
  field_simp [hdC]
  ring

private lemma rieszStep_isPrimitiveRoot (d : ℕ) (hd : 0 < d) :
    IsPrimitiveRoot (rieszStep d) (2 * d) := by
  unfold rieszStep
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    Complex.isPrimitiveRoot_exp (2 * d) (by omega)

private lemma rieszStep_pow_ne_one (d m : ℕ) (hd : 0 < d)
    (hm0 : 0 < m) (hm : m < 2 * d) :
    rieszStep d ^ m ≠ 1 := by
  intro h
  have hdiv := ((rieszStep_isPrimitiveRoot d hd).pow_eq_one_iff_dvd m).mp h
  exact (Nat.not_dvd_of_pos_of_lt hm0 hm) hdiv

private lemma sum_rieszStep_pow_eq_zero (d m : ℕ) (hd : 0 < d)
    (hm0 : 0 < m) (hm : m < 2 * d) :
    ∑ j ∈ Finset.range (2 * d), (rieszStep d ^ m) ^ j = 0 := by
  have hpow : (rieszStep d ^ m) ^ (2 * d) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul,
      (rieszStep_isPrimitiveRoot d hd).pow_eq_one, one_pow]
  have hgeom := geom_sum_mul (rieszStep d ^ m) (2 * d)
  rw [hpow, sub_self] at hgeom
  rcases mul_eq_zero.mp hgeom with hsum | hstep
  · exact hsum
  · exfalso
    exact (rieszStep_pow_ne_one d m hd hm0 hm) (sub_eq_zero.mp hstep)

/-- Nonconstant Fourier modes below frequency `2d` sum to zero on the
`2d` midpoint phases. -/
lemma sum_rieszPhase_pow_eq_zero (d m : ℕ) (hd : 0 < d)
    (hm0 : 0 < m) (hm : m < 2 * d) :
    ∑ j ∈ Finset.range (2 * d), rieszPhase d j ^ m = 0 := by
  calc
    (∑ j ∈ Finset.range (2 * d), rieszPhase d j ^ m) =
        ∑ j ∈ Finset.range (2 * d),
          rieszPhase d 0 ^ m * (rieszStep d ^ m) ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rieszPhase_eq_first_mul_step_pow d j hd, mul_pow]
      congr 1
      calc
        (rieszStep d ^ j) ^ m = rieszStep d ^ (j * m) := (pow_mul _ _ _).symm
        _ = rieszStep d ^ (m * j) := by rw [mul_comm]
        _ = (rieszStep d ^ m) ^ j := pow_mul _ _ _
    _ = rieszPhase d 0 ^ m *
        (∑ j ∈ Finset.range (2 * d), (rieszStep d ^ m) ^ j) := by
      rw [Finset.mul_sum]
    _ = 0 := by rw [sum_rieszStep_pow_eq_zero d m hd hm0 hm, mul_zero]

/-- Real-part form of midpoint Fourier orthogonality. -/
lemma sum_cos_mul_rieszAngle_eq_zero (d m : ℕ) (hd : 0 < d)
    (hm0 : 0 < m) (hm : m < 2 * d) :
    ∑ j ∈ Finset.range (2 * d), Real.cos ((m : ℝ) * rieszAngle d j) = 0 := by
  have h := congr_arg Complex.re (sum_rieszPhase_pow_eq_zero d m hd hm0 hm)
  rw [Complex.re_sum] at h
  simp only [Complex.zero_re] at h
  calc
    (∑ j ∈ Finset.range (2 * d), Real.cos ((m : ℝ) * rieszAngle d j)) =
        ∑ j ∈ Finset.range (2 * d), (rieszPhase d j ^ m).re := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rieszPhase, ← Complex.exp_nat_mul]
      rw [show (m : ℂ) * ((rieszAngle d j : ℂ) * Complex.I) =
        (((m : ℝ) * rieszAngle d j : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I_re]
    _ = 0 := h

/-- Imaginary-part form of midpoint Fourier orthogonality. -/
lemma sum_sin_mul_rieszAngle_eq_zero (d m : ℕ) (hd : 0 < d)
    (hm0 : 0 < m) (hm : m < 2 * d) :
    ∑ j ∈ Finset.range (2 * d), Real.sin ((m : ℝ) * rieszAngle d j) = 0 := by
  have h := congr_arg Complex.im (sum_rieszPhase_pow_eq_zero d m hd hm0 hm)
  rw [Complex.im_sum] at h
  simp only [Complex.zero_im] at h
  calc
    (∑ j ∈ Finset.range (2 * d), Real.sin ((m : ℝ) * rieszAngle d j)) =
        ∑ j ∈ Finset.range (2 * d), (rieszPhase d j ^ m).im := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rieszPhase, ← Complex.exp_nat_mul]
      rw [show (m : ℂ) * ((rieszAngle d j : ℂ) * Complex.I) =
        (((m : ℝ) * rieszAngle d j : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I_im]
    _ = 0 := h

private lemma rieszPhase_pow_two_mul (d j : ℕ) (hd : 0 < d) :
    rieszPhase d j ^ (2 * d) = -1 := by
  rw [rieszPhase, ← Complex.exp_nat_mul]
  rw [show (((2 * d : ℕ) : ℂ)) * ((rieszAngle d j : ℂ) * Complex.I) =
      (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I by
    dsimp [rieszAngle]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp [hdC]]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I,
    Complex.exp_pi_mul_I, one_mul]

private lemma rieszPhase_ne_one (d j : ℕ) (hd : 0 < d) :
    rieszPhase d j ≠ 1 := by
  intro h
  have hp := rieszPhase_pow_two_mul d j hd
  rw [h, one_pow] at hp
  norm_num at hp

private lemma rieszPhase_ne_zero (d j : ℕ) : rieszPhase d j ≠ 0 := by
  exact Complex.exp_ne_zero ((rieszAngle d j : ℂ) * Complex.I)

private lemma rieszAngle_reflect (d j : ℕ) (hd : 0 < d) (hj : j < 2 * d) :
    rieszAngle d (2 * d - 1 - j) = 2 * Real.pi - rieszAngle d j := by
  dsimp [rieszAngle]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub (by omega : j ≤ 2 * d - 1),
    Nat.cast_sub (by omega : 1 ≤ 2 * d)]
  push_cast
  field_simp [hdR]
  ring

private lemma rieszPhase_reflect (d j : ℕ) (hd : 0 < d) (hj : j < 2 * d) :
    rieszPhase d (2 * d - 1 - j) = (rieszPhase d j)⁻¹ := by
  rw [rieszPhase, rieszPhase, rieszAngle_reflect d j hd hj]
  rw [show (((2 * Real.pi - rieszAngle d j : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I -
        (rieszAngle d j : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_sub, Complex.exp_two_pi_mul_I, one_div]

private lemma sum_one_div_one_sub_rieszPhase (d : ℕ) (hd : 0 < d) :
    ∑ j ∈ Finset.range (2 * d), 1 / (1 - rieszPhase d j) = (d : ℂ) := by
  let S : ℂ := ∑ j ∈ Finset.range (2 * d), 1 / (1 - rieszPhase d j)
  have href := Finset.sum_range_reflect
    (fun j ↦ (1 / (1 - rieszPhase d j) : ℂ)) (2 * d)
  have hleft :
      (∑ j ∈ Finset.range (2 * d),
        1 / (1 - rieszPhase d (2 * d - 1 - j))) =
        ∑ j ∈ Finset.range (2 * d),
          (1 - 1 / (1 - rieszPhase d j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    rw [rieszPhase_reflect d j hd hjlt]
    have hz0 := rieszPhase_ne_zero d j
    have hz1 := rieszPhase_ne_one d j hd
    have hden : 1 - rieszPhase d j ≠ 0 := sub_ne_zero.mpr hz1.symm
    have hrev : -1 + rieszPhase d j ≠ 0 := by
      intro h
      apply hz1
      linear_combination h
    calc
      1 / (1 - (rieszPhase d j)⁻¹) =
          rieszPhase d j / (rieszPhase d j - 1) := by
        field_simp [hz0, hden, hrev]
      _ = 1 - 1 / (1 - rieszPhase d j) := by
        rw [show 1 - rieszPhase d j = -(rieszPhase d j - 1) by ring,
          one_div, inv_neg]
        have hzsub : rieszPhase d j - 1 ≠ 0 := sub_ne_zero.mpr hz1
        have hzfrac :
            rieszPhase d j / (rieszPhase d j - 1) =
              1 + 1 / (rieszPhase d j - 1) := by
          calc
            rieszPhase d j / (rieszPhase d j - 1) =
                ((rieszPhase d j - 1) + 1) / (rieszPhase d j - 1) := by
              congr 1
              ring
            _ = 1 + 1 / (rieszPhase d j - 1) := by
              rw [add_div, div_self hzsub]
        simpa only [one_div, sub_neg_eq_add] using hzfrac
  rw [hleft] at href
  have hsumOne :
      (∑ j ∈ Finset.range (2 * d), (1 : ℂ)) = (2 * d : ℕ) := by simp
  simp only [Finset.sum_sub_distrib] at href
  rw [hsumOne] at href
  push_cast at href
  have htwo :
      (2 : ℂ) * (∑ j ∈ Finset.range (2 * d),
        1 / (1 - rieszPhase d j)) = 2 * (d : ℂ) := by
    linear_combination -href
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo

private lemma sum_phase_div_one_sub (d : ℕ) (hd : 0 < d) :
    ∑ j ∈ Finset.range (2 * d),
      rieszPhase d j / (1 - rieszPhase d j) = -(d : ℂ) := by
  calc
    (∑ j ∈ Finset.range (2 * d),
        rieszPhase d j / (1 - rieszPhase d j)) =
        ∑ j ∈ Finset.range (2 * d),
          (1 / (1 - rieszPhase d j) - 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hz1 := rieszPhase_ne_one d j hd
      have hden : 1 - rieszPhase d j ≠ 0 := sub_ne_zero.mpr hz1.symm
      apply (div_eq_iff hden).2
      field_simp [hden]
      ring
    _ = -(d : ℂ) := by
      rw [Finset.sum_sub_distrib, sum_one_div_one_sub_rieszPhase d hd]
      simp
      ring

private lemma sum_phase_pow_div_one_sub (d m : ℕ) (hd : 0 < d)
    (hm0 : 1 ≤ m) (hmN : m ≤ 2 * d) :
    ∑ j ∈ Finset.range (2 * d),
      rieszPhase d j ^ m / (1 - rieszPhase d j) = -(d : ℂ) := by
  induction m, hm0 using Nat.le_induction with
  | base => simpa using sum_phase_div_one_sub d hd
  | succ m hm1 ih =>
      have hmLt : m < 2 * d := by omega
      calc
        (∑ j ∈ Finset.range (2 * d),
            rieszPhase d j ^ (m + 1) / (1 - rieszPhase d j)) =
            ∑ j ∈ Finset.range (2 * d),
              (rieszPhase d j ^ m / (1 - rieszPhase d j) -
                rieszPhase d j ^ m) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hz1 := rieszPhase_ne_one d j hd
          have hden : 1 - rieszPhase d j ≠ 0 := sub_ne_zero.mpr hz1.symm
          rw [pow_succ]
          field_simp [hden]
          ring
        _ = (∑ j ∈ Finset.range (2 * d),
              rieszPhase d j ^ m / (1 - rieszPhase d j)) -
            (∑ j ∈ Finset.range (2 * d), rieszPhase d j ^ m) := by
          rw [Finset.sum_sub_distrib]
        _ = -(d : ℂ) := by
          rw [ih (by omega), sum_rieszPhase_pow_eq_zero d m hd hm1 hmLt, sub_zero]

/-- The rational root moments appearing in the Riesz coefficients. -/
def rieszRootMoment (d m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (2 * d),
    rieszPhase d j ^ m / (1 - rieszPhase d j) ^ 2

private lemma rieszRootMoment_succ_sub (d m : ℕ) (hd : 0 < d)
    (hm0 : 1 ≤ m) (hmN : m ≤ 2 * d) :
    rieszRootMoment d (m + 1) - rieszRootMoment d m = (d : ℂ) := by
  rw [rieszRootMoment, rieszRootMoment, ← Finset.sum_sub_distrib]
  calc
    (∑ j ∈ Finset.range (2 * d),
        (rieszPhase d j ^ (m + 1) / (1 - rieszPhase d j) ^ 2 -
          rieszPhase d j ^ m / (1 - rieszPhase d j) ^ 2)) =
        -(∑ j ∈ Finset.range (2 * d),
          rieszPhase d j ^ m / (1 - rieszPhase d j)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hz1 := rieszPhase_ne_one d j hd
      have hden : 1 - rieszPhase d j ≠ 0 := sub_ne_zero.mpr hz1.symm
      rw [pow_succ]
      field_simp [hden]
      ring
    _ = (d : ℂ) := by rw [sum_phase_pow_div_one_sub d m hd hm0 hmN, neg_neg]

private lemma reflected_rootMoment_center_term (d j : ℕ) (hd : 0 < d) :
    (rieszPhase d j)⁻¹ ^ (d + 1) /
        (1 - (rieszPhase d j)⁻¹) ^ 2 =
      -(rieszPhase d j ^ (d + 1) / (1 - rieszPhase d j) ^ 2) := by
  let z := rieszPhase d j
  have hz0 : z ≠ 0 := rieszPhase_ne_zero d j
  have hz1 : z ≠ 1 := rieszPhase_ne_one d j hd
  have hden : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hzpow : z ^ (2 * d) = -1 := rieszPhase_pow_two_mul d j hd
  have hmiddle : z ^ (d + 1) * z ^ (d - 1) = -1 := by
    rw [← pow_add]
    rw [show d + 1 + (d - 1) = 2 * d by omega]
    exact hzpow
  have hpowrel : z ^ 2 * (1 / z) ^ (d + 1) = -z ^ (d + 1) := by
    have hsquare : z ^ (d + 1) * z ^ (d + 1) = -z ^ 2 := by
      have hpower : z ^ (d + 1) = z ^ (d - 1) * z ^ 2 := by
        rw [← pow_add]
        rw [show d - 1 + 2 = d + 1 by
          calc
            d - 1 + 2 = (d - 1 + 1) + 1 := by omega
            _ = d + 1 := by rw [Nat.sub_add_cancel (by omega)]]
      calc
        z ^ (d + 1) * z ^ (d + 1) =
            (z ^ (d + 1) * z ^ (d - 1)) * z ^ 2 := by
          rw [hpower, mul_assoc]
          ring
        _ = -z ^ 2 := by rw [hmiddle, neg_one_mul]
    rw [one_div, inv_pow, ← div_eq_mul_inv]
    apply (div_eq_iff (pow_ne_zero _ hz0)).2
    rw [neg_mul, hsquare]
    ring
  dsimp only [z] at hz0 hz1 hden hzpow hmiddle ⊢
  field_simp [hz0, hden]
  rw [show (1 - rieszPhase d j) ^ 2 = (rieszPhase d j - 1) ^ 2 by ring]
  field_simp [sub_ne_zero.mpr hz1]
  exact hpowrel

private lemma rieszRootMoment_center (d : ℕ) (hd : 0 < d) :
    rieszRootMoment d (d + 1) = 0 := by
  have href := Finset.sum_range_reflect
    (fun j ↦ rieszPhase d j ^ (d + 1) / (1 - rieszPhase d j) ^ 2) (2 * d)
  have hleft :
      (∑ j ∈ Finset.range (2 * d),
        rieszPhase d (2 * d - 1 - j) ^ (d + 1) /
          (1 - rieszPhase d (2 * d - 1 - j)) ^ 2) =
        -(∑ j ∈ Finset.range (2 * d),
          rieszPhase d j ^ (d + 1) / (1 - rieszPhase d j) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [rieszPhase_reflect d j hd (Finset.mem_range.mp hj)]
    exact reflected_rootMoment_center_term d j hd
  rw [hleft] at href
  rw [rieszRootMoment]
  have htwo :
      (2 : ℂ) * (∑ j ∈ Finset.range (2 * d),
        rieszPhase d j ^ (d + 1) / (1 - rieszPhase d j) ^ 2) = 0 := by
    linear_combination -href
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

lemma rieszRootMoment_center_add (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    rieszRootMoment d (d + 1 + k) = (d : ℂ) * k := by
  induction k with
  | zero => simpa using rieszRootMoment_center d hd
  | succ k ih =>
      have hkLt : k < d := by omega
      have hstep := rieszRootMoment_succ_sub d (d + 1 + k) hd
        (by omega : 1 ≤ d + 1 + k) (by omega : d + 1 + k ≤ 2 * d)
      rw [show d + 1 + (k + 1) = (d + 1 + k) + 1 by omega]
      rw [sub_eq_iff_eq_add] at hstep
      rw [hstep, ih (by omega)]
      push_cast
      ring

/-- The signed coefficient in the finite Riesz derivative formula. -/
def rieszSignedWeight (d j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j /
    (4 * (d : ℝ) * Real.sin (rieszAngle d j / 2) ^ 2)

private lemma rieszPhase_pow_d (d j : ℕ) (hd : 0 < d) :
    rieszPhase d j ^ d = Complex.I * ((-1 : ℝ) ^ j : ℂ) := by
  rw [rieszPhase, ← Complex.exp_nat_mul]
  rw [show (d : ℂ) * ((rieszAngle d j : ℂ) * Complex.I) =
      (j : ℂ) * ((Real.pi : ℂ) * Complex.I) +
        (Real.pi : ℂ) / 2 * Complex.I by
    dsimp [rieszAngle]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp [hdC]]
  rw [Complex.exp_add, Complex.exp_nat_mul,
    Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
  push_cast
  ring

private lemma one_sub_rieszPhase_sq (d j : ℕ) :
    (1 - rieszPhase d j) ^ 2 =
      -4 * rieszPhase d j * (Real.sin (rieszAngle d j / 2) : ℂ) ^ 2 := by
  let u : ℂ := Complex.exp (((rieszAngle d j / 2 : ℝ) : ℂ) * Complex.I)
  have hu_sq : u ^ 2 = rieszPhase d j := by
    dsimp only [u]
    rw [rieszPhase, ← Complex.exp_nat_mul]
    apply congr_arg Complex.exp
    push_cast
    ring
  have hu_euler :
      u = (Real.cos (rieszAngle d j / 2) : ℂ) +
        (Real.sin (rieszAngle d j / 2) : ℂ) * Complex.I := by
    dsimp only [u]
    rw [Complex.exp_mul_I]
    simp
  have htrig := Real.sin_sq_add_cos_sq (rieszAngle d j / 2)
  have htrigC :
      (Real.sin (rieszAngle d j / 2) : ℂ) ^ 2 +
        (Real.cos (rieszAngle d j / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast htrig
  have hone :
      1 - u ^ 2 = -2 * Complex.I * u *
        (Real.sin (rieszAngle d j / 2) : ℂ) := by
    rw [hu_euler]
    ring_nf
    rw [Complex.I_sq]
    ring_nf at htrigC ⊢
    have hcos :
        (Real.cos (rieszAngle d j * (1 / 2)) : ℂ) ^ 2 =
          1 - (Real.sin (rieszAngle d j * (1 / 2)) : ℂ) ^ 2 := by
      linear_combination htrigC
    rw [hcos]
    ring
  rw [← hu_sq, hone]
  ring_nf
  rw [Complex.I_sq]
  ring

private lemma rieszSignedWeight_cast (d j : ℕ) (hd : 0 < d) :
    (rieszSignedWeight d j : ℂ) =
      Complex.I / (d : ℂ) *
        (rieszPhase d j ^ (d + 1) / (1 - rieszPhase d j) ^ 2) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hz0 := rieszPhase_ne_zero d j
  have hz1 := rieszPhase_ne_one d j hd
  have hden : (1 - rieszPhase d j) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz1.symm)
  have hsin : (Real.sin (rieszAngle d j / 2) : ℂ) ^ 2 ≠ 0 := by
    intro h
    have hsquare := one_sub_rieszPhase_sq d j
    rw [h, mul_zero] at hsquare
    exact hden (hsquare.trans (by norm_num))
  rw [rieszSignedWeight]
  push_cast
  rw [show rieszPhase d j ^ (d + 1) =
    rieszPhase d j ^ d * rieszPhase d j by rw [pow_succ]]
  rw [rieszPhase_pow_d d j hd, one_sub_rieszPhase_sq]
  field_simp [hdC, hz0, hden, hsin]
  rw [Complex.I_sq]
  push_cast
  ring

/-- Complex Fourier moment of the signed Riesz weights. -/
lemma sum_rieszSignedWeight_mul_phase_pow (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    ∑ j ∈ Finset.range (2 * d),
      (rieszSignedWeight d j : ℂ) * rieszPhase d j ^ k =
        Complex.I * (k : ℂ) := by
  calc
    (∑ j ∈ Finset.range (2 * d),
        (rieszSignedWeight d j : ℂ) * rieszPhase d j ^ k) =
        Complex.I / (d : ℂ) * rieszRootMoment d (d + 1 + k) := by
      rw [rieszRootMoment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [rieszSignedWeight_cast d j hd]
      rw [pow_add]
      ring
    _ = Complex.I * (k : ℂ) := by
      rw [rieszRootMoment_center_add d k hd hk]
      have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
      field_simp [hdC]

/-- Cosine moment of the signed weights. -/
lemma sum_rieszSignedWeight_mul_cos (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    ∑ j ∈ Finset.range (2 * d),
      rieszSignedWeight d j * Real.cos ((k : ℝ) * rieszAngle d j) = 0 := by
  have h := congr_arg Complex.re (sum_rieszSignedWeight_mul_phase_pow d k hd hk)
  rw [Complex.re_sum] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.I_re, Complex.I_im, one_mul] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [rieszPhase, ← Complex.exp_nat_mul]
  rw [show (k : ℂ) * ((rieszAngle d j : ℂ) * Complex.I) =
    (((k : ℝ) * rieszAngle d j : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]
  simp

/-- Sine moment of the signed weights. -/
lemma sum_rieszSignedWeight_mul_sin (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    ∑ j ∈ Finset.range (2 * d),
      rieszSignedWeight d j * Real.sin ((k : ℝ) * rieszAngle d j) = (k : ℝ) := by
  have h := congr_arg Complex.im (sum_rieszSignedWeight_mul_phase_pow d k hd hk)
  rw [Complex.im_sum] at h
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.I_re, Complex.I_im, one_mul] at h
  calc
    (∑ j ∈ Finset.range (2 * d),
        rieszSignedWeight d j * Real.sin ((k : ℝ) * rieszAngle d j)) =
        ∑ j ∈ Finset.range (2 * d),
          ((rieszSignedWeight d j : ℂ) * rieszPhase d j ^ k).im := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [rieszPhase, ← Complex.exp_nat_mul]
      rw [show (k : ℂ) * ((rieszAngle d j : ℂ) * Complex.I) =
        (((k : ℝ) * rieszAngle d j : ℝ) : ℂ) * Complex.I by push_cast; ring]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      rw [Complex.exp_ofReal_mul_I_im]
    _ = (k : ℝ) := by simpa using h

/-- Exact Riesz formula for one cosine mode. -/
lemma sum_rieszSignedWeight_mul_cos_add (d k : ℕ) (hd : 0 < d) (hk : k ≤ d)
    (θ : ℝ) :
    ∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
      Real.cos ((k : ℝ) * (θ + rieszAngle d j)) =
        -(k : ℝ) * Real.sin ((k : ℝ) * θ) := by
  simp_rw [mul_add, Real.cos_add, mul_sub]
  rw [Finset.sum_sub_distrib]
  calc
    (∑ x ∈ Finset.range (2 * d),
        rieszSignedWeight d x *
          (Real.cos ((k : ℝ) * θ) * Real.cos ((k : ℝ) * rieszAngle d x))) -
        ∑ x ∈ Finset.range (2 * d),
          rieszSignedWeight d x *
            (Real.sin ((k : ℝ) * θ) * Real.sin ((k : ℝ) * rieszAngle d x)) =
      Real.cos ((k : ℝ) * θ) *
          (∑ x ∈ Finset.range (2 * d),
            rieszSignedWeight d x * Real.cos ((k : ℝ) * rieszAngle d x)) -
        Real.sin ((k : ℝ) * θ) *
          (∑ x ∈ Finset.range (2 * d),
            rieszSignedWeight d x * Real.sin ((k : ℝ) * rieszAngle d x)) := by
        congr 1 <;> rw [Finset.mul_sum] <;>
          apply Finset.sum_congr rfl <;> intro j hj <;> ring
    _ = -(k : ℝ) * Real.sin ((k : ℝ) * θ) := by
      rw [sum_rieszSignedWeight_mul_cos d k hd hk,
        sum_rieszSignedWeight_mul_sin d k hd hk]
      ring

/-- The exact Riesz derivative formula on a Chebyshev basis vector. -/
lemma riesz_formula_chebyshevT (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) (θ : ℝ) :
    -Real.sin θ *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).derivative.eval (Real.cos θ) =
      ∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
        (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
          (Real.cos (θ + rieszAngle d j)) := by
  simp_rw [Polynomial.Chebyshev.T_real_cos]
  norm_num only [Int.cast_natCast]
  rw [sum_rieszSignedWeight_mul_cos_add d k hd hk]
  cases k with
  | zero => simp
  | succ k =>
      rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul,
        Polynomial.eval_intCast]
      rw [show ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
      have hU := Polynomial.Chebyshev.U_real_cos θ (k : ℤ)
      norm_num only [Int.cast_natCast, Nat.cast_add, Nat.cast_one] at hU ⊢
      rw [← hU]
      push_cast
      ring

private def HasRieszFormula (d : ℕ) (p : ℝ[X]) : Prop :=
  ∀ θ : ℝ,
    -Real.sin θ * p.derivative.eval (Real.cos θ) =
      ∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
        p.eval (Real.cos (θ + rieszAngle d j))

private lemma hasRieszFormula_zero (d : ℕ) : HasRieszFormula d (0 : ℝ[X]) := by
  intro θ
  simp

private lemma HasRieszFormula.add {d : ℕ} {p q : ℝ[X]}
    (hp : HasRieszFormula d p) (hq : HasRieszFormula d q) :
    HasRieszFormula d (p + q) := by
  intro θ
  simp only [HasRieszFormula] at hp hq ⊢
  simp only [Polynomial.derivative_add, Polynomial.eval_add, mul_add,
    Finset.sum_add_distrib]
  rw [← hp θ, ← hq θ]

private lemma HasRieszFormula.neg {d : ℕ} {p : ℝ[X]}
    (hp : HasRieszFormula d p) : HasRieszFormula d (-p) := by
  intro θ
  simp only [HasRieszFormula] at hp ⊢
  simp only [Polynomial.derivative_neg, Polynomial.eval_neg, mul_neg,
    Finset.sum_neg_distrib]
  rw [← hp θ]

private lemma HasRieszFormula.sub {d : ℕ} {p q : ℝ[X]}
    (hp : HasRieszFormula d p) (hq : HasRieszFormula d q) :
    HasRieszFormula d (p - q) := by
  rw [sub_eq_add_neg]
  exact hp.add hq.neg

private lemma HasRieszFormula.C_mul {d : ℕ} {p : ℝ[X]}
    (hp : HasRieszFormula d p) (c : ℝ) :
    HasRieszFormula d (Polynomial.C c * p) := by
  intro θ
  simp only [HasRieszFormula] at hp ⊢
  rw [Polynomial.derivative_C_mul, Polynomial.eval_C_mul]
  simp_rw [Polynomial.eval_C_mul]
  calc
    -Real.sin θ * (c * p.derivative.eval (Real.cos θ)) =
        c * (-Real.sin θ * p.derivative.eval (Real.cos θ)) := by ring
    _ = c * (∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
        p.eval (Real.cos (θ + rieszAngle d j))) := by rw [hp θ]
    _ = ∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
        (c * p.eval (Real.cos (θ + rieszAngle d j))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private lemma hasRieszFormula_chebyshevT (d k : ℕ) (hd : 0 < d) (hk : k ≤ d) :
    HasRieszFormula d (Polynomial.Chebyshev.T ℝ (k : ℤ)) :=
  riesz_formula_chebyshevT d k hd hk

/-- Exact finite Riesz interpolation formula for every real polynomial of
degree at most `d`. -/
theorem riesz_derivative_formula (d : ℕ) (hd : 0 < d) (p : ℝ[X])
    (hdeg : p.natDegree ≤ d) (θ : ℝ) :
    -Real.sin θ * p.derivative.eval (Real.cos θ) =
      ∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
        p.eval (Real.cos (θ + rieszAngle d j)) := by
  have hall : ∀ q : ℝ[X], q.natDegree ≤ d → HasRieszFormula d q := by
    intro q hqd
    induction hn : q.natDegree using Nat.strong_induction_on generalizing q with
    | h n ih =>
        by_cases hq0 : q = 0
        · simpa [hq0] using hasRieszFormula_zero d
        let Tn : ℝ[X] := Polynomial.Chebyshev.T ℝ (n : ℤ)
        have hTdeg : Tn.natDegree = n := by
          simp [Tn]
        have hTlc : Tn.leadingCoeff ≠ 0 := by
          rw [Polynomial.Chebyshev.leadingCoeff_T]
          norm_num only [Int.natAbs_natCast]
          positivity
        let c : ℝ := q.leadingCoeff / Tn.leadingCoeff
        have hc : c ≠ 0 := by
          dsimp [c]
          exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hq0) hTlc
        let head : ℝ[X] := Polynomial.C c * Tn
        have hhead_degree : q.degree = head.degree := by
          dsimp [head]
          rw [Polynomial.degree_C_mul hc]
          rw [Polynomial.degree_eq_natDegree hq0, hn, ← hTdeg]
          exact (Polynomial.degree_eq_natDegree (by
            dsimp [Tn]
            exact Polynomial.Chebyshev.T_ne_zero (R := ℝ) (n : ℤ))).symm
        have hhead_lc : q.leadingCoeff = head.leadingCoeff := by
          dsimp [head, c]
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
          field_simp [hTlc]
        let tail : ℝ[X] := q - head
        have htail_degree : tail.degree < q.degree := by
          exact Polynomial.degree_sub_lt hhead_degree hq0 hhead_lc
        have hhead_formula : HasRieszFormula d head := by
          dsimp [head]
          exact (hasRieszFormula_chebyshevT d n hd (by omega)).C_mul c
        have htail_formula : HasRieszFormula d tail := by
          by_cases htail0 : tail = 0
          · simpa [htail0] using hasRieszFormula_zero d
          have htail_nat : tail.natDegree < n := by
            rw [Polynomial.degree_eq_natDegree htail0,
              Polynomial.degree_eq_natDegree hq0, hn] at htail_degree
            exact_mod_cast htail_degree
          exact ih tail.natDegree htail_nat tail (by omega) rfl
        have hqeq : q = tail + head := by
          dsimp [tail]
          abel
        rw [hqeq]
        exact htail_formula.add hhead_formula
  exact hall p hdeg θ

/-- The signed coefficients in the exact formula have total absolute mass `d`. -/
theorem sum_abs_rieszSignedWeight (d : ℕ) (hd : 0 < d) :
    ∑ j ∈ Finset.range (2 * d), |rieszSignedWeight d j| = (d : ℝ) := by
  rw [← sum_riesz_midpoint_weights d hd]
  apply Finset.sum_congr rfl
  intro j hj
  rw [rieszSignedWeight, abs_div]
  have hden : 0 ≤
      4 * (d : ℝ) * Real.sin (rieszAngle d j / 2) ^ 2 := by positivity
  rw [abs_of_nonneg hden]
  simp only [abs_pow, abs_neg, abs_one, one_pow, one_div]
  congr 2
  dsimp [rieszAngle]
  have hdR : (d : ℝ) ≠ 0 := by positivity
  field_simp [hdR]
  ring_nf

/-- Sharp weighted Bernstein inequality obtained directly from the finite
Riesz formula. -/
theorem weighted_bernstein_of_pos (d : ℕ) (hd : 0 < d) (p : ℝ[X])
    (hdeg : p.natDegree ≤ d) (M : ℝ)
    (hbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| ≤ (d : ℝ) * M := by
  let θ := Real.arccos x
  have hcos : Real.cos θ = x := by
    dsimp [θ]
    exact Real.cos_arccos hx.1 hx.2
  have hformula := riesz_derivative_formula d hd p hdeg θ
  rw [hcos] at hformula
  have habs := congr_arg abs hformula
  simp only [abs_mul, abs_neg] at habs
  have hsin : Real.sin θ = Real.sqrt (1 - x ^ 2) := by
    dsimp [θ]
    exact Real.sin_arccos x
  rw [hsin, abs_of_nonneg (Real.sqrt_nonneg _)] at habs
  calc
    Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| =
        |∑ j ∈ Finset.range (2 * d), rieszSignedWeight d j *
          p.eval (Real.cos (θ + rieszAngle d j))| := habs
    _ ≤ ∑ j ∈ Finset.range (2 * d),
        |rieszSignedWeight d j *
          p.eval (Real.cos (θ + rieszAngle d j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (2 * d), |rieszSignedWeight d j| * M := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      gcongr
      exact hbound _ ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    _ = (d : ℝ) * M := by
      rw [← Finset.sum_mul, sum_abs_rieszSignedWeight d hd]

/-- Root-specialized sharp weighted Bernstein inequality, in the exact form
needed by the interpolation argument.  The finite Riesz formula actually proves
the stronger result without using the root hypothesis. -/
theorem root_weighted_bernstein (d : ℕ) (p : ℝ[X])
    (hdeg : p.natDegree ≤ d) (M : ℝ)
    (hbound : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) (_hroot : p.eval x = 0) :
    Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| ≤ (d : ℝ) * M := by
  cases d with
  | zero =>
      have hp0 : p.natDegree = 0 := Nat.eq_zero_of_le_zero hdeg
      rw [Polynomial.derivative_of_natDegree_zero hp0]
      simp
  | succ d =>
      exact weighted_bernstein_of_pos (d + 1) (by omega) p hdeg M hbound hx

end

end ClassicalBound
end Randy1153
