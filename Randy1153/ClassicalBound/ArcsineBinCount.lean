import Randy1153.ClassicalBound.ArcsinePartition

/-!
# A logarithmic count for the geometric arcsine partition

The geometric partition reaches scale one once

    q ^ K * cubicChebyshevFloor d >= 1.

For `q > 1` we choose `K` as the natural ceiling of the logarithmic
ratio.  The inverse-square lower bound on the cubic Chebyshev floor then
gives an explicit `O_q(log d)` estimate, with all ceiling losses visible.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- The least integer ceiling supplied by the logarithmic terminal-scale
calculation. -/
def arcsineGeometricExponent (d : ℕ) (q : ℝ) : ℕ :=
  ⌈Real.log (cubicChebyshevFloor d)⁻¹ / Real.log q⌉₊

/-- For positive degree, the cubic Chebyshev floor is at most one. -/
lemma cubicChebyshevFloor_le_one {d : ℕ} (hd : 1 ≤ d) :
    cubicChebyshevFloor d ≤ 1 := by
  unfold cubicChebyshevFloor
  have hden : 0 < (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := by
    positivity
  apply (div_le_iff₀ hden).2
  norm_num only [one_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith [sq_nonneg (d : ℝ)]

/-- The logarithmic ratio defining the exponent is nonnegative. -/
lemma arcsineGeometricExponent_ratio_nonneg {d : ℕ} {q : ℝ}
    (hd : 1 ≤ d) (hq : 1 < q) :
    0 ≤ Real.log (cubicChebyshevFloor d)⁻¹ / Real.log q := by
  have hc0 := cubicChebyshevFloor_pos d
  have hcinv : 1 ≤ (cubicChebyshevFloor d)⁻¹ :=
    (one_le_inv₀ hc0).2 (cubicChebyshevFloor_le_one hd)
  exact div_nonneg (Real.log_nonneg hcinv) (Real.log_pos hq).le

/-- The ceiling exponent really reaches the terminal scale. -/
theorem arcsineGeometricExponent_terminal {d : ℕ} {q : ℝ}
    (_hd : 1 ≤ d) (hq : 1 < q) :
    1 ≤ q ^ arcsineGeometricExponent d q * cubicChebyshevFloor d := by
  let c := cubicChebyshevFloor d
  let K := arcsineGeometricExponent d q
  have hc0 : 0 < c := cubicChebyshevFloor_pos d
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hceil : Real.log c⁻¹ / Real.log q ≤ (K : ℝ) := by
    exact Nat.le_ceil _
  have hlogs : Real.log c⁻¹ ≤ (K : ℝ) * Real.log q :=
    (div_le_iff₀ hlogq).1 hceil
  have hexp : c⁻¹ ≤ q ^ K := by
    have h := Real.exp_le_exp.mpr hlogs
    rw [Real.exp_log (inv_pos.mpr hc0), Real.exp_nat_mul,
      Real.exp_log (by linarith : 0 < q)] at h
    exact h
  calc
    1 = c⁻¹ * c := by field_simp
    _ ≤ q ^ K * c := mul_le_mul_of_nonneg_right hexp hc0.le
    _ = q ^ arcsineGeometricExponent d q * cubicChebyshevFloor d := rfl

/-- Exact ceiling loss: the number `K+1` of half-bins is at most the
unrounded logarithmic ratio plus two. -/
theorem arcsineGeometricExponent_add_one_le_logRatio_add_two
    {d : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q) :
    ((arcsineGeometricExponent d q + 1 : ℕ) : ℝ) ≤
      Real.log (cubicChebyshevFloor d)⁻¹ / Real.log q + 2 := by
  have hratio := arcsineGeometricExponent_ratio_nonneg hd hq
  have hceil := Nat.ceil_lt_add_one hratio
  rw [arcsineGeometricExponent]
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

/-- The reciprocal cubic floor is bounded above by `2 d^2`. -/
lemma cubicChebyshevFloor_inv_le_two_mul_sq {d : ℕ} (hd : 1 ≤ d) :
    (cubicChebyshevFloor d)⁻¹ ≤ 2 * (d : ℝ) ^ 2 := by
  have hA : 0 < 2 * (d : ℝ) ^ 2 := by
    positivity
  have hc0 : 0 < cubicChebyshevFloor d := cubicChebyshevFloor_pos d
  simpa [one_div] using
    (one_div_le hA hc0).1
      (by simpa [one_div] using inv_two_mul_sq_le_cubicChebyshevFloor hd)

/-- Finite logarithmic half-bin count.  This is the explicit estimate
behind the `O_q(log d)` assertion; no asymptotic notation is hidden. -/
theorem arcsineGeometricExponent_add_one_le_logDegree
    {d : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q) :
    ((arcsineGeometricExponent d q + 1 : ℕ) : ℝ) ≤
      (Real.log 2 + 2 * Real.log (d : ℝ)) / Real.log q + 2 := by
  have hc0 : 0 < cubicChebyshevFloor d := cubicChebyshevFloor_pos d
  have hA : 0 < 2 * (d : ℝ) ^ 2 := by positivity
  have hlog : Real.log (cubicChebyshevFloor d)⁻¹ ≤
      Real.log (2 * (d : ℝ) ^ 2) :=
    Real.log_le_log (inv_pos.mpr hc0)
      (cubicChebyshevFloor_inv_le_two_mul_sq hd)
  have hlogq : 0 < Real.log q := Real.log_pos hq
  calc
    ((arcsineGeometricExponent d q + 1 : ℕ) : ℝ) ≤
        Real.log (cubicChebyshevFloor d)⁻¹ / Real.log q + 2 :=
      arcsineGeometricExponent_add_one_le_logRatio_add_two hd hq
    _ ≤ Real.log (2 * (d : ℝ) ^ 2) / Real.log q + 2 := by
      gcongr
    _ = (Real.log 2 + 2 * Real.log (d : ℝ)) / Real.log q + 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (by positivity : (d : ℝ) ^ 2 ≠ 0), Real.log_pow]
      norm_num

/-- A literal constant-times-`(log d + 1)` version of the half-bin count.
The coefficient depends only on the fixed geometric ratio `q`. -/
theorem arcsineGeometricExponent_add_one_le_constant_mul_logDegree
    {d : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q) :
    ((arcsineGeometricExponent d q + 1 : ℕ) : ℝ) ≤
      ((Real.log 2 + 2) / Real.log q + 2) *
        (Real.log (d : ℝ) + 1) := by
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hdR
  have ha : 0 ≤ Real.log 2 / Real.log q := by positivity
  have hb : 0 ≤ 2 / Real.log q := by positivity
  have hsurplus :
      0 ≤ Real.log 2 / Real.log q * Real.log (d : ℝ) +
        2 * Real.log (d : ℝ) +
        2 / Real.log q :=
    add_nonneg
      (add_nonneg (mul_nonneg ha hlogd) (mul_nonneg (by norm_num) hlogd)) hb
  have hidentity :
      (((Real.log 2 + 2) / Real.log q + 2) *
          (Real.log (d : ℝ) + 1)) -
        ((Real.log 2 + 2 * Real.log (d : ℝ)) / Real.log q + 2) =
      Real.log 2 / Real.log q * Real.log (d : ℝ) +
        2 * Real.log (d : ℝ) +
        2 / Real.log q := by
    ring
  calc
    ((arcsineGeometricExponent d q + 1 : ℕ) : ℝ) ≤
        (Real.log 2 + 2 * Real.log (d : ℝ)) / Real.log q + 2 :=
      arcsineGeometricExponent_add_one_le_logDegree hd hq
    _ ≤ ((Real.log 2 + 2) / Real.log q + 2) *
          (Real.log (d : ℝ) + 1) := by
      linarith

/-- The corresponding reflected construction has twice as many bins. -/
theorem two_mul_arcsineGeometricExponent_add_one_le_logDegree
    {d : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q) :
    ((2 * (arcsineGeometricExponent d q + 1) : ℕ) : ℝ) ≤
      2 * ((Real.log 2 + 2 * Real.log (d : ℝ)) / Real.log q + 2) := by
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left
    (arcsineGeometricExponent_add_one_le_logDegree hd hq) (by norm_num)

/-- Constant-times-log bound for the total number of reflected bins. -/
theorem two_mul_arcsineGeometricExponent_add_one_le_constant_mul_logDegree
    {d : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q) :
    ((2 * (arcsineGeometricExponent d q + 1) : ℕ) : ℝ) ≤
      2 * (((Real.log 2 + 2) / Real.log q + 2) *
        (Real.log (d : ℝ) + 1)) := by
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left
    (arcsineGeometricExponent_add_one_le_constant_mul_logDegree hd hq)
    (by norm_num)

/-- The logarithmic exponent instantiates the explicit half-partition. -/
def logarithmicHalfArcsinePartition (d : ℕ) (q : ℝ)
    (hd : 1 ≤ d) (hq : 1 < q) :
    HalfArcsinePartition d (arcsineGeometricExponent d q + 1) q :=
  geometricHalfArcsinePartition d (arcsineGeometricExponent d q) q hq
    (arcsineGeometricExponent_terminal hd hq)

end

end ClassicalBound
end Randy1153
