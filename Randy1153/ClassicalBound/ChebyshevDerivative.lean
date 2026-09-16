import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Elementary Chebyshev derivative control on `[-1, 1]`

This file proves the two elementary estimates needed when Chebyshev
polynomials are used as test polynomials.  The proof is deliberately direct:
the second-kind estimate comes from the trigonometric evaluation formula and
an induction for integer multiples of sine, including the endpoints where
division by `sin θ` is unavailable.  The first-kind derivative estimate then
follows from Mathlib's exact derivative identity.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- The sine of a natural multiple is at most that multiple times the original sine.

This is the elementary triangle-inequality estimate obtained by induction from
the sine addition formula.  It is stated without any restriction on `θ`.
-/
lemma abs_sin_nat_mul_le (m : ℕ) (θ : ℝ) :
    |Real.sin ((m : ℝ) * θ)| ≤ (m : ℝ) * |Real.sin θ| := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.cast_succ, add_mul, one_mul, Real.sin_add]
      calc
        |Real.sin ((m : ℝ) * θ) * Real.cos θ +
            Real.cos ((m : ℝ) * θ) * Real.sin θ| ≤
            |Real.sin ((m : ℝ) * θ) * Real.cos θ| +
              |Real.cos ((m : ℝ) * θ) * Real.sin θ| := abs_add_le _ _
        _ = |Real.sin ((m : ℝ) * θ)| * |Real.cos θ| +
              |Real.cos ((m : ℝ) * θ)| * |Real.sin θ| := by
                rw [abs_mul, abs_mul]
        _ ≤ ((m : ℝ) * |Real.sin θ|) * 1 + 1 * |Real.sin θ| := by
              gcongr
              · exact Real.abs_cos_le_one θ
              · exact Real.abs_cos_le_one ((m : ℝ) * θ)
        _ = ((m : ℝ) + 1) * |Real.sin θ| := by ring

/-- On `[-1,1]`, the `k`-th Chebyshev polynomial of the second kind has
absolute value at most `k + 1`.

At interior points this is `U_k(cos θ) sin θ = sin((k+1)θ)` followed by
`abs_sin_nat_mul_le`.  If `sin θ = 0`, the point is an endpoint and the
explicit endpoint evaluations give equality in absolute value.
-/
theorem abs_eval_chebyshevU_le (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.U ℝ k).eval x| ≤ (k : ℝ) + 1 := by
  let θ := Real.arccos x
  have hxcos : Real.cos θ = x := by
    exact Real.cos_arccos hx.1 hx.2
  by_cases hs : Real.sin θ = 0
  · have hx_sq : x ^ 2 = 1 := by
      calc
        x ^ 2 = Real.cos θ ^ 2 := by rw [hxcos]
        _ = 1 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    rcases (sq_eq_one_iff.mp hx_sq) with rfl | rfl
    · rw [Polynomial.Chebyshev.U_eval_one]
      norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [abs_of_nonneg (by positivity)]
    · rw [Polynomial.Chebyshev.U_eval_neg_one, abs_mul]
      have hsign : |((((k : ℤ).negOnePow : ℤ) : ℝ))| = 1 := by
        rw [← Int.cast_abs, Int.abs_negOnePow]
        norm_num
      rw [hsign, one_mul]
      norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one]
      rw [abs_of_nonneg (by positivity)]
  · have htrig := Polynomial.Chebyshev.U_real_cos θ (k : ℤ)
    rw [hxcos] at htrig
    norm_num only [Int.cast_add, Int.cast_natCast, Int.cast_one] at htrig
    have hsin := abs_sin_nat_mul_le (k + 1) θ
    norm_num only [Nat.cast_add, Nat.cast_one] at hsin
    have hmul :
        |(Polynomial.Chebyshev.U ℝ k).eval x| * |Real.sin θ| ≤
          ((k : ℝ) + 1) * |Real.sin θ| := by
      rw [← abs_mul, htrig]
      exact hsin
    exact le_of_mul_le_mul_right hmul (abs_pos.mpr hs)

/-- On `[-1,1]`, the derivative of the `k`-th Chebyshev polynomial of the
first kind has absolute value at most `k²`.
-/
theorem abs_eval_derivative_chebyshevT_le (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(Polynomial.Chebyshev.T ℝ k).derivative.eval x| ≤ (k : ℝ) ^ 2 := by
  cases k with
  | zero => simp
  | succ k =>
      rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul,
        Polynomial.eval_intCast, abs_mul]
      rw [show (↑(k + 1) : ℤ) - 1 = (k : ℤ) by omega]
      norm_num only [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
      rw [abs_of_nonneg (by positivity)]
      push_cast
      have hU := abs_eval_chebyshevU_le k hx
      calc
        ((k : ℝ) + 1) * |(Polynomial.Chebyshev.U ℝ k).eval x| ≤
            ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
              gcongr
        _ = ((k : ℝ) + 1) ^ 2 := by ring

end

end ClassicalBound
end Randy1153
