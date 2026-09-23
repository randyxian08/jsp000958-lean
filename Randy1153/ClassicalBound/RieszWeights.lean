import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# Normalization of the finite Riesz weights

For `d > 0`, the `2d` midpoint angles

`((2j+1)π)/(4d)`, `0 ≤ j < 2d`,

are the angles of the roots of `T_{2d}`.  Applying the logarithmic derivative
of that polynomial at `1` and `-1` computes the sum of the reciprocal squared
sines at those angles.  This is precisely the positive-weight normalization
in the finite Riesz derivative formula.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

private lemma chebyshevT_splits_real (n : ℕ) :
    (Polynomial.Chebyshev.T ℝ n).Splits := by
  rw [Polynomial.splits_iff_card_roots,
    Polynomial.Chebyshev.roots_T_real,
    Polynomial.Chebyshev.natDegree_T]
  change (Finset.image
    (fun k : ℕ ↦ Real.cos ((2 * (k : ℝ) + 1) * Real.pi / (2 * (n : ℝ))))
    (Finset.range n)).card = n
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a ha b hb hab
    have hnodup := Polynomial.Chebyshev.roots_T_real_nodup n
    exact Multiset.inj_on_of_nodup_map hnodup a (by simpa using ha) b
      (by simpa using hb) hab

private lemma chebyshevT_root_sum_one (n : ℕ) :
    ((Polynomial.Chebyshev.T ℝ n).roots.map
      (fun r : ℝ ↦ 1 / (1 - r))).sum = (n : ℝ) ^ 2 := by
  have hlog := (chebyshevT_splits_real n).eval_derivative_div_eval_of_ne_zero
    (x := (1 : ℝ)) (by simp [Polynomial.Chebyshev.T_eval_one])
  rw [Polynomial.Chebyshev.T_eval_one,
    Polynomial.Chebyshev.derivative_T_eval_one, div_one] at hlog
  norm_num only [Int.cast_natCast] at hlog
  exact hlog.symm

private lemma chebyshevT_even_root_sum_neg_one (d : ℕ) :
    ((Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots.map
      (fun r : ℝ ↦ 1 / (1 + r))).sum = ((2 * d : ℕ) : ℝ) ^ 2 := by
  let n : ℕ := 2 * d
  have hnNegOnePow : ((n : ℤ).negOnePow : ℤ) = 1 := by
    have hu : (n : ℤ).negOnePow = (1 : ℤˣ) := by
      apply Int.negOnePow_even
      exact ⟨(d : ℤ), by simp [n]; ring⟩
    exact congr_arg Units.val hu
  have hnSubNegOnePow : (((n : ℤ) - 1).negOnePow : ℤ) = -1 := by
    have hu : ((n : ℤ) - 1).negOnePow = (-1 : ℤˣ) := by
      rw [Int.negOnePow_sub]
      have hEvenUnit : (n : ℤ).negOnePow = 1 := by
        apply Int.negOnePow_even
        exact ⟨(d : ℤ), by simp [n]; ring⟩
      rw [hEvenUnit, Int.negOnePow_one, one_mul]
    exact congr_arg Units.val hu
  have hlog := (chebyshevT_splits_real n).eval_derivative_div_eval_of_ne_zero
    (x := (-1 : ℝ)) (by
      rw [Polynomial.Chebyshev.T_eval_neg_one, hnNegOnePow]
      norm_num)
  have hderiv :
      (Polynomial.Chebyshev.T ℝ n).derivative.eval (-1) = -((n : ℝ) ^ 2) := by
    rw [Polynomial.Chebyshev.T_derivative_eq_U, Polynomial.eval_mul,
      Polynomial.eval_intCast, Polynomial.Chebyshev.U_eval_neg_one,
      hnSubNegOnePow]
    push_cast
    ring
  rw [hderiv, Polynomial.Chebyshev.T_eval_neg_one, hnNegOnePow] at hlog
  norm_num only [Int.cast_one, div_one] at hlog
  have hneg :
      ((Polynomial.Chebyshev.T ℝ n).roots.map
        (fun r : ℝ ↦ 1 / (-1 - r))).sum = -((n : ℝ) ^ 2) := hlog.symm
  have hmap :
      ((Polynomial.Chebyshev.T ℝ n).roots.map
        (fun r : ℝ ↦ 1 / (-1 - r))).sum =
        -((Polynomial.Chebyshev.T ℝ n).roots.map
          (fun r : ℝ ↦ 1 / (1 + r))).sum := by
    rw [← Multiset.sum_map_neg]
    apply congr_arg Multiset.sum
    apply Multiset.map_congr rfl
    intro r hr
    simp only [one_div]
    rw [show -1 - r = -(1 + r) by ring, inv_neg]
  rw [hmap] at hneg
  have := neg_inj.mp hneg
  simpa only [n] using this

private lemma chebyshevT_even_root_cosecant_sum (d : ℕ) :
    ((Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots.map
      (fun r : ℝ ↦ 1 / (1 - r ^ 2))).sum = ((2 * d : ℕ) : ℝ) ^ 2 := by
  have hplus :
      ((Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots.map
        (fun r : ℝ ↦ 1 / (1 - r))).sum = ((2 * d : ℕ) : ℝ) ^ 2 :=
    chebyshevT_root_sum_one (2 * d)
  have hminus := chebyshevT_even_root_sum_neg_one d
  calc
    ((Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots.map
        (fun r : ℝ ↦ 1 / (1 - r ^ 2))).sum =
        (1 / 2 : ℝ) *
          (((Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots.map
              (fun r : ℝ ↦ 1 / (1 - r))).sum +
            ((Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots.map
              (fun r : ℝ ↦ 1 / (1 + r))).sum) := by
      rw [← Multiset.sum_map_add, ← Multiset.sum_map_mul_left]
      apply congr_arg Multiset.sum
      apply Multiset.map_congr rfl
      intro r hr
      have hrOne : r ≠ 1 := by
        intro h
        subst r
        have hnot :
            (1 : ℝ) ∉ (Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).roots := by
          simp
        exact hnot hr
      have hrNegOne : r ≠ -1 := by
        intro h
        subst r
        have hroot := (Polynomial.mem_roots'
          (p := Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ))).mp hr
        have heval :
            (Polynomial.Chebyshev.T ℝ ((2 * d : ℕ) : ℤ)).eval (-1) = 0 := by
          simpa only [Polynomial.IsRoot] using hroot.2
        rw [Polynomial.Chebyshev.T_eval_neg_one] at heval
        have hpow : ((((2 * d : ℕ) : ℤ).negOnePow : ℤ)) = 1 := by
          have hu : (((2 * d : ℕ) : ℤ).negOnePow) = (1 : ℤˣ) := by
            apply Int.negOnePow_even
            exact ⟨(d : ℤ), by push_cast; ring⟩
          exact congr_arg Units.val hu
        rw [hpow] at heval
        norm_num at heval
      have hOneSub : 1 - r ≠ 0 := sub_ne_zero.mpr hrOne.symm
      have hOneAdd : 1 + r ≠ 0 := by
        intro h
        apply hrNegOne
        linarith
      have hSq : 1 - r ^ 2 ≠ 0 := by
        intro h
        have hrsq : r ^ 2 = 1 := by linarith
        rcases sq_eq_one_iff.mp hrsq with h | h
        · exact hrOne h
        · exact hrNegOne h
      field_simp [hOneSub, hOneAdd, hSq]
      ring
    _ = ((2 * d : ℕ) : ℝ) ^ 2 := by rw [hplus, hminus]; ring

/-- The positive coefficients in the `2d`-point Riesz derivative formula have
total mass exactly `d`.
-/
theorem sum_riesz_midpoint_weights (d : ℕ) (hd : 0 < d) :
    ∑ j ∈ Finset.range (2 * d),
        1 / (4 * (d : ℝ) *
          Real.sin (((2 * (j : ℝ) + 1) * Real.pi) / (4 * (d : ℝ))) ^ 2) =
      (d : ℝ) := by
  let angle : ℕ → ℝ := fun j ↦
    ((2 * (j : ℝ) + 1) * Real.pi) / (4 * (d : ℝ))
  have hinj : Set.InjOn
      (fun j : ℕ ↦ Real.cos
        ((2 * (j : ℝ) + 1) * Real.pi / (2 * ((2 * d : ℕ) : ℝ))))
      (Finset.range (2 * d)) := by
    have hnodup := Polynomial.Chebyshev.roots_T_real_nodup (2 * d)
    intro a ha b hb hab
    exact Multiset.inj_on_of_nodup_map hnodup a (by simpa using ha) b
      (by simpa using hb) hab
  have hroots := chebyshevT_even_root_cosecant_sum d
  rw [Polynomial.Chebyshev.roots_T_real] at hroots
  change (∑ r ∈ Finset.image
      (fun j : ℕ ↦ Real.cos
        ((2 * (j : ℝ) + 1) * Real.pi / (2 * ((2 * d : ℕ) : ℝ))))
      (Finset.range (2 * d)), 1 / (1 - r ^ 2)) = ((2 * d : ℕ) : ℝ) ^ 2 at hroots
  rw [Finset.sum_image hinj] at hroots
  have hangle (j : ℕ) :
      ((2 * (j : ℝ) + 1) * Real.pi / (2 * ((2 * d : ℕ) : ℝ))) = angle j := by
    dsimp [angle]
    push_cast
    ring
  have hcsc :
      (∑ j ∈ Finset.range (2 * d), 1 / Real.sin (angle j) ^ 2) =
        ((2 * d : ℕ) : ℝ) ^ 2 := by
    rw [← hroots]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hangle, Real.sin_sq]
  change (∑ j ∈ Finset.range (2 * d),
    1 / (4 * (d : ℝ) * Real.sin (angle j) ^ 2)) = (d : ℝ)
  calc
    (∑ j ∈ Finset.range (2 * d),
        1 / (4 * (d : ℝ) * Real.sin (angle j) ^ 2)) =
        (4 * (d : ℝ))⁻¹ *
          (∑ j ∈ Finset.range (2 * d), (Real.sin (angle j) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [one_div, mul_inv_rev]
      ring
    _ = (d : ℝ) := by
      rw [show (∑ j ∈ Finset.range (2 * d), (Real.sin (angle j) ^ 2)⁻¹) =
        ((2 * d : ℕ) : ℝ) ^ 2 by simpa only [one_div] using hcsc]
      have hd0 : (d : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

end

end ClassicalBound
end Randy1153
