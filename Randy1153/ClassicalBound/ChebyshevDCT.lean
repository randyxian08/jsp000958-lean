import Randy1153.ClassicalBound.ChebyshevExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Bounded Chebyshev expansions from explicit orthogonality

This file proves the analytic input left transparent in
`ChebyshevExpansion.lean`.  The construction first uses the triangular
leading-coefficient structure of the first-kind Chebyshev polynomials to
obtain a finite exact expansion.  Continuous cosine orthogonality on
`[0, π]` then identifies each nonconstant coefficient with its explicit
Fourier--Chebyshev integral, giving the uniform bound `|c_k| ≤ 2 M`.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- Purely algebraic triangularity: every polynomial of natural degree at
most `d` has an exact expansion in `T_0, ..., T_d`. -/
private theorem exists_chebyshevExpansionOfNatDegreeLE (d : ℕ) (p : ℝ[X])
    (hpdeg : p.natDegree ≤ d) :
    ∃ c : Fin (d + 1) → ℝ,
      p = ∑ k : Fin (d + 1),
        Polynomial.C (c k) * Polynomial.Chebyshev.T ℝ (k.val : ℤ) := by
  induction d generalizing p with
  | zero =>
      refine ⟨fun _ ↦ p.coeff 0, ?_⟩
      rw [show p = Polynomial.C (p.coeff 0) from
        Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hpdeg)]
      simp
  | succ d ih =>
      let Ttop : ℝ[X] := Polynomial.Chebyshev.T ℝ ((d + 1 : ℕ) : ℤ)
      let top : ℝ := p.coeff (d + 1) / Ttop.leadingCoeff
      let q : ℝ[X] := p - Polynomial.C top * Ttop
      have hTdeg : Ttop.natDegree = d + 1 := by
        dsimp only [Ttop]
        rw [Polynomial.Chebyshev.natDegree_T]
        omega
      have hTlead : Ttop.leadingCoeff = (2 : ℝ) ^ d := by
        dsimp only [Ttop]
        rw [Polynomial.Chebyshev.leadingCoeff_T]
        congr 1
      have hTleadne : Ttop.leadingCoeff ≠ 0 := by
        rw [hTlead]
        positivity
      have hqdeg : q.natDegree ≤ d := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        by_cases htopN : N = d + 1
        · subst N
          dsimp only [q]
          rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
          rw [show Ttop.coeff (d + 1) = Ttop.leadingCoeff by
            rw [Polynomial.leadingCoeff, hTdeg]]
          dsimp only [top]
          field_simp
          ring
        · have hNd : d + 1 < N := by omega
          have hpzero : p.coeff N = 0 :=
            (Polynomial.natDegree_le_iff_coeff_eq_zero.mp hpdeg) N (by omega)
          have hTzero : Ttop.coeff N = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (hTdeg ▸ hNd)
          simp [q, hpzero, hTzero]
      obtain ⟨c, hc⟩ := ih q hqdeg
      let c' : Fin (d + 2) → ℝ := Fin.lastCases top c
      refine ⟨c', ?_⟩
      rw [Fin.sum_univ_castSucc]
      have hbelow :
          (∑ k : Fin (d + 1),
              Polynomial.C (c' k.castSucc) *
                Polynomial.Chebyshev.T ℝ (k.castSucc.val : ℤ)) = q := by
        simpa only [c', Fin.lastCases_castSucc, Fin.val_castSucc] using hc.symm
      rw [hbelow]
      simp only [c', Fin.lastCases_last, Fin.val_last]
      dsimp only [q, top, Ttop]
      ring

/-- Every nonzero integral frequency has zero cosine average on `[0, π]`. -/
private lemma integral_cos_int_mul_eq_zero (m : ℤ) (hm : m ≠ 0) :
    (∫ θ : ℝ in 0..Real.pi, Real.cos ((m : ℝ) * θ)) = 0 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos) (m : ℝ)
  rw [integral_cos] at h
  simp only [mul_zero, Real.sin_zero, sub_zero] at h
  rw [show (m : ℝ) * Real.pi = (m : ℤ) * Real.pi by rfl,
    Real.sin_int_mul_pi] at h
  exact (mul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hm)

/-- Product-to-sum under the interval integral. -/
private lemma two_mul_integral_cos_mul_cos (j k : ℕ) :
    2 * (∫ θ : ℝ in 0..Real.pi,
      Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
      (∫ θ : ℝ in 0..Real.pi,
        Real.cos ((((j : ℤ) - (k : ℤ)) : ℝ) * θ)) +
      ∫ θ : ℝ in 0..Real.pi,
        Real.cos ((((j : ℤ) + (k : ℤ)) : ℝ) * θ) := by
  let f : ℝ → ℝ := fun θ ↦
    Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)
  let g : ℝ → ℝ := fun θ ↦
    Real.cos ((((j : ℤ) - (k : ℤ)) : ℝ) * θ)
  let h : ℝ → ℝ := fun θ ↦
    Real.cos ((((j : ℤ) + (k : ℤ)) : ℝ) * θ)
  have hg : Continuous g :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hh : Continuous h :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  calc
    2 * (∫ θ : ℝ in 0..Real.pi, f θ) =
        ∫ θ : ℝ in 0..Real.pi, 2 * f θ := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ θ : ℝ in 0..Real.pi, (g θ + h θ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp only [f, g, h]
      simpa only [Int.cast_sub, Int.cast_add, Int.cast_natCast, sub_mul,
        add_mul, mul_assoc] using
        Real.two_mul_cos_mul_cos ((j : ℝ) * θ) ((k : ℝ) * θ)
    _ = (∫ θ : ℝ in 0..Real.pi, g θ) +
        ∫ θ : ℝ in 0..Real.pi, h θ := by
      rw [intervalIntegral.integral_add (hg.intervalIntegrable 0 Real.pi)
        (hh.intervalIntegrable 0 Real.pi)]

/-- Exact continuous cosine orthogonality on `[0, π]`. -/
private lemma integral_cos_mul_cos (j k : ℕ) :
    (∫ θ : ℝ in 0..Real.pi,
      Real.cos ((j : ℝ) * θ) * Real.cos ((k : ℝ) * θ)) =
      if j = k then (if j = 0 then Real.pi else Real.pi / 2) else 0 := by
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    by_cases hj : j = 0
    · subst j
      simp
    · rw [if_neg hj]
      have h := two_mul_integral_cos_mul_cos j j
      push_cast at h
      have hsum : (j : ℤ) + (j : ℤ) ≠ 0 := by omega
      have hsumzero := integral_cos_int_mul_eq_zero ((j : ℤ) + (j : ℤ)) hsum
      simp only [Int.cast_add, Int.cast_natCast] at hsumzero
      rw [hsumzero] at h
      simp only [sub_self, zero_mul, Real.cos_zero,
        intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one,
        ] at h
      linarith
  · rw [if_neg hjk]
    have hdiff : (j : ℤ) - (k : ℤ) ≠ 0 := by
      exact sub_ne_zero.mpr (Int.ofNat_injective.ne hjk)
    have hsum : (j : ℤ) + (k : ℤ) ≠ 0 := by
      intro hzero
      have : j = 0 ∧ k = 0 := by omega
      exact hjk (this.1.trans this.2.symm)
    have h := two_mul_integral_cos_mul_cos j k
    push_cast at h
    have hdiffzero := integral_cos_int_mul_eq_zero ((j : ℤ) - (k : ℤ)) hdiff
    have hsumzero := integral_cos_int_mul_eq_zero ((j : ℤ) + (k : ℤ)) hsum
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at hdiffzero hsumzero
    rw [hdiffzero, hsumzero] at h
    linarith

/-- Integrating an exact Chebyshev expansion against one cosine reduces to
the finite cosine Gram matrix. -/
private lemma integral_eval_cos_mul_cos_eq_sum {d : ℕ} {p : ℝ[X]}
    (c : Fin (d + 1) → ℝ)
    (hp : p = ∑ j : Fin (d + 1),
      Polynomial.C (c j) * Polynomial.Chebyshev.T ℝ (j.val : ℤ))
    (k : Fin (d + 1)) :
    (∫ θ : ℝ in 0..Real.pi,
      p.eval (Real.cos θ) * Real.cos ((k.val : ℝ) * θ)) =
      ∑ j : Fin (d + 1), c j *
        (∫ θ : ℝ in 0..Real.pi,
          Real.cos ((j.val : ℝ) * θ) *
            Real.cos ((k.val : ℝ) * θ)) := by
  have heval (θ : ℝ) :
      p.eval (Real.cos θ) * Real.cos ((k.val : ℝ) * θ) =
        ∑ j : Fin (d + 1), c j *
          (Real.cos ((j.val : ℝ) * θ) *
            Real.cos ((k.val : ℝ) * θ)) := by
    rw [hp, Polynomial.eval_finset_sum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.Chebyshev.T_real_cos, Int.cast_natCast]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  calc
    (∫ θ : ℝ in 0..Real.pi,
        p.eval (Real.cos θ) * Real.cos ((k.val : ℝ) * θ)) =
        ∫ θ : ℝ in 0..Real.pi,
          ∑ j : Fin (d + 1), c j *
            (Real.cos ((j.val : ℝ) * θ) *
              Real.cos ((k.val : ℝ) * θ)) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact heval θ
    _ = ∑ j : Fin (d + 1),
        ∫ θ : ℝ in 0..Real.pi, c j *
          (Real.cos ((j.val : ℝ) * θ) *
            Real.cos ((k.val : ℝ) * θ)) := by
      rw [intervalIntegral.integral_finset_sum]
      intro j hj
      apply Continuous.intervalIntegrable
      exact continuous_const.mul
        ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    _ = ∑ j : Fin (d + 1), c j *
        (∫ θ : ℝ in 0..Real.pi,
          Real.cos ((j.val : ℝ) * θ) *
            Real.cos ((k.val : ℝ) * θ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]

/-- Continuous orthogonality extracts the exact coefficient from any finite
Chebyshev expansion. -/
private lemma integral_eval_cos_mul_cos_eq_coefficient {d : ℕ} {p : ℝ[X]}
    (c : Fin (d + 1) → ℝ)
    (hp : p = ∑ j : Fin (d + 1),
      Polynomial.C (c j) * Polynomial.Chebyshev.T ℝ (j.val : ℤ))
    (k : Fin (d + 1)) :
    (∫ θ : ℝ in 0..Real.pi,
      p.eval (Real.cos θ) * Real.cos ((k.val : ℝ) * θ)) =
      if k.val = 0 then Real.pi * c k else (Real.pi / 2) * c k := by
  rw [integral_eval_cos_mul_cos_eq_sum c hp k]
  rw [Finset.sum_eq_single k]
  · rw [integral_cos_mul_cos]
    by_cases hk : k.val = 0
    · simp only [if_true, if_pos hk]
      ring
    · simp only [if_true, if_neg hk]
      ring
  · intro j hj hjk
    rw [integral_cos_mul_cos]
    have hval : j.val ≠ k.val := fun h ↦ hjk (Fin.ext h)
    rw [if_neg hval]
    simp
  · intro hknot
    exact (hknot (Finset.mem_univ k)).elim

/-- The Fourier--Chebyshev numerator is bounded by `M π` whenever `p` is
bounded by `M` on `[-1,1]`. -/
private lemma abs_integral_eval_cos_mul_cos_le {p : ℝ[X]} {M : ℝ}
    (hM : 0 ≤ M)
    (hsup : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (k : ℕ) :
    |∫ θ : ℝ in 0..Real.pi,
      p.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ)| ≤ M * Real.pi := by
  have hpoint (θ : ℝ) :
      ‖p.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ)‖ ≤ M := by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |p.eval (Real.cos θ)| * |Real.cos ((k : ℝ) * θ)| ≤ M * 1 := by
        exact mul_le_mul (hsup _ (Real.cos_mem_Icc θ))
          (Real.abs_cos_le_one _) (abs_nonneg _) hM
      _ = M := by ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := Real.pi) (C := M)
    (f := fun θ : ℝ ↦
      p.eval (Real.cos θ) * Real.cos ((k : ℝ) * θ))
    (fun θ hθ ↦ hpoint θ)
  simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos Real.pi_pos] using h

/-- Each coefficient of an exact degree-bounded Chebyshev expansion is at
most `2 M` in absolute value. -/
private lemma abs_chebyshevExpansion_coefficient_le_two_mul
    {d : ℕ} {p : ℝ[X]} {M : ℝ}
    (hM : 0 ≤ M)
    (hsup : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M)
    (c : Fin (d + 1) → ℝ)
    (hp : p = ∑ j : Fin (d + 1),
      Polynomial.C (c j) * Polynomial.Chebyshev.T ℝ (j.val : ℤ))
    (k : Fin (d + 1)) :
    |c k| ≤ 2 * M := by
  have hI := abs_integral_eval_cos_mul_cos_le hM hsup k.val
  have hcoeff := integral_eval_cos_mul_cos_eq_coefficient c hp k
  rw [hcoeff] at hI
  by_cases hk : k.val = 0
  · rw [if_pos hk, abs_mul, abs_of_pos Real.pi_pos] at hI
    have hcM : |c k| ≤ M := by
      apply (mul_le_mul_iff_right₀ Real.pi_pos).mp
      calc
        Real.pi * |c k| ≤ M * Real.pi := hI
        _ = Real.pi * M := by ring
    linarith
  · rw [if_neg hk, abs_mul, abs_of_pos (half_pos Real.pi_pos)] at hI
    apply (mul_le_mul_iff_right₀ (half_pos Real.pi_pos)).mp
    calc
      (Real.pi / 2) * |c k| ≤ M * Real.pi := hI
      _ = (Real.pi / 2) * (2 * M) := by ring

/-- Every real polynomial of natural degree at most `d`, uniformly bounded
by a nonnegative `M` on `[-1,1]`, has the bounded Chebyshev expansion used by
the cubic derivative argument. -/
theorem boundedChebyshevExpansion_of_natDegree_le_of_sup_le
    {d : ℕ} {p : ℝ[X]} {M : ℝ}
    (hM : 0 ≤ M) (hpdeg : p.natDegree ≤ d)
    (hsup : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ M) :
    BoundedChebyshevExpansion d p M := by
  obtain ⟨c, hp⟩ := exists_chebyshevExpansionOfNatDegreeLE d p hpdeg
  exact ⟨hpdeg, c, hp,
    fun k ↦ abs_chebyshevExpansion_coefficient_le_two_mul hM hsup c hp k⟩

end

end ClassicalBound
end Randy1153
