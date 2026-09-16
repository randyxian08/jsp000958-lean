import Randy1153.ClassicalBound.ChebyshevDerivative
import Randy1153.ClassicalBound.PairEnergy

/-!
# Bounded Chebyshev expansions and cubic derivative control

This file records a transparent finite interface for the missing coefficient
estimate in the classical argument.  Once a degree-`d` polynomial is given
an exact first-kind Chebyshev expansion whose coefficients are bounded by
`2 M`, the already checked estimate `|T_k'| ≤ k²` gives the cubic derivative
bound by summing the first `d` squares.

Existence of such a bounded expansion is not asserted here.  Nor is the
root-weighted Bernstein inequality used in the final optional bridge.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- A degree-at-most-`d` polynomial together with an exact Chebyshev
expansion and the uniform coefficient estimate `|c_k| ≤ 2 M`.

The zeroth coefficient could be bounded more sharply, but its derivative is
zero, so the uniform bound is exactly sufficient for the argument below. -/
def BoundedChebyshevExpansion (d : ℕ) (p : ℝ[X]) (M : ℝ) : Prop :=
  p.natDegree ≤ d ∧
    ∃ c : Fin (d + 1) → ℝ,
      p = ∑ k : Fin (d + 1),
        Polynomial.C (c k) * Polynomial.Chebyshev.T ℝ (k.val : ℤ) ∧
      ∀ k : Fin (d + 1), |c k| ≤ 2 * M

/-- Exact real sum of the squares `0² + ... + d²`. -/
lemma sum_fin_cast_sq (d : ℕ) :
    (∑ k : Fin (d + 1), (k.val : ℝ) ^ 2) =
      (d : ℝ) * ((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ) / 6 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one]
      rw [ih]
      push_cast
      ring

/-- A concrete bounded Chebyshev expansion gives the cubic derivative
estimate on the entire source interval. -/
theorem abs_derivative_le_cubic_of_boundedChebyshevExpansion
    {d : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hM : 0 ≤ M) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hexp : BoundedChebyshevExpansion d p M) :
    |p.derivative.eval x| ≤
      M * (d : ℝ) * ((d + 1 : ℕ) : ℝ) *
        ((2 * d + 1 : ℕ) : ℝ) / 3 := by
  rcases hexp.2 with ⟨c, hp, hc⟩
  rw [hp]
  simp only [Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  calc
    |∑ k : Fin (d + 1),
        c k * (Polynomial.Chebyshev.T ℝ (k.val : ℤ)).derivative.eval x| ≤
        ∑ k : Fin (d + 1),
          |c k *
            (Polynomial.Chebyshev.T ℝ (k.val : ℤ)).derivative.eval x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin (d + 1),
        |c k| *
          |(Polynomial.Chebyshev.T ℝ (k.val : ℤ)).derivative.eval x| := by
      simp only [abs_mul]
    _ ≤ ∑ k : Fin (d + 1), (2 * M) * (k.val : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul (hc k)
        (abs_eval_derivative_chebyshevT_le k.val hx)
        (abs_nonneg _) (by positivity)
    _ = (2 * M) * ∑ k : Fin (d + 1), (k.val : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
    _ = M * (d : ℝ) * ((d + 1 : ℕ) : ℝ) *
        ((2 * d + 1 : ℕ) : ℝ) / 3 := by
      rw [sum_fin_cast_sq]
      ring

/-- The exact cubic-Chebyshev floor converts the cubic derivative estimate
into the endpoint branch of the clipped Bernstein bound. -/
lemma cubicChebyshevFloor_mul_abs_derivative_le_degree_mul
    {d : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hcubic : |p.derivative.eval x| ≤
      M * (d : ℝ) * ((d + 1 : ℕ) : ℝ) *
        ((2 * d + 1 : ℕ) : ℝ) / 3) :
    cubicChebyshevFloor d * |p.derivative.eval x| ≤ (d : ℝ) * M := by
  calc
    cubicChebyshevFloor d * |p.derivative.eval x| ≤
        cubicChebyshevFloor d *
          (M * (d : ℝ) * ((d + 1 : ℕ) : ℝ) *
            ((2 * d + 1 : ℕ) : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hcubic (cubicChebyshevFloor_nonneg d)
    _ = M * (cubicChebyshevFloor d *
        ((d : ℝ) * ((d + 1 : ℕ) : ℝ) *
          ((2 * d + 1 : ℕ) : ℝ) / 3)) := by ring
    _ = M * (d : ℝ) := by
      rw [cubicChebyshevFloor_mul_cubicDerivativeFactor]
    _ = (d : ℝ) * M := by ring

/-- A bounded expansion supplies the floor branch directly. -/
theorem cubicChebyshevFloor_mul_abs_derivative_le_of_boundedExpansion
    {d : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hM : 0 ≤ M) (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (hexp : BoundedChebyshevExpansion d p M) :
    cubicChebyshevFloor d * |p.derivative.eval x| ≤ (d : ℝ) * M :=
  cubicChebyshevFloor_mul_abs_derivative_le_degree_mul
    (abs_derivative_le_cubic_of_boundedChebyshevExpansion hM hx hexp)

/-- The other, genuinely sharp branch required at an individual point. -/
def RootWeightedBernsteinAt (d : ℕ) (p : ℝ[X]) (x M : ℝ) : Prop :=
  Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| ≤ (d : ℝ) * M

/-- If the bounded expansion and the root-weighted inequality are both
provided, the two branches combine into the existing transparent clipped
Bernstein interface.  Neither input is asserted to exist. -/
theorem pointwiseClippedBernsteinAt_of_boundedExpansion_of_rootWeighted
    {d : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hM : 0 ≤ M) (hexp : BoundedChebyshevExpansion d p M)
    (hroot : RootWeightedBernsteinAt d p x M) :
    PointwiseClippedBernsteinAt d p x M := by
  intro hd hpdeg hx hsup
  rw [clippedArcsineScale,
    max_mul_of_nonneg _ _ (abs_nonneg (p.derivative.eval x))]
  apply max_le
  · exact hroot
  · exact cubicChebyshevFloor_mul_abs_derivative_le_of_boundedExpansion
      hM hx hexp

end

end ClassicalBound
end Randy1153
