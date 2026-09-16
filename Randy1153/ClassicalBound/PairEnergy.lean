import Randy1153.ClassicalBound.Sharp
import Randy1153.CompactMax
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Clipped pair energy and derivative-row polynomials

This file isolates the finite algebraic half of a classical sharp
Bernstein--Randy--Turán argument.  For every interpolation node `x_j`, the
polynomial `signedDerivativeRowPolynomial nodes j` assigns to the other
nodes the signs of the corresponding cross derivatives.  Its derivative at
`x_j` is therefore the full absolute derivative-row mass.

The final estimate in this file is conditional on the explicitly stated
pointwise clipped Bernstein inequality, applied only to these concrete row
polynomials.  No analytic Bernstein theorem is asserted here.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- The exact positive endpoint floor compatible with the cubic
Chebyshev-coefficient derivative estimate

`|p'| ≤ M * d * (d + 1) * (2 * d + 1) / 3`.

Multiplying that estimate by this floor leaves precisely `d * M`. -/
def cubicChebyshevFloor (d : ℕ) : ℝ :=
  3 / (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ))

lemma cubicChebyshevFloor_pos (d : ℕ) : 0 < cubicChebyshevFloor d := by
  unfold cubicChebyshevFloor
  positivity

lemma cubicChebyshevFloor_nonneg (d : ℕ) : 0 ≤ cubicChebyshevFloor d :=
  (cubicChebyshevFloor_pos d).le

/-- Exact cancellation with the cubic derivative factor. -/
lemma cubicChebyshevFloor_mul_cubicDerivativeFactor (d : ℕ) :
    cubicChebyshevFloor d *
        ((d : ℝ) * ((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ) / 3) =
      (d : ℝ) := by
  unfold cubicChebyshevFloor
  have h₁ : (((d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h₂ : (((2 * d + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp

/-- For positive degrees, the exact floor is bounded below by a simple
inverse-square scale. -/
lemma inv_two_mul_sq_le_cubicChebyshevFloor {d : ℕ} (hd : 1 ≤ d) :
    (2 * (d : ℝ) ^ 2)⁻¹ ≤ cubicChebyshevFloor d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdenpos :
      0 < (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := by
    positivity
  have hlargepos : 0 < 6 * (d : ℝ) ^ 2 := by positivity
  have hdenle :
      (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) ≤
        6 * (d : ℝ) ^ 2 := by
    push_cast
    nlinarith
  calc
    (2 * (d : ℝ) ^ 2)⁻¹ = 3 / (6 * (d : ℝ) ^ 2) := by
      field_simp
      ring
    _ ≤ 3 / (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := by
      apply (div_le_div_iff₀ hlargepos hdenpos).2
      nlinarith
    _ = cubicChebyshevFloor d := rfl

/-- For positive degrees, the exact floor is also bounded above by the
matching inverse-square scale up to the factor three. -/
lemma cubicChebyshevFloor_le_three_mul_inv_two_mul_sq {d : ℕ} (hd : 1 ≤ d) :
    cubicChebyshevFloor d ≤ 3 * (2 * (d : ℝ) ^ 2)⁻¹ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.zero_lt_of_lt hd)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdenpos :
      0 < (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := by
    positivity
  have hsmallpos : 0 < 2 * (d : ℝ) ^ 2 := by positivity
  have hdenge :
      2 * (d : ℝ) ^ 2 ≤
        (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith
  calc
    cubicChebyshevFloor d =
        3 / (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := rfl
    _ ≤ 3 / (2 * (d : ℝ) ^ 2) := by
      apply (div_le_div_iff₀ hdenpos hsmallpos).2
      nlinarith
    _ = 3 * (2 * (d : ℝ) ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-- The arcsine scale with its endpoint degeneration clipped at the exact
positive cubic-Chebyshev floor. -/
def clippedArcsineScale (d : ℕ) (x : ℝ) : ℝ :=
  max (Real.sqrt (1 - x ^ 2)) (cubicChebyshevFloor d)

lemma clippedArcsineScale_nonneg (d : ℕ) (x : ℝ) :
    0 ≤ clippedArcsineScale d x := by
  exact (Real.sqrt_nonneg _).trans (le_max_left _ _)

lemma clippedArcsineScale_pos (d : ℕ) (x : ℝ) :
    0 < clippedArcsineScale d x := by
  exact (cubicChebyshevFloor_pos d).trans_le (le_max_right _ _)

/-- The sign attached to the `k`th cardinal derivative in the row based at
`x_j`. -/
def derivativeRowSign {n : ℕ} (nodes : OrderedNodes n) (j k : Fin n) : ℝ :=
  interpolationSign
    ((lagrangeBasis nodes.toNodeFamily k).derivative.eval (nodes.point j))

/-- The signed derivative-row polynomial based at `x_j`:

`P_j = ∑_{k ≠ j} sign(ℓ_k'(x_j)) ℓ_k`.
-/
def signedDerivativeRowPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (j : Fin n) : ℝ[X] :=
  ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
    Polynomial.C (derivativeRowSign nodes j k) *
      lagrangeBasis nodes.toNodeFamily k

lemma natDegree_signedDerivativeRowPolynomial_le {n : ℕ}
    (nodes : OrderedNodes n) (j : Fin n) :
    (signedDerivativeRowPolynomial nodes j).natDegree ≤ n - 1 := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (natDegree_lagrangeBasis_le nodes.toNodeFamily k)

lemma degree_signedDerivativeRowPolynomial_lt {n : ℕ}
    (nodes : OrderedNodes n) (j : Fin n) :
    (signedDerivativeRowPolynomial nodes j).degree < n := by
  by_cases hp : signedDerivativeRowPolynomial nodes j = 0
  · simp [hp]
  · rw [← Polynomial.natDegree_lt_iff_degree_lt hp]
    have hn : 0 < n := Fin.pos j
    exact (natDegree_signedDerivativeRowPolynomial_le nodes j).trans_lt (by omega)

@[simp]
lemma signedDerivativeRowPolynomial_eval_self {n : ℕ}
    (nodes : OrderedNodes n) (j : Fin n) :
    (signedDerivativeRowPolynomial nodes j).eval (nodes.point j) = 0 := by
  classical
  simp only [signedDerivativeRowPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_eq_zero
  intro k hk
  have hjk : j ≠ k := by
    exact (Finset.mem_erase.mp hk).1.symm
  rw [lagrangeBasis_eval_of_ne nodes.toNodeFamily hjk, mul_zero]

lemma signedDerivativeRowPolynomial_eval_of_ne {n : ℕ}
    (nodes : OrderedNodes n) {j m : Fin n} (hmj : m ≠ j) :
    (signedDerivativeRowPolynomial nodes j).eval (nodes.point m) =
      derivativeRowSign nodes j m := by
  classical
  simp only [signedDerivativeRowPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  rw [Finset.sum_eq_single m]
  · rw [lagrangeBasis_eval_self, mul_one]
  · intro k hk hkm
    have hmk : m ≠ k := hkm.symm
    rw [lagrangeBasis_eval_of_ne nodes.toNodeFamily hmk, mul_zero]
  · intro hmnot
    exact (hmnot (Finset.mem_erase.mpr ⟨hmj, Finset.mem_univ m⟩)).elim

lemma abs_signedDerivativeRowPolynomial_eval_node_le_one {n : ℕ}
    (nodes : OrderedNodes n) (j m : Fin n) :
    |(signedDerivativeRowPolynomial nodes j).eval (nodes.point m)| ≤ 1 := by
  by_cases hmj : m = j
  · subst m
    simp
  · rw [signedDerivativeRowPolynomial_eval_of_ne nodes hmj,
      derivativeRowSign, abs_interpolationSign]

lemma abs_signedDerivativeRowPolynomial_eval_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) (j : Fin n) (t : ℝ) :
    |(signedDerivativeRowPolynomial nodes j).eval t| ≤
      lebesgueFunction nodes.toNodeFamily t := by
  exact abs_eval_le_lebesgueFunction nodes.toNodeFamily
    (signedDerivativeRowPolynomial nodes j)
    (degree_signedDerivativeRowPolynomial_lt nodes j) t
    (abs_signedDerivativeRowPolynomial_eval_node_le_one nodes j)

lemma abs_signedDerivativeRowPolynomial_eval_le_lebesgueOn {n : ℕ}
    (nodes : OrderedNodes n) (j : Fin n) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |(signedDerivativeRowPolynomial nodes j).eval t| ≤
      lebesgueOn nodes.toNodeFamily (-1) 1 := by
  exact (abs_signedDerivativeRowPolynomial_eval_le_lebesgueFunction nodes j t).trans
    (lebesgueFunction_le_lebesgueOn nodes.toNodeFamily (by norm_num) ht)

lemma signedDerivativeRowPolynomial_derivative_eval_self {n : ℕ}
    (nodes : OrderedNodes n) (j : Fin n) :
    (signedDerivativeRowPolynomial nodes j).derivative.eval (nodes.point j) =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
        |(lagrangeBasis nodes.toNodeFamily k).derivative.eval (nodes.point j)| := by
  classical
  simp only [signedDerivativeRowPolynomial, Polynomial.derivative_sum,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k hk
  exact interpolationSign_mul_self _

/-- The pointwise analytic input needed by the finite argument.  It is
deliberately a proposition, not an asserted theorem: a proof must supply the
clipped Bernstein estimate for the particular polynomial, degree, point, and
full-interval norm displayed here. -/
def PointwiseClippedBernsteinAt (d : ℕ) (p : ℝ[X]) (x M : ℝ) : Prop :=
  1 ≤ d →
    p.natDegree ≤ d →
    x ∈ Set.Icc (-1 : ℝ) 1 →
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, |p.eval t| ≤ M) →
    clippedArcsineScale d x * |p.derivative.eval x| ≤ (d : ℝ) * M

/-- The symmetric contribution of one distinct pair to the clipped energy. -/
def clippedPairWeight (d : ℕ) {n : ℕ} (nodes : OrderedNodes n)
    (j k : Fin n) : ℝ :=
  Real.sqrt
      (clippedArcsineScale d (nodes.point j) *
        clippedArcsineScale d (nodes.point k)) *
    |nodes.point j - nodes.point k|⁻¹

/-- One directed entry in a clipped absolute derivative row. -/
def clippedDerivativeRowEntry (d : ℕ) {n : ℕ} (nodes : OrderedNodes n)
    (j k : Fin n) : ℝ :=
  clippedArcsineScale d (nodes.point j) *
    |(lagrangeBasis nodes.toNodeFamily k).derivative.eval (nodes.point j)|

/-- Half the sum over ordered distinct pairs, hence one copy of every
unordered pair.  The pair weight is the geometric mean of the two clipped
arcsine scales divided by the node separation. -/
def clippedPairEnergy (d : ℕ) {n : ℕ} (nodes : OrderedNodes n) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ j : Fin n,
    ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
      clippedPairWeight d nodes j k

/-- AM--GM together with the exact cross-derivative product identity turns
one symmetric pair-energy term into the two directed derivative entries. -/
lemma two_mul_clippedPairWeight_le_rowEntries {d n : ℕ}
    (nodes : OrderedNodes n) {j k : Fin n} (hjk : j ≠ k) :
    2 * clippedPairWeight d nodes j k ≤
      clippedDerivativeRowEntry d nodes j k +
        clippedDerivativeRowEntry d nodes k j := by
  let sj := clippedArcsineScale d (nodes.point j)
  let sk := clippedArcsineScale d (nodes.point k)
  let Aj := |(lagrangeBasis nodes.toNodeFamily k).derivative.eval (nodes.point j)|
  let Ak := |(lagrangeBasis nodes.toNodeFamily j).derivative.eval (nodes.point k)|
  let r := Real.sqrt (sj * sk) * |nodes.point j - nodes.point k|⁻¹
  have hsj : 0 ≤ sj := clippedArcsineScale_nonneg _ _
  have hsk : 0 ≤ sk := clippedArcsineScale_nonneg _ _
  have hcross : Aj * Ak = (|nodes.point j - nodes.point k| ^ 2)⁻¹ := by
    dsimp only [Aj, Ak]
    rw [← abs_mul, derivative_lagrangeBasis_mul_swap nodes.toNodeFamily hjk]
    simp only [abs_neg, abs_inv, abs_pow]
  have hr_sq : r ^ 2 = (sj * Aj) * (sk * Ak) := by
    dsimp only [r]
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hsj hsk), inv_pow, ← hcross]
    ring
  change 2 * r ≤ sj * Aj + sk * Ak
  exact two_mul_le_add_of_sq_eq_mul
    (mul_nonneg hsj (abs_nonneg _))
    (mul_nonneg hsk (abs_nonneg _)) hr_sq

/-- Swapping the two indices preserves a complete off-diagonal double sum. -/
private lemma sum_erase_swap {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ j : Fin n, ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, f k j) =
      ∑ j : Fin n, ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, f j k := by
  classical
  calc
    (∑ j : Fin n,
        ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, f k j) =
        ∑ j : Fin n, ((∑ k : Fin n, f k j) - f j j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact eq_sub_of_add_eq
        (Finset.sum_erase_add Finset.univ (fun k ↦ f k j)
          (Finset.mem_univ j))
    _ = (∑ j : Fin n, ∑ k : Fin n, f k j) - ∑ j : Fin n, f j j := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ j : Fin n, ∑ k : Fin n, f j k) - ∑ j : Fin n, f j j := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin n, ((∑ k : Fin n, f j k) - f j j) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ j : Fin n,
        ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, f j k := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (eq_sub_of_add_eq
        (Finset.sum_erase_add Finset.univ (fun k ↦ f j k)
          (Finset.mem_univ j))).symm

/-- The total clipped pair energy is bounded by the full directed clipped
derivative mass.  This statement is entirely finite algebra. -/
lemma two_mul_clippedPairEnergy_le_derivativeRows {d n : ℕ}
    (nodes : OrderedNodes n) :
    2 * clippedPairEnergy d nodes ≤
      ∑ j : Fin n,
        ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
          clippedDerivativeRowEntry d nodes j k := by
  classical
  let E : ℝ := ∑ j : Fin n,
    ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
      clippedPairWeight d nodes j k
  let R : ℝ := ∑ j : Fin n,
    ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
      clippedDerivativeRowEntry d nodes j k
  have hpairs : 2 * E ≤ R + R := by
    dsimp only [E, R]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    calc
      (∑ j : Fin n,
          ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
            2 * clippedPairWeight d nodes j k) ≤
          ∑ j : Fin n,
            ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
              (clippedDerivativeRowEntry d nodes j k +
                clippedDerivativeRowEntry d nodes k j) := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro k hk
        exact two_mul_clippedPairWeight_le_rowEntries nodes
          (Finset.mem_erase.mp hk).1.symm
      _ = (∑ j : Fin n,
              ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
                clippedDerivativeRowEntry d nodes j k) +
            ∑ j : Fin n,
              ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
                clippedDerivativeRowEntry d nodes k j := by
        simp only [Finset.sum_add_distrib]
      _ = (∑ j : Fin n,
              ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
                clippedDerivativeRowEntry d nodes j k) +
            ∑ j : Fin n,
              ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
                clippedDerivativeRowEntry d nodes j k := by
        rw [sum_erase_swap]
  have hE : E ≤ R := by linarith
  change 2 * ((2 : ℝ)⁻¹ * E) ≤ R
  calc
    2 * ((2 : ℝ)⁻¹ * E) = E := by ring
    _ ≤ R := hE

/-- A pointwise clipped Bernstein estimate for every concrete signed row
polynomial bounds the clipped pair energy.  The dimension hypothesis makes
the polynomial degree `n - 1` a genuinely positive clipping degree.

Everything except `hBernstein` is finite interpolation algebra. -/
theorem two_mul_clippedPairEnergy_le_of_pointwiseClippedBernstein
    {n : ℕ} (nodes : OrderedNodes n) (hn : 2 ≤ n)
    (hBernstein : ∀ j : Fin n,
      PointwiseClippedBernsteinAt (n - 1)
        (signedDerivativeRowPolynomial nodes j) (nodes.point j)
        (lebesgueOn nodes.toNodeFamily (-1) 1)) :
    2 * clippedPairEnergy (n - 1) nodes ≤
      (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        lebesgueOn nodes.toNodeFamily (-1) 1 := by
  classical
  have hd : 1 ≤ n - 1 := by omega
  have hrow (j : Fin n) :
      clippedArcsineScale (n - 1) (nodes.point j) *
          (∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
            |(lagrangeBasis nodes.toNodeFamily k).derivative.eval
              (nodes.point j)|) ≤
        ((n - 1 : ℕ) : ℝ) * lebesgueOn nodes.toNodeFamily (-1) 1 := by
    have h := hBernstein j hd
      (natDegree_signedDerivativeRowPolynomial_le nodes j)
      (nodes.mem_Icc j)
      (fun t ht ↦ abs_signedDerivativeRowPolynomial_eval_le_lebesgueOn
        nodes j ht)
    rw [signedDerivativeRowPolynomial_derivative_eval_self] at h
    rw [abs_of_nonneg (Finset.sum_nonneg fun k hk ↦ abs_nonneg _)] at h
    exact h
  calc
    2 * clippedPairEnergy (n - 1) nodes ≤
        ∑ j : Fin n,
          ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
            clippedDerivativeRowEntry (n - 1) nodes j k :=
      two_mul_clippedPairEnergy_le_derivativeRows nodes
    _ = ∑ j : Fin n,
        clippedArcsineScale (n - 1) (nodes.point j) *
          (∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
            |(lagrangeBasis nodes.toNodeFamily k).derivative.eval
              (nodes.point j)|) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      rfl
    _ ≤ ∑ _j : Fin n,
        ((n - 1 : ℕ) : ℝ) * lebesgueOn nodes.toNodeFamily (-1) 1 := by
      exact Finset.sum_le_sum fun j hj ↦ hrow j
    _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
        lebesgueOn nodes.toNodeFamily (-1) 1 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

end

end ClassicalBound
end Randy1153
