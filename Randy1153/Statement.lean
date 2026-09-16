import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

/-!
# The statement of Randy problem 1153

This file gives an independent, literal formalization of the problem.  A
`NodeFamily n` consists of exactly `n` pairwise distinct real interpolation
nodes in `[-1, 1]`.  The Lagrange fundamental functions and their associated
Lebesgue function are exposed below before the asymptotic target is stated.

The informal expression `o(1)` is represented by an epsilon/eventual
quantifier.  Its threshold may depend on the fixed interval and on epsilon,
but is chosen before the node family, so the assertion is uniform over all
node configurations.
-/

namespace Randy1153

open Polynomial

noncomputable section

/-- An injectively enumerated family of exactly `n` nodes in `[-1, 1]`. -/
structure NodeFamily (n : ℕ) where
  point : Fin n → ℝ
  injective : Function.Injective point
  mem_Icc : ∀ i, point i ∈ Set.Icc (-1 : ℝ) 1

/-- The `k`th Lagrange fundamental polynomial for `nodes`. -/
def lagrangeBasis {n : ℕ} (nodes : NodeFamily n) (k : Fin n) : ℝ[X] :=
  Lagrange.basis Finset.univ nodes.point k

/-- The source formula for the `k`th Lagrange fundamental function:

`∏ i ≠ k, (t - xᵢ) / (xₖ - xᵢ)`.
-/
def lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n)
    (t : ℝ) : ℝ :=
  ∏ i ∈ Finset.univ.erase k,
    (t - nodes.point i) / (nodes.point k - nodes.point i)

/-- `lagrangeBasis` is visibly the product of its normalized linear factors. -/
lemma lagrangeBasis_eq_product {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    lagrangeBasis nodes k =
      ∏ i ∈ Finset.univ.erase k,
        (Polynomial.X - Polynomial.C (nodes.point i)) *
          Polynomial.C (nodes.point k - nodes.point i)⁻¹ := by
  classical
  simp only [lagrangeBasis, Lagrange.basis, Lagrange.basisDivisor]
  apply Finset.prod_congr rfl
  intro i _
  exact mul_comm _ _

/-- Evaluating the polynomial gives the literal fundamental-function formula. -/
lemma lagrangeBasis_eval {n : ℕ} (nodes : NodeFamily n) (k : Fin n) (t : ℝ) :
    (lagrangeBasis nodes k).eval t = lagrangeFundamental nodes k t := by
  classical
  rw [lagrangeBasis_eq_product]
  simp only [lagrangeFundamental, Polynomial.eval_prod, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, div_eq_mul_inv]

/-- A fundamental function is one at its own node. -/
@[simp]
lemma lagrangeBasis_eval_self {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (lagrangeBasis nodes k).eval (nodes.point k) = 1 := by
  simpa only [lagrangeBasis] using
    (Lagrange.eval_basis_self nodes.injective.injOn (Finset.mem_univ k))

/-- A fundamental function vanishes at every other node. -/
@[simp]
lemma lagrangeBasis_eval_of_ne {n : ℕ} (nodes : NodeFamily n) {j k : Fin n}
    (hjk : j ≠ k) :
    (lagrangeBasis nodes k).eval (nodes.point j) = 0 := by
  simpa only [lagrangeBasis] using
    (Lagrange.eval_basis_of_ne (s := Finset.univ) (v := nodes.point)
      (i := k) (j := j) hjk.symm (Finset.mem_univ j))

/-- The Lebesgue function associated to a node family. -/
def lebesgueFunction {n : ℕ} (nodes : NodeFamily n) (t : ℝ) : ℝ :=
  ∑ k : Fin n, |lagrangeFundamental nodes k t|

/-- Every Lagrange fundamental function is continuous. -/
lemma continuous_lagrangeFundamental {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    Continuous (lagrangeFundamental nodes k) := by
  exact (lagrangeBasis nodes k).continuous.congr fun t => lagrangeBasis_eval nodes k t

/-- A finite sum of absolute values of fundamental functions is continuous. -/
lemma continuous_lebesgueFunction {n : ℕ} (nodes : NodeFamily n) :
    Continuous (lebesgueFunction nodes) := by
  classical
  exact continuous_finset_sum Finset.univ fun k _ =>
    (continuous_lagrangeFundamental nodes k).abs

/-- The supremum of the Lebesgue function on the closed interval `[a, b]`.
For the nonempty intervals used in `Target`, continuity makes this supremum a
maximum; using `sSup` keeps the statement independent of a chosen maximizer. -/
def lebesgueOn {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) : ℝ :=
  sSup (lebesgueFunction nodes '' Set.Icc a b)

/-- On a nonempty closed interval, `lebesgueOn` is attained by the Lebesgue
function and is an upper bound for every other value on that interval. -/
lemma exists_lebesgueOn_eq_and_ge {n : ℕ} (nodes : NodeFamily n) {a b : ℝ}
    (hab : a ≤ b) :
    ∃ t ∈ Set.Icc a b,
      lebesgueOn nodes a b = lebesgueFunction nodes t ∧
        ∀ u ∈ Set.Icc a b, lebesgueFunction nodes u ≤ lebesgueFunction nodes t := by
  simpa only [lebesgueOn] using
    (isCompact_Icc.exists_sSup_image_eq_and_ge (Set.nonempty_Icc.mpr hab)
      (continuous_lebesgueFunction nodes).continuousOn)

/-- Strictly exceeding a bound at the interval supremum is equivalent to
strictly exceeding it at an explicit point of the interval. -/
lemma lt_lebesgueOn_iff {n : ℕ} (nodes : NodeFamily n) {a b c : ℝ}
    (hab : a ≤ b) :
    c < lebesgueOn nodes a b ↔
      ∃ t ∈ Set.Icc a b, c < lebesgueFunction nodes t := by
  obtain ⟨t, ht, hsup, hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
  constructor
  · intro h
    exact ⟨t, ht, by simpa only [hsup] using h⟩
  · rintro ⟨u, hu, hcu⟩
    rw [hsup]
    exact hcu.trans_le (hmax u hu)

/-- The exact epsilon/eventual reading of Randy problem 1153.

For every fixed nondegenerate `[a,b] ⊆ [-1,1]` and every positive `ε`, one
threshold works simultaneously for every sufficiently large cardinality and
every choice of distinct nodes.  The cast in `Real.log (n : ℝ)` makes explicit
that `n` is the cardinality of the indexing type `Fin n`.
-/
def Target : Prop :=
  ∀ a b : ℝ,
    -1 ≤ a → a < b → b ≤ 1 →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 2 ≤ N ∧
        ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
          ∃ t ∈ Set.Icc a b,
            (2 / Real.pi - ε) * Real.log (n : ℝ) < lebesgueFunction nodes t

end

end Randy1153
