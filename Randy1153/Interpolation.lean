import Randy1153.NodeOrder
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Lagrange interpolation and the Lebesgue inequality

Mathlib's checked `Lagrange.interpolate` operator is specialized here to the
frozen Randy 1153 node representation.  The principal output is the
pointwise interpolation inequality with either an arbitrary common nodal
bound or the actual finite nodal maximum.
-/

namespace Randy1153

open Polynomial

noncomputable section

/-- Every polynomial of degree below the number of nodes has its Lagrange
expansion. -/
lemma lagrangeExpansion {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hp : p.degree < n) :
    p = ∑ k : Fin n,
      Polynomial.C (p.eval (nodes.point k)) * lagrangeBasis nodes k := by
  have hp' : p.degree < (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using hp
  simpa [lagrangeBasis] using
    (Lagrange.eq_interpolate (s := Finset.univ) nodes.injective.injOn hp')

/-- Pointwise form of the Lagrange expansion. -/
lemma eval_lagrangeExpansion {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hp : p.degree < n) (t : ℝ) :
    p.eval t = ∑ k : Fin n,
      p.eval (nodes.point k) * lagrangeFundamental nodes k t := by
  calc
    p.eval t =
        (∑ k : Fin n,
          Polynomial.C (p.eval (nodes.point k)) * lagrangeBasis nodes k).eval t :=
      congrArg (fun q : ℝ[X] => q.eval t) (lagrangeExpansion nodes p hp)
    _ = ∑ k : Fin n,
        p.eval (nodes.point k) * lagrangeFundamental nodes k t := by
      rw [Polynomial.eval_finset_sum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, lagrangeBasis_eval]

/-- The fundamental interpolation inequality with an arbitrary common upper
bound for the absolute nodal values. -/
lemma abs_eval_le_mul_lebesgueFunction {n : ℕ} (nodes : NodeFamily n)
    (p : ℝ[X]) (hp : p.degree < n) (M t : ℝ)
    (hM : ∀ k : Fin n, |p.eval (nodes.point k)| ≤ M) :
    |p.eval t| ≤ M * lebesgueFunction nodes t := by
  rw [eval_lagrangeExpansion nodes p hp t]
  calc
    |∑ k : Fin n, p.eval (nodes.point k) * lagrangeFundamental nodes k t| ≤
        ∑ k : Fin n, |p.eval (nodes.point k) * lagrangeFundamental nodes k t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin n,
        |p.eval (nodes.point k)| * |lagrangeFundamental nodes k t| := by
      simp only [abs_mul]
    _ ≤ ∑ k : Fin n, M * |lagrangeFundamental nodes k t| := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (hM k) (abs_nonneg _)
    _ = M * lebesgueFunction nodes t := by
      rw [lebesgueFunction, Finset.mul_sum]

/-- In particular, nodal values bounded by one are controlled by the
Lebesgue function itself. -/
lemma abs_eval_le_lebesgueFunction {n : ℕ} (nodes : NodeFamily n)
    (p : ℝ[X]) (hp : p.degree < n) (t : ℝ)
    (hp_nodes : ∀ k : Fin n, |p.eval (nodes.point k)| ≤ 1) :
    |p.eval t| ≤ lebesgueFunction nodes t := by
  simpa only [one_mul] using
    abs_eval_le_mul_lebesgueFunction nodes p hp 1 t hp_nodes

private lemma fin_univ_nonempty_of_pos {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

/-- The maximum absolute value of `p` on a nonempty node family. -/
def nodalMax {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X]) (hn : 0 < n) : ℝ :=
  Finset.univ.sup' (fin_univ_nonempty_of_pos hn)
    (fun k : Fin n => |p.eval (nodes.point k)|)

/-- Every nodal absolute value is bounded by `nodalMax`. -/
lemma abs_eval_node_le_nodalMax {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hn : 0 < n) (k : Fin n) :
    |p.eval (nodes.point k)| ≤ nodalMax nodes p hn := by
  unfold nodalMax
  exact Finset.le_sup'
    (f := fun j : Fin n => |p.eval (nodes.point j)|) (Finset.mem_univ k)

/-- The finite nodal maximum is attained. -/
lemma exists_nodalMax_eq {n : ℕ} (nodes : NodeFamily n) (p : ℝ[X])
    (hn : 0 < n) :
    ∃ k : Fin n, nodalMax nodes p hn = |p.eval (nodes.point k)| := by
  simpa only [nodalMax, Finset.mem_univ, true_and] using
    (Finset.exists_mem_eq_sup' (fin_univ_nonempty_of_pos hn)
      (fun k : Fin n => |p.eval (nodes.point k)|))

/-- Pointwise interpolation inequality in the conventional finite-maximum
form. -/
lemma abs_eval_le_nodalMax_mul_lebesgueFunction {n : ℕ}
    (nodes : NodeFamily n) (p : ℝ[X]) (hp : p.degree < n)
    (hn : 0 < n) (t : ℝ) :
    |p.eval t| ≤ nodalMax nodes p hn * lebesgueFunction nodes t :=
  abs_eval_le_mul_lebesgueFunction nodes p hp (nodalMax nodes p hn) t
    (abs_eval_node_le_nodalMax nodes p hn)

end

end Randy1153
