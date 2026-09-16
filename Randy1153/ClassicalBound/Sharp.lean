import Randy1153.ClassicalBound.Mesoscopic
import Randy1153.NodeOrder

/-!
# Algebraic spine of a sharp classical bound

This file develops the source-free barycentric identities needed by the
classical Bernstein--Randy--Turán route.  The central object is the monic
nodal polynomial.  Away from the nodes, the Lebesgue function is exactly its
absolute value times a reciprocal derivative-distance row.

The final universal harmonic lower bound is not asserted here.  Its missing
content is a genuine finite geometric dichotomy: either a normalized
reciprocal row has harmonic mass at a point where the nodal polynomial is
large, or the failure of that clock estimate must itself force a large
cardinal polynomial.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- The monic degree-`n` polynomial whose roots are exactly the nodes. -/
def nodalPolynomial {n : ℕ} (nodes : NodeFamily n) : ℝ[X] :=
  Lagrange.nodal Finset.univ nodes.point

lemma nodalPolynomial_eq_product {n : ℕ} (nodes : NodeFamily n) :
    nodalPolynomial nodes =
      ∏ k : Fin n, (Polynomial.X - Polynomial.C (nodes.point k)) := by
  rfl

@[simp]
lemma natDegree_nodalPolynomial {n : ℕ} (nodes : NodeFamily n) :
    (nodalPolynomial nodes).natDegree = n := by
  simp [nodalPolynomial]

@[simp]
lemma degree_nodalPolynomial {n : ℕ} (nodes : NodeFamily n) :
    (nodalPolynomial nodes).degree = n := by
  simp [nodalPolynomial]

lemma monic_nodalPolynomial {n : ℕ} (nodes : NodeFamily n) :
    (nodalPolynomial nodes).Monic := by
  exact Lagrange.nodal_monic

lemma eval_nodalPolynomial {n : ℕ} (nodes : NodeFamily n) (t : ℝ) :
    (nodalPolynomial nodes).eval t =
      ∏ k : Fin n, (t - nodes.point k) := by
  simpa only [nodalPolynomial] using
    (Lagrange.eval_nodal (s := Finset.univ) (v := nodes.point) (x := t))

lemma eval_nodalPolynomial_ne_zero_of_off_nodes {n : ℕ}
    (nodes : NodeFamily n) {t : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k) :
    (nodalPolynomial nodes).eval t ≠ 0 := by
  simpa only [nodalPolynomial] using
    (Lagrange.eval_nodal_not_at_node
      (s := Finset.univ) (v := nodes.point) (x := t)
      (fun k _ ↦ ht k))

/-- Compact full-interval maximum of the absolute nodal polynomial. -/
def nodalMaximum {n : ℕ} (nodes : NodeFamily n) : ℝ :=
  sSup ((fun t ↦ |(nodalPolynomial nodes).eval t|) ''
    Set.Icc (-1 : ℝ) 1)

lemma exists_nodalMaximum_eq_and_ge {n : ℕ} (nodes : NodeFamily n) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      nodalMaximum nodes = |(nodalPolynomial nodes).eval t| ∧
        ∀ u ∈ Set.Icc (-1 : ℝ) 1,
          |(nodalPolynomial nodes).eval u| ≤
            |(nodalPolynomial nodes).eval t| := by
  simpa only [nodalMaximum] using
    (isCompact_Icc.exists_sSup_image_eq_and_ge
      (Set.nonempty_Icc.mpr (by norm_num : (-1 : ℝ) ≤ 1))
      (nodalPolynomial nodes).continuous.abs.continuousOn)

/-- The monic nodal polynomial has a strictly positive full-interval
maximum, even if some nodes are endpoints. -/
lemma nodalMaximum_pos {n : ℕ} (nodes : NodeFamily n) :
    0 < nodalMaximum nodes := by
  obtain ⟨t, htIcc, htNot⟩ :=
    (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)).exists_notMem_finset
      nodes.nodeFinset
  have ht : ∀ k : Fin n, t ≠ nodes.point k := by
    intro k htk
    apply htNot
    exact (nodes.mem_nodeFinset t).2 ⟨k, htk.symm⟩
  obtain ⟨u, huIcc, hmax, hge⟩ := exists_nodalMaximum_eq_and_ge nodes
  rw [hmax]
  exact (abs_pos.mpr (eval_nodalPolynomial_ne_zero_of_off_nodes nodes ht)).trans_le
    (hge t htIcc)

/-- A maximizer cannot be an interpolation node. -/
lemma exists_nodalMaximum_eq_and_off_nodes {n : ℕ} (nodes : NodeFamily n) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      nodalMaximum nodes = |(nodalPolynomial nodes).eval t| ∧
        (∀ u ∈ Set.Icc (-1 : ℝ) 1,
          |(nodalPolynomial nodes).eval u| ≤
            |(nodalPolynomial nodes).eval t|) ∧
        ∀ k : Fin n, t ≠ nodes.point k := by
  obtain ⟨t, htIcc, hmax, hge⟩ := exists_nodalMaximum_eq_and_ge nodes
  refine ⟨t, htIcc, hmax, hge, ?_⟩
  intro k htk
  subst t
  have hzero : nodalMaximum nodes = 0 := by
    calc
      nodalMaximum nodes =
          |(nodalPolynomial nodes).eval (nodes.point k)| := hmax
      _ = 0 := by
        rw [show (nodalPolynomial nodes).eval (nodes.point k) = 0 by
          simpa only [nodalPolynomial] using
            (Lagrange.eval_nodal_at_node
              (s := Finset.univ) (v := nodes.point) (Finset.mem_univ k))]
        simp
  exact (nodalMaximum_pos nodes).ne' hzero

@[simp]
lemma eval_nodalPolynomial_at_node {n : ℕ} (nodes : NodeFamily n) (k : Fin n) :
    (nodalPolynomial nodes).eval (nodes.point k) = 0 := by
  simpa only [nodalPolynomial] using
    (Lagrange.eval_nodal_at_node (s := Finset.univ) (v := nodes.point)
      (Finset.mem_univ k))

/-- At a simple node, the derivative of the nodal polynomial is the product
of all the remaining differences. -/
lemma derivative_nodalPolynomial_eval_node {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) :
    (nodalPolynomial nodes).derivative.eval (nodes.point k) =
      ∏ j ∈ Finset.univ.erase k, (nodes.point k - nodes.point j) := by
  rw [nodalPolynomial,
    Lagrange.eval_nodal_derivative_eval_node_eq (Finset.mem_univ k),
    Lagrange.eval_nodal]

/-- Node injectivity makes every nodal derivative nonzero. -/
lemma derivative_nodalPolynomial_eval_node_ne_zero {n : ℕ}
    (nodes : NodeFamily n) (k : Fin n) :
    (nodalPolynomial nodes).derivative.eval (nodes.point k) ≠ 0 := by
  rw [derivative_nodalPolynomial_eval_node, Finset.prod_ne_zero_iff]
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  exact sub_ne_zero.mpr (nodes.point_ne hjk.symm)

/-- Polynomial barycentric form before evaluation. -/
lemma lagrangeBasis_eq_C_derivative_inv_mul_nodal_erase {n : ℕ}
    (nodes : NodeFamily n) (k : Fin n) :
    lagrangeBasis nodes k =
      Polynomial.C
          ((nodalPolynomial nodes).derivative.eval (nodes.point k))⁻¹ *
        Lagrange.nodal (Finset.univ.erase k) nodes.point := by
  change Lagrange.basis Finset.univ nodes.point k = _
  rw [Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ k),
    ← Lagrange.nodal_erase_eq_nodal_div (Finset.mem_univ k),
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ k)]
  rfl

/-- Derivative of a cardinal polynomial at a different node, expressed only
through the two nodal derivatives and the node separation. -/
lemma derivative_lagrangeBasis_eval_of_ne {n : ℕ} (nodes : NodeFamily n)
    {j k : Fin n} (hjk : j ≠ k) :
    (lagrangeBasis nodes k).derivative.eval (nodes.point j) =
      (nodalPolynomial nodes).derivative.eval (nodes.point j) *
        ((nodalPolynomial nodes).derivative.eval (nodes.point k))⁻¹ *
          (nodes.point j - nodes.point k)⁻¹ := by
  let q : ℝ[X] := Lagrange.nodal (Finset.univ.erase k) nodes.point
  have hjmem : j ∈ Finset.univ.erase k := by
    exact Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩
  have hdiff : nodes.point j - nodes.point k ≠ 0 :=
    sub_ne_zero.mpr (nodes.point_ne hjk)
  have hfactor :
      (nodalPolynomial nodes).derivative.eval (nodes.point j) =
        (nodes.point j - nodes.point k) * q.derivative.eval (nodes.point j) := by
    rw [nodalPolynomial,
      Lagrange.nodal_eq_mul_nodal_erase (s := Finset.univ)
        (v := nodes.point) (Finset.mem_univ k)]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
      one_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, one_mul, q]
    rw [Lagrange.eval_nodal_at_node hjmem, zero_add]
  have hq : q.derivative.eval (nodes.point j) =
      (nodalPolynomial nodes).derivative.eval (nodes.point j) *
        (nodes.point j - nodes.point k)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq₀ hdiff).2
    rw [mul_comm]
    exact hfactor.symm
  rw [lagrangeBasis_eq_C_derivative_inv_mul_nodal_erase,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_mul, Polynomial.eval_C, hq]
  ring

/-- Reciprocal derivative identity for two different cardinal polynomials.
This is the exact algebraic cancellation used in classical clock/defect
arguments. -/
lemma derivative_lagrangeBasis_mul_swap {n : ℕ} (nodes : NodeFamily n)
    {j k : Fin n} (hjk : j ≠ k) :
    (lagrangeBasis nodes k).derivative.eval (nodes.point j) *
        (lagrangeBasis nodes j).derivative.eval (nodes.point k) =
      -((nodes.point j - nodes.point k) ^ 2)⁻¹ := by
  rw [derivative_lagrangeBasis_eval_of_ne nodes hjk,
    derivative_lagrangeBasis_eval_of_ne nodes hjk.symm]
  have hjderiv := derivative_nodalPolynomial_eval_node_ne_zero nodes j
  have hkderiv := derivative_nodalPolynomial_eval_node_ne_zero nodes k
  have hjkpoint : nodes.point j - nodes.point k ≠ 0 :=
    sub_ne_zero.mpr (nodes.point_ne hjk)
  have hkjpoint : nodes.point k - nodes.point j ≠ 0 :=
    sub_ne_zero.mpr (nodes.point_ne hjk.symm)
  field_simp
  ring

/-- Absolute-value form of the reciprocal derivative identity. -/
lemma abs_derivative_lagrangeBasis_mul_swap {n : ℕ} (nodes : NodeFamily n)
    {j k : Fin n} (hjk : j ≠ k) :
    |(lagrangeBasis nodes k).derivative.eval (nodes.point j)| *
        |(lagrangeBasis nodes j).derivative.eval (nodes.point k)| =
      (|nodes.point j - nodes.point k| ^ 2)⁻¹ := by
  rw [← abs_mul, derivative_lagrangeBasis_mul_swap nodes hjk]
  simp only [abs_neg, abs_inv, abs_pow]

/-- Barycentric form of one fundamental function, with the derivative of the
nodal polynomial visible. -/
lemma lagrangeFundamental_eq_nodalPolynomial_mul {n : ℕ}
    (nodes : NodeFamily n) (k : Fin n) {t : ℝ}
    (htk : t ≠ nodes.point k) :
    lagrangeFundamental nodes k t =
      (nodalPolynomial nodes).eval t *
        (((nodalPolynomial nodes).derivative.eval (nodes.point k))⁻¹ *
          (t - nodes.point k)⁻¹) := by
  rw [← lagrangeBasis_eval]
  change (Lagrange.basis Finset.univ nodes.point k).eval t = _
  simpa only [nodalPolynomial,
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ k)] using
    (Lagrange.eval_basis_not_at_node
      (s := Finset.univ) (v := nodes.point) (i := k) (x := t)
      (Finset.mem_univ k) htk)

/-- Absolute barycentric form. -/
lemma abs_lagrangeFundamental_eq_nodalPolynomial {n : ℕ}
    (nodes : NodeFamily n) (k : Fin n) {t : ℝ}
    (htk : t ≠ nodes.point k) :
    |lagrangeFundamental nodes k t| =
      |(nodalPolynomial nodes).eval t| *
        (|(nodalPolynomial nodes).derivative.eval (nodes.point k)| *
          |t - nodes.point k|)⁻¹ := by
  rw [lagrangeFundamental_eq_nodalPolynomial_mul nodes k htk]
  simp only [abs_mul, abs_inv]
  rw [mul_inv]

/-- Exact reciprocal derivative-distance row for the Lebesgue function. -/
lemma lebesgueFunction_eq_nodalPolynomial_mul_sum {n : ℕ}
    (nodes : NodeFamily n) {t : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k) :
    lebesgueFunction nodes t =
      |(nodalPolynomial nodes).eval t| *
        ∑ k : Fin n,
          (|(nodalPolynomial nodes).derivative.eval (nodes.point k)| *
            |t - nodes.point k|)⁻¹ := by
  rw [lebesgueFunction, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact abs_lagrangeFundamental_eq_nodalPolynomial nodes k (ht k)

/-- A pointwise upper envelope on the nodal derivatives gives a checked
lower envelope on the complete reciprocal row. -/
lemma nodalPolynomial_mul_sum_inv_le_lebesgueFunction {n : ℕ}
    (nodes : NodeFamily n) {t : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k)
    (D : Fin n → ℝ) (hD : ∀ k, 0 < D k)
    (hderiv : ∀ k,
      |(nodalPolynomial nodes).derivative.eval (nodes.point k)| ≤ D k) :
    |(nodalPolynomial nodes).eval t| *
        ∑ k : Fin n, (D k * |t - nodes.point k|)⁻¹ ≤
      lebesgueFunction nodes t := by
  rw [lebesgueFunction_eq_nodalPolynomial_mul_sum nodes ht]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply Finset.sum_le_sum
  intro k _
  have hderivpos :
      0 < |(nodalPolynomial nodes).derivative.eval (nodes.point k)| :=
    abs_pos.mpr (derivative_nodalPolynomial_eval_node_ne_zero nodes k)
  have hdistpos : 0 < |t - nodes.point k| :=
    abs_pos.mpr (sub_ne_zero.mpr (ht k))
  apply (inv_le_inv₀
    (mul_pos (hD k) hdistpos)
    (mul_pos hderivpos hdistpos)).2
  exact mul_le_mul_of_nonneg_right (hderiv k) hdistpos.le

/-- The precise output of a weighted Bernstein estimate at the roots.

If `M` is a positive value attained by the nodal polynomial at `t`, and the
weighted root derivatives satisfy the classical Bernstein scale, then the
Lebesgue function dominates the arcsine reciprocal mass of the nodes seen
from `t`.  No distribution estimate for that mass is assumed or hidden in
this lemma.
-/
lemma arcsine_reciprocal_mass_le_lebesgueFunction {n : ℕ}
    (nodes : NodeFamily n) (hn : 0 < n) {t M : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k) (hM : 0 < M)
    (heval : |(nodalPolynomial nodes).eval t| = M)
    (hbernstein : ∀ k : Fin n,
      Real.sqrt (1 - (nodes.point k) ^ 2) *
          |(nodalPolynomial nodes).derivative.eval (nodes.point k)| ≤
        (n : ℝ) * M) :
    (n : ℝ)⁻¹ *
        ∑ k : Fin n,
          Real.sqrt (1 - (nodes.point k) ^ 2) *
            |t - nodes.point k|⁻¹ ≤
      lebesgueFunction nodes t := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [lebesgueFunction_eq_nodalPolynomial_mul_sum nodes ht, heval]
  calc
    (n : ℝ)⁻¹ *
          ∑ k : Fin n,
            Real.sqrt (1 - (nodes.point k) ^ 2) *
              |t - nodes.point k|⁻¹ =
        M * ∑ k : Fin n,
          Real.sqrt (1 - (nodes.point k) ^ 2) *
            (((n : ℝ) * M * |t - nodes.point k|)⁻¹) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hdist : |t - nodes.point k| ≠ 0 :=
        (abs_ne_zero.mpr (sub_ne_zero.mpr (ht k)))
      field_simp
    _ ≤ M * ∑ k : Fin n,
        (|(nodalPolynomial nodes).derivative.eval (nodes.point k)| *
          |t - nodes.point k|)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ hM.le
      apply Finset.sum_le_sum
      intro k _
      let s := Real.sqrt (1 - (nodes.point k) ^ 2)
      let d := |(nodalPolynomial nodes).derivative.eval (nodes.point k)|
      let r := |t - nodes.point k|
      have hd : 0 < d := by
        exact abs_pos.mpr (derivative_nodalPolynomial_eval_node_ne_zero nodes k)
      have hr : 0 < r := by
        exact abs_pos.mpr (sub_ne_zero.mpr (ht k))
      have hleft : 0 < (n : ℝ) * M * r := mul_pos (mul_pos hnR hM) hr
      have hright : 0 < d * r := mul_pos hd hr
      change s * (((n : ℝ) * M * r)⁻¹) ≤ (d * r)⁻¹
      rw [← div_eq_mul_inv, ← one_div]
      apply (div_le_div_iff₀ hleft hright).2
      calc
        s * (d * r) = (s * d) * r := by ring
        _ ≤ ((n : ℝ) * M) * r :=
          mul_le_mul_of_nonneg_right (hbernstein k) hr.le
        _ = 1 * ((n : ℝ) * M * r) := by ring
    _ = M * ∑ k : Fin n,
        (|(nodalPolynomial nodes).derivative.eval (nodes.point k)| *
          |t - nodes.point k|)⁻¹ := rfl

/-- Full-interval version of
`arcsine_reciprocal_mass_le_lebesgueFunction`. -/
lemma arcsine_reciprocal_mass_le_lebesgueOn {n : ℕ}
    (nodes : NodeFamily n) (hn : 0 < n) {t M : ℝ}
    (htIcc : t ∈ Set.Icc (-1 : ℝ) 1)
    (ht : ∀ k : Fin n, t ≠ nodes.point k) (hM : 0 < M)
    (heval : |(nodalPolynomial nodes).eval t| = M)
    (hbernstein : ∀ k : Fin n,
      Real.sqrt (1 - (nodes.point k) ^ 2) *
          |(nodalPolynomial nodes).derivative.eval (nodes.point k)| ≤
        (n : ℝ) * M) :
    (n : ℝ)⁻¹ *
        ∑ k : Fin n,
          Real.sqrt (1 - (nodes.point k) ^ 2) *
            |t - nodes.point k|⁻¹ ≤
      lebesgueOn nodes (-1) 1 := by
  obtain ⟨u, hu, hsup, hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes (by norm_num : (-1 : ℝ) ≤ 1)
  rw [hsup]
  exact (arcsine_reciprocal_mass_le_lebesgueFunction nodes hn ht hM heval
    hbernstein).trans (hmax t htIcc)

/-- At a genuine maximum of the nodal polynomial, the weighted Bernstein
root estimate reduces the full classical problem to a geometric reciprocal
mass estimate. -/
lemma exists_arcsine_reciprocal_mass_le_lebesgueOn_of_rootBernstein
    {n : ℕ} (nodes : NodeFamily n) (hn : 0 < n)
    (hbernstein : ∀ k : Fin n,
      Real.sqrt (1 - (nodes.point k) ^ 2) *
          |(nodalPolynomial nodes).derivative.eval (nodes.point k)| ≤
        (n : ℝ) * nodalMaximum nodes) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      (∀ k : Fin n, t ≠ nodes.point k) ∧
        (n : ℝ)⁻¹ *
            ∑ k : Fin n,
              Real.sqrt (1 - (nodes.point k) ^ 2) *
                |t - nodes.point k|⁻¹ ≤
          lebesgueOn nodes (-1) 1 := by
  obtain ⟨t, htIcc, hmax, _, ht⟩ :=
    exists_nodalMaximum_eq_and_off_nodes nodes
  refine ⟨t, htIcc, ht, ?_⟩
  exact arcsine_reciprocal_mass_le_lebesgueOn nodes hn htIcc ht
    (nodalMaximum_pos nodes) hmax.symm hbernstein

end

end ClassicalBound
end Randy1153
