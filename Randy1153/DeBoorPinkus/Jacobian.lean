import Randy1153.DeBoorPinkus.Simplex
import Randy1153.DeBoorPinkus.GapCritical
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The endpoint-coordinate Jacobian

This file isolates the analytic and algebraic parts of the Jacobian argument
in de Boor--Pinkus.  The interpolation polynomial is first written on the
ambient space of interior coordinates.  The formula remains meaningful away
from the ordered simplex (it merely uses inverses of node differences), while
on the simplex it is definitionally the project's `gapPolynomial`.

The source's envelope calculation says that, at the unique critical point
`τ_g`, moving an interior node `t_j` changes the gap height by

`-F'_g(t_j) * l_j(τ_g)`.

The factorization `F'_g = (X - τ_g) Q_g` then rewrites this as a row factor,
the evaluation `Q_g(t_j)`, and a column factor.  Consequently every maximal
minor of the height Jacobian is the corresponding minor of the quotient
evaluation matrix times explicit nonzero diagonal factors.  Those algebraic
reductions are unconditional below.

The local implicit-function/envelope mechanism is also packaged without a
postulate: its hypotheses are ordinary Mathlib derivative judgments.  Thus a
later analytic proof can discharge exactly the two coordinate derivative
calculations without changing the downstream determinant argument.
-/

namespace Randy1153.DeBoorPinkus

open Polynomial
open scoped BigOperators Topology

noncomputable section

/-! ## The interpolation polynomial in ambient interior coordinates -/

/-- The `k`th cardinal polynomial after adjoining the fixed endpoints `A,B`
to an arbitrary ambient interior vector `u`. -/
def coordinateLagrangePolynomial {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k : Fin (d + 2)) : ℝ[X] :=
  ∏ i ∈ Finset.univ.erase k,
    (X - C (endpointPoint A B u i)) *
      C (endpointPoint A B u k - endpointPoint A B u i)⁻¹

/-- The signed gap polynomial as a rational-polynomial expression in the
ambient interior coordinates. -/
def coordinateGapPolynomial {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) : ℝ[X] :=
  ∑ k : Fin (d + 2),
    C (gapCoefficient g k) * coordinateLagrangePolynomial A B u k

/-- Evaluation of the coordinate gap polynomial. -/
def coordinateGapValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  (coordinateGapPolynomial A B u g).eval x

/-- The critical equation `F'_g(x)=0`, expressed in the same coordinates. -/
def coordinateCriticalValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  (coordinateGapPolynomial A B u g).derivative.eval x

lemma coordinateLagrangePolynomial_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) :
    coordinateLagrangePolynomial A B u.1 k =
      lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily k := by
  rw [lagrangeBasis_eq_product]
  rfl

/-- On the ordered simplex the ambient coordinate formula is exactly the
committed signed gap polynomial, not merely an extension with the same nodal
values. -/
lemma coordinateGapPolynomial_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) :
    coordinateGapPolynomial A B u.1 g =
      gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g := by
  classical
  simp only [coordinateGapPolynomial, gapPolynomial, Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [coordinateLagrangePolynomial_eq hAB u]
  rfl

lemma coordinateGapValue_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    coordinateGapValue A B u.1 g x =
      (gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).eval x := by
  rw [coordinateGapValue, coordinateGapPolynomial_eq hAB u]

lemma coordinateCriticalValue_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    coordinateCriticalValue A B u.1 g x =
      (gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).derivative.eval x := by
  rw [coordinateCriticalValue, coordinateGapPolynomial_eq hAB u]

/-- The gap height in the simplex chart. -/
def coordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : ℝ :=
  gapHeight (endpointArrayOfInterior hAB u).toOrderedNodes g

/-- The selected unique critical point in the simplex chart. -/
def coordinateGapArgmax {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : ℝ :=
  gapArgmax (endpointArrayOfInterior hAB u).toOrderedNodes g

lemma coordinateGapHeight_eq_value_at_argmax {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) :
    coordinateGapHeight hAB u g =
      coordinateGapValue A B u.1 g (coordinateGapArgmax hAB u g) := by
  rw [coordinateGapHeight, coordinateGapArgmax, coordinateGapValue_eq hAB u]
  exact gapHeight_eq_eval_gapArgmax _ _

/-! ## The source factorization of the height differential -/

/-- Product `ω_u(x)=∏_k (x-t_k)` of all endpoint-adjoined node factors,
written as a value because only its values enter the Jacobian. -/
def coordinateNodalValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) (x : ℝ) : ℝ :=
  ∏ k : Fin (d + 2), (x - endpointPoint A B u k)

/-- Barycentric denominator `∏_{k≠j}(t_j-t_k)` at an interior node. -/
def coordinateBasisDenominator {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (j : Fin d) : ℝ :=
  ∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
    (endpointPoint A B u (interiorNodeIndex j) - endpointPoint A B u k)

lemma coordinateBasisDenominator_ne_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) (j : Fin d) :
    coordinateBasisDenominator A B u.1 j ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  have hne : interiorNodeIndex j ≠ k := (Finset.mem_erase.mp hk).1.symm
  exact sub_ne_zero.mpr ((endpointPoint_strictMono hAB.2.1 u.2).injective.ne hne)

lemma coordinateNodalValue_eq_mul_erase {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (x : ℝ) :
    coordinateNodalValue A B u x =
      (x - endpointPoint A B u (interiorNodeIndex j)) *
        ∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
          (x - endpointPoint A B u k) := by
  classical
  exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin (d + 2)))
    (fun k => x - endpointPoint A B u k) (Finset.mem_univ _)).symm

lemma lagrangeFundamental_interior_eq {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) (x : ℝ) :
    lagrangeFundamental (endpointArrayOfInterior hAB u).toNodeFamily
        (interiorNodeIndex j) x =
      (∏ k ∈ Finset.univ.erase (interiorNodeIndex j),
          (x - endpointPoint A B u.1 k)) *
        (coordinateBasisDenominator A B u.1 j)⁻¹ := by
  classical
  rw [lagrangeFundamental]
  simp only [endpointArrayOfInterior_point, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rfl

/-- The row factors in the source Jacobian reduction. -/
def gapJacobianRowFactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  coordinateNodalValue A B nodes.interior (gapArgmax nodes.toOrderedNodes g)

/-- The column factors in the source Jacobian reduction. -/
def gapJacobianColumnFactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) : ℝ :=
  (coordinateBasisDenominator A B nodes.interior j)⁻¹

/-- The quotient-evaluation matrix singled out in source Lemma 2.  It has
one row for every gap and one column for every moving interior node. -/
def gapQuotientEvaluationMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun g j => (gapDerivativeQuotient nodes.toOrderedNodes g).eval
    (nodes.point (interiorNodeIndex j))

/-- The factored matrix predicted for the differential of all gap heights. -/
def gapHeightJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin (d + 1)) (Fin d) ℝ :=
  fun g j => gapJacobianRowFactor nodes g *
    gapQuotientEvaluationMatrix nodes g j * gapJacobianColumnFactor nodes j

lemma gapPolynomial_derivative_eval_interior_eq {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) (j : Fin d) :
    (gapPolynomial nodes.toOrderedNodes g).derivative.eval
        (nodes.point (interiorNodeIndex j)) =
      (nodes.point (interiorNodeIndex j) - gapArgmax nodes.toOrderedNodes g) *
        (gapDerivativeQuotient nodes.toOrderedNodes g).eval
          (nodes.point (interiorNodeIndex j)) := by
  have h := congrArg (Polynomial.eval (nodes.point (interiorNodeIndex j)))
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes.toOrderedNodes
      (by have := j.isLt; omega) g)
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using h.symm

/-- Entrywise envelope formula after removing the critical factor.  This is
the algebraic heart of the Jacobian calculation; it does not assume that the
height map has already been differentiated. -/
lemma gapHeightJacobianModel_apply_eq {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) (j : Fin d) :
    gapHeightJacobianModel nodes g j =
      -(gapPolynomial nodes.toOrderedNodes g).derivative.eval
          (nodes.point (interiorNodeIndex j)) *
        lagrangeFundamental nodes.toNodeFamily (interiorNodeIndex j)
          (gapArgmax nodes.toOrderedNodes g) := by
  let hAB := nodes.admissibleInterval
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  have hnodes : endpointArrayOfInterior hAB u = nodes :=
    endpointArrayOfInterior_interior hAB nodes
  have hnodal := coordinateNodalValue_eq_mul_erase A B nodes.interior j
    (gapArgmax nodes.toOrderedNodes g)
  have hfund := lagrangeFundamental_interior_eq hAB u j
    (gapArgmax nodes.toOrderedNodes g)
  dsimp [u] at hfund
  rw [hnodes] at hfund
  rw [gapHeightJacobianModel, gapJacobianRowFactor,
    gapQuotientEvaluationMatrix, gapJacobianColumnFactor,
    gapPolynomial_derivative_eval_interior_eq, hfund, hnodal]
  simp only [endpointPoint_interior, EndpointArray.interior_apply]
  ring

lemma gapJacobianRowFactor_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    gapJacobianRowFactor nodes g ≠ 0 := by
  classical
  rw [gapJacobianRowFactor, coordinateNodalValue]
  apply Finset.prod_ne_zero_iff.mpr
  intro k _hk
  apply sub_ne_zero.mpr
  intro heq
  have hopen := gapArgmax_mem_openGap nodes.toOrderedNodes (by omega) g
  have hpoint : endpointPoint A B nodes.interior k = nodes.point k := by
    let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
    have harr := endpointArrayOfInterior_interior nodes.admissibleInterval nodes
    have := congrArg (fun z : EndpointArray d A B => z.point k) harr
    exact this
  by_cases hkleft : k ≤ gapLeftIndex (n := d + 2) g
  · have hle := nodes.strictMono.monotone hkleft
    rw [← hpoint, ← heq] at hle
    exact (not_lt_of_ge hle hopen.1)
  · have hkright : gapRightIndex (n := d + 2) g ≤ k := by
      apply Fin.le_iff_val_le_val.mpr
      have hlt : (gapLeftIndex (n := d + 2) g).val < k.val := by
        exact Fin.lt_def.mp (lt_of_not_ge hkleft)
      simp only [gapRightIndex_val, gapLeftIndex_val] at hlt ⊢
      omega
    have hle := nodes.strictMono.monotone hkright
    rw [← hpoint, ← heq] at hle
    exact (not_lt_of_ge hle hopen.2)

lemma gapJacobianColumnFactor_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    gapJacobianColumnFactor nodes j ≠ 0 := by
  rw [gapJacobianColumnFactor]
  exact inv_ne_zero (coordinateBasisDenominator_ne_zero nodes.admissibleInterval
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ j)

/-! ## Maximal-minor reduction -/

lemma gapHeightJacobianModel_factorization {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    gapHeightJacobianModel nodes =
      Matrix.diagonal (gapJacobianRowFactor nodes) *
        gapQuotientEvaluationMatrix nodes *
          Matrix.diagonal (gapJacobianColumnFactor nodes) := by
  ext g j
  simp [gapHeightJacobianModel, Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The maximal minor obtained by deleting row `omitted`. -/
def deletedRowMinor {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin d) ℝ)
    (omitted : Fin (d + 1)) : ℝ :=
  (M.submatrix omitted.succAbove id).det

/-- Every maximal height-Jacobian minor is the corresponding quotient-
evaluation minor times the explicit row and column products. -/
theorem deletedRowMinor_gapHeightJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted =
      (∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
        deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
          ∏ j : Fin d, gapJacobianColumnFactor nodes j := by
  let R : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i => gapJacobianRowFactor nodes (omitted.succAbove i))
  let Q : Matrix (Fin d) (Fin d) ℝ :=
    (gapQuotientEvaluationMatrix nodes).submatrix omitted.succAbove id
  let C : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (gapJacobianColumnFactor nodes)
  have hmatrix :
      (gapHeightJacobianModel nodes).submatrix omitted.succAbove id = R * Q * C := by
    ext i j
    simp [R, Q, C, gapHeightJacobianModel, Matrix.diagonal_mul,
      Matrix.mul_diagonal]
  rw [deletedRowMinor, hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp [R, Q, C, deletedRowMinor]

theorem deletedRowMinor_gapHeightJacobianModel_ne_zero_iff {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted ≠ 0 ↔
      deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0 := by
  rw [deletedRowMinor_gapHeightJacobianModel]
  have hrow : (∏ i : Fin d,
      gapJacobianRowFactor nodes (omitted.succAbove i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      gapJacobianRowFactor_ne_zero nodes hd _
  have hcol : (∏ j : Fin d, gapJacobianColumnFactor nodes j) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      gapJacobianColumnFactor_ne_zero nodes j
  simp [hrow, hcol]

/-! ## The zero-dimensional/two-node exception -/

lemma coordinateGapPolynomial_zero_dim (A B : ℝ) (u v : Fin 0 → ℝ)
    (g : Fin 1) :
    coordinateGapPolynomial A B u g = coordinateGapPolynomial A B v g := by
  rw [Subsingleton.elim u v]

lemma coordinateGapPolynomial_zero_dim_eq_one {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B}) (g : Fin 1) :
    coordinateGapPolynomial A B u.1 g = 1 := by
  rw [coordinateGapPolynomial_eq hAB u]
  exact gapPolynomial_eq_one_of_two_nodes
    (endpointArrayOfInterior hAB u).toOrderedNodes g

lemma coordinateCriticalValue_zero_dim {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B})
    (g : Fin 1) (x : ℝ) :
    coordinateCriticalValue A B u.1 g x = 0 := by
  rw [coordinateCriticalValue_eq hAB u,
    gapPolynomial_derivative_eq_zero_of_two_nodes]
  simp

lemma coordinateGapHeight_zero_dim {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin 0 → ℝ // v ∈ endpointNodeSpace 0 A B}) (g : Fin 1) :
    coordinateGapHeight hAB u g = 1 := by
  rw [coordinateGapHeight, gapHeight_eq_eval_gapArgmax,
    gapPolynomial_eq_one_of_two_nodes]
  simp

lemma gapHeightJacobianModel_zero_dim {A B : ℝ}
    (nodes : EndpointArray 0 A B) :
    gapHeightJacobianModel nodes = (0 : Matrix (Fin 1) (Fin 0) ℝ) := by
  ext g j
  exact Fin.elim0 j

lemma deletedRowMinor_zero_dim {A B : ℝ} (nodes : EndpointArray 0 A B)
    (omitted : Fin 1) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted = 1 := by
  rw [gapHeightJacobianModel_zero_dim]
  simp [deletedRowMinor]

/-! ## Checked implicit-function and envelope infrastructure

The analytic calculation is stated at the level at which Mathlib's Fréchet
calculus consumes it. `GapCoordinateDerivativesAt` records the two concrete
rational derivative computations for `coordinateGapPolynomial`. Everything
from that record through the implicit-function theorem, envelope cancellation,
and Jacobian entry formula is checked here; the final section constructs the
record directly from finite product differentiation and interpolation.
-/

/-- The coordinate value map on the product of ambient node coordinates and
the evaluation variable. -/
def coordinateGapValueMap {d : ℕ} (A B : ℝ) (g : Fin (d + 1)) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z => coordinateGapValue A B z.1 g z.2

/-- The coordinate critical equation on that product. -/
def coordinateCriticalMap {d : ℕ} (A B : ℝ) (g : Fin (d + 1)) :
    (Fin d → ℝ) × ℝ → ℝ :=
  fun z => coordinateCriticalValue A B z.1 g z.2

/-- The vertical derivative of the critical equation at the chosen critical
point is `F''_g(τ_g)`. -/
def criticalVerticalCoefficient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  (gapPolynomial nodes.toOrderedNodes g).derivative.derivative.eval
    (gapArgmax nodes.toOrderedNodes g)

lemma criticalVerticalCoefficient_neg {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) (g : Fin (d + 1)) :
    criticalVerticalCoefficient nodes g < 0 := by
  exact gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes.toOrderedNodes
    (by omega) g

/-- In the one-coordinate/three-node case the second derivative need not use
the `n ≥ 4` logarithmic-concavity argument: the first derivative is a
nonzero polynomial of degree at most one with a root at the maximizer. -/
lemma criticalVerticalCoefficient_ne_zero_of_one_coordinate {A B : ℝ}
    (nodes : EndpointArray 1 A B) (g : Fin 2) :
    criticalVerticalCoefficient nodes g ≠ 0 := by
  let dp : ℝ[X] := (gapPolynomial nodes.toOrderedNodes g).derivative
  have hdegree : dp.natDegree ≤ 1 :=
    natDegree_gapPolynomial_derivative_le_one_of_three_nodes
      nodes.toOrderedNodes g
  obtain ⟨a, b, hab⟩ :=
    Polynomial.exists_eq_X_add_C_of_natDegree_le_one hdegree
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero
    nodes.toOrderedNodes (by norm_num) g
  have hcrit : dp.eval (gapArgmax nodes.toOrderedNodes g) = 0 :=
    gapPolynomial_derivative_eval_gapArgmax nodes.toOrderedNodes
      (by norm_num) g
  change dp.derivative.eval (gapArgmax nodes.toOrderedNodes g) ≠ 0
  intro hsecond
  rw [hab] at hdp hcrit hsecond
  simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_mul, mul_one,
    zero_add] at hsecond
  have ha : a = 0 := by simpa using hsecond
  rw [ha] at hdp hcrit
  simp at hdp hcrit
  exact hdp hcrit

/-- The vertical derivative is nonzero in every nonexceptional dimension.
This combines the elementary three-node case with strict negativity for at
least four nodes. -/
lemma criticalVerticalCoefficient_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    criticalVerticalCoefficient nodes g ≠ 0 := by
  by_cases hd1 : d = 1
  · subst d
    exact criticalVerticalCoefficient_ne_zero_of_one_coordinate nodes g
  · exact ne_of_lt (criticalVerticalCoefficient_neg nodes (by omega) g)

lemma coordinateCriticalMap_eq_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    coordinateCriticalMap A B g (u.1, coordinateGapArgmax hAB u g) = 0 := by
  rw [coordinateCriticalMap, coordinateGapArgmax,
    coordinateCriticalValue_eq hAB u]
  exact gapPolynomial_derivative_eval_gapArgmax
    (endpointArrayOfInterior hAB u).toOrderedNodes (by omega) g

/-- The exact local coordinate-calculus obligations for one gap.  The
horizontal formula is the source's node-sensitivity identity; the vertical
formula for the value map is stationarity at `τ_g`. -/
structure GapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) where
  criticalDifferential : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ
  valueDifferential : ((Fin d → ℝ) × ℝ) →L[ℝ] ℝ
  hasFDerivAt_critical : HasFDerivAt (coordinateCriticalMap A B g)
    criticalDifferential (u.1, coordinateGapArgmax hAB u g)
  contDiffAt_critical : ContDiffAt ℝ 1 (coordinateCriticalMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  critical_vertical :
    criticalDifferential.comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (criticalVerticalCoefficient (endpointArrayOfInterior hAB u) g)
  hasFDerivAt_value : HasFDerivAt (coordinateGapValueMap A B g)
    valueDifferential (u.1, coordinateGapArgmax hAB u g)
  value_vertical :
    valueDifferential.comp
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) = 0
  value_horizontal_sensitivity : ∀ j : Fin d,
    (valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) =
      -(gapPolynomial (endpointArrayOfInterior hAB u).toOrderedNodes g).derivative.eval
          ((endpointArrayOfInterior hAB u).point (interiorNodeIndex j)) *
        lagrangeFundamental (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j) (coordinateGapArgmax hAB u g)

private lemma continuousLinearMap_bijective_of_apply_one_ne_zero
    (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) : Function.Bijective L := by
  have hformula (x : ℝ) : L x = x * L 1 := by
    calc
      L x = L (x • (1 : ℝ)) := by simp
      _ = x • L 1 := map_smul L x 1
      _ = x * L 1 := by simp [smul_eq_mul]
  constructor
  · intro x y hxy
    have hx := hformula x
    have hy := hformula y
    exact mul_right_cancel₀ h (hx.symm.trans (hxy.trans hy))
  · intro y
    refine ⟨y / L 1, ?_⟩
    rw [hformula]
    exact div_mul_cancel₀ y h

/-- Negative second derivative turns the checked coordinate derivative data
into Mathlib's implicit-function predicate. -/
def gapCriticalIsContDiffImplicitAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    IsContDiffImplicitAt 1 (coordinateCriticalMap A B g)
      data.criticalDifferential (u.1, coordinateGapArgmax hAB u g) where
  hasFDerivAt := data.hasFDerivAt_critical
  contDiffAt := data.contDiffAt_critical
  bijective := by
    rw [data.critical_vertical]
    apply continuousLinearMap_bijective_of_apply_one_ne_zero
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      one_smul]
    exact criticalVerticalCoefficient_ne_zero
      (endpointArrayOfInterior hAB u) hd g
  ne_zero := by norm_num

private theorem gapCriticalIFTInvertible {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    (fderiv ℝ (coordinateCriticalMap A B g)
      (u.1, coordinateGapArgmax hAB u g) ∘L
      ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ).IsInvertible := by
  rw [data.hasFDerivAt_critical.fderiv]
  let L := data.criticalDifferential.comp
    (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ)
  have hbij : Function.Bijective L :=
    (gapCriticalIsContDiffImplicitAt hAB u hd g data).bijective
  exact ⟨ContinuousLinearEquiv.ofBijective L
      (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2),
    ContinuousLinearEquiv.coe_ofBijective L
      (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2)⟩

/-- The local critical branch supplied by the implicit-function theorem. -/
def localGapCriticalPoint {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) : (Fin d → ℝ) → ℝ :=
  data.contDiffAt_critical.implicitFunction (by norm_num)
    (gapCriticalIFTInvertible hAB u hd g data)

lemma localGapCriticalPoint_eq_at_base {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    localGapCriticalPoint hAB u hd g data u.1 = coordinateGapArgmax hAB u g := by
  exact data.contDiffAt_critical.implicitFunction_apply_self (by norm_num)
    (gapCriticalIFTInvertible hAB u hd g data)

lemma contDiffAt_localGapCriticalPoint {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ContDiffAt ℝ 1 (localGapCriticalPoint hAB u hd g data) u.1 :=
  data.contDiffAt_critical.contDiffAt_implicitFunction (by norm_num)
    (gapCriticalIFTInvertible hAB u hd g data)

lemma eventually_coordinateCriticalMap_localGapCriticalPoint_eq_zero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1,
      coordinateCriticalMap A B g
        (v, localGapCriticalPoint hAB u hd g data v) = 0 := by
  have hevent :=
    data.contDiffAt_critical.eventually_apply_implicitFunction (by norm_num)
      (gapCriticalIFTInvertible hAB u hd g data)
  rw [coordinateCriticalMap_eq_zero hAB u (by omega) g] at hevent
  exact hevent

/-- Pointwise identification of the IFT branch with the already-proved unique
own-gap critical point.  The explicit open-gap premise is the local geometric
condition used to select the source branch. -/
lemma localGapCriticalPoint_eq_gapArgmax_of_mem_openGap
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g)
    (v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hcritical : coordinateCriticalMap A B g
      (v.1, localGapCriticalPoint hAB u hd g data v.1) = 0)
    (hgap : localGapCriticalPoint hAB u hd g data v.1 ∈
      openGap (endpointArrayOfInterior hAB v).toOrderedNodes g) :
    localGapCriticalPoint hAB u hd g data v.1 =
      coordinateGapArgmax hAB v g := by
  have hderiv :
      (gapPolynomial (endpointArrayOfInterior hAB v).toOrderedNodes g).derivative.eval
        (localGapCriticalPoint hAB u hd g data v.1) = 0 := by
    rw [← coordinateCriticalValue_eq hAB v]
    exact hcritical
  by_cases hd1 : d = 1
  · subst d
    exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes
      (endpointArrayOfInterior hAB v).toOrderedNodes g hderiv
  · exact eq_gapArgmax_of_derivative_eval_eq_zero
      (endpointArrayOfInterior hAB v).toOrderedNodes (by omega) g hgap hderiv

/-- Abstract envelope cancellation: when the vertical derivative of the
value vanishes, the derivative of `u ↦ F(u,τ(u))` is just the horizontal
partial derivative, independently of `Dτ`. -/
lemma hasFDerivAt_envelope_of_vertical_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E × ℝ → ℝ} {F' : E × ℝ →L[ℝ] ℝ} {τ : E → ℝ}
    {τ' : E →L[ℝ] ℝ} {u : E}
    (hF : HasFDerivAt F F' (u, τ u)) (hτ : HasFDerivAt τ τ' u)
    (hvertical : F'.comp (ContinuousLinearMap.inr ℝ E ℝ) = 0) :
    HasFDerivAt (fun v => F (v, τ v))
      (F'.comp (ContinuousLinearMap.inl ℝ E ℝ)) u := by
  have hpair : HasFDerivAt (fun v : E => (v, τ v))
      ((1 : E →L[ℝ] E).prod τ') u :=
    (hasFDerivAt_id u).prodMk hτ
  have hcomp := hF.comp u hpair
  have hmaps : F'.comp ((1 : E →L[ℝ] E).prod τ') =
      F'.comp (ContinuousLinearMap.inl ℝ E ℝ) := by
    ext v
    have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L (τ' v)) hvertical
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.zero_apply] at hv
    change F' (v, τ' v) = F' (v, 0)
    rw [show (v, τ' v) = (v, 0) + (0, τ' v) by ext <;> simp]
    rw [map_add, hv, add_zero]
  rw [hmaps] at hcomp
  convert hcomp using 1 <;> try rfl

/-- The local critical-value branch.  Near the base point it is the genuine
gap height once the preceding branch-identification lemma is applied. -/
def localGapCriticalHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) : (Fin d → ℝ) → ℝ :=
  fun v => coordinateGapValue A B v g
    (localGapCriticalPoint hAB u hd g data v)

private lemma continuous_endpointPoint_coordinate {d : ℕ} (A B : ℝ)
    (k : Fin (d + 2)) :
    Continuous (fun v : Fin d → ℝ => endpointPoint A B v k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split
    · fun_prop
    · fun_prop

/-- The implicit branch remains in its owning moving gap near the base
array.  This supplies the geometric branch selection needed to use the
unique-critical-point theorem. -/
lemma eventually_localGapCriticalPoint_mem_coordinate_openGap
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1,
      endpointPoint A B v (gapLeftIndex (n := d + 2) g) <
          localGapCriticalPoint hAB u hd g data v ∧
        localGapCriticalPoint hAB u hd g data v <
          endpointPoint A B v (gapRightIndex (n := d + 2) g) := by
  have hτcont : ContinuousAt (localGapCriticalPoint hAB u hd g data) u.1 :=
    (contDiffAt_localGapCriticalPoint hAB u hd g data).continuousAt
  have hopen := gapArgmax_mem_openGap
    (endpointArrayOfInterior hAB u).toOrderedNodes (by omega) g
  have hbaseLeft :
      endpointPoint A B u.1 (gapLeftIndex (n := d + 2) g) <
        localGapCriticalPoint hAB u hd g data u.1 := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact hopen.1
  have hbaseRight :
      localGapCriticalPoint hAB u hd g data u.1 <
        endpointPoint A B u.1 (gapRightIndex (n := d + 2) g) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact hopen.2
  exact ((continuous_endpointPoint_coordinate A B
      (gapLeftIndex (n := d + 2) g)).continuousAt.eventually_lt
        hτcont hbaseLeft).and
    (hτcont.eventually_lt
      (continuous_endpointPoint_coordinate A B
        (gapRightIndex (n := d + 2) g)).continuousAt hbaseRight)

/-- Near the base point, the local critical-value branch is exactly the
compactly defined gap height for every ordered coordinate vector. -/
lemma eventually_localGapCriticalHeight_eq_coordinateGapHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    ∀ᶠ v in 𝓝 u.1, ∀ hv : v ∈ endpointNodeSpace d A B,
      localGapCriticalHeight hAB u hd g data v =
        coordinateGapHeight hAB ⟨v, hv⟩ g := by
  filter_upwards
      [eventually_coordinateCriticalMap_localGapCriticalPoint_eq_zero
        hAB u hd g data,
       eventually_localGapCriticalPoint_mem_coordinate_openGap
        hAB u hd g data] with v hcritical hgap
  intro hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  have hgap' : localGapCriticalPoint hAB u hd g data v ∈
      openGap (endpointArrayOfInterior hAB v').toOrderedNodes g := hgap
  have harg := localGapCriticalPoint_eq_gapArgmax_of_mem_openGap
    hAB u hd g data v' hcritical hgap'
  rw [coordinateGapHeight_eq_value_at_argmax]
  change coordinateGapValue A B v g
      (localGapCriticalPoint hAB u hd g data v) =
    coordinateGapValue A B v g (coordinateGapArgmax hAB v' g)
  rw [harg]

/-- A total ambient extension of the genuine gap height.  Outside the open
simplex it uses the local critical-value expression; inside it is exactly
`gapHeight`. -/
def extendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) (v : Fin d → ℝ) : ℝ := by
  classical
  exact if hv : v ∈ endpointNodeSpace d A B then
      coordinateGapHeight hAB ⟨v, hv⟩ g
    else localGapCriticalHeight hAB u hd g data v

lemma hasFDerivAt_localGapCriticalHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    HasFDerivAt (localGapCriticalHeight hAB u hd g data)
      (data.valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 := by
  have hτdiff : DifferentiableAt ℝ
      (localGapCriticalPoint hAB u hd g data) u.1 :=
    (contDiffAt_localGapCriticalPoint hAB u hd g data).differentiableAt
      (by norm_num)
  have hτ := hτdiff.hasFDerivAt
  have hvalue : HasFDerivAt (coordinateGapValueMap A B g)
      data.valueDifferential
      (u.1, localGapCriticalPoint hAB u hd g data u.1) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact data.hasFDerivAt_value
  exact hasFDerivAt_envelope_of_vertical_eq_zero hvalue hτ data.value_vertical

/-- Conditional on the explicit coordinate derivative package, the actual
gap height has a differentiable ambient extension at every array with at
least one moving node. -/
lemma hasFDerivAt_extendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) :
    HasFDerivAt (extendedCoordinateGapHeight hAB u hd g data)
      (data.valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 := by
  apply (hasFDerivAt_localGapCriticalHeight hAB u hd g data).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 u.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  filter_upwards [hspace,
    eventually_localGapCriticalHeight_eq_coordinateGapHeight
      hAB u hd g data] with v hv heq
  rw [extendedCoordinateGapHeight, dif_pos hv]
  exact (heq hv).symm

/-- On every coordinate basis vector, the checked envelope derivative is the
unconditional factored Jacobian model above. -/
lemma localGapCriticalHeight_fderiv_basis_eq_model {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1))
    (data : GapCoordinateDerivativesAt hAB u g) (j : Fin d) :
    fderiv ℝ (localGapCriticalHeight hAB u hd g data) u.1 (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) g j := by
  rw [(hasFDerivAt_localGapCriticalHeight hAB u hd g data).fderiv]
  rw [data.value_horizontal_sensitivity]
  exact (gapHeightJacobianModel_apply_eq
    (endpointArrayOfInterior hAB u) g j).symm

/-! The only downstream sign input is named as a proposition.  Importantly,
this file does not construct an inhabitant of it. -/

/-- Cross-polynomial sign/interlacing must ultimately prove these quotient
evaluation minors nonzero. -/
def QuotientEvaluationMaximalMinorsNonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  ∀ omitted : Fin (d + 1),
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0

theorem gapHeightJacobianModel_maximalMinors_nonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (hQ : QuotientEvaluationMaximalMinorsNonzero nodes) :
    ∀ omitted : Fin (d + 1),
      deletedRowMinor (gapHeightJacobianModel nodes) omitted ≠ 0 := by
  intro omitted
  exact (deletedRowMinor_gapHeightJacobianModel_ne_zero_iff
    nodes hd omitted).2 (hQ omitted)

/-! ## Discharging the coordinate-calculus interface -/

/-- One normalized scalar factor of a coordinate cardinal polynomial. -/
def coordinateLagrangeFactorValue {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k i : Fin (d + 2)) (x : ℝ) : ℝ :=
  (x - endpointPoint A B u i) *
    (endpointPoint A B u k - endpointPoint A B u i)⁻¹

lemma coordinateLagrangePolynomial_eval_eq_prod_factor {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangePolynomial A B u k).eval x =
      ∏ i ∈ Finset.univ.erase k,
        coordinateLagrangeFactorValue A B u k i x := by
  simp only [coordinateLagrangePolynomial, Polynomial.eval_prod,
    Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, coordinateLagrangeFactorValue]

@[fun_prop]
lemma differentiable_endpointPoint_coordinate {d : ℕ} (A B : ℝ)
    (k : Fin (d + 2)) :
    Differentiable ℝ (fun u : Fin d → ℝ => endpointPoint A B u k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split <;> fun_prop

lemma endpointPoint_sub_ne_zero {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) :
    endpointPoint A B u.1 k - endpointPoint A B u.1 i ≠ 0 := by
  exact sub_ne_zero.mpr
    ((endpointPoint_strictMono hAB.2.1 u.2).injective.ne hki)

lemma differentiableAt_coordinateLagrangeFactorValue {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) :
    DifferentiableAt ℝ (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeFactorValue A B z.1 k i z.2) (u.1, x) := by
  unfold coordinateLagrangeFactorValue
  apply DifferentiableAt.mul
  · exact differentiableAt_snd.sub
      ((differentiable_endpointPoint_coordinate A B i).differentiableAt.comp
        _ differentiableAt_fst)
  · apply DifferentiableAt.inv
    · exact ((differentiable_endpointPoint_coordinate A B k).differentiableAt.comp
          _ differentiableAt_fst).sub
        ((differentiable_endpointPoint_coordinate A B i).differentiableAt.comp
          _ differentiableAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u hki

lemma differentiableAt_coordinateLagrangePolynomial_eval {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) (x : ℝ) :
    DifferentiableAt ℝ (fun z : (Fin d → ℝ) × ℝ =>
      (coordinateLagrangePolynomial A B z.1 k).eval z.2) (u.1, x) := by
  simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
  let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
    fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
  have hfac : ∀ i ∈ Finset.univ.erase k,
      DifferentiableAt ℝ (fac i) (u.1, x) := by
    intro i hi
    exact differentiableAt_coordinateLagrangeFactorValue hAB u
      (Finset.mem_erase.mp hi).1.symm x
  have hprod := HasFDerivAt.finset_prod
    (g' := fun i => fderiv ℝ (fac i) (u.1, x))
    (fun i hi => (hfac i hi).hasFDerivAt)
  exact hprod.differentiableAt

lemma differentiableAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    DifferentiableAt ℝ (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  have hsum := DifferentiableAt.sum (u := Finset.univ)
    (A := fun k (z : (Fin d → ℝ) × ℝ) => gapCoefficient g k *
      (coordinateLagrangePolynomial A B z.1 k).eval z.2)
    (fun k _ => (differentiableAt_const (c := gapCoefficient g k)).mul
      (differentiableAt_coordinateLagrangePolynomial_eval hAB u k x))
  convert hsum using 1 <;> first | rfl | (funext z; simp)

/-- The derivative with respect to the evaluation variable of one cardinal
product, displayed as the product rule. -/
def coordinateLagrangeCriticalFormula {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.erase k,
    (∏ m ∈ (Finset.univ.erase k).erase i,
      coordinateLagrangeFactorValue A B u k m x) *
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹

lemma hasDerivAt_coordinateLagrangeFactorValue_evaluation {d : ℕ}
    {A B : ℝ} {u : Fin d → ℝ} {k i : Fin (d + 2)} {x : ℝ} :
    HasDerivAt (fun y => coordinateLagrangeFactorValue A B u k i y)
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹ x := by
  unfold coordinateLagrangeFactorValue
  convert ((hasDerivAt_id x).sub_const
    (endpointPoint A B u i)).mul_const
      (endpointPoint A B u k - endpointPoint A B u i)⁻¹ using 1
  all_goals first | rfl | ring

lemma coordinateLagrangeCriticalFormula_eq {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangePolynomial A B u k).derivative.eval x =
      coordinateLagrangeCriticalFormula A B u k x := by
  have hp := (coordinateLagrangePolynomial A B u k).hasDerivAt x
  have hprod := HasDerivAt.finset_prod (x := x)
    (u := Finset.univ.erase k)
    (f := fun i y => coordinateLagrangeFactorValue A B u k i y)
    (f' := fun i => (endpointPoint A B u k - endpointPoint A B u i)⁻¹)
    (fun _i _ => hasDerivAt_coordinateLagrangeFactorValue_evaluation)
  have hprod' : HasDerivAt
      (fun y => ∏ i ∈ Finset.univ.erase k,
        coordinateLagrangeFactorValue A B u k i y)
      (coordinateLagrangeCriticalFormula A B u k x) x := by
    convert hprod using 1 <;> first | rfl | (funext y; simp)
  have heqfun :
      (fun y => (coordinateLagrangePolynomial A B u k).eval y) =
        fun y => ∏ i ∈ Finset.univ.erase k,
          coordinateLagrangeFactorValue A B u k i y := by
    funext y
    exact coordinateLagrangePolynomial_eval_eq_prod_factor A B u k y
  rw [heqfun] at hp
  exact hp.unique hprod'

def coordinateGapCriticalFormula {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (x : ℝ) : ℝ :=
  ∑ k : Fin (d + 2), gapCoefficient g k *
    coordinateLagrangeCriticalFormula A B u k x

lemma coordinateGapCriticalFormula_eq {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (x : ℝ) :
    coordinateCriticalValue A B u g x =
      coordinateGapCriticalFormula A B u g x := by
  simp only [coordinateCriticalValue, coordinateGapPolynomial,
    Polynomial.derivative_sum, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
    coordinateGapCriticalFormula, coordinateLagrangeCriticalFormula_eq]

@[fun_prop]
lemma contDiff_endpointPoint_coordinate {d : ℕ} (n : WithTop ℕ∞)
    (A B : ℝ) (k : Fin (d + 2)) :
    ContDiff ℝ n (fun u : Fin d → ℝ => endpointPoint A B u k) := by
  unfold endpointPoint
  split
  · fun_prop
  · split <;> fun_prop

private lemma contDiffAt_finset_prod_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (1 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hf a (by simp)).mul (ih (fun i hi => hf i (by simp [hi])))

private lemma contDiffAt_finset_sum_scalar {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : WithTop ℕ∞)
    (s : Finset ι) (f : ι → E → ℝ) (z : E)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) z) :
    ContDiffAt ℝ n (fun w => ∑ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (contDiffAt_const (x := z) (c := (0 : ℝ)))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi])))

lemma contDiffAt_coordinateLagrangeFactorValue {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeFactorValue A B z.1 k i z.2) (u.1, x) := by
  unfold coordinateLagrangeFactorValue
  apply ContDiffAt.mul
  · exact contDiffAt_snd.sub
      ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
        (u.1, x) contDiffAt_fst)
  · apply ContDiffAt.inv
    · exact ((contDiff_endpointPoint_coordinate n A B k).contDiffAt.comp
          (u.1, x) contDiffAt_fst).sub
        ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
          (u.1, x) contDiffAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u hki

lemma contDiffAt_coordinateLagrangeCriticalFormula {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun z : (Fin d → ℝ) × ℝ =>
      coordinateLagrangeCriticalFormula A B z.1 k z.2) (u.1, x) := by
  unfold coordinateLagrangeCriticalFormula
  apply contDiffAt_finset_sum_scalar
  intro i hi
  apply ContDiffAt.mul
  · apply contDiffAt_finset_prod_scalar
    intro m hm
    exact contDiffAt_coordinateLagrangeFactorValue hAB u (by
      have hm' := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hm)).1
      exact hm'.symm) x n
  · apply ContDiffAt.inv
    · exact ((contDiff_endpointPoint_coordinate n A B k).contDiffAt.comp
          (u.1, x) contDiffAt_fst).sub
        ((contDiff_endpointPoint_coordinate n A B i).contDiffAt.comp
          (u.1, x) contDiffAt_fst)
    · exact endpointPoint_sub_ne_zero hAB u
        (Finset.mem_erase.mp hi).1.symm

lemma contDiffAt_coordinateCriticalMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (coordinateCriticalMap A B g) (u.1, x) := by
  rw [show coordinateCriticalMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        coordinateLagrangeCriticalFormula A B z.1 k z.2 by
    funext z
    exact coordinateGapCriticalFormula_eq A B z.1 g z.2]
  apply contDiffAt_finset_sum_scalar
  intro k _
  exact contDiffAt_const.mul
    (contDiffAt_coordinateLagrangeCriticalFormula hAB u k x n)

private lemma fderiv_comp_inr_eq_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hx : HasDerivAt (fun y => f (u, y)) c x) :
    (fderiv ℝ f (u, x)).comp (ContinuousLinearMap.inr ℝ E ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c := by
  have hcurve : HasFDerivAt (fun y : ℝ => (u, y))
      (ContinuousLinearMap.inr ℝ E ℝ) x := by
    convert (hasFDerivAt_const (x := x) (c := u)).prodMk
      (hasFDerivAt_id x) using 1 <;> first | rfl | (ext; simp)
  have hcomp := hf.hasFDerivAt.comp x hcurve
  exact hcomp.unique hx

lemma coordinateGapValueMap_fderiv_vertical {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    (fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)).comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (coordinateCriticalValue A B u.1 g x) := by
  apply fderiv_comp_inr_eq_of_hasDeriv
    (differentiableAt_coordinateGapValueMap hAB u g x)
  change HasDerivAt (fun y => coordinateGapValue A B u.1 g y)
    (coordinateCriticalValue A B u.1 g x) x
  simpa only [coordinateGapValue, coordinateCriticalValue] using
    (coordinateGapPolynomial A B u.1 g).hasDerivAt x

lemma coordinateCriticalMap_fderiv_vertical {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    (fderiv ℝ (coordinateCriticalMap A B g) (u.1, x)).comp
        (ContinuousLinearMap.inr ℝ (Fin d → ℝ) ℝ) =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((coordinateGapPolynomial A B u.1 g).derivative.derivative.eval x) := by
  apply fderiv_comp_inr_eq_of_hasDeriv
    ((contDiffAt_coordinateCriticalMap hAB u g x 1).differentiableAt
      (by norm_num))
  change HasDerivAt (fun y => coordinateCriticalValue A B u.1 g y)
    ((coordinateGapPolynomial A B u.1 g).derivative.derivative.eval x) x
  simpa only [coordinateCriticalValue] using
    (coordinateGapPolynomial A B u.1 g).derivative.hasDerivAt x

/-! ### Moving one interior node -/

/-- Unit coordinate direction for the `j`th interior node. -/
def coordinateDirection {d : ℕ} (j : Fin d) : Fin d → ℝ := Pi.single j 1

/-- Affine line which moves only the `j`th interior node. -/
def coordinateShift {d : ℕ} (u : Fin d → ℝ) (j : Fin d) (s : ℝ) :
    Fin d → ℝ :=
  u + s • coordinateDirection j

@[simp]
lemma coordinateShift_zero {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    coordinateShift u j 0 = u := by
  ext i
  simp [coordinateShift]

lemma coordinateShift_apply_self {d : ℕ} (u : Fin d → ℝ)
    (j : Fin d) (s : ℝ) :
    coordinateShift u j s j = u j + s := by
  simp [coordinateShift, coordinateDirection]

lemma coordinateShift_apply_of_ne {d : ℕ} (u : Fin d → ℝ)
    {j i : Fin d} (hij : i ≠ j) (s : ℝ) :
    coordinateShift u j s i = u i := by
  simp [coordinateShift, coordinateDirection, hij]

/-- Velocity of a full endpoint-adjoined node under `coordinateShift`. -/
def coordinateNodeVelocity {d : ℕ} (j : Fin d) (k : Fin (d + 2)) : ℝ :=
  if k = interiorNodeIndex j then 1 else 0

lemma hasDerivAt_endpointPoint_coordinateShift {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) :
    HasDerivAt (fun s => endpointPoint A B (coordinateShift u j s) k)
      (coordinateNodeVelocity j k) 0 := by
  rcases endpoint_index_cases k with rfl | rfl | ⟨i, rfl⟩
  · simp only [endpointPoint_left]
    have hne : endpointLeftIndex d ≠ interiorNodeIndex j :=
      (endpointLeftIndex_lt_interior j).ne
    simpa [coordinateNodeVelocity, hne] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := A))
  · simp only [endpointPoint_right]
    have hne : endpointRightIndex d ≠ interiorNodeIndex j :=
      (interior_lt_endpointRightIndex j).ne'
    simpa [coordinateNodeVelocity, hne] using
      (hasDerivAt_const (x := (0 : ℝ)) (c := B))
  · simp only [endpointPoint_interior]
    by_cases hij : i = j
    · subst i
      simp only [coordinateShift_apply_self]
      convert (hasDerivAt_const (x := (0 : ℝ)) (c := u j)).add
        (hasDerivAt_id 0) using 1 <;>
        first | rfl | (funext s; simp [coordinateNodeVelocity]) |
          simp [coordinateNodeVelocity]
    · have hfun : (fun s => coordinateShift u j s i) = fun _ => u i := by
        funext s
        exact coordinateShift_apply_of_ne u hij s
      have hnode : interiorNodeIndex i ≠ interiorNodeIndex j :=
        interiorNodeIndex_strictMono.injective.ne hij
      rw [hfun]
      simpa [coordinateNodeVelocity, hnode] using
        (hasDerivAt_const (x := (0 : ℝ)) (c := u i))

lemma endpointPoint_coordinateShift {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) (s : ℝ) :
    endpointPoint A B (coordinateShift u j s) k =
      endpointPoint A B u k + s * coordinateNodeVelocity j k := by
  rcases endpoint_index_cases k with rfl | rfl | ⟨i, rfl⟩
  · have hne : endpointLeftIndex d ≠ interiorNodeIndex j :=
      (endpointLeftIndex_lt_interior j).ne
    simp [coordinateNodeVelocity, hne]
  · have hne : endpointRightIndex d ≠ interiorNodeIndex j :=
      (interior_lt_endpointRightIndex j).ne'
    simp [coordinateNodeVelocity, hne]
  · by_cases hij : i = j
    · subst i
      simp [coordinateNodeVelocity, coordinateShift_apply_self]
    · have hne : interiorNodeIndex i ≠ interiorNodeIndex j :=
        interiorNodeIndex_strictMono.injective.ne hij
      simp [coordinateNodeVelocity, hne,
        coordinateShift_apply_of_ne u hij]

lemma hasFDerivAt_coordinateShift {d : ℕ} (u : Fin d → ℝ) (j : Fin d) :
    HasFDerivAt (coordinateShift u j)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (coordinateDirection j)) 0 := by
  let L : ℝ →L[ℝ] (Fin d → ℝ) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (coordinateDirection j)
  have h := (hasFDerivAt_const (x := (0 : ℝ)) (c := u)).add L.hasFDerivAt
  simpa [coordinateShift, L, smul_eq_mul, mul_comm] using h

/-- Polynomial form of one normalized factor. -/
def coordinateLagrangeFactorPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k i : Fin (d + 2)) : ℝ[X] :=
  (X - C (endpointPoint A B u i)) *
    C (endpointPoint A B u k - endpointPoint A B u i)⁻¹

/-- Directional derivative of one normalized factor when interior node `j`
moves.  This is the quotient rule written as a polynomial in `X`. -/
def coordinateLagrangeFactorPartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k i : Fin (d + 2)) : ℝ[X] :=
  (C (-(coordinateNodeVelocity j i) *
        (endpointPoint A B u k - endpointPoint A B u i)) -
      (X - C (endpointPoint A B u i)) *
        C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)) *
    C (((endpointPoint A B u k - endpointPoint A B u i) ^ 2)⁻¹)

lemma coordinateLagrangeFactorPolynomial_eval {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (k i : Fin (d + 2)) (x : ℝ) :
    (coordinateLagrangeFactorPolynomial A B u k i).eval x =
      coordinateLagrangeFactorValue A B u k i x := by
  simp [coordinateLagrangeFactorPolynomial,
    coordinateLagrangeFactorValue]

lemma hasDerivAt_coordinateLagrangeFactor_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) {k i : Fin (d + 2)} (hki : k ≠ i) (x : ℝ) :
    HasDerivAt (fun s => coordinateLagrangeFactorValue A B
      (coordinateShift u.1 j s) k i x)
      ((coordinateLagrangeFactorPartialPolynomial A B u.1 j k i).eval x) 0 := by
  have hti := hasDerivAt_endpointPoint_coordinateShift A B u.1 j i
  have htk := hasDerivAt_endpointPoint_coordinateShift A B u.1 j k
  have hnum : HasDerivAt
      (fun s => x - endpointPoint A B (coordinateShift u.1 j s) i)
      (-(coordinateNodeVelocity j i)) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := x)).sub hti using 1
    all_goals first | rfl | simp [coordinateNodeVelocity]
  have hden : HasDerivAt
      (fun s => endpointPoint A B (coordinateShift u.1 j s) k -
        endpointPoint A B (coordinateShift u.1 j s) i)
      (coordinateNodeVelocity j k - coordinateNodeVelocity j i) 0 := by
    exact htk.sub hti
  have hne := endpointPoint_sub_ne_zero hAB u hki
  have hquot := hnum.div hden (by simpa using hne)
  convert hquot using 1 <;>
    first
    | rfl
    | (funext s; simp [coordinateLagrangeFactorValue])
    | (simp only [coordinateLagrangeFactorPartialPolynomial,
        Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X, coordinateShift_zero]; field_simp [hne])

/-- Product-rule directional derivative of a coordinate cardinal polynomial. -/
def coordinateLagrangePartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) : ℝ[X] :=
  ∑ i ∈ Finset.univ.erase k,
    coordinateLagrangeFactorPartialPolynomial A B u j k i *
      ∏ m ∈ (Finset.univ.erase k).erase i,
        coordinateLagrangeFactorPolynomial A B u k m

/-- Directional derivative polynomial of the signed gap polynomial. -/
def coordinateGapPartialPolynomial {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (j : Fin d) : ℝ[X] :=
  ∑ k : Fin (d + 2), C (gapCoefficient g k) *
    coordinateLagrangePartialPolynomial A B u j k

lemma hasDerivAt_coordinateLagrange_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (j : Fin d) (k : Fin (d + 2)) (x : ℝ) :
    HasDerivAt (fun s =>
      (coordinateLagrangePolynomial A B (coordinateShift u.1 j s) k).eval x)
      ((coordinateLagrangePartialPolynomial A B u.1 j k).eval x) 0 := by
  let fac : Fin (d + 2) → ℝ → ℝ := fun i s =>
    coordinateLagrangeFactorValue A B (coordinateShift u.1 j s) k i x
  have hprod := HasDerivAt.finset_prod (x := (0 : ℝ))
    (u := Finset.univ.erase k) (f := fac)
    (f' := fun i =>
      (coordinateLagrangeFactorPartialPolynomial A B u.1 j k i).eval x)
    (fun i hi => hasDerivAt_coordinateLagrangeFactor_coordinateShift
      hAB u j (Finset.mem_erase.mp hi).1.symm x)
  convert hprod using 1 <;> try rfl
  · funext s
    rw [coordinateLagrangePolynomial_eval_eq_prod_factor]
    simp [fac]
  · try simp only [coordinateLagrangePartialPolynomial,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod,
      fac, coordinateLagrangeFactorPolynomial_eval, smul_eq_mul,
      coordinateShift_zero]
    apply Finset.sum_congr rfl
    intro i _
    ring

private lemma hasDerivAt_finset_sum_scalar {ι : Type*} {s : Finset ι}
    {f : ι → ℝ → ℝ} {f' : ι → ℝ} {x : ℝ}
    (hf : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, f' i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (x := x) (c := (0 : ℝ))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      convert (hf a (by simp)).add (ih (fun i hi => hf i (by simp [hi]))) using 1 <;>
        first | rfl | (funext y; simp)

lemma hasDerivAt_coordinateGapValue_coordinateShift {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    HasDerivAt (fun s => coordinateGapValue A B
      (coordinateShift u.1 j s) g x)
      ((coordinateGapPartialPolynomial A B u.1 g j).eval x) 0 := by
  rw [show (fun s => coordinateGapValue A B
      (coordinateShift u.1 j s) g x) =
      fun s => ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B
          (coordinateShift u.1 j s) k).eval x by
    funext s
    simp only [coordinateGapValue, coordinateGapPolynomial,
      Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]]
  have hsum := hasDerivAt_finset_sum_scalar (s := Finset.univ)
    (f := fun k s => gapCoefficient g k *
      (coordinateLagrangePolynomial A B
        (coordinateShift u.1 j s) k).eval x)
    (f' := fun k => gapCoefficient g k *
      (coordinateLagrangePartialPolynomial A B u.1 j k).eval x)
    (fun k _ => (hasDerivAt_coordinateLagrange_coordinateShift
      hAB u j k x).const_mul (gapCoefficient g k))
  convert hsum using 1
  simp only [coordinateGapPartialPolynomial,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]

private lemma fderiv_apply_inl_direction_eq_of_hasDeriv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E × ℝ → ℝ} {u v : E} {x c : ℝ}
    (hf : DifferentiableAt ℝ f (u, x))
    (hv : HasFDerivAt (fun s : ℝ => u + s • v)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v) 0)
    (hx : HasDerivAt (fun s : ℝ => f (u + s • v, x)) c 0) :
    fderiv ℝ f (u, x) (v, 0) = c := by
  have hcurve : HasFDerivAt (fun s : ℝ => (u + s • v, x))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v).prod
        (0 : ℝ →L[ℝ] ℝ)) 0 :=
    hv.prodMk (hasFDerivAt_const (x := (0 : ℝ)) (c := x))
  have hfbase : HasFDerivAt f (fderiv ℝ f (u, x))
      (u + (0 : ℝ) • v, x) := by
    simpa using hf.hasFDerivAt
  have hcomp := hfbase.comp 0 hcurve
  have hvalue := hcomp.unique (by
    convert hx.hasFDerivAt using 1 <;>
      first | rfl | (funext s; rfl))
  have happly := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hvalue
  simpa using happly

lemma coordinateGapValueMap_fderiv_horizontal_explicit {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)
        (coordinateDirection j, 0) =
      (coordinateGapPartialPolynomial A B u.1 g j).eval x := by
  apply fderiv_apply_inl_direction_eq_of_hasDeriv
    (differentiableAt_coordinateGapValueMap hAB u g x)
  · convert hasFDerivAt_coordinateShift u.1 j using 1 <;> try rfl
  · simpa only [coordinateGapValueMap, coordinateShift] using
      hasDerivAt_coordinateGapValue_coordinateShift hAB u g j x

/-! ### Identification of the moving-node derivative -/

lemma eventually_coordinateShift_mem_endpointNodeSpace {d : ℕ}
    {A B : ℝ}
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) (j : Fin d) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      coordinateShift u.1 j s ∈ endpointNodeSpace d A B := by
  have hmem : endpointNodeSpace d A B ∈ 𝓝 (coordinateShift u.1 j 0) := by
    simpa using (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  exact (hasFDerivAt_coordinateShift u.1 j).continuousAt.eventually hmem

lemma eventually_coordinateGapValue_shift_at_node {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (k : Fin (d + 2)) :
    ∀ᶠ s in 𝓝 (0 : ℝ),
      coordinateGapValue A B (coordinateShift u.1 j s) g
        (endpointPoint A B (coordinateShift u.1 j s) k) =
          gapCoefficient g k := by
  filter_upwards [eventually_coordinateShift_mem_endpointNodeSpace u j] with s hs
  let v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} :=
    ⟨coordinateShift u.1 j s, hs⟩
  rw [coordinateGapValue_eq hAB v]
  exact gapPolynomial_eval_node
    (endpointArrayOfInterior hAB v).toOrderedNodes g k

/-- The directional derivative polynomial has the values forced by
differentiating the interpolation equations: it vanishes at every stationary
node and equals `-F'_g(t_j)` at the moving node. -/
lemma coordinateGapPartialPolynomial_eval_node {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (k : Fin (d + 2)) :
    (coordinateGapPartialPolynomial A B u.1 g j).eval
        (endpointPoint A B u.1 k) =
      -(coordinateNodeVelocity j k) *
        (coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 k) := by
  let t : ℝ := endpointPoint A B u.1 k
  let L := fderiv ℝ (coordinateGapValueMap A B g) (u.1, t)
  have hdiff := differentiableAt_coordinateGapValueMap hAB u g t
  have hpoint := hasDerivAt_endpointPoint_coordinateShift A B u.1 j k
  have hcurve : HasFDerivAt
      (fun s : ℝ => (coordinateShift u.1 j s,
        endpointPoint A B (coordinateShift u.1 j s) k))
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (coordinateDirection j)).prod
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (coordinateNodeVelocity j k))) 0 :=
    (hasFDerivAt_coordinateShift u.1 j).prodMk hpoint.hasFDerivAt
  have hbase : (coordinateShift u.1 j 0,
      endpointPoint A B (coordinateShift u.1 j 0) k) = (u.1, t) := by
    simp [t]
  have hFbase : HasFDerivAt (coordinateGapValueMap A B g) L
      (coordinateShift u.1 j 0,
        endpointPoint A B (coordinateShift u.1 j 0) k) := by
    rw [hbase]
    exact hdiff.hasFDerivAt
  have hcomp := hFbase.comp 0 hcurve
  have hevent :
      (fun s => coordinateGapValueMap A B g
        (coordinateShift u.1 j s,
          endpointPoint A B (coordinateShift u.1 j s) k)) =ᶠ[𝓝 0]
      (fun _ => gapCoefficient g k) := by
    convert
      eventually_coordinateGapValue_shift_at_node hAB u g j k
      using 1 <;> try rfl
  have hzero : HasFDerivAt
      (fun s => coordinateGapValueMap A B g
        (coordinateShift u.1 j s,
          endpointPoint A B (coordinateShift u.1 j s) k))
      (0 : ℝ →L[ℝ] ℝ) 0 := by
    exact (hasFDerivAt_const (x := (0 : ℝ))
      (c := gapCoefficient g k)).congr_of_eventuallyEq hevent
  have hmaps := hcomp.unique hzero
  have happly := congrArg (fun M : ℝ →L[ℝ] ℝ => M 1) hmaps
  have hhorizontal := coordinateGapValueMap_fderiv_horizontal_explicit
    hAB u g j t
  have hverticalMap := coordinateGapValueMap_fderiv_vertical hAB u g t
  have hvertical := congrArg (fun M : ℝ →L[ℝ] ℝ =>
    M (coordinateNodeVelocity j k)) hverticalMap
  change L (coordinateDirection j, 0) =
      (coordinateGapPartialPolynomial A B u.1 g j).eval t at hhorizontal
  change L (0, coordinateNodeVelocity j k) =
      coordinateNodeVelocity j k *
        coordinateCriticalValue A B u.1 g t at hvertical
  have hsplit : L (coordinateDirection j, coordinateNodeVelocity j k) =
      L (coordinateDirection j, 0) +
        L (0, coordinateNodeVelocity j k) := by
    calc
      L (coordinateDirection j, coordinateNodeVelocity j k) =
          L ((coordinateDirection j, 0) +
            (0, coordinateNodeVelocity j k)) := by congr <;> simp
      _ = _ := map_add L _ _
  have happly' : L (coordinateDirection j, coordinateNodeVelocity j k) = 0 := by
    simpa using happly
  rw [hsplit, hhorizontal, hvertical] at happly'
  rw [coordinateCriticalValue] at happly'
  change (coordinateGapPartialPolynomial A B u.1 g j).eval t =
    -(coordinateNodeVelocity j k) *
      (coordinateGapPolynomial A B u.1 g).derivative.eval t
  linarith

lemma degree_coordinateLagrangeFactorPolynomial_le_one {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (k i : Fin (d + 2)) :
    (coordinateLagrangeFactorPolynomial A B u k i).degree ≤ 1 := by
  unfold coordinateLagrangeFactorPolynomial
  have hc : (C (endpointPoint A B u k - endpointPoint A B u i)⁻¹ :
      ℝ[X]).degree ≤ 0 := degree_C_le
  exact (degree_mul_le _ _).trans <| by
    simpa using add_le_add
      (degree_X_sub_C_le (R := ℝ) (endpointPoint A B u i)) hc

lemma degree_coordinateLagrangeFactorPartialPolynomial_le_one {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (j : Fin d)
    (k i : Fin (d + 2)) :
    (coordinateLagrangeFactorPartialPolynomial A B u j k i).degree ≤ 1 := by
  unfold coordinateLagrangeFactorPartialPolynomial
  apply (degree_mul_le _ _).trans
  have hcvel : (C (coordinateNodeVelocity j k -
      coordinateNodeVelocity j i) : ℝ[X]).degree ≤ 0 := degree_C_le
  have hmul : ((X - C (endpointPoint A B u i)) *
      C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)).degree ≤ 1 :=
    (degree_mul_le _ _).trans <| by
      simpa using add_le_add
        (degree_X_sub_C_le (R := ℝ) (endpointPoint A B u i)) hcvel
  have hcfirst : (C (-(coordinateNodeVelocity j i) *
      (endpointPoint A B u k - endpointPoint A B u i)) : ℝ[X]).degree ≤ 0 :=
    degree_C_le
  have hsub : (C (-(coordinateNodeVelocity j i) *
        (endpointPoint A B u k - endpointPoint A B u i)) -
      (X - C (endpointPoint A B u i)) *
        C (coordinateNodeVelocity j k - coordinateNodeVelocity j i)).degree ≤ 1 :=
    (degree_sub_le _ _).trans <| by
      exact max_le (hcfirst.trans (by simp)) hmul
  have hclast :
      (C (((endpointPoint A B u k - endpointPoint A B u i) ^ 2)⁻¹) :
        ℝ[X]).degree ≤ 0 := degree_C_le
  simpa using add_le_add hsub hclast

lemma degree_coordinateLagrangePartialPolynomial_le {d : ℕ}
    (A B : ℝ) (u : Fin d → ℝ) (j : Fin d) (k : Fin (d + 2)) :
    (coordinateLagrangePartialPolynomial A B u j k).degree ≤
      (d + 1 : ℕ) := by
  classical
  unfold coordinateLagrangePartialPolynomial
  apply (degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i hi
  apply (degree_mul_le _ _).trans
  have hcard : ((Finset.univ.erase k).erase i).card = d := by
    rw [Finset.card_erase_of_mem hi,
      Finset.card_erase_of_mem (Finset.mem_univ k),
      Finset.card_univ, Fintype.card_fin]
    omega
  have hprod :
      (∏ m ∈ (Finset.univ.erase k).erase i,
        coordinateLagrangeFactorPolynomial A B u k m).degree ≤ (d : ℕ) := by
    apply (degree_prod_le _ _).trans
    calc
      (∑ m ∈ (Finset.univ.erase k).erase i,
          (coordinateLagrangeFactorPolynomial A B u k m).degree) ≤
          ∑ _m ∈ (Finset.univ.erase k).erase i, (1 : WithBot ℕ) :=
        Finset.sum_le_sum fun m _ =>
          degree_coordinateLagrangeFactorPolynomial_le_one A B u k m
      _ = (d : ℕ) := by simp [hcard]
  simpa [Nat.cast_add, Nat.cast_one, add_comm] using
    add_le_add
      (degree_coordinateLagrangeFactorPartialPolynomial_le_one A B u j k i)
      hprod

lemma degree_coordinateGapPartialPolynomial_lt {d : ℕ} (A B : ℝ)
    (u : Fin d → ℝ) (g : Fin (d + 1)) (j : Fin d) :
    (coordinateGapPartialPolynomial A B u g j).degree < (d + 2 : ℕ) := by
  classical
  unfold coordinateGapPartialPolynomial
  have hle : (∑ k : Fin (d + 2), C (gapCoefficient g k) *
      coordinateLagrangePartialPolynomial A B u j k).degree ≤
      (d + 1 : ℕ) := by
    apply (degree_sum_le _ _).trans
    apply Finset.sup_le
    intro k _
    apply (degree_mul_le _ _).trans
    have hc : (C (gapCoefficient g k) : ℝ[X]).degree ≤ 0 := degree_C_le
    simpa using add_le_add hc
      (degree_coordinateLagrangePartialPolynomial_le A B u j k)
  exact hle.trans_lt (by
    rw [Nat.cast_withBot, Nat.cast_withBot, WithBot.coe_lt_coe]
    omega)

/-- The moving-node derivative is the source sensitivity polynomial
`-F'_g(t_j) l_j`.  The proof uses its derived nodal values and the degree
budget, rather than assuming the formula. -/
lemma coordinateGapPartialPolynomial_eq_sourceSensitivity {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) :
    coordinateGapPartialPolynomial A B u.1 g j =
      C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
        (endpointPoint A B u.1 (interiorNodeIndex j))) *
        coordinateLagrangePolynomial A B u.1 (interiorNodeIndex j) := by
  classical
  let rhs : ℝ[X] :=
    C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
      (endpointPoint A B u.1 (interiorNodeIndex j))) *
      coordinateLagrangePolynomial A B u.1 (interiorNodeIndex j)
  have hdegLeft : (coordinateGapPartialPolynomial A B u.1 g j).degree <
      ((Finset.univ : Finset (Fin (d + 2))).card : ℕ) := by
    simpa using degree_coordinateGapPartialPolynomial_lt A B u.1 g j
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
    (endpointPoint_strictMono hAB.2.1 u.2).injective.injOn hdegLeft
  · have hbasis := Lagrange.degree_basis
      (s := Finset.univ) (v := (endpointArrayOfInterior hAB u).point)
      (endpointArrayOfInterior hAB u).injective.injOn
      (Finset.mem_univ (interiorNodeIndex j))
    have hcoord : (coordinateLagrangePolynomial A B u.1
        (interiorNodeIndex j)).degree = (d + 1 : ℕ) := by
      rw [coordinateLagrangePolynomial_eq hAB u, lagrangeBasis]
      simpa using hbasis
    have hright : rhs.degree < (d + 2 : ℕ) := by
      unfold rhs
      apply (degree_mul_le _ _).trans_lt
      have hc : (C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 (interiorNodeIndex j))) : ℝ[X]).degree ≤ 0 :=
        degree_C_le
      calc
        (C (-(coordinateGapPolynomial A B u.1 g).derivative.eval
              (endpointPoint A B u.1 (interiorNodeIndex j)))).degree +
            (coordinateLagrangePolynomial A B u.1
              (interiorNodeIndex j)).degree ≤
            0 + (d + 1 : ℕ) := add_le_add hc hcoord.le
        _ < (d + 2 : ℕ) := by
          rw [zero_add, Nat.cast_withBot, Nat.cast_withBot,
            WithBot.coe_lt_coe]
          omega
    simpa only [Finset.card_univ, Fintype.card_fin] using hright
  · intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C,
      coordinateGapPartialPolynomial_eval_node hAB u g j k]
    by_cases hk : k = interiorNodeIndex j
    · subst k
      simp only [coordinateNodeVelocity]
      rw [coordinateLagrangePolynomial_eq hAB u]
      change _ = _ *
        (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j)).eval
            ((endpointArrayOfInterior hAB u).point (interiorNodeIndex j))
      rw [lagrangeBasis_eval_self, mul_one]
      norm_num
    · rw [show coordinateNodeVelocity j k = 0 by
        simp [coordinateNodeVelocity, hk]]
      simp only [neg_zero, zero_mul]
      rw [coordinateLagrangePolynomial_eq hAB u]
      have heval :
          (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
            (interiorNodeIndex j)).eval
              ((endpointArrayOfInterior hAB u).point k) = 0 :=
        lagrangeBasis_eval_of_ne _ hk
      change 0 = _ *
        (lagrangeBasis (endpointArrayOfInterior hAB u).toNodeFamily
          (interiorNodeIndex j)).eval
            ((endpointArrayOfInterior hAB u).point k)
      rw [heval, mul_zero]

lemma coordinateGapValueMap_fderiv_horizontal_source {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (j : Fin d) (x : ℝ) :
    fderiv ℝ (coordinateGapValueMap A B g) (u.1, x)
        (coordinateDirection j, 0) =
      -(coordinateGapPolynomial A B u.1 g).derivative.eval
          (endpointPoint A B u.1 (interiorNodeIndex j)) *
        (coordinateLagrangePolynomial A B u.1
          (interiorNodeIndex j)).eval x := by
  rw [coordinateGapValueMap_fderiv_horizontal_explicit hAB u g j x,
    coordinateGapPartialPolynomial_eq_sourceSensitivity hAB u g j,
    Polynomial.eval_mul, Polynomial.eval_C]

/-! ### The concrete derivative package and unconditional height Jacobian -/

/-- The formerly abstract coordinate derivative package, now constructed
from the finite product and interpolation calculations above. -/
def concreteGapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : GapCoordinateDerivativesAt hAB u g where
  criticalDifferential := fderiv ℝ (coordinateCriticalMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  valueDifferential := fderiv ℝ (coordinateGapValueMap A B g)
    (u.1, coordinateGapArgmax hAB u g)
  hasFDerivAt_critical :=
    ((contDiffAt_coordinateCriticalMap hAB u g
      (coordinateGapArgmax hAB u g) 1).differentiableAt
        (by norm_num)).hasFDerivAt
  contDiffAt_critical :=
    contDiffAt_coordinateCriticalMap hAB u g
      (coordinateGapArgmax hAB u g) 1
  critical_vertical := by
    rw [coordinateCriticalMap_fderiv_vertical hAB u g
      (coordinateGapArgmax hAB u g)]
    rw [coordinateGapPolynomial_eq hAB u]
    rfl
  hasFDerivAt_value :=
    (differentiableAt_coordinateGapValueMap hAB u g
      (coordinateGapArgmax hAB u g)).hasFDerivAt
  value_vertical := by
    rw [coordinateGapValueMap_fderiv_vertical hAB u g
      (coordinateGapArgmax hAB u g)]
    have hcrit : coordinateCriticalValue A B u.1 g
        (coordinateGapArgmax hAB u g) = 0 := by
      by_cases hd : d = 0
      · subst d
        exact coordinateCriticalValue_zero_dim hAB u g _
      · exact coordinateCriticalMap_eq_zero hAB u
          (Nat.one_le_iff_ne_zero.mpr hd) g
    rw [hcrit]
    ext
    simp
  value_horizontal_sensitivity := by
    intro j
    change fderiv ℝ (coordinateGapValueMap A B g)
      (u.1, coordinateGapArgmax hAB u g) (Pi.single j 1, 0) = _
    rw [show Pi.single j 1 = coordinateDirection j by rfl,
      coordinateGapValueMap_fderiv_horizontal_source hAB u g j
        (coordinateGapArgmax hAB u g)]
    rw [coordinateGapPolynomial_eq hAB u,
      coordinateLagrangePolynomial_eq hAB u, lagrangeBasis_eval]
    rfl

/-- The analytic interface is inhabited at every simplex point, in every
dimension including the zero-dimensional/two-node exception. -/
theorem exists_gapCoordinateDerivativesAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) : Nonempty (GapCoordinateDerivativesAt hAB u g) :=
  ⟨concreteGapCoordinateDerivativesAt hAB u g⟩

/-- Canonical ambient extension of the genuine compact gap height.  On the
open simplex it is definitionally the compact height, while its off-simplex
values merely provide a total domain for Fréchet differentiation. -/
def canonicalExtendedCoordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) : (Fin d → ℝ) → ℝ :=
  extendedCoordinateGapHeight hAB u hd g
    (concreteGapCoordinateDerivativesAt hAB u g)

/-- Unconditional differentiability of a local ambient extension of the
coordinate gap height. -/
theorem hasFDerivAt_canonicalExtendedCoordinateGapHeight {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    HasFDerivAt (canonicalExtendedCoordinateGapHeight hAB u hd g)
      ((concreteGapCoordinateDerivativesAt hAB u g).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) u.1 :=
  hasFDerivAt_extendedCoordinateGapHeight hAB u hd g
    (concreteGapCoordinateDerivativesAt hAB u g)

/-- Unconditional Jacobian-entry formula for genuine coordinate gap heights.
The right-hand side is the already-factored quotient-evaluation model. -/
theorem canonicalCoordinateGapHeight_fderiv_basis_eq_model {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) (j : Fin d) :
    fderiv ℝ (canonicalExtendedCoordinateGapHeight hAB u hd g) u.1
        (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) g j := by
  rw [(hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd g).fderiv]
  exact ((concreteGapCoordinateDerivativesAt hAB u g).value_horizontal_sensitivity
    j).trans
      (gapHeightJacobianModel_apply_eq
        (endpointArrayOfInterior hAB u) g j).symm

end

end Randy1153.DeBoorPinkus
