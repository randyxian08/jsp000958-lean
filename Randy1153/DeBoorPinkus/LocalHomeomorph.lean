import Randy1153.DeBoorPinkus.Jacobian
import Randy1153.DeBoorPinkus.Statement
import Randy1153.DeBoorPinkus.GlobalHomeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.LinearAlgebra.Determinant

/-!
# The local homeomorphism of consecutive gap-height differences

This file passes from the checked coordinate derivative of each individual
gap height to the source map

`Γ_i = h_{i+1} - h_i`.

Continuity is unconditional.  The sole algebraic input to the inverse
function theorem is isolated as nonvanishing of the determinant of the
explicit consecutive-row-difference matrix.  No inhabitant of that
proposition is asserted here; it is the output expected from the coherent
maximal-minor sign argument.
-/

namespace Randy1153.DeBoorPinkus

open Filter Function Topology

noncomputable section

/-! ## The explicit Jacobian model -/

/-- Consecutive row differences of the checked gap-height Jacobian. -/
def gapDifferenceJacobianModel {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => gapHeightJacobianModel nodes i.succ j -
    gapHeightJacobianModel nodes i.castSucc j

/-- The exact algebraic residue of the local-homeomorphism argument.
It is deliberately a proposition, not an assumed theorem. -/
def GapDifferenceJacobianDeterminantCondition (d : ℕ) (A B : ℝ) : Prop :=
  ∀ nodes : EndpointArray d A B,
    Matrix.det (gapDifferenceJacobianModel nodes) ≠ 0

/-! ## `C¹` regularity of the local critical-value extension -/

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

/-- The rational coordinate gap-value map is `C¹` at every simplex point
and every evaluation point. -/
lemma contDiffAt_coordinateGapValueMap {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (g : Fin (d + 1)) (x : ℝ) :
    ContDiffAt ℝ 1 (coordinateGapValueMap A B g) (u.1, x) := by
  rw [show coordinateGapValueMap A B g = fun z =>
      ∑ k : Fin (d + 2), gapCoefficient g k *
        (coordinateLagrangePolynomial A B z.1 k).eval z.2 by
    funext z
    simp only [coordinateGapValueMap, coordinateGapValue,
      coordinateGapPolynomial, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]]
  apply contDiffAt_finset_sum_scalar
  intro k _
  exact contDiffAt_const.mul (by
    simp only [coordinateLagrangePolynomial_eval_eq_prod_factor]
    let fac : Fin (d + 2) → ((Fin d → ℝ) × ℝ) → ℝ :=
      fun i z => coordinateLagrangeFactorValue A B z.1 k i z.2
    have hfac : ∀ i ∈ Finset.univ.erase k,
        ContDiffAt ℝ 1 (fac i) (u.1, x) := by
      intro i hi
      exact contDiffAt_coordinateLagrangeFactorValue hAB u
        (Finset.mem_erase.mp hi).1.symm x 1
    exact contDiffAt_finset_prod_scalar 1 (Finset.univ.erase k) fac
      (u.1, x) hfac)

/-- The genuine local critical-value branch is `C¹` at its base point. -/
lemma contDiffAt_localGapCriticalHeight_concrete {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ContDiffAt ℝ 1
      (localGapCriticalHeight hAB u hd g
        (concreteGapCoordinateDerivativesAt hAB u g)) u.1 := by
  let data := concreteGapCoordinateDerivativesAt hAB u g
  have hpair : ContDiffAt ℝ 1
      (fun v : Fin d → ℝ =>
        (v, localGapCriticalPoint hAB u hd g data v)) u.1 :=
    contDiffAt_id.prodMk
      (contDiffAt_localGapCriticalPoint hAB u hd g data)
  have hvalue : ContDiffAt ℝ 1 (coordinateGapValueMap A B g)
      (u.1, localGapCriticalPoint hAB u hd g data u.1) := by
    rw [localGapCriticalPoint_eq_at_base hAB u hd g data]
    exact contDiffAt_coordinateGapValueMap hAB u g
      (coordinateGapArgmax hAB u g)
  convert hvalue.comp u.1 hpair using 1 <;> rfl

/-- The canonical ambient extension used for differentiation is `C¹` at
its base point. -/
lemma contDiffAt_canonicalExtendedCoordinateGapHeight {d : ℕ}
    {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ContDiffAt ℝ 1
      (canonicalExtendedCoordinateGapHeight hAB u hd g) u.1 := by
  let data := concreteGapCoordinateDerivativesAt hAB u g
  apply (contDiffAt_localGapCriticalHeight_concrete hAB u hd g).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 u.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds u.2
  filter_upwards [hspace,
    eventually_localGapCriticalHeight_eq_coordinateGapHeight
      hAB u hd g data] with v hv heq
  rw [canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos hv]
  exact (heq hv).symm

/-! ## Continuity of genuine gap heights -/

lemma continuous_coordinateGapHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (g : Fin (d + 1)) :
    Continuous (fun u : {v : Fin d → ℝ //
      v ∈ endpointNodeSpace d A B} => coordinateGapHeight hAB u g) := by
  rw [continuous_iff_continuousAt]
  intro u
  by_cases hd0 : d = 0
  · subst d
    have heq : (fun v : {w : Fin 0 → ℝ //
        w ∈ endpointNodeSpace 0 A B} => coordinateGapHeight hAB v g) =
        fun _ => (1 : ℝ) := by
      funext v
      exact coordinateGapHeight_zero_dim hAB v g
    rw [heq]
    exact continuousAt_const
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hamb :=
      (hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd g).continuousAt
    have hcomp := hamb.comp continuousAt_subtype_val
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [] with v
    change coordinateGapHeight hAB v g =
      canonicalExtendedCoordinateGapHeight hAB u hd g v.1
    rw [canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
      dif_pos v.2]

/-- Each compactly defined gap height is continuous in the induced endpoint
array topology. -/
theorem continuous_endpointArray_height_of_admissible {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (g : Fin (d + 1)) :
    Continuous (fun nodes : EndpointArray d A B => nodes.height g) := by
  let H : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → ℝ :=
    fun u => coordinateGapHeight hAB u g
  have hH : Continuous H := continuous_coordinateGapHeight hAB g
  have heq : (fun nodes : EndpointArray d A B => nodes.height g) =
      H ∘ endpointArrayHomeomorph hAB := by
    funext nodes
    change nodes.height g = coordinateGapHeight hAB
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ g
    rw [coordinateGapHeight, endpointArrayOfInterior_interior]
    rfl
  rw [heq]
  exact hH.comp (endpointArrayHomeomorph hAB).continuous

/-- Each gap height is continuous for arbitrary endpoint parameters.  At a
point of the domain, the endpoint array itself supplies the required
admissible-interval witness; if the domain is empty there are no points to
check. -/
theorem continuous_endpointArray_height {d : ℕ} {A B : ℝ}
    (g : Fin (d + 1)) :
    Continuous (fun nodes : EndpointArray d A B => nodes.height g) := by
  rw [continuous_iff_continuousAt]
  intro nodes
  exact (continuous_endpointArray_height_of_admissible
    nodes.admissibleInterval g).continuousAt

/-- The source map `Γ` is continuous, with no interval or Jacobian-sign
hypothesis. -/
theorem continuous_gapDifference {d : ℕ} {A B : ℝ} :
    Continuous (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  apply continuous_pi
  intro i
  exact (continuous_endpointArray_height i.succ).sub
    (continuous_endpointArray_height i.castSucc)

/-- The version with an explicit interval witness is retained as a direct
bridge for callers already carrying one. -/
theorem continuous_gapDifference_of_admissible {d : ℕ} {A B : ℝ}
    (_hAB : AdmissibleInterval A B) :
    Continuous (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  exact continuous_gapDifference

/-! ## The ambient derivative of consecutive differences -/

/-- A total ambient representative of `Γ` based at one simplex point. -/
def canonicalExtendedCoordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) : (Fin d → ℝ) → Fin d → ℝ :=
  fun v i =>
    canonicalExtendedCoordinateGapHeight hAB u hd i.succ v -
      canonicalExtendedCoordinateGapHeight hAB u hd i.castSucc v

/-- Its checked differential, formed before choosing any matrix
coordinates. -/
def gapDifferenceDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ) -
      (concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

theorem hasFDerivAt_canonicalExtendedCoordinateGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateGapDifference hAB u hd)
      (gapDifferenceDifferentialAt hAB u hd) u.1 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).sub
    (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc)

theorem contDiffAt_canonicalExtendedCoordinateGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    ContDiffAt ℝ 1 (canonicalExtendedCoordinateGapDifference hAB u hd) u.1 := by
  rw [contDiffAt_pi]
  intro i
  exact (contDiffAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).sub
    (contDiffAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc)

/-- Every coordinate entry of the differential is literally the difference
of the two consecutive rows of `gapHeightJacobianModel`. -/
theorem gapDifferenceDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (i j : Fin d) :
    gapDifferenceDifferentialAt hAB u hd (Pi.single j 1) i =
      gapDifferenceJacobianModel (endpointArrayOfInterior hAB u) i j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) -
      ((concreteGapCoordinateDerivativesAt hAB u i.castSucc).valueDifferential.comp
        (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.succ).fderiv,
    ← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
      hAB u hd i.castSucc).fderiv,
    canonicalCoordinateGapHeight_fderiv_basis_eq_model,
    canonicalCoordinateGapHeight_fderiv_basis_eq_model]
  rfl

/-- Matrix form of the preceding entrywise derivative theorem. -/
theorem gapDifferenceDifferentialAt_toMatrix_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    LinearMap.toMatrix' (gapDifferenceDifferentialAt hAB u hd).toLinearMap =
      gapDifferenceJacobianModel (endpointArrayOfInterior hAB u) := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  exact gapDifferenceDifferentialAt_basis_eq_model hAB u hd i j

/-- Therefore the determinant condition is exactly invertibility of the
actual ambient differential consumed by the inverse function theorem. -/
theorem gapDifferenceDifferentialAt_det_ne_zero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hdet : Matrix.det
      (gapDifferenceJacobianModel (endpointArrayOfInterior hAB u)) ≠ 0) :
    (gapDifferenceDifferentialAt hAB u hd).det ≠ 0 := by
  change LinearMap.det (gapDifferenceDifferentialAt hAB u hd).toLinearMap ≠ 0
  rw [← LinearMap.det_toMatrix',
    gapDifferenceDifferentialAt_toMatrix_eq_model hAB u hd]
  exact hdet

/-! ## Restriction to the open simplex and inverse function theorem -/

/-- The genuine source map in the open-simplex chart. -/
def coordinateGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => gapDifference (endpointArrayOfInterior hAB v)

lemma canonicalExtendedCoordinateGapDifference_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    canonicalExtendedCoordinateGapDifference hAB u hd v.1 =
      coordinateGapDifference hAB v := by
  funext i
  simp only [canonicalExtendedCoordinateGapDifference,
    canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos v.2, coordinateGapDifference, gapDifference,
    coordinateGapHeight]
  rfl

/-- On the positive-dimensional simplex, the determinant condition gives
a local homeomorphism by the finite-dimensional `C¹` inverse function
theorem. -/
theorem isLocalHomeomorph_coordinateGapDifference_of_determinant
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B) (hd : 1 ≤ d)
    (hdet : GapDifferenceJacobianDeterminantCondition d A B) :
    IsLocalHomeomorph (coordinateGapDifference (d := d) hAB) := by
  apply IsLocalHomeomorph.mk
  intro u
  let F := canonicalExtendedCoordinateGapDifference hAB u hd
  let L := gapDifferenceDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    gapDifferenceDifferentialAt_det_ne_zero hAB u hd
      (hdet (endpointArrayOfInterior hAB u))
  let eL : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    L.toContinuousLinearEquivOfDetNeZero hLdet
  have hFderiv : HasFDerivAt F (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    change HasFDerivAt (canonicalExtendedCoordinateGapDifference hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateGapDifference hAB u hd
  have hFcont : ContDiffAt ℝ 1 F u.1 :=
    contDiffAt_canonicalExtendedCoordinateGapDifference hAB u hd
  let e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
    hFcont.toOpenPartialHomeomorph F hFderiv (by norm_num)
  have hue : u.1 ∈ e.source :=
    hFcont.mem_toOpenPartialHomeomorph_source hFderiv (by norm_num)
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨endpointNodeSpace d A B, isOpen_endpointNodeSpace d A B⟩
  have hS : Nonempty S := ⟨u⟩
  let es : OpenPartialHomeomorph S (Fin d → ℝ) := e.subtypeRestr hS
  refine ⟨es, ?_, ?_⟩
  · simpa only [es, OpenPartialHomeomorph.subtypeRestr_source,
      Set.mem_preimage] using hue
  · intro v _hv
    change coordinateGapDifference hAB v = F v.1
    exact (canonicalExtendedCoordinateGapDifference_eq_coordinate
      hAB u v hd).symm

/-! ## Endpoint arrays, including dimension zero -/

/-- In dimension zero the displayed determinant condition holds
automatically: both matrix index types are empty. -/
theorem gapDifferenceJacobianDeterminantCondition_zero (A B : ℝ) :
    GapDifferenceJacobianDeterminantCondition 0 A B := by
  intro nodes
  simp

private theorem isLocalHomeomorph_gapDifference_zero
    {A B : ℝ} (hAB : AdmissibleInterval A B) :
    IsLocalHomeomorph
      (gapDifference : EndpointArray 0 A B → Fin 0 → ℝ) := by
  let u0 : Fin 0 → ℝ := fun i => Fin.elim0 i
  have hu0 : u0 ∈ endpointNodeSpace 0 A B := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun i => Fin.elim0 i
    · intro i
      exact Fin.elim0 i
    · exact fun i => Fin.elim0 i
  let S := {u : Fin 0 → ℝ // u ∈ endpointNodeSpace 0 A B}
  letI : Unique S := {
    default := ⟨u0, hu0⟩
    uniq := fun v => Subtype.ext (Subsingleton.elim _ _) }
  let e0 : S ≃ₜ (Fin 0 → ℝ) :=
    Homeomorph.homeomorphOfUnique S (Fin 0 → ℝ)
  let e : EndpointArray 0 A B ≃ₜ (Fin 0 → ℝ) :=
    (endpointArrayHomeomorph hAB).trans e0
  have heq : (gapDifference : EndpointArray 0 A B → Fin 0 → ℝ) = e := by
    funext nodes
    exact Subsingleton.elim _ _
  rw [heq]
  exact e.isLocalHomeomorph

/-- Shortest checked route from the explicit determinant condition to the
canonical unconditional local-homeomorphism statement.  At each array, that
array supplies its own admissible-interval witness.  Thus arbitrary `A,B`,
including an empty endpoint-array domain, are handled honestly.  The `d = 0`
branch is discharged without invoking a positive-dimensional critical-point
theorem. -/
theorem gapDifference_localHomeomorphStatement_of_determinant
    (d : ℕ) (A B : ℝ)
    (hdet : GapDifferenceJacobianDeterminantCondition d A B) :
    GapDifferenceLocalHomeomorphStatement d A B := by
  intro nodes
  let hAB : AdmissibleInterval A B := nodes.admissibleInterval
  by_cases hd0 : d = 0
  · subst d
    exact (isLocalHomeomorph_gapDifference_zero hAB) nodes
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    have hcoord :=
      isLocalHomeomorph_coordinateGapDifference_of_determinant hAB hd hdet
    have hchart := (endpointArrayHomeomorph (d := d) hAB).isLocalHomeomorph
    have hcomp := hcoord.comp hchart
    have heq :
        (gapDifference : EndpointArray d A B → Fin d → ℝ) =
          coordinateGapDifference hAB ∘ endpointArrayHomeomorph hAB := by
      funext r
      change gapDifference r = gapDifference
        (endpointArrayOfInterior hAB
          ⟨r.interior, r.interior_mem_endpointNodeSpace⟩)
      rw [endpointArrayOfInterior_interior]
    rw [heq]
    exact hcomp nodes

/-- Discharge the committed canonical continuity proposition, with no
interval or determinant input. -/
theorem gapDifference_continuityStatement (d : ℕ) (A B : ℝ) :
    GapDifferenceContinuityStatement d A B :=
  continuous_gapDifference

end

end Randy1153.DeBoorPinkus
