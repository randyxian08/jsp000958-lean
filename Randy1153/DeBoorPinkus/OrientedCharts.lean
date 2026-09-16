import Randy1153.DeBoorPinkus.Jacobian
import Randy1153.DeBoorPinkus.LocalHomeomorph
import Randy1153.DeBoorPinkus.Orientation
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Oriented local charts for the tail-height map

This file supplies the analytic input isolated by `Orientation.lean`.  The
tail heights have the height-Jacobian with row zero deleted.  Coherent signs
make this square differential invertible; the inverse function theorem then
gives a chart.  Cramer's rule identifies every partial derivative of the
omitted height with the strictly negative coefficient recorded in
`heightZeroCramerCoefficient`.  Integrating those derivatives along a line
segment in a convex target proves the required strict order reversal.
-/

namespace Randy1153.DeBoorPinkus

open Filter Function Topology
open scoped BigOperators Matrix

noncomputable section

/-! ## The tail-height differential -/

/-- An ambient representative of all heights except height zero. -/
def canonicalExtendedCoordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) : (Fin d → ℝ) → Fin d → ℝ :=
  fun v i => canonicalExtendedCoordinateGapHeight hAB u hd i.succ v

/-- The differential of the ambient tail-height representative. -/
def tailHeightDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (_hd : 1 ≤ d) : (Fin d → ℝ) →L[ℝ] Fin d → ℝ :=
  ContinuousLinearMap.pi fun i =>
    (concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

theorem hasFDerivAt_canonicalExtendedCoordinateTailHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB u hd)
      (tailHeightDifferentialAt hAB u hd) u.1 := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact hasFDerivAt_canonicalExtendedCoordinateGapHeight hAB u hd i.succ

theorem contDiffAt_canonicalExtendedCoordinateTailHeight
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    ContDiffAt ℝ 1 (canonicalExtendedCoordinateTailHeight hAB u hd) u.1 := by
  rw [contDiffAt_pi]
  intro i
  exact contDiffAt_canonicalExtendedCoordinateGapHeight hAB u hd i.succ

theorem tailHeightDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (i j : Fin d) :
    tailHeightDifferentialAt hAB u hd (Pi.single j 1) i =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) i.succ j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u i.succ).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB u hd i.succ).fderiv]
  exact canonicalCoordinateGapHeight_fderiv_basis_eq_model hAB u hd i.succ j

theorem tailHeightDifferentialAt_toMatrix_eq_deletedZero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    LinearMap.toMatrix' (tailHeightDifferentialAt hAB u hd).toLinearMap =
      (gapHeightJacobianModel (endpointArrayOfInterior hAB u)).submatrix
        (0 : Fin (d + 1)).succAbove id := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  simpa using tailHeightDifferentialAt_basis_eq_model hAB u hd i j

theorem tailHeightDifferentialAt_det_eq_deletedZero
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    (tailHeightDifferentialAt hAB u hd).det =
      deletedRowMinor (gapHeightJacobianModel
        (endpointArrayOfInterior hAB u)) (0 : Fin (d + 1)) := by
  change LinearMap.det (tailHeightDifferentialAt hAB u hd).toLinearMap = _
  rw [← LinearMap.det_toMatrix',
    tailHeightDifferentialAt_toMatrix_eq_deletedZero hAB u hd]
  rfl

theorem tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (tailHeightDifferentialAt hAB u hd).det ≠ 0 := by
  rw [tailHeightDifferentialAt_det_eq_deletedZero hAB u hd]
  exact deletedRowMinor_ne_zero_of_coherentSigns hsigns _

/-! ## The deleted-row Cramer identity -/

private lemma updateRow_tailMatrix_eq_permuted_deletedRow
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    (H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0) =
      (H.submatrix k.succ.succAbove id).submatrix k.cycleRange id := by
  letI : NeZero d := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt k.isLt)⟩
  ext i j
  by_cases hik : i = k
  · subst i
    simp
  · by_cases hil : i < k
    · rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_lt hil]
      rw [Fin.succAbove_succ_of_le k (i + 1) (by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one_of_lt' (by omega)]
        omega)]
      apply congrArg (fun q => H q j)
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_succ,
        Fin.val_add_one_of_lt' (by omega)]
    · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hil) (Ne.symm hik)
      rw [Matrix.updateRow_ne hik]
      simp only [Matrix.submatrix_apply, id_eq, Fin.zero_succAbove]
      rw [Fin.cycleRange_of_gt hki]
      rw [Fin.succAbove_succ_of_lt k i hki]

/-- Replacing row `k` of the tail matrix by row zero is the deleted-`k+1`
minor, with exactly the row-cycle sign used in source equation (8). -/
theorem det_updateRow_tailMatrix
    {d : ℕ} (H : Matrix (Fin (d + 1)) (Fin d) ℝ) (k : Fin d) :
    ((H.submatrix (0 : Fin (d + 1)).succAbove id).updateRow k (H 0)).det =
      (-1 : ℝ) ^ (k.val + 2) * deletedRowMinor H k.succ := by
  rw [updateRow_tailMatrix_eq_permuted_deletedRow H k, Matrix.det_permute]
  simp only [Fin.sign_cycleRange, deletedRowMinor]
  norm_num [pow_add]

/-! ## Cramer's rule for the omitted height -/

/-- The differential of height zero at an ordered coordinate vector. -/
def heightZeroDifferentialAt {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (Fin d → ℝ) →L[ℝ] ℝ :=
  (concreteGapCoordinateDerivativesAt hAB u (0 : Fin (d + 1))).valueDifferential.comp
    (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)

theorem heightZeroDifferentialAt_basis_eq_model
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (j : Fin d) :
    heightZeroDifferentialAt hAB u (Pi.single j 1) =
      gapHeightJacobianModel (endpointArrayOfInterior hAB u) 0 j := by
  change
    ((concreteGapCoordinateDerivativesAt hAB u 0).valueDifferential.comp
      (ContinuousLinearMap.inl ℝ (Fin d → ℝ) ℝ)) (Pi.single j 1) = _
  rw [← (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB u hd 0).fderiv]
  exact canonicalCoordinateGapHeight_fderiv_basis_eq_model hAB u hd 0 j

private lemma continuousLinearEquiv_symm_apply_eq_nonsingInv_mulVec
    {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) (hdet : L.det ≠ 0)
    (v : Fin d → ℝ) :
    (L.toContinuousLinearEquivOfDetNeZero hdet).symm v =
      ((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v := by
  let eL := L.toContinuousLinearEquivOfDetNeZero hdet
  apply eL.injective
  change L (eL.symm v) = L
    (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v)
  rw [show L (eL.symm v) = v by
    change eL (eL.symm v) = v
    exact eL.apply_symm_apply v]
  symm
  calc
    L (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v) =
        LinearMap.toMatrix' L.toLinearMap *ᵥ
          (((LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v) :=
      (LinearMap.toMatrix'_mulVec L.toLinearMap _).symm
    _ = ((LinearMap.toMatrix' L.toLinearMap) *
          (LinearMap.toMatrix' L.toLinearMap)⁻¹) *ᵥ v := by
      rw [Matrix.mulVec_mulVec]
    _ = v := by
      rw [Matrix.mul_nonsing_inv]
      · exact Matrix.one_mulVec v
      · exact isUnit_iff_ne_zero.mpr (by
          rw [LinearMap.det_toMatrix']
          exact hdet)

/-- The actual inverse-chart partial derivative of height zero is the
source's deleted-minor quotient. -/
theorem heightZeroDifferential_comp_tailInverse_basis
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) (k : Fin d) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap
        (Pi.single k 1) =
      heightZeroCramerCoefficient (endpointArrayOfInterior hAB u) hd k := by
  let H := gapHeightJacobianModel (endpointArrayOfInterior hAB u)
  let T := H.submatrix (0 : Fin (d + 1)).succAbove id
  let L := tailHeightDifferentialAt hAB u hd
  let D := heightZeroDifferentialAt hAB u
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  have hT : LinearMap.toMatrix' L.toLinearMap = T := by
    exact tailHeightDifferentialAt_toMatrix_eq_deletedZero hAB u hd
  have hTdet : T.det ≠ 0 := by
    rw [← hT, LinearMap.det_toMatrix']
    exact hLdet
  have hTunit : IsUnit T.det := isUnit_iff_ne_zero.mpr hTdet
  have hD : ∀ j : Fin d, D (Pi.single j 1) = H 0 j := by
    intro j
    exact heightZeroDifferentialAt_basis_eq_model hAB u hd j
  have hinv :
      (L.toContinuousLinearEquivOfDetNeZero hLdet).symm (Pi.single k 1) =
        (T⁻¹) *ᵥ Pi.single k 1 := by
    rw [continuousLinearEquiv_symm_apply_eq_nonsingInv_mulVec L hLdet]
    rw [hT]
  change D ((L.toContinuousLinearEquivOfDetNeZero hLdet).symm
    (Pi.single k 1)) = _
  rw [hinv]
  have hD_apply (v : Fin d → ℝ) : D v = H 0 ⬝ᵥ v := by
    have hv : v = ∑ i : Fin d,
        (v i) • (Pi.single i (1 : ℝ) : Fin d → ℝ) :=
      pi_eq_sum_univ' v
    calc
      D v = D (∑ i : Fin d,
          (v i) • (Pi.single i (1 : ℝ) : Fin d → ℝ)) := congrArg D hv
      _ = ∑ i, v i * H 0 i := by
        simp only [map_sum, map_smul, smul_eq_mul, hD]
      _ = H 0 ⬝ᵥ v := by
        simp only [dotProduct]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hD_apply, Matrix.dotProduct_mulVec, dotProduct_single_one]
  have hcramer := Matrix.det_smul_inv_vecMul_eq_cramer_transpose
    T (H 0) hTunit
  have hcramerK := congrFun hcramer k
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_transpose_apply] at hcramerK
  rw [det_updateRow_tailMatrix H k] at hcramerK
  rw [heightZeroCramerCoefficient]
  change (H 0 ᵥ* T⁻¹) k =
    (-1) ^ (k.val + 2) * deletedRowMinor H k.succ /
      deletedRowMinor H 0
  have hTdetMinor : T.det = deletedRowMinor H 0 := rfl
  rw [← hTdetMinor]
  apply (eq_div_iff hTdet).2
  nlinarith

/-! ## The genuine tail map on the open simplex -/

/-- Tail gap heights in the interior-coordinate chart. -/
def coordinateTailHeight {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ :=
  fun v => tailGapHeight (endpointArrayOfInterior hAB v)

lemma canonicalExtendedCoordinateTailHeight_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    canonicalExtendedCoordinateTailHeight hAB u hd v.1 =
      coordinateTailHeight hAB v := by
  funext i
  simp only [canonicalExtendedCoordinateTailHeight,
    canonicalExtendedCoordinateGapHeight, extendedCoordinateGapHeight,
    dif_pos v.2, coordinateTailHeight, tailGapHeight,
    coordinateGapHeight]
  rfl

lemma canonicalExtendedCoordinateGapHeight_eq_coordinate
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u v : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) (g : Fin (d + 1)) :
    canonicalExtendedCoordinateGapHeight hAB u hd g v.1 =
      coordinateGapHeight hAB v g := by
  simp only [canonicalExtendedCoordinateGapHeight,
    extendedCoordinateGapHeight, dif_pos v.2]

/-- Although the inverse-function chart is constructed from an ambient
representative based at one point, at every other simplex point its
derivative is the point's own concrete tail differential. -/
theorem hasFDerivAt_canonicalTailHeight_at_simplexPoint
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base x : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB base hd)
      (tailHeightDifferentialAt hAB x hd) x.1 := by
  apply (hasFDerivAt_canonicalExtendedCoordinateTailHeight
    hAB x hd).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 x.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds x.2
  filter_upwards [hspace] with v hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  exact (canonicalExtendedCoordinateTailHeight_eq_coordinate
    hAB base v' hd).trans
      (canonicalExtendedCoordinateTailHeight_eq_coordinate hAB x v' hd).symm

/-- The analogous base-independence for the omitted height. -/
theorem hasFDerivAt_canonicalHeightZero_at_simplexPoint
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base x : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d) :
    HasFDerivAt (canonicalExtendedCoordinateGapHeight hAB base hd 0)
      (heightZeroDifferentialAt hAB x) x.1 := by
  apply (hasFDerivAt_canonicalExtendedCoordinateGapHeight
    hAB x hd 0).congr_of_eventuallyEq
  have hspace : endpointNodeSpace d A B ∈ 𝓝 x.1 :=
    (isOpen_endpointNodeSpace d A B).mem_nhds x.2
  filter_upwards [hspace] with v hv
  let v' : {w : Fin d → ℝ // w ∈ endpointNodeSpace d A B} := ⟨v, hv⟩
  exact (canonicalExtendedCoordinateGapHeight_eq_coordinate
    hAB base v' hd 0).trans
      (canonicalExtendedCoordinateGapHeight_eq_coordinate hAB x v' hd 0).symm

theorem heightZeroDifferential_comp_tailInverse_apply
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) (w : Fin d → ℝ) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap w =
      ∑ k, w k * heightZeroCramerCoefficient
        (endpointArrayOfInterior hAB u) hd k := by
  let C := (heightZeroDifferentialAt hAB u).comp
    ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
      (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
        hAB u hd hsigns)).symm.toContinuousLinearMap
  have hw : w = ∑ k : Fin d,
      (w k) • (Pi.single k (1 : ℝ) : Fin d → ℝ) := pi_eq_sum_univ' w
  change C w = _
  calc
    C w = C (∑ k : Fin d,
        (w k) • (Pi.single k (1 : ℝ) : Fin d → ℝ)) := congrArg C hw
    _ = ∑ k, w k * C (Pi.single k 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [heightZeroDifferential_comp_tailInverse_basis hAB u hd hsigns k]

theorem heightZeroDifferential_comp_tailInverse_neg
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u))
    {w : Fin d → ℝ} (hw : ∀ k, 0 ≤ w k) (hw0 : w ≠ 0) :
    (heightZeroDifferentialAt hAB u).comp
        ((tailHeightDifferentialAt hAB u hd).toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
            hAB u hd hsigns)).symm.toContinuousLinearMap w < 0 := by
  rw [heightZeroDifferential_comp_tailInverse_apply hAB u hd hsigns w]
  have hex : ∃ k, 0 < w k := by
    by_contra hn
    push_neg at hn
    apply hw0
    funext k
    exact le_antisymm (hn k) (hw k)
  obtain ⟨k0, hk0⟩ := hex
  have hnonpos : ∀ k, w k * heightZeroCramerCoefficient
      (endpointArrayOfInterior hAB u) hd k ≤ 0 := by
    intro k
    exact mul_nonpos_of_nonneg_of_nonpos (hw k)
      (heightZeroCramerCoefficient_neg_of_coherentSigns
        _ hd hsigns k).le
  have hstrict : w k0 * heightZeroCramerCoefficient
      (endpointArrayOfInterior hAB u) hd k0 < 0 :=
    mul_neg_of_pos_of_neg hk0
      (heightZeroCramerCoefficient_neg_of_coherentSigns
        _ hd hsigns k0)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k0)]
  have herase : ∑ k ∈ Finset.univ.erase k0,
      w k * heightZeroCramerCoefficient
        (endpointArrayOfInterior hAB u) hd k ≤ 0 := by
    exact Finset.sum_nonpos fun k _ => hnonpos k
  linarith

/-! ## Differential of height zero through an ambient inverse chart -/

private theorem hasFDerivAt_heightZero_through_ambientInverse
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (e : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (he : (e : (Fin d → ℝ) → Fin d → ℝ) =
      canonicalExtendedCoordinateTailHeight hAB base hd)
    {y : Fin d → ℝ} (hy : y ∈ e.target)
    (hyspace : e.symm y ∈ endpointNodeSpace d A B)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB ⟨e.symm y, hyspace⟩)) :
    HasFDerivAt
      (fun q => canonicalExtendedCoordinateGapHeight hAB
        ⟨e.symm y, hyspace⟩ hd 0 (e.symm q))
      ((heightZeroDifferentialAt hAB ⟨e.symm y, hyspace⟩).comp
        (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
          (tailHeightDifferentialAt hAB ⟨e.symm y, hyspace⟩ hd)
            (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
              hAB ⟨e.symm y, hyspace⟩ hd hsigns)).symm.toContinuousLinearMap) y := by
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨e.symm y, hyspace⟩
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have heDeriv : HasFDerivAt e (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ)
      (e.symm y) := by
    rw [he]
    change HasFDerivAt (canonicalExtendedCoordinateTailHeight hAB base hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalTailHeight_at_simplexPoint hAB base u hd
  have heInv : HasFDerivAt e.symm
      (eL.symm : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) y :=
    e.hasFDerivAt_symm hy heDeriv
  have hzero := hasFDerivAt_canonicalHeightZero_at_simplexPoint
    hAB u u hd
  exact hzero.comp y heInv

/-! ## The inverse-function chart and its simplex restriction -/

/-- The ambient inverse-function chart based at one endpoint array. -/
def ambientTailHeightChart {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) := by
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have hderiv : HasFDerivAt
      (canonicalExtendedCoordinateTailHeight hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateTailHeight hAB u hd
  exact ContDiffAt.toOpenPartialHomeomorph
    (canonicalExtendedCoordinateTailHeight hAB u hd)
    (contDiffAt_canonicalExtendedCoordinateTailHeight hAB u hd)
    hderiv (by norm_num)

@[simp]
theorem ambientTailHeightChart_coe {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (ambientTailHeightChart hAB u hd hsigns :
      (Fin d → ℝ) → Fin d → ℝ) =
      canonicalExtendedCoordinateTailHeight hAB u hd := by
  simp only [ambientTailHeightChart]
  apply ContDiffAt.toOpenPartialHomeomorph_coe

theorem mem_ambientTailHeightChart_source {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    u.1 ∈ (ambientTailHeightChart hAB u hd hsigns).source := by
  let L := tailHeightDifferentialAt hAB u hd
  have hLdet : L.det ≠ 0 :=
    tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB u hd hsigns
  let eL := L.toContinuousLinearEquivOfDetNeZero hLdet
  have hderiv : HasFDerivAt
      (canonicalExtendedCoordinateTailHeight hAB u hd)
      (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) u.1 := by
    rw [show (eL : (Fin d → ℝ) →L[ℝ] Fin d → ℝ) = L by
      exact L.coe_toContinuousLinearEquivOfDetNeZero hLdet]
    exact hasFDerivAt_canonicalExtendedCoordinateTailHeight hAB u hd
  simpa only [ambientTailHeightChart] using
    (ContDiffAt.mem_toOpenPartialHomeomorph_source
      (contDiffAt_canonicalExtendedCoordinateTailHeight hAB u hd)
      hderiv (by norm_num))

/-- Restriction of the ambient IFT chart to the ordered open simplex. -/
def simplexTailHeightChart {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    OpenPartialHomeomorph
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} (Fin d → ℝ) :=
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨endpointNodeSpace d A B, isOpen_endpointNodeSpace d A B⟩
  (ambientTailHeightChart hAB u hd hsigns).subtypeRestr
    (show Nonempty S from ⟨u⟩)

theorem mem_simplexTailHeightChart_source {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    u ∈ (simplexTailHeightChart hAB u hd hsigns).source := by
  simpa only [simplexTailHeightChart,
    OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using
      mem_ambientTailHeightChart_source hAB u hd hsigns

@[simp]
theorem simplexTailHeightChart_coe {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u)) :
    (simplexTailHeightChart hAB u hd hsigns :
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ) =
      coordinateTailHeight hAB := by
  funext v
  rw [show (simplexTailHeightChart hAB u hd hsigns :
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} → Fin d → ℝ) v =
      (ambientTailHeightChart hAB u hd hsigns) v.1 by rfl]
  rw [ambientTailHeightChart_coe]
  exact canonicalExtendedCoordinateTailHeight_eq_coordinate hAB u v hd

private theorem hasFDerivAt_coordinateHeightZero_through_simplexInverse
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB base))
    {y : Fin d → ℝ}
    (hy : y ∈ (simplexTailHeightChart hAB base hd hbase).target) :
    let uy := (simplexTailHeightChart hAB base hd hbase).symm y
    HasFDerivAt
      (fun q => coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm q) 0)
      ((heightZeroDifferentialAt hAB uy).comp
        (ContinuousLinearEquiv.toContinuousLinearMap
          (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
            (tailHeightDifferentialAt hAB uy hd)
            (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns
              hAB uy hd (hsignsAll (endpointArrayOfInterior hAB uy)))).symm)) y := by
  dsimp only
  let e := ambientTailHeightChart hAB base hd hbase
  let es := simplexTailHeightChart hAB base hd hbase
  let uy := es.symm y
  have hyAmbient : y ∈ e.target := by
    exact OpenPartialHomeomorph.subtypeRestr_target_subset e
      (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hy
  have hval : uy.1 = e.symm y := by
    change (Subtype.val ∘ es.symm) y = e.symm y
    exact e.subtypeRestr_symm_apply
      (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hy
  have hyspace : e.symm y ∈ endpointNodeSpace d A B := by
    rw [← hval]
    exact uy.2
  let ue : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨e.symm y, hyspace⟩
  have hue : ue = uy := Subtype.ext hval.symm
  have hderiv := hasFDerivAt_heightZero_through_ambientInverse
    hAB base hd e (ambientTailHeightChart_coe hAB base hd hbase)
    hyAmbient hyspace (hsignsAll (endpointArrayOfInterior hAB ue))
  have hevent : ∀ᶠ q in 𝓝 y, q ∈ es.target :=
    es.open_target.mem_nhds hy
  have heq :
      (fun q => coordinateGapHeight hAB (es.symm q) 0) =ᶠ[𝓝 y]
        (fun q => canonicalExtendedCoordinateGapHeight hAB ue hd 0 (e.symm q)) := by
    filter_upwards [hevent] with q hq
    have hqval : (es.symm q).1 = e.symm q := by
      change (Subtype.val ∘ es.symm) q = e.symm q
      exact e.subtypeRestr_symm_apply
        (show Nonempty {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} from ⟨base⟩) hq
    rw [← hqval]
    exact (canonicalExtendedCoordinateGapHeight_eq_coordinate
      hAB ue (es.symm q) hd 0).symm
  have hout := hderiv.congr_of_eventuallyEq heq
  convert hout using 1
  congr 3
  exact hue.symm
  congr 2
  exact hue.symm

/-! ## Integrating the negative Cramer partials -/

private theorem coordinateHeightZero_strictAntiOn_convexTarget
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (base : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB base))
    {V : Set (Fin d → ℝ)}
    (hVconvex : Convex ℝ V)
    (hV : V ⊆ (simplexTailHeightChart hAB base hd hbase).target)
    {y z : Fin d → ℝ} (hy : y ∈ V) (hz : z ∈ V)
    (hyz : ∀ i, y i ≤ z i) (hyzNe : y ≠ z) :
    coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm z) 0 <
      coordinateGapHeight hAB
        ((simplexTailHeightChart hAB base hd hbase).symm y) 0 := by
  let es := simplexTailHeightChart hAB base hd hbase
  let φ : ℝ → ℝ := fun t =>
    coordinateGapHeight hAB (es.symm (AffineMap.lineMap y z t)) 0
  let w : Fin d → ℝ := z - y
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    exact sub_nonneg.mpr (hyz i)
  have hw0 : w ≠ 0 := by
    intro hwzero
    apply hyzNe
    exact (sub_eq_zero.mp hwzero).symm
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      AffineMap.lineMap y z t ∈ V :=
    hVconvex.lineMap_mem hy hz ht
  have hpathDeriv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt φ
        (((heightZeroDifferentialAt hAB
            (es.symm (AffineMap.lineMap y z t))).comp
          (ContinuousLinearEquiv.toContinuousLinearMap
            (ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero
              (tailHeightDifferentialAt hAB
                (es.symm (AffineMap.lineMap y z t)) hd)
              (tailHeightDifferentialAt_det_ne_zero_of_coherentSigns hAB
                (es.symm (AffineMap.lineMap y z t)) hd
                (hsignsAll (endpointArrayOfInterior hAB
                  (es.symm (AffineMap.lineMap y z t)))))).symm)) w) t := by
    have houter :=
      hasFDerivAt_coordinateHeightZero_through_simplexInverse
        hAB base hd hsignsAll hbase
          (hV (hline t ht))
    have hcomp := houter.comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := t))
    simpa only [φ, es, Function.comp_def, w] using hcomp
  have hcont : ContinuousOn φ (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hpathDeriv t ht).continuousAt.continuousWithinAt
  have hderivNeg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), deriv φ t < 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
    rw [(hpathDeriv t htIcc).deriv]
    exact heightZeroDifferential_comp_tailInverse_neg hAB
      (es.symm (AffineMap.lineMap y z t)) hd
      (hsignsAll (endpointArrayOfInterior hAB
        (es.symm (AffineMap.lineMap y z t)))) hw hw0
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc (0 : ℝ) 1)
    hcont hderivNeg
  have h01 := hanti (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_lt_one
  simpa only [φ, es, AffineMap.lineMap_apply_zero,
    AffineMap.lineMap_apply_one] using h01

/-! ## Assembly of the canonical oriented chart -/

/-- Coherent maximal-minor signs construct the local oriented chart required
by `Orientation.lean`.  The target is explicitly shrunk to a norm ball, so
its convexity is kernel-visible. -/
theorem nonempty_orientedTailHeightChart_of_coherentSigns
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes)
    (nodes : EndpointArray d A B) :
    Nonempty (OrientedTailHeightChart nodes) := by
  let hAB : AdmissibleInterval A B := nodes.admissibleInterval
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    (endpointArrayHomeomorph hAB) nodes
  have huNodes : endpointArrayOfInterior hAB u = nodes := by
    exact (endpointArrayHomeomorph hAB).symm_apply_apply nodes
  have hbase : CoherentHeightMaximalMinorSigns
      (endpointArrayOfInterior hAB u) := by
    rw [huNodes]
    exact hsignsAll nodes
  let es := simplexTailHeightChart hAB u hd hbase
  have huSource : u ∈ es.source :=
    mem_simplexTailHeightChart_source hAB u hd hbase
  let center : Fin d → ℝ := coordinateTailHeight hAB u
  have hcenter : center ∈ es.target := by
    have hmapped := es.map_source huSource
    change coordinateTailHeight hAB u ∈ es.target
    rw [← simplexTailHeightChart_coe hAB u hd hbase]
    exact hmapped
  obtain ⟨r, hr, hball⟩ :=
    Metric.isOpen_iff.mp es.open_target center hcenter
  let ball : Set (Fin d → ℝ) := Metric.ball center r
  let esSmall : OpenPartialHomeomorph
      {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} (Fin d → ℝ) :=
    (es.symm.restrOpen ball Metric.isOpen_ball).symm
  have hesSmallTarget : esSmall.target = ball := by
    change es.target ∩ ball = ball
    exact Set.inter_eq_right.mpr hball
  have hcenterBall : center ∈ ball := Metric.mem_ball_self hr
  have hcenterSmallTarget : center ∈ esSmall.target := by
    rw [hesSmallTarget]
    exact hcenterBall
  have huSmallSource : u ∈ esSmall.source := by
    have hmapped := esSmall.map_target hcenterSmallTarget
    have hinv : esSmall.symm center = u := by
      change (es.symm.restrOpen ball Metric.isOpen_ball) center = u
      change es.symm center = u
      have hcenterEq : es u = center := by
        change es u = coordinateTailHeight hAB u
        exact congrFun (simplexTailHeightChart_coe hAB u hd hbase) u
      rw [← hcenterEq]
      exact es.left_inv huSource
    rwa [hinv] at hmapped
  let chart : OpenPartialHomeomorph (EndpointArray d A B) (Fin d → ℝ) :=
    (endpointArrayHomeomorph hAB).transOpenPartialHomeomorph esSmall
  have hnodesSource : nodes ∈ chart.source := by
    change nodes ∈ (Homeomorph.transOpenPartialHomeomorph
      (endpointArrayHomeomorph hAB) esSmall).source
    rw [Homeomorph.transOpenPartialHomeomorph_source]
    change u ∈ esSmall.source
    exact huSmallSource
  have hchartEq :
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) = chart := by
    funext x
    change tailGapHeight x = esSmall ((endpointArrayHomeomorph hAB) x)
    change tailGapHeight x = es ((endpointArrayHomeomorph hAB) x)
    rw [simplexTailHeightChart_coe]
    change tailGapHeight x = tailGapHeight
      (endpointArrayOfInterior hAB ((endpointArrayHomeomorph hAB) x))
    congr 1
    exact (endpointArrayHomeomorph hAB).symm_apply_apply x |>.symm
  have hchartTarget : chart.target = ball := by
    change (Homeomorph.transOpenPartialHomeomorph
      (endpointArrayHomeomorph hAB) esSmall).target = ball
    rw [Homeomorph.transOpenPartialHomeomorph_target, hesSmallTarget]
  have hconvex : Convex ℝ chart.target := by
    rw [hchartTarget]
    exact convex_ball center r
  refine ⟨{
    chart := chart
    mem_source := hnodesSource
    chart_eq := hchartEq
    convex_target := hconvex
    height_zero_strictAnti := ?_ }⟩
  intro y z hy hz hyz hyzNe
  have hyBall : y ∈ ball := by rwa [← hchartTarget]
  have hzBall : z ∈ ball := by rwa [← hchartTarget]
  have hstrict := coordinateHeightZero_strictAntiOn_convexTarget
    hAB u hd hsignsAll hbase (convex_ball center r) hball
      hyBall hzBall hyz hyzNe
  change (chart.symm z).height 0 < (chart.symm y).height 0
  change (endpointArrayOfInterior hAB (esSmall.symm z)).height 0 <
    (endpointArrayOfInterior hAB (esSmall.symm y)).height 0
  change coordinateGapHeight hAB (esSmall.symm z) 0 <
    coordinateGapHeight hAB (esSmall.symm y) 0
  change coordinateGapHeight hAB (es.symm z) 0 <
    coordinateGapHeight hAB (es.symm y) 0
  exact hstrict

/-- The local orientation proposition isolated by `Orientation.lean` is a
theorem of the ordinary coherent-sign input.  Height-zero continuity is
unconditional; for `d = 0` the chart clause is vacuous because it quantifies
an impossible witness `1 ≤ 0`. -/
theorem tailHeightLocalOrientationStatement_of_coherentSigns
    (d : ℕ) (A B : ℝ)
    (hsignsAll : ∀ nodes : EndpointArray d A B,
      CoherentHeightMaximalMinorSigns nodes) :
    TailHeightLocalOrientationStatement d A B := by
  refine ⟨continuous_endpointArray_height (0 : Fin (d + 1)), ?_⟩
  intro hd nodes
  exact nonempty_orientedTailHeightChart_of_coherentSigns hd hsignsAll nodes

end

end Randy1153.DeBoorPinkus
