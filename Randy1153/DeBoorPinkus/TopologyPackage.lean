import Randy1153.DeBoorPinkus.Minors
import Randy1153.DeBoorPinkus.LocalHomeomorph
import Randy1153.DeBoorPinkus.GlobalHomeomorph

/-!
# Unconditional topology package for the gap-difference map

This file closes the de Boor--Pinkus topology chain.  The coherent-minor
argument proves the explicit Jacobian determinant condition; the committed
inverse-function and properness arguments then promote that condition first
to a local homeomorphism and finally to the canonical global homeomorphism
statement.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- The explicit consecutive-difference Jacobian is nonsingular at every
endpoint array. -/
theorem gapDifference_jacobianDeterminantCondition
    (d : ℕ) (A B : ℝ) :
    GapDifferenceJacobianDeterminantCondition d A B := by
  intro nodes
  change (Matrix.det (fun i j =>
    gapHeightJacobianModel nodes i.succ j -
      gapHeightJacobianModel nodes i.castSucc j)) ≠ 0
  exact gapHeightJacobianModel_consecutiveDifference_det_ne_zero nodes

/-- The gap-difference map is unconditionally a local homeomorphism. -/
theorem gapDifference_localHomeomorphStatement
    (d : ℕ) (A B : ℝ) :
    GapDifferenceLocalHomeomorphStatement d A B :=
  gapDifference_localHomeomorphStatement_of_determinant d A B
    (gapDifference_jacobianDeterminantCondition d A B)

/-- The canonical global homeomorphism statement for the gap-difference
map, obtained from local inversion and the committed properness theorem. -/
theorem gapDifference_homeomorphismStatement
    (d : ℕ) (A B : ℝ) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph
    (gapDifference_localHomeomorphStatement d A B)

end

end Randy1153.DeBoorPinkus
