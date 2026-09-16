import Randy1153.DeBoorPinkus.SignBridge
import Randy1153.DeBoorPinkus.TopologyPackage
import Randy1153.DeBoorPinkus.OrientedCharts

/-!
# Unconditional de Boor--Pinkus package

This module is the final assembly layer for the endpoint-fixed comparison
theory.  The interlacing/minor computation supplies coherent orientation,
the topology package supplies the global gap-difference homeomorphism, and
the oriented local charts supply the path and ray lifts.  No additional
hypothesis is introduced here.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- The tail-height map has coherently oriented local charts at every
endpoint array. -/
theorem tailHeightLocalOrientationStatement (d : ℕ) (A B : ℝ) :
    TailHeightLocalOrientationStatement d A B :=
  tailHeightLocalOrientationStatement_of_coherentSigns d A B
    coherentHeightMaximalMinorSigns_unconditional

/-- The global increasing-segment and decreasing-ray lifts, with their
source-faithful height-zero orientation. -/
theorem gapHeightPathRayOrientationStatement (d : ℕ) (A B : ℝ) :
    GapHeightPathRayOrientationStatement d A B :=
  gapHeightPathRayOrientation_of_homeomorphism_of_localOrientation
    (gapDifference_homeomorphismStatement d A B)
    (tailHeightLocalOrientationStatement d A B)

/-- The unconditional comparison package used by the block-collapse
argument. -/
theorem comparisonPackage (d : ℕ) (A B : ℝ) :
    ComparisonPackage d A B :=
  comparisonPackage_of_homeomorphism_of_pathRayOrientation
    (gapDifference_homeomorphismStatement d A B)
    (gapHeightPathRayOrientationStatement d A B)

/-- Smoke theorem: the package contains the unique equioscillating endpoint
array asserted by source Theorem 1. -/
theorem existsUniqueEquioscillatingStatement (d : ℕ) (A B : ℝ) :
    ExistsUniqueEquioscillatingStatement d A B :=
  (comparisonPackage d A B).exists_unique_equioscillating

end

end Randy1153.DeBoorPinkus
