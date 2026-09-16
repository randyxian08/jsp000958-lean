import Randy1153.DeBoorPinkus.GlobalHomeomorph

/-!
# Equioscillation and coordinatewise comparison

The first part of this file is unconditional: a global homeomorphism for the
gap-difference map has a unique zero, and zero consecutive differences are
exactly equioscillation.

The second part isolates the one source input not yet delivered by the
Jacobian/interlacing lane.  De Boor--Pinkus use the coherent signs of the
maximal height-Jacobian minors twice:

* lift the straight segment in the coordinates consisting of all heights
  except the first; the first height moves strictly in the opposite
  direction;
* lift the diagonal decreasing ray in those coordinates until the first
  gap difference crosses a prescribed lower value.

`GapHeightPathRayOrientationStatement` records exactly those two oriented
lift conclusions, including the actual continuous lifted paths.  It is an
ordinary proposition and no inhabitant is asserted here.  The full
coordinatewise rigidity theorem and the project `ComparisonPackage` are
proved below from that single orientation input and the already-checked
global homeomorphism.
-/

namespace Randy1153.DeBoorPinkus

open Function Topology unitInterval

noncomputable section

/-! ## Consecutive differences and equioscillation -/

/-- The coordinates used by source Theorem 2: all gap heights except the
first one. -/
def tailGapHeight {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i ↦ nodes.height i.succ

/-- Vanishing consecutive height differences are equivalent to equality of
all gap heights. -/
theorem equioscillates_iff_gapDifference_eq_zero
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Equioscillates nodes ↔
      gapDifference nodes = (0 : Fin d → ℝ) := by
  constructor
  · intro heq
    funext i
    simp only [gapDifference, Pi.zero_apply, sub_eq_zero]
    exact heq i.succ i.castSucc
  · intro hzero
    have hadj (i : Fin d) :
        nodes.height i.succ = nodes.height i.castSucc := by
      have hi := congrFun hzero i
      simpa only [gapDifference, Pi.zero_apply, sub_eq_zero] using hi
    have hbase (i : Fin (d + 1)) :
        nodes.height i = nodes.height (0 : Fin (d + 1)) := by
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
          exact (hadj i).trans ih
    intro i j
    exact (hbase i).trans (hbase j).symm

/-- Source Theorem 1 immediately gives the unique equioscillating endpoint
array as the unique inverse image of the zero difference vector. -/
theorem existsUniqueEquioscillating_of_gapDifferenceHomeomorphism
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B) :
    ExistsUniqueEquioscillatingStatement d A B := by
  intro hAB
  let hglobal := hhomeomorph hAB
  obtain ⟨nodes, hnodes⟩ := hglobal.surjective (0 : Fin d → ℝ)
  refine ⟨nodes, (equioscillates_iff_gapDifference_eq_zero nodes).2 hnodes, ?_⟩
  intro other hother
  apply hglobal.injective
  rw [(equioscillates_iff_gapDifference_eq_zero other).1 hother, hnodes]

/-! ## The exact coherent-orientation continuation input -/

/-- The source-faithful output required from coherent maximal-minor signs.

For positive dimension, `lift_increasingSegment` is the lift of the affine
segment in `(height 1, ..., height d)` and records strict decrease of
`height 0`.  `lift_decreasingRay_to_firstDifference` is the finite initial
piece of the diagonal decreasing ray, stopped when its first consecutive
difference reaches the prescribed smaller value.  Both fields expose the
continuous lifted curve and its exact coordinate formula; neither assumes
coordinatewise rigidity or injectivity of a height-coordinate projection.
-/
structure GapHeightPathRayOrientationStatement (d : ℕ) (A B : ℝ) : Prop where
  lift_increasingSegment :
    ∀ (_hd : 1 ≤ d) (s : EndpointArray d A B) (y : Fin d → ℝ),
      (∀ i, tailGapHeight s i ≤ y i) →
      y ≠ tailGapHeight s →
      ∃ g : C(I, EndpointArray d A B),
        g 0 = s ∧
        (∀ u i,
          tailGapHeight (g u) i =
            (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i) ∧
        StrictAnti (fun u : I ↦ (g u).height (0 : Fin (d + 1)))
  lift_decreasingRay_to_firstDifference :
    ∀ (hd : 1 ≤ d) (r : EndpointArray d A B) (c : ℝ),
      c < gapDifference r ⟨0, hd⟩ →
      ∃ α : ℝ, 0 < α ∧
        ∃ g : C(I, EndpointArray d A B),
          g 0 = r ∧
          (∀ u i,
            tailGapHeight (g u) i =
              tailGapHeight r i - (u : ℝ) * α) ∧
          gapDifference (g 1) ⟨0, hd⟩ = c

/-- Endpoint form of the increasing-segment lift. -/
theorem exists_tail_eq_and_height_zero_lt_of_le_of_ne
    {d : ℕ} {A B : ℝ}
    (horient : GapHeightPathRayOrientationStatement d A B)
    (hd : 1 ≤ d) (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) :
    ∃ r : EndpointArray d A B,
      tailGapHeight r = y ∧
        r.height (0 : Fin (d + 1)) < s.height (0 : Fin (d + 1)) := by
  obtain ⟨g, hgzero, hgtail, hganti⟩ :=
    horient.lift_increasingSegment hd s y hle hne
  refine ⟨g 1, ?_, ?_⟩
  · funext i
    simpa using hgtail 1 i
  · have hzeroOne : (0 : I) < 1 := zero_lt_one
    have hstrict := hganti hzeroOne
    simpa only [hgzero] using hstrict

/-! ## Difference reconstruction after a diagonal tail shift -/

/-- If every noninitial height is shifted by the same amount and the first
height difference is fixed separately, then the entire consecutive-
difference vector is fixed. -/
lemma gapDifference_eq_of_tail_eq_sub_and_zero_eq
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    {q t : EndpointArray d A B} {α : ℝ}
    (htail : ∀ i, tailGapHeight q i = tailGapHeight t i - α)
    (hzero : gapDifference q ⟨0, hd⟩ =
      gapDifference t ⟨0, hd⟩) :
    gapDifference q = gapDifference t := by
  let i₀ : Fin d := ⟨0, hd⟩
  funext i
  by_cases hi : i = i₀
  · simpa only [hi] using hzero
  · have hiVal : i.val ≠ 0 := by
      intro hval
      apply hi
      apply Fin.ext
      simpa only [i₀] using hval
    let j : Fin d := ⟨i.val - 1, by omega⟩
    have hjsucc : j.succ = i.castSucc := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    rw [gapDifference, gapDifference]
    have hright := htail i
    have hleft := htail j
    simp only [tailGapHeight] at hright hleft
    rw [hjsucc] at hleft
    linarith

/-! ## Coordinatewise rigidity -/

/-- De Boor--Pinkus Theorem 2 from the global difference homeomorphism and
the exact coherent-minor path/ray orientation input. -/
theorem gapHeightLeRigidity_of_homeomorphism_of_pathRayOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (horient : GapHeightPathRayOrientationStatement d A B) :
    GapHeightLeRigidityStatement d A B := by
  intro s t hle
  by_cases hd : d = 0
  · subst d
    exact endpointArray_zero_unique s t
  have hdpos : 1 ≤ d := by omega
  let i₀ : Fin d := ⟨0, hdpos⟩
  by_contra hst
  have htailCases : tailGapHeight s = tailGapHeight t ∨
      tailGapHeight s ≠ tailGapHeight t := eq_or_ne _ _
  obtain ⟨r, hrtail, hrzero⟩ :
      ∃ r : EndpointArray d A B,
        tailGapHeight r = tailGapHeight t ∧
          r.height (0 : Fin (d + 1)) < t.height (0 : Fin (d + 1)) := by
    rcases htailCases with htailEq | htailNe
    · refine ⟨s, htailEq, ?_⟩
      have hzeroLe := hle (0 : Fin (d + 1))
      exact lt_of_le_of_ne hzeroLe fun heq ↦ by
        apply hst
        apply (hhomeomorph s.admissibleInterval).injective
        apply gapDifference_eq_of_tail_eq_sub_and_zero_eq
          (hd := hdpos) (α := 0)
        · intro i
          have htail := congrFun htailEq i
          simpa using htail
        · rw [gapDifference, gapDifference]
          have htail := congrFun htailEq i₀
          simp only [tailGapHeight] at htail
          change s.height i₀.succ - s.height i₀.castSucc =
            t.height i₀.succ - t.height i₀.castSucc
          have hi₀cast : i₀.castSucc = (0 : Fin (d + 1)) := by
            apply Fin.ext
            rfl
          rw [hi₀cast, heq]
          exact congrArg (fun z ↦ z - t.height (0 : Fin (d + 1))) htail
    · have htailLe : ∀ i, tailGapHeight s i ≤ tailGapHeight t i := by
        intro i
        exact hle i.succ
      obtain ⟨r, hrtail, hrs⟩ :=
        exists_tail_eq_and_height_zero_lt_of_le_of_ne
          horient hdpos s (tailGapHeight t) htailLe htailNe.symm
      exact ⟨r, hrtail, hrs.trans_le (hle (0 : Fin (d + 1)))⟩
  have hfirst : gapDifference t i₀ < gapDifference r i₀ := by
    rw [gapDifference, gapDifference]
    have htail0 := congrFun hrtail i₀
    simp only [tailGapHeight] at htail0
    have hi₀cast : i₀.castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext
      rfl
    rw [hi₀cast]
    linarith
  obtain ⟨α, hα, g, hgzero, hgtail, hgfirst⟩ :=
    horient.lift_decreasingRay_to_firstDifference hdpos r
      (gapDifference t i₀) hfirst
  let q : EndpointArray d A B := g 1
  have hqtail : ∀ i, tailGapHeight q i = tailGapHeight t i - α := by
    intro i
    have hpath := hgtail 1 i
    calc
      tailGapHeight q i = tailGapHeight r i - α := by simpa [q] using hpath
      _ = tailGapHeight t i - α := by rw [congrFun hrtail i]
  have hqzero : gapDifference q i₀ = gapDifference t i₀ := by
    simpa [q] using hgfirst
  have hqdiff : gapDifference q = gapDifference t :=
    gapDifference_eq_of_tail_eq_sub_and_zero_eq hdpos hqtail hqzero
  have hqt : q = t :=
    (hhomeomorph t.admissibleInterval).injective hqdiff
  have hshift := hqtail i₀
  rw [hqt] at hshift
  linarith

/-! ## Project packaging -/

/-- Construct the complete comparison package from source Theorem 1 and the
single remaining coherent-orientation continuation input. -/
theorem comparisonPackage_of_homeomorphism_of_pathRayOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (horient : GapHeightPathRayOrientationStatement d A B) :
    ComparisonPackage d A B where
  gapHeight_le_rigidity :=
    gapHeightLeRigidity_of_homeomorphism_of_pathRayOrientation
      hhomeomorph horient
  exists_unique_equioscillating :=
    existsUniqueEquioscillating_of_gapDifferenceHomeomorphism hhomeomorph

end

end Randy1153.DeBoorPinkus
