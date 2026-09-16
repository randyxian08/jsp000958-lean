import Randy1153.DeBoorPinkus.Comparison
import Randy1153.DeBoorPinkus.Jacobian
import Mathlib.Analysis.Convex.PathConnected

/-!
# Local coherent orientation for the de Boor--Pinkus comparison paths

This file moves strictly below the path/ray contract in `Comparison`.
First it records coherent signs of the maximal height-Jacobian minors and
derives the source's Cramer-rule sign (equation (8)).  It then gives the
smallest continuation-ready local input: around every endpoint array, the
tail-height map has a convex local-homeomorphism chart and height zero is
strictly order-reversing in that chart.

From this genuinely local input we prove that the tail-height map is a local
homeomorphism and construct every chart-contained affine lift, including
strict opposite motion of height zero.  A generic compact-continuation
theorem then glues the unique local branches.  Compact height slabs handle
the increasing segment; for the decreasing ray, failure to cross a prescribed
first difference bounds height zero and gives the same compact continuation.
The resulting theorem inhabits the exact path/ray interface from `Comparison`.
-/

namespace Randy1153.DeBoorPinkus

open Filter Function Topology unitInterval
open scoped BigOperators

noncomputable section

/-! ## Coherent deleted-minor signs and source equation (8) -/

/-- Cramer's-rule coefficient for height zero as a function of tail height
coordinate `k`.  With zero-based indices, source `J_{k+2}` is the minor
obtained by deleting row `k.succ`, while `J_1` deletes row zero. -/
def heightZeroCramerCoefficient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (k : Fin d) : ℝ :=
  (-1 : ℝ) ^ (k.val + 2) *
    deletedRowMinor (gapHeightJacobianModel nodes) k.succ /
      deletedRowMinor (gapHeightJacobianModel nodes) ⟨0, by omega⟩

/-- Exact coherent orientation of all maximal height-Jacobian minors.

The extra exponent `omitted.val + 1` converts the project's zero-based gap
index to the source's one-based `J_k`.  The common sign is required to
be `±1`, so this proposition contains both nonvanishing and the coherent
relative signs used in equation (8). -/
def CoherentHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
    ∀ omitted : Fin (d + 1),
      0 < sign * (-1 : ℝ) ^ (omitted.val + 1) *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted

/-- Coherent signs in particular make every maximal minor nonzero. -/
theorem deletedRowMinor_ne_zero_of_coherentSigns
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (hsigns : CoherentHeightMaximalMinorSigns nodes)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapHeightJacobianModel nodes) omitted ≠ 0 := by
  obtain ⟨sign, hsignValue, hsign⟩ := hsigns
  intro hzero
  have h := hsign omitted
  rw [hzero, mul_zero] at h
  linarith

/-- Source equation (8): every Cramer coefficient expressing the omitted
height as a function of the other heights is strictly negative. -/
theorem heightZeroCramerCoefficient_neg_of_coherentSigns
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (hsigns : CoherentHeightMaximalMinorSigns nodes) (k : Fin d) :
    heightZeroCramerCoefficient nodes hd k < 0 := by
  obtain ⟨sign, hsignValue, hsign⟩ := hsigns
  let D₀ : ℝ := deletedRowMinor (gapHeightJacobianModel nodes) ⟨0, by omega⟩
  let Dk : ℝ := deletedRowMinor (gapHeightJacobianModel nodes) k.succ
  let sk : ℝ := (-1 : ℝ) ^ (k.val + 2)
  have h₀ : 0 < sign * (-1 : ℝ) * D₀ := by
    simpa only [D₀, Fin.val_zero, zero_add, pow_one] using
      hsign (⟨0, by omega⟩ : Fin (d + 1))
  have hk : 0 < sign * sk * Dk := by
    simpa only [Dk, sk, Fin.val_succ, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hsign k.succ
  have hsignSq : sign * sign = 1 := by
    rcases hsignValue with rfl | rfl <;> norm_num
  have hsignD₀ : sign * D₀ < 0 := by nlinarith
  have hsignSkDk : 0 < sign * (sk * Dk) := by
    nlinarith
  have hprod : sk * Dk * D₀ < 0 := by
    have hmul := mul_neg_of_pos_of_neg hsignSkDk hsignD₀
    calc
      sk * Dk * D₀ = (sign * (sk * Dk)) * (sign * D₀) := by
        symm
        calc
          (sign * (sk * Dk)) * (sign * D₀) =
              (sign * sign) * (sk * Dk * D₀) := by ring
          _ = sk * Dk * D₀ := by rw [hsignSq, one_mul]
      _ < 0 := hmul
  have hD₀ : D₀ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at h₀
    linarith
  have hD₀sq : 0 < D₀ ^ 2 := sq_pos_of_ne_zero hD₀
  rw [heightZeroCramerCoefficient]
  change sk * Dk / D₀ < 0
  rw [show sk * Dk / D₀ = (sk * Dk * D₀) / D₀ ^ 2 by
    field_simp]
  exact div_neg_of_neg_of_pos hprod hD₀sq

/-! ## The smallest local analytic/orientation input -/

/-- One convex tail-height chart carrying the integrated form of equation
(8).  The strict order reversal is local: it is asserted only for comparable
points in this chart's convex target. -/
structure OrientedTailHeightChart {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) where
  chart : OpenPartialHomeomorph (EndpointArray d A B) (Fin d → ℝ)
  mem_source : nodes ∈ chart.source
  chart_eq :
    (tailGapHeight : EndpointArray d A B → Fin d → ℝ) = chart
  convex_target : Convex ℝ chart.target
  height_zero_strictAnti : ∀ {y z : Fin d → ℝ},
    y ∈ chart.target → z ∈ chart.target →
      (∀ i, y i ≤ z i) → y ≠ z →
        (chart.symm z).height (0 : Fin (d + 1)) <
          (chart.symm y).height (0 : Fin (d + 1))

/-- Ordinary proposition reserved for the exact remaining local analytic
input.  Continuity of height zero follows from the same envelope derivative
calculation as the Jacobian.  `oriented_chart` is the inverse-function
theorem plus coherent Cramer signs, shrunk to a convex target neighborhood.
-/
def TailHeightLocalOrientationStatement (d : ℕ) (A B : ℝ) : Prop :=
  Continuous
    (fun nodes : EndpointArray d A B ↦
      nodes.height (0 : Fin (d + 1))) ∧
    ∀ (_hd : 1 ≤ d) (nodes : EndpointArray d A B),
      Nonempty (OrientedTailHeightChart nodes)

/-- The local oriented charts make the tail-height map a genuine local
homeomorphism. -/
theorem tailGapHeight_isLocalHomeomorph_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hlocal : TailHeightLocalOrientationStatement d A B) (hd : 1 ≤ d) :
    IsLocalHomeomorph
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) := by
  intro nodes
  let e := (hlocal.2 hd nodes).some
  exact ⟨e.chart, e.mem_source, e.chart_eq⟩

/-- Consequently all tail heights vary continuously. -/
theorem continuous_tailGapHeight_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hlocal : TailHeightLocalOrientationStatement d A B) (hd : 1 ≤ d) :
    Continuous
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ) :=
  (tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd).continuous

lemma OrientedTailHeightChart.tail_mem_target
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) :
    tailGapHeight nodes ∈ e.chart.target := by
  rw [e.chart_eq]
  exact e.chart.map_source e.mem_source

@[simp]
lemma OrientedTailHeightChart.symm_tail_eq
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) :
    e.chart.symm (tailGapHeight nodes) = nodes := by
  rw [e.chart_eq]
  exact e.chart.left_inv e.mem_source

/-! ## Checked local affine lifting -/

/-- The affine segment between two tail vectors. -/
def tailLine {d : ℕ} (y z : Fin d → ℝ) (u : I) : Fin d → ℝ :=
  fun i ↦ (1 - (u : ℝ)) * y i + (u : ℝ) * z i

lemma continuous_tailLine {d : ℕ} (y z : Fin d → ℝ) :
    Continuous (tailLine y z) := by
  unfold tailLine
  fun_prop

lemma tailLine_mem_segment {d : ℕ} (y z : Fin d → ℝ) (u : I) :
    tailLine y z u ∈ segment ℝ y z := by
  rw [segment_eq_image_lineMap]
  refine ⟨(u : ℝ), u.2, ?_⟩
  funext i
  simp only [tailLine, AffineMap.lineMap_apply_module, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Every affine segment contained in one oriented chart has a continuous
lift.  Comparable nonconstant target endpoints force height zero to be
strictly antitone along the entire lift, not merely at its endpoints. -/
def OrientedTailHeightChart.liftSegment
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) :
    C(I, EndpointArray d A B) where
  toFun u := e.chart.symm (tailLine y z u)
  continuous_toFun := by
    apply e.chart.continuousOn_invFun.comp_continuous
      (continuous_tailLine y z)
    intro u
    exact e.convex_target.segment_subset hy hz (tailLine_mem_segment y z u)

lemma OrientedTailHeightChart.tail_liftSegment
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) (u : I) :
    tailGapHeight (e.liftSegment hy hz u) = tailLine y z u := by
  rw [e.chart_eq]
  exact e.chart.right_inv
    (e.convex_target.segment_subset hy hz (tailLine_mem_segment y z u))

@[simp]
lemma OrientedTailHeightChart.liftSegment_zero
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) :
    e.liftSegment hy hz 0 = e.chart.symm y := by
  change e.chart.symm (tailLine y z 0) = e.chart.symm y
  congr 1
  funext i
  simp [tailLine]

@[simp]
lemma OrientedTailHeightChart.liftSegment_one
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target) :
    e.liftSegment hy hz 1 = e.chart.symm z := by
  change e.chart.symm (tailLine y z 1) = e.chart.symm z
  congr 1
  funext i
  simp [tailLine]

/-- Integrated equation (8) on one convex chart. -/
theorem OrientedTailHeightChart.height_zero_strictAnti_liftSegment
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target)
    (hle : ∀ i, y i ≤ z i) (hne : y ≠ z) :
    StrictAnti
      (fun u : I ↦ (e.liftSegment hy hz u).height
        (0 : Fin (d + 1))) := by
  have hex : ∃ i, y i < z i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (hle i) (h i)
  obtain ⟨i₀, hi₀⟩ := hex
  intro u v huv
  apply e.height_zero_strictAnti
  · exact e.convex_target.segment_subset hy hz (tailLine_mem_segment y z u)
  · exact e.convex_target.segment_subset hy hz (tailLine_mem_segment y z v)
  · intro i
    unfold tailLine
    have hu : (u : ℝ) ≤ (v : ℝ) := huv.le
    have hi := hle i
    nlinarith
  · intro heq
    have hcoord := congrFun heq i₀
    unfold tailLine at hcoord
    have huv' : (u : ℝ) < (v : ℝ) := huv
    nlinarith

/-- The reversed form of integrated equation (8): if every tail coordinate
decreases along a nonconstant chart-contained affine segment, height zero
strictly increases.  This is the local motion used for the source's diagonal
ray. -/
theorem OrientedTailHeightChart.height_zero_strictMono_liftSegment
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes)
    {y z : Fin d → ℝ} (hy : y ∈ e.chart.target)
    (hz : z ∈ e.chart.target)
    (hle : ∀ i, z i ≤ y i) (hne : z ≠ y) :
    StrictMono
      (fun u : I ↦ (e.liftSegment hy hz u).height
        (0 : Fin (d + 1))) := by
  have hex : ∃ i, z i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (hle i) (h i)
  obtain ⟨i₀, hi₀⟩ := hex
  intro u v huv
  apply e.height_zero_strictAnti
  · exact e.convex_target.segment_subset hy hz (tailLine_mem_segment y z v)
  · exact e.convex_target.segment_subset hy hz (tailLine_mem_segment y z u)
  · intro i
    unfold tailLine
    have hu : (u : ℝ) ≤ (v : ℝ) := huv.le
    have hi := hle i
    nlinarith
  · intro heq
    have hcoord := congrFun heq i₀
    unfold tailLine at hcoord
    have huv' : (u : ℝ) < (v : ℝ) := huv
    nlinarith

/-! ## Source-oriented local steps based at an endpoint array -/

/-- The increasing affine lift supplied while the target segment remains in
one local chart.  This is the exact local step iterated in the source's
maximal-interval argument. -/
theorem exists_local_increasingSegment_lift
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (nodes : EndpointArray d A B) (z : Fin d → ℝ)
    (hzle : ∀ i, tailGapHeight nodes i ≤ z i)
    (hzmem : z ∈ ((hlocal.2 hd nodes).some).chart.target)
    (hzNe : z ≠ tailGapHeight nodes) :
    ∃ g : C(I, EndpointArray d A B),
      g 0 = nodes ∧
      (∀ u, tailGapHeight (g u) =
        tailLine (tailGapHeight nodes) z u) ∧
      StrictAnti (fun u : I ↦
        (g u).height (0 : Fin (d + 1))) := by
  let e := (hlocal.2 hd nodes).some
  have hymem : tailGapHeight nodes ∈ e.chart.target := e.tail_mem_target
  let g := e.liftSegment hymem hzmem
  refine ⟨g, ?_, ?_, ?_⟩
  · exact e.liftSegment_zero hymem hzmem |>.trans e.symm_tail_eq
  · intro u
    exact e.tail_liftSegment hymem hzmem u
  · exact e.height_zero_strictAnti_liftSegment hymem hzmem hzle hzNe.symm

/-- Dually, a chart-contained common decrease of all tail coordinates makes
height zero strictly increase. -/
theorem height_zero_lt_of_local_diagonal_decrease
    {d : ℕ} {A B : ℝ} {nodes : EndpointArray d A B}
    (e : OrientedTailHeightChart nodes) (z : Fin d → ℝ)
    (hzmem : z ∈ e.chart.target)
    (hzle : ∀ i, z i ≤ tailGapHeight nodes i)
    (hzNe : z ≠ tailGapHeight nodes) :
    nodes.height (0 : Fin (d + 1)) <
      (e.chart.symm z).height (0 : Fin (d + 1)) := by
  calc
    nodes.height (0 : Fin (d + 1)) =
        (e.chart.symm (tailGapHeight nodes)).height
          (0 : Fin (d + 1)) := by
      exact congrArg (fun r ↦ r.height (0 : Fin (d + 1)))
        e.symm_tail_eq.symm
    _ < (e.chart.symm z).height (0 : Fin (d + 1)) :=
      e.height_zero_strictAnti hzmem e.tail_mem_target hzle hzNe

/-- A chart-contained common decrease of the tail coordinates has a
continuous lift on which height zero strictly increases.  This is the exact
local step iterated in the decreasing-ray continuation. -/
theorem exists_local_decreasingDiagonal_lift
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (nodes : EndpointArray d A B) (alpha : ℝ) (halpha : 0 < alpha)
    (hzmem : (fun i ↦ tailGapHeight nodes i - alpha) ∈
      ((hlocal.2 hd nodes).some).chart.target) :
    ∃ g : C(I, EndpointArray d A B),
      g 0 = nodes ∧
      (∀ u i, tailGapHeight (g u) i =
        tailGapHeight nodes i - (u : ℝ) * alpha) ∧
      StrictMono (fun u : I ↦
        (g u).height (0 : Fin (d + 1))) := by
  let e := (hlocal.2 hd nodes).some
  let y : Fin d → ℝ := tailGapHeight nodes
  let z : Fin d → ℝ := fun i ↦ tailGapHeight nodes i - alpha
  have hymem : y ∈ e.chart.target := e.tail_mem_target
  have hzy : ∀ i, z i ≤ y i := by
    intro i
    dsimp only [z, y]
    linarith
  have hzne : z ≠ y := by
    intro heq
    have hcoord := congrFun heq ⟨0, hd⟩
    dsimp only [z, y] at hcoord
    linarith
  let g := e.liftSegment hymem hzmem
  refine ⟨g, ?_, ?_, ?_⟩
  · exact e.liftSegment_zero hymem hzmem |>.trans e.symm_tail_eq
  · intro u i
    rw [e.tail_liftSegment hymem hzmem]
    dsimp only [tailLine, y, z]
    ring
  · exact e.height_zero_strictMono_liftSegment hymem hzmem hzy hzne

/-! ## Compactness kernel for maximal continuation -/

/-- Reconstruct consecutive differences from height zero and the tail-height
vector. -/
def differenceOfBaseTail {d : ℕ} (z : ℝ × (Fin d → ℝ)) : Fin d → ℝ :=
  fun i ↦ if hi : i.val = 0 then z.2 i - z.1
    else z.2 i - z.2 ⟨i.val - 1, by omega⟩

lemma continuous_differenceOfBaseTail {d : ℕ} :
    Continuous (differenceOfBaseTail :
      ℝ × (Fin d → ℝ) → Fin d → ℝ) := by
  apply continuous_pi
  intro i
  unfold differenceOfBaseTail
  split_ifs
  · fun_prop
  · fun_prop

lemma differenceOfBaseTail_height_eq_gapDifference
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    differenceOfBaseTail
      (nodes.height (0 : Fin (d + 1)), tailGapHeight nodes) =
        gapDifference nodes := by
  funext i
  unfold differenceOfBaseTail gapDifference
  split_ifs with hi
  · have hcast : i.castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext
      exact hi
    rw [hcast]
    rfl
  · let j : Fin d := ⟨i.val - 1, by omega⟩
    have hjsucc : j.succ = i.castSucc := by
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    simp only [tailGapHeight]
    rw [hjsucc]

/-- Endpoint arrays whose tail vector lies in `K` and whose first height lies
in `[a,b]`. -/
def tailHeightSlab {d : ℕ} {A B : ℝ}
    (K : Set (Fin d → ℝ)) (a b : ℝ) : Set (EndpointArray d A B) :=
  {nodes | tailGapHeight nodes ∈ K ∧
    nodes.height (0 : Fin (d + 1)) ∈ Set.Icc a b}

/-- The compactness fact used at every finite maximal-lift endpoint.

The proof is deliberately routed through the global difference
homeomorphism.  On the slab, `(height 0, tailHeight)` lies in the compact box
`[a,b] × K`; `differenceOfBaseTail` maps this box to a bounded set containing
all gap-difference vectors.  The slab is closed, so its image under the
homeomorphism is closed and bounded in finite-dimensional Euclidean space. -/
theorem isCompact_tailHeightSlab
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (a b : ℝ) :
    IsCompact (tailHeightSlab (A := A) (B := B) K a b) := by
  let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
    (hhomeomorph hAB).homeomorph gapDifference
  let box : Set (ℝ × (Fin d → ℝ)) := Set.Icc a b ×ˢ K
  have hbox : IsCompact box := isCompact_Icc.prod hK
  have hslabClosed :
      IsClosed (tailHeightSlab (A := A) (B := B) K a b) := by
    have htail : Continuous
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ) :=
      continuous_tailGapHeight_of_localOrientation hlocal hd
    exact (hK.isClosed.preimage htail).inter
      (isClosed_Icc.preimage hlocal.1)
  have himageClosed :
      IsClosed (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    e.isClosedMap _ hslabClosed
  have hboundContainer :=
    (hbox.image continuous_differenceOfBaseTail).isBounded
  have himageSubset :
      e '' tailHeightSlab (A := A) (B := B) K a b ⊆
        differenceOfBaseTail '' box := by
    rintro y ⟨nodes, hnodes, rfl⟩
    refine ⟨(nodes.height (0 : Fin (d + 1)), tailGapHeight nodes), ?_, ?_⟩
    · exact ⟨hnodes.2, hnodes.1⟩
    · exact differenceOfBaseTail_height_eq_gapDifference nodes
  have himageBounded :=
    hboundContainer.subset himageSubset
  have himageCompact :
      IsCompact (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨himageClosed, himageBounded⟩
  exact e.isCompact_image.mp himageCompact

/-- Every source-oriented increasing-segment lift lies in one fixed slab:
the tail stays in its compact affine segment, height zero is bounded below
by the elementary Lebesgue bound `1`, and strict antitonicity bounds it above
by its initial value.  Thus no finite continuation time can escape through
the boundary while such a lift exists. -/
theorem increasingSegment_lift_range_subset_tailHeightSlab
    {d : ℕ} {A B : ℝ} (s : EndpointArray d A B)
    (y : Fin d → ℝ) (g : C(I, EndpointArray d A B))
    (hgzero : g 0 = s)
    (hgtail : ∀ u i, tailGapHeight (g u) i =
      (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i)
    (hganti : StrictAnti (fun u : I ↦
      (g u).height (0 : Fin (d + 1)))) :
    Set.range g ⊆ tailHeightSlab
      (segment ℝ (tailGapHeight s) y) 1
        (s.height (0 : Fin (d + 1))) := by
  rintro _ ⟨u, rfl⟩
  constructor
  · have htail : tailGapHeight (g u) =
        tailLine (tailGapHeight s) y u := by
      funext i
      exact hgtail u i
    rw [htail]
    exact tailLine_mem_segment _ _ _
  · constructor
    · exact one_le_height (g u) (0 : Fin (d + 1))
    · have hzeroLe :
          (g u).height (0 : Fin (d + 1)) ≤
            (g 0).height (0 : Fin (d + 1)) :=
        hganti.antitone (show (0 : I) ≤ u from bot_le)
      simpa only [hgzero] using hzeroLe

/-- In particular, under the already-committed global difference
homeomorphism, the range of every increasing-segment lift is contained in a
compact subset of endpoint-array space. -/
theorem exists_compact_superset_range_increasingSegment_lift
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (g : C(I, EndpointArray d A B))
    (hgzero : g 0 = s)
    (hgtail : ∀ u i, tailGapHeight (g u) i =
      (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i)
    (hganti : StrictAnti (fun u : I ↦
      (g u).height (0 : Fin (d + 1)))) :
    ∃ K : Set (EndpointArray d A B), IsCompact K ∧ Set.range g ⊆ K := by
  let K := tailHeightSlab (A := A) (B := B)
    (segment ℝ (tailGapHeight s) y) 1
      (s.height (0 : Fin (d + 1)))
  refine ⟨K, ?_, ?_⟩
  · have hsegment : IsCompact (segment ℝ (tailGapHeight s) y) := by
      rw [segment_eq_image_lineMap]
      exact isCompact_Icc.image (by fun_prop)
    exact isCompact_tailHeightSlab hd hAB hhomeomorph hlocal
      hsegment _ _
  · exact increasingSegment_lift_range_subset_tailHeightSlab
      s y g hgzero hgtail hganti

/-- Sequential form of the compact slab, ready for the endpoint step in a
maximal-lift argument. -/
theorem exists_convergent_subsequence_of_tailHeightSlab
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d) (hAB : AdmissibleInterval A B)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (a b : ℝ)
    (nodes : ℕ → EndpointArray d A B)
    (hnodes : ∀ n, nodes n ∈ tailHeightSlab K a b) :
    ∃ limit ∈ tailHeightSlab K a b, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧ Tendsto (nodes ∘ phi) atTop (𝓝 limit) := by
  let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
    endpointArrayLogRatioHomeomorph hAB
  have hslab : IsCompact (tailHeightSlab (A := A) (B := B) K a b) :=
    isCompact_tailHeightSlab hd hAB hhomeomorph hlocal hK a b
  have himage : IsCompact (e '' tailHeightSlab (A := A) (B := B) K a b) :=
    hslab.image e.continuous
  obtain ⟨z, hz, phi, hphi, htend⟩ := himage.isSeqCompact
    (fun n ↦ ⟨nodes n, hnodes n, rfl⟩)
  refine ⟨e.symm z, ?_, phi, hphi, ?_⟩
  · obtain ⟨limit, hlimit, rfl⟩ := hz
    simpa only [e.symm_apply_apply] using hlimit
  · have hpull := (e.symm.continuous.tendsto z).comp htend
    convert hpull using 1
    funext n
    simp

/-! ## Generic compact continuation for a local homeomorphism -/

/-- A lift of the prefix `[0,u]` of a real-parameterized curve.  Keeping the
domain as an ambient real function makes restriction and chart-local gluing
literal, while continuity is required only on the relevant closed interval. -/
structure PrefixLift {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (f : E → X) (gamma : ℝ → X) (e0 : E) (u : ℝ) where
  toFun : ℝ → E
  continuousOn : ContinuousOn toFun (Set.Icc 0 u)
  zero_eq : toFun 0 = e0
  map_eq : Set.EqOn (f ∘ toFun) gamma (Set.Icc 0 u)

namespace PrefixLift

instance {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u : ℝ} :
    CoeFun (PrefixLift f gamma e0 u) (fun _ ↦ ℝ → E) :=
  ⟨PrefixLift.toFun⟩

/-- The constant lift of a zero-length prefix. -/
def zero {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} (hzero : f e0 = gamma 0) :
    PrefixLift f gamma e0 0 where
  toFun := fun _ ↦ e0
  continuousOn := continuous_const.continuousOn
  zero_eq := rfl
  map_eq := by
    intro t ht
    have ht0 : t = 0 := by exact le_antisymm ht.2 ht.1
    subst t
    exact hzero

/-- Restricting a prefix lift to an earlier nonnegative endpoint. -/
def restrict {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v : ℝ}
    (L : PrefixLift f gamma e0 u) (_hv : 0 ≤ v) (hvu : v ≤ u) :
    PrefixLift f gamma e0 v where
  toFun := L
  continuousOn := L.continuousOn.mono fun _ ht ↦
    ⟨ht.1, ht.2.trans hvu⟩
  zero_eq := L.zero_eq
  map_eq := by
    intro t ht
    exact L.map_eq ⟨ht.1, ht.2.trans hvu⟩

/-- Prefix lifts through a local homeomorphism are unique on their common
interval once their initial values agree. -/
theorem eqOn {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] {f : E → X} {gamma : ℝ → X} {e0 : E} {u : ℝ}
    (hloc : IsLocalHomeomorph f) (hu : 0 ≤ u)
    (L M : PrefixLift f gamma e0 u) :
    Set.EqOn L M (Set.Icc 0 u) := by
  apply (T2Space.isSeparatedMap f).eqOn_of_comp_eqOn
    hloc.isLocallyInjective isPreconnected_Icc
    L.continuousOn M.continuousOn
  · intro t ht
    exact (L.map_eq ht).trans (M.map_eq ht).symm
  · exact ⟨le_rfl, hu⟩
  · exact L.zero_eq.trans M.zero_eq.symm

/-- Extend a prefix inside one local-homeomorphism chart.  On the overlap the
old lift and the chart inverse agree by the left inverse law, so this is an
actual continuous gluing rather than an independent choice of branch. -/
def appendChart {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v : ℝ}
    (L : PrefixLift f gamma e0 u) (hu : 0 ≤ u) (_huv : u ≤ v)
    (chart : OpenPartialHomeomorph E X) (hsource : L u ∈ chart.source)
    (hchart : f = chart) (hgamma : Continuous gamma)
    (htarget : ∀ t ∈ Set.Icc u v, gamma t ∈ chart.target) :
    PrefixLift f gamma e0 v where
  toFun t := if t ≤ u then L t else chart.symm (gamma t)
  continuousOn := by
    apply ContinuousOn.if (p := fun t : ℝ ↦ t ≤ u)
    · intro t ht
      have htEq : t = u := by
        have htfront := ht.2
        change t ∈ frontier (Set.Iic u) at htfront
        simpa using htfront
      subst t
      have hmap : f (L u) = gamma u :=
        L.map_eq ⟨hu, le_rfl⟩
      calc
        L u = chart.symm (chart (L u)) := (chart.left_inv hsource).symm
        _ = chart.symm (f (L u)) :=
          congrArg chart.symm (congrFun hchart (L u)).symm
        _ = chart.symm (gamma u) := by rw [hmap]
    · apply L.continuousOn.mono
      rintro t ⟨ht, htclosure⟩
      have htu : t ≤ u := by
        change t ∈ closure (Set.Iic u) at htclosure
        rwa [closure_Iic] at htclosure
      exact ⟨ht.1, htu⟩
    · apply chart.continuousOn_invFun.comp hgamma.continuousOn
      rintro t ⟨ht, htclosure⟩
      have hut : u ≤ t := by
        rw [show {a : ℝ | ¬ a ≤ u} = Set.Ioi u by ext; simp] at htclosure
        rwa [closure_Ioi] at htclosure
      exact htarget t ⟨hut, ht.2⟩
  zero_eq := by
    simp only [if_pos hu, L.zero_eq]
  map_eq := by
    intro t ht
    by_cases htu : t ≤ u
    · simp only [Function.comp_apply, if_pos htu]
      exact L.map_eq ⟨ht.1, htu⟩
    · simp only [Function.comp_apply, if_neg htu]
      rw [hchart]
      exact chart.right_inv (htarget t ⟨le_of_not_ge htu, ht.2⟩)

@[simp]
theorem appendChart_apply_of_le
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {u v t : ℝ}
    (L : PrefixLift f gamma e0 u) (hu : 0 ≤ u) (huv : u ≤ v)
    (chart : OpenPartialHomeomorph E X) (hsource : L u ∈ chart.source)
    (hchart : f = chart) (hgamma : Continuous gamma)
    (htarget : ∀ r ∈ Set.Icc u v, gamma r ∈ chart.target)
    (htu : t ≤ u) :
    appendChart L hu huv chart hsource hchart hgamma htarget t = L t := by
  simp [appendChart, htu]

end PrefixLift

/-- Compact-continuation theorem for local homeomorphisms.

Every finite prefix has a unique branch because the total space is
Hausdorff and the map is locally injective.  Reachable prefix lengths form
an open set by `PrefixLift.appendChart`.  Sequential compactness of the set
containing every reachable endpoint makes that set closed: endpoints along
a convergent sequence of prefix lengths have a convergent subsequence, and
one final chart glues in the limiting prefix.  Connectedness of `[0,T]` then
gives a lift of the entire curve. -/
theorem exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X]
    {f : E → X} {gamma : ℝ → X} {e0 : E} {T : ℝ}
    (hloc : IsLocalHomeomorph f) (hgamma : Continuous gamma)
    (hT : 0 ≤ T) (hzero : f e0 = gamma 0)
    {K : Set E} (hK : IsSeqCompact K)
    (hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 T →
      ∀ L : PrefixLift f gamma e0 u, L u ∈ K) :
    Nonempty (PrefixLift f gamma e0 T) := by
  let Q := {u : ℝ // u ∈ Set.Icc 0 T}
  let S : Set Q := {u | Nonempty (PrefixLift f gamma e0 u.1)}
  have hSseq : IsSeqClosed S := by
    intro q p hq hp
    let L : ∀ n, PrefixLift f gamma e0 (q n).1 :=
      fun n ↦ (hq n).some
    let endpoint : ℕ → E := fun n ↦ L n (q n).1
    have hendpointK : ∀ n, endpoint n ∈ K := by
      intro n
      exact hendpoint (q n).2 (L n)
    obtain ⟨e, heK, phi, hphi, hephi⟩ := hK hendpointK
    have hqphi : Tendsto (fun n ↦ (q (phi n)).1) atTop (𝓝 p.1) := by
      exact (continuous_subtype_val.tendsto p).comp (hp.comp hphi.tendsto_atTop)
    have hmapEndpoint : ∀ n, f (endpoint n) = gamma (q n).1 := by
      intro n
      exact (L n).map_eq ⟨(q n).2.1, le_rfl⟩
    have hfe : f e = gamma p.1 := by
      have hleft := (hloc.continuous.tendsto e).comp hephi
      have hright := (hgamma.tendsto p.1).comp hqphi
      have hright' : Tendsto (fun n ↦ f (endpoint (phi n))) atTop
          (𝓝 (gamma p.1)) := by
        convert hright using 1
        funext n
        exact hmapEndpoint (phi n)
      exact tendsto_nhds_unique hleft hright'
    obtain ⟨chart, hesource, hchart⟩ := hloc e
    have hgammaTarget : gamma p.1 ∈ chart.target := by
      rw [← hfe, hchart]
      exact chart.map_source hesource
    have hopenPreimage : IsOpen (gamma ⁻¹' chart.target) :=
      chart.open_target.preimage hgamma
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopenPreimage
      p.1 hgammaTarget
    by_cases habove : ∃ n, p.1 ≤ (q n).1
    · obtain ⟨n, hn⟩ := habove
      exact ⟨(L n).restrict p.2.1 hn⟩
    · have hbelow : ∀ n, (q n).1 < p.1 := by
        intro n
        exact lt_of_not_ge fun h ↦ habove ⟨n, h⟩
      have heventSource : ∀ᶠ n in atTop, endpoint (phi n) ∈ chart.source :=
        hephi.eventually (chart.open_source.mem_nhds hesource)
      have heventBall : ∀ᶠ n in atTop,
          (q (phi n)).1 ∈ Metric.ball p.1 eps :=
        hqphi.eventually (Metric.ball_mem_nhds p.1 heps)
      obtain ⟨n, hnsource, hnball⟩ :=
        (heventSource.and heventBall).exists
      have htarget : ∀ t ∈ Set.Icc (q (phi n)).1 p.1,
          gamma t ∈ chart.target := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq] at hnball ⊢
        have hleft := hbelow (phi n)
        have habsLeft : |(q (phi n)).1 - p.1| = p.1 - (q (phi n)).1 := by
          rw [abs_of_nonpos (sub_nonpos.mpr hleft.le)]
          ring
        have habs : |t - p.1| = p.1 - t := by
          rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
          ring
        rw [habsLeft] at hnball
        rw [habs]
        have hqt := ht.1
        linarith
      exact ⟨(L (phi n)).appendChart (q (phi n)).2.1
        (hbelow (phi n)).le chart hnsource hchart hgamma htarget⟩
  have hSclosed : IsClosed S := hSseq.isClosed
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    let L : PrefixLift f gamma e0 q.1 := hq.some
    obtain ⟨chart, hsource, hchart⟩ := hloc (L q.1)
    have hmap : f (L q.1) = gamma q.1 :=
      L.map_eq ⟨q.2.1, le_rfl⟩
    have hgammaTarget : gamma q.1 ∈ chart.target := by
      exact hmap ▸ (congrFun hchart (L q.1)).symm ▸
        chart.map_source hsource
    have hopenPreimage : IsOpen (gamma ⁻¹' chart.target) :=
      chart.open_target.preimage hgamma
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hopenPreimage
      q.1 hgammaTarget
    let V : Set Q := {r | r.1 < q.1 + eps}
    have hVopen : IsOpen V := by
      exact isOpen_lt continuous_subtype_val continuous_const
    have hqV : q ∈ V := by
      dsimp only [V]
      exact lt_add_of_pos_right q.1 heps
    apply Filter.mem_of_superset (hVopen.mem_nhds hqV)
    intro r hr
    by_cases hrq : r.1 ≤ q.1
    · exact ⟨L.restrict r.2.1 hrq⟩
    · have hqr : q.1 ≤ r.1 := le_of_not_ge hrq
      have htarget : ∀ t ∈ Set.Icc q.1 r.1,
          gamma t ∈ chart.target := by
        intro t ht
        apply hball
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |t - q.1| = t - q.1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
        rw [habs]
        have hrv : r.1 < q.1 + eps := hr
        have htr := ht.2
        linarith
      exact ⟨L.appendChart q.2.1 hqr chart hsource hchart hgamma htarget⟩
  have hSnonempty : S.Nonempty := by
    let q0 : Q := ⟨0, ⟨le_rfl, hT⟩⟩
    exact ⟨q0, ⟨PrefixLift.zero hzero⟩⟩
  letI : PreconnectedSpace Q :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hSuniv : S = Set.univ :=
    IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSnonempty
  let qT : Q := ⟨T, ⟨hT, le_rfl⟩⟩
  have hqT : qT ∈ S := by rw [hSuniv]; exact Set.mem_univ _
  exact hqT

/-! ## Applying compact continuation to the oriented tail-height map -/

/-- The real-parameter version of `tailLine`. -/
def realTailLine {d : ℕ} (y z : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i ↦ (1 - t) * y i + t * z i

lemma continuous_realTailLine {d : ℕ} (y z : Fin d → ℝ) :
    Continuous (realTailLine y z) := by
  unfold realTailLine
  fun_prop

/-- A lifted increasing affine tail prefix cannot finish above its initial
height zero.  The extreme-value proof is the formal version of the source's
monotonicity sentence: if a maximum occurred at positive time, a sufficiently
close point immediately to its left would lie in the same oriented chart and
have strictly larger height zero. -/
theorem PrefixLift.heightZero_endpoint_le_of_realTailLine
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) {u : ℝ} (hu : u ∈ Set.Icc 0 1)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u) :
    (L u).height (0 : Fin (d + 1)) ≤
      s.height (0 : Fin (d + 1)) := by
  let H : ℝ → ℝ := fun t ↦ (L t).height (0 : Fin (d + 1))
  have hHcont : ContinuousOn H (Set.Icc 0 u) := by
    exact hlocal.1.comp_continuousOn L.continuousOn
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, ⟨le_rfl, hu.1⟩⟩ hHcont
  by_contra hnot
  have hendGt : H 0 < H u := by
    simpa only [H, L.zero_eq] using lt_of_not_ge hnot
  have htGt : H 0 < H t := hendGt.trans_le (hmax ⟨hu.1, le_rfl⟩)
  have htpos : 0 < t := by
    exact lt_of_le_of_ne ht.1 fun htzero ↦ by
      subst t
      exact (lt_irrefl _ htGt).elim
  let e := (hlocal.2 hd (L t)).some
  have hpre : L ⁻¹' e.chart.source ∈ 𝓝[Set.Icc 0 u] t :=
    (L.continuousOn t ht).preimage_mem_nhdsWithin
      (e.chart.open_source.mem_nhds e.mem_source)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let delta : ℝ := min (t / 2) (eps / 2)
  let r : ℝ := t - delta
  have hdelta : 0 < delta := by
    exact lt_min (half_pos htpos) (half_pos heps)
  have hdeltat : delta < t :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self htpos)
  have hdeltaeps : delta < eps :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self heps)
  have hrlt : r < t := by dsimp only [r]; linarith
  have hrmem : r ∈ Set.Icc 0 u := by
    constructor
    · dsimp only [r]
      linarith
    · exact hrlt.le.trans ht.2
  have hrball : r ∈ Metric.ball t eps := by
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |r - t| = delta := by
      dsimp only [r]
      rw [show t - delta - t = -delta by ring, abs_neg,
        abs_of_pos hdelta]
    rw [habs]
    exact hdeltaeps
  have hrsource : L r ∈ e.chart.source :=
    hball ⟨hrball, hrmem⟩
  have htailR : tailGapHeight (L r) =
      realTailLine (tailGapHeight s) y r :=
    L.map_eq hrmem
  have htailT : tailGapHeight (L t) =
      realTailLine (tailGapHeight s) y t :=
    L.map_eq ht
  have htailLe : ∀ i, tailGapHeight (L r) i ≤
      tailGapHeight (L t) i := by
    intro i
    rw [htailR, htailT]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hex : ∃ i, tailGapHeight s i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (h i) (hle i)
  obtain ⟨i0, hi0⟩ := hex
  have htailNe : tailGapHeight (L r) ≠ tailGapHeight (L t) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailR, htailT] at hi
    unfold realTailLine at hi
    nlinarith
  have htailEqChartR : tailGapHeight (L r) = e.chart (L r) :=
    congrFun e.chart_eq (L r)
  have htailRtarget : tailGapHeight (L r) ∈ e.chart.target := by
    exact htailEqChartR.symm ▸ e.chart.map_source hrsource
  have hdecrease := e.height_zero_strictAnti
    htailRtarget e.tail_mem_target htailLe htailNe
  have hsymmR : e.chart.symm (tailGapHeight (L r)) = L r := by
    exact (congrArg e.chart.symm htailEqChartR).trans
      (e.chart.left_inv hrsource)
  rw [hsymmR, e.symm_tail_eq] at hdecrease
  exact (not_lt_of_ge (hmax hrmem) hdecrease).elim

/-- Reparameterize a subinterval of an affine-tail prefix back to `[0,1]`.
The new target curve is definitionally the affine segment between the two
actual endpoint tail vectors. -/
def PrefixLift.reparamRealTailLine
    {d : ℕ} {A B : ℝ} {s : EndpointArray d A B}
    {y : Fin d → ℝ} {u a b : ℝ}
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u)
    (ha : a ∈ Set.Icc 0 u) (hb : b ∈ Set.Icc 0 u) (hab : a ≤ b) :
    PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight (L a)) (tailGapHeight (L b)))
      (L a) 1 where
  toFun t := L ((1 - t) * a + t * b)
  continuousOn := by
    apply L.continuousOn.comp (by fun_prop)
    intro t ht
    constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
  zero_eq := by simp
  map_eq := by
    intro t ht
    have hw : (1 - t) * a + t * b ∈ Set.Icc 0 u := by
      constructor <;> nlinarith [ht.1, ht.2, ha.1, hb.2]
    have hmain := L.map_eq hw
    have hleft := L.map_eq ha
    have hright := L.map_eq hb
    simp only [Function.comp_apply] at hmain hleft hright ⊢
    funext i
    have hmaini := congrFun hmain i
    have hlefti := congrFun hleft i
    have hrighti := congrFun hright i
    unfold realTailLine at hmaini hlefti hrighti ⊢
    rw [hmaini, hlefti, hrighti]
    ring

/-- Strict form of the endpoint estimate for a positive-length increasing
tail prefix.  A short first piece lies in the initial oriented chart and
strictly lowers height zero; the non-strict extreme-value estimate applied to
the remaining reparameterized suffix preserves that strict loss. -/
theorem PrefixLift.heightZero_endpoint_lt_of_realTailLine
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) {u : ℝ} (hu0 : 0 < u) (_hu1 : u ≤ 1)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (realTailLine (tailGapHeight s) y) s u) :
    (L u).height (0 : Fin (d + 1)) <
      s.height (0 : Fin (d + 1)) := by
  let e := (hlocal.2 hd s).some
  have hpre : L ⁻¹' e.chart.source ∈ 𝓝[Set.Icc 0 u] 0 :=
    (L.continuousOn 0 ⟨le_rfl, hu0.le⟩).preimage_mem_nhdsWithin
      (e.chart.open_source.mem_nhds (by simpa [L.zero_eq] using e.mem_source))
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let delta : ℝ := min (u / 2) (eps / 2)
  have hdelta : 0 < delta :=
    lt_min (half_pos hu0) (half_pos heps)
  have hdeltau : delta < u :=
    lt_of_le_of_lt (min_le_left _ _) (half_lt_self hu0)
  have hdeltaeps : delta < eps :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self heps)
  have hdeltamem : delta ∈ Set.Icc 0 u := ⟨hdelta.le, hdeltau.le⟩
  have hdeltaball : delta ∈ Metric.ball (0 : ℝ) eps := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hdelta]
    exact hdeltaeps
  have hdeltasource : L delta ∈ e.chart.source :=
    hball ⟨hdeltaball, hdeltamem⟩
  have htailZero : tailGapHeight (L 0) = tailGapHeight s := by
    rw [L.zero_eq]
  have htailDelta : tailGapHeight (L delta) =
      realTailLine (tailGapHeight s) y delta :=
    L.map_eq hdeltamem
  have htailLe : ∀ i, tailGapHeight s i ≤ tailGapHeight (L delta) i := by
    intro i
    rw [htailDelta]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hex : ∃ i, tailGapHeight s i < y i := by
    by_contra h
    push_neg at h
    apply hne
    funext i
    exact le_antisymm (h i) (hle i)
  obtain ⟨i0, hi0⟩ := hex
  have htailNe : tailGapHeight s ≠ tailGapHeight (L delta) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailDelta] at hi
    unfold realTailLine at hi
    nlinarith
  have htailDeltaTarget : tailGapHeight (L delta) ∈ e.chart.target := by
    have heq : tailGapHeight (L delta) = e.chart (L delta) :=
      congrFun e.chart_eq (L delta)
    exact heq.symm ▸ e.chart.map_source hdeltasource
  have hfirst := e.height_zero_strictAnti e.tail_mem_target
    htailDeltaTarget htailLe htailNe
  have hsymmDelta : e.chart.symm (tailGapHeight (L delta)) = L delta := by
    have heq : tailGapHeight (L delta) = e.chart (L delta) :=
      congrFun e.chart_eq (L delta)
    exact (congrArg e.chart.symm heq).trans
      (e.chart.left_inv hdeltasource)
  rw [e.symm_tail_eq, hsymmDelta] at hfirst
  let M := L.reparamRealTailLine hdeltamem ⟨hu0.le, le_rfl⟩ hdeltau.le
  have htailU : tailGapHeight (L u) =
      realTailLine (tailGapHeight s) y u :=
    L.map_eq ⟨hu0.le, le_rfl⟩
  have hsuffixLe : ∀ i, tailGapHeight (L delta) i ≤
      tailGapHeight (L u) i := by
    intro i
    rw [htailDelta, htailU]
    unfold realTailLine
    have hi := hle i
    nlinarith
  have hsuffixNe : tailGapHeight (L u) ≠ tailGapHeight (L delta) := by
    intro heq
    have hi := congrFun heq i0
    rw [htailU, htailDelta] at hi
    unfold realTailLine at hi
    nlinarith
  have hsuffix := M.heightZero_endpoint_le_of_realTailLine hd hlocal
    (L delta) (tailGapHeight (L u)) hsuffixLe hsuffixNe
    (u := 1) ⟨zero_le_one, le_rfl⟩
  have hfinal := hsuffix.trans_lt hfirst
  change (L ((1 - (1 : ℝ)) * delta + (1 : ℝ) * u)).height
      (0 : Fin (d + 1)) < s.height (0 : Fin (d + 1)) at hfinal
  simpa using hfinal

/-- The globally continued increasing affine-tail lift, including the
source-required strict antitonicity of height zero. -/
theorem exists_increasingSegment_lift_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (s : EndpointArray d A B) (y : Fin d → ℝ)
    (hle : ∀ i, tailGapHeight s i ≤ y i)
    (hne : y ≠ tailGapHeight s) :
    ∃ g : C(I, EndpointArray d A B),
      g 0 = s ∧
      (∀ u i, tailGapHeight (g u) i =
        (1 - (u : ℝ)) * tailGapHeight s i + (u : ℝ) * y i) ∧
      StrictAnti (fun u : I ↦
        (g u).height (0 : Fin (d + 1))) := by
  letI : T2Space (EndpointArray d A B) :=
    (endpointArrayLogRatioHomeomorph s.admissibleInterval).isEmbedding.t2Space
  let gamma : ℝ → (Fin d → ℝ) := realTailLine (tailGapHeight s) y
  let K : Set (EndpointArray d A B) := tailHeightSlab
    (segment ℝ (tailGapHeight s) y) 1
      (s.height (0 : Fin (d + 1)))
  have hsegment : IsCompact (segment ℝ (tailGapHeight s) y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hKseq : IsSeqCompact K := by
    intro nodes hnodes
    exact exists_convergent_subsequence_of_tailHeightSlab hd
      s.admissibleInterval hhomeomorph hlocal hsegment 1
        (s.height (0 : Fin (d + 1))) nodes hnodes
  have hloc := tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd
  have hgamma : Continuous gamma := continuous_realTailLine _ _
  have hzero : tailGapHeight s = gamma 0 := by
    funext i
    simp [gamma, realTailLine]
  have hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 1 →
      ∀ L : PrefixLift
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
        gamma s u, L u ∈ K := by
    intro u hu L
    constructor
    · have htail : tailGapHeight (L u) = gamma u :=
        L.map_eq ⟨hu.1, le_rfl⟩
      rw [htail]
      rw [segment_eq_image_lineMap]
      refine ⟨u, hu, ?_⟩
      funext i
      simp only [gamma, realTailLine, AffineMap.lineMap_apply_module,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    · constructor
      · exact one_le_height (L u) (0 : Fin (d + 1))
      · exact L.heightZero_endpoint_le_of_realTailLine hd hlocal s y hle hne hu
  obtain ⟨L⟩ := exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    hloc hgamma (T := 1) zero_le_one hzero hKseq hendpoint
  let g : C(I, EndpointArray d A B) :=
    ⟨fun u ↦ L u, continuousOn_iff_continuous_restrict.mp L.continuousOn⟩
  refine ⟨g, ?_, ?_, ?_⟩
  · exact L.zero_eq
  · intro u i
    have hmap := L.map_eq u.2
    have hi := congrFun hmap i
    simpa only [Function.comp_apply, gamma, realTailLine] using hi
  · intro u v huv
    have huMem : (u : ℝ) ∈ Set.Icc 0 1 := u.2
    have hvMem : (v : ℝ) ∈ Set.Icc 0 1 := v.2
    let M := L.reparamRealTailLine huMem hvMem huv.le
    have htailU : tailGapHeight (L (u : ℝ)) = gamma (u : ℝ) :=
      L.map_eq huMem
    have htailV : tailGapHeight (L (v : ℝ)) = gamma (v : ℝ) :=
      L.map_eq hvMem
    have htailLe : ∀ i, tailGapHeight (L (u : ℝ)) i ≤
        tailGapHeight (L (v : ℝ)) i := by
      intro i
      rw [htailU, htailV]
      dsimp only [gamma, realTailLine]
      have hi := hle i
      nlinarith [show (u : ℝ) < (v : ℝ) from huv]
    have hex : ∃ i, tailGapHeight s i < y i := by
      by_contra h
      push_neg at h
      apply hne
      funext i
      exact le_antisymm (h i) (hle i)
    obtain ⟨i0, hi0⟩ := hex
    have htailNe : tailGapHeight (L (v : ℝ)) ≠
        tailGapHeight (L (u : ℝ)) := by
      intro heq
      have hi := congrFun heq i0
      rw [htailU, htailV] at hi
      dsimp only [gamma, realTailLine] at hi
      nlinarith [show (u : ℝ) < (v : ℝ) from huv]
    have hstrict := M.heightZero_endpoint_lt_of_realTailLine hd hlocal
      (L (u : ℝ)) (tailGapHeight (L (v : ℝ))) htailLe htailNe
      (u := 1) zero_lt_one (by rfl)
    change (L ((1 - (1 : ℝ)) * (u : ℝ) + (1 : ℝ) * (v : ℝ))).height
      (0 : Fin (d + 1)) <
        (L (u : ℝ)).height (0 : Fin (d + 1)) at hstrict
    norm_num at hstrict
    exact hstrict

/-- The source's diagonal decreasing tail ray, with real time parameter. -/
def decreasingTailRay {d : ℕ} (y : Fin d → ℝ) (t : ℝ) : Fin d → ℝ :=
  fun i ↦ y i - t

lemma continuous_decreasingTailRay {d : ℕ} (y : Fin d → ℝ) :
    Continuous (decreasingTailRay y) := by
  unfold decreasingTailRay
  fun_prop

/-- Stop and reparameterize a decreasing-ray prefix once its first
consecutive difference has fallen to the prescribed level.  The intermediate
value theorem supplies the first required time; positivity follows because
the initial difference is strictly larger. -/
theorem exists_stopped_decreasingRay_of_prefix_endpoint_le
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (r : EndpointArray d A B) (c : ℝ)
    (hc : c < gapDifference r ⟨0, hd⟩)
    {u : ℝ} (hu : 0 ≤ u)
    (L : PrefixLift
      (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
      (decreasingTailRay (tailGapHeight r)) r u)
    (hend : gapDifference (L u) ⟨0, hd⟩ ≤ c) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∃ g : C(I, EndpointArray d A B),
        g 0 = r ∧
        (∀ v i, tailGapHeight (g v) i =
          tailGapHeight r i - (v : ℝ) * alpha) ∧
        gapDifference (g 1) ⟨0, hd⟩ = c := by
  let F : ℝ → ℝ := fun t ↦ gapDifference (L t) ⟨0, hd⟩
  have hFcont : ContinuousOn F (Set.Icc 0 u) := by
    have hdiffCont :=
      (hhomeomorph r.admissibleInterval).continuous.comp_continuousOn
        L.continuousOn
    simpa only [F, Function.comp_def] using
      (continuous_apply ⟨0, hd⟩).comp_continuousOn hdiffCont
  have hFzero : F 0 = gapDifference r ⟨0, hd⟩ := by
    simp only [F, L.zero_eq]
  have hcIcc : c ∈ Set.Icc (F u) (F 0) := by
    exact ⟨hend, by simpa only [hFzero] using hc.le⟩
  obtain ⟨alpha, halphaMem, halphaEq⟩ :=
    intermediate_value_Icc' hu hFcont hcIcc
  have halpha : 0 < alpha := by
    exact lt_of_le_of_ne halphaMem.1 fun hzero ↦ by
      subst alpha
      rw [hFzero] at halphaEq
      exact (ne_of_gt hc) halphaEq
  let g : C(I, EndpointArray d A B) :=
    ⟨fun v ↦ L ((v : ℝ) * alpha), by
      apply L.continuousOn.comp_continuous
      · fun_prop
      · intro v
        exact ⟨mul_nonneg v.2.1 halpha.le,
          (mul_le_of_le_one_left halpha.le v.2.2).trans halphaMem.2⟩⟩
  refine ⟨alpha, halpha, g, ?_, ?_, ?_⟩
  · change L ((0 : ℝ) * alpha) = r
    rw [zero_mul, L.zero_eq]
  · intro v i
    have htime : (v : ℝ) * alpha ∈ Set.Icc 0 u :=
      ⟨mul_nonneg v.2.1 halpha.le,
        (mul_le_of_le_one_left halpha.le v.2.2).trans halphaMem.2⟩
    have hmap := L.map_eq htime
    have hi := congrFun hmap i
    simpa only [Function.comp_apply, decreasingTailRay, g] using hi
  · change gapDifference (L ((1 : ℝ) * alpha)) ⟨0, hd⟩ = c
    simpa only [one_mul, F] using halphaEq

/-- Global continuation of the decreasing diagonal ray until its first
difference reaches any prescribed lower value.  Under the negation of such a
stopped lift, every reachable prefix has first difference `> c`; hence height
zero is bounded above by `tail₀(r)-c`, while all tail vectors remain in a
fixed compact segment.  Compact continuation reaches a time at which the
elementary bound `height ≥ 1` forces the first difference below `c`, and the
preceding stopping lemma gives the contradiction. -/
theorem exists_decreasingRay_to_firstDifference_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ} (hd : 1 ≤ d)
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B)
    (r : EndpointArray d A B) (c : ℝ)
    (hc : c < gapDifference r ⟨0, hd⟩) :
    ∃ alpha : ℝ, 0 < alpha ∧
      ∃ g : C(I, EndpointArray d A B),
        g 0 = r ∧
        (∀ v i, tailGapHeight (g v) i =
          tailGapHeight r i - (v : ℝ) * alpha) ∧
        gapDifference (g 1) ⟨0, hd⟩ = c := by
  let i0 : Fin d := ⟨0, hd⟩
  let T : ℝ := tailGapHeight r i0 - c
  have hi0cast : i0.castSucc = (0 : Fin (d + 1)) := by
    apply Fin.ext
    rfl
  have honeR : 1 ≤ r.height (0 : Fin (d + 1)) :=
    one_le_height r (0 : Fin (d + 1))
  have hdiffR : gapDifference r i0 =
      tailGapHeight r i0 - r.height (0 : Fin (d + 1)) := by
    rw [gapDifference, tailGapHeight, hi0cast]
  have hT : 0 < T := by
    rw [hdiffR] at hc
    dsimp only [T]
    linarith
  by_contra hno
  push_neg at hno
  letI : T2Space (EndpointArray d A B) :=
    (endpointArrayLogRatioHomeomorph r.admissibleInterval).isEmbedding.t2Space
  let gamma : ℝ → (Fin d → ℝ) := decreasingTailRay (tailGapHeight r)
  let tailEnd : Fin d → ℝ := gamma T
  let K : Set (EndpointArray d A B) := tailHeightSlab
    (segment ℝ (tailGapHeight r) tailEnd) 1 T
  have hsegment : IsCompact (segment ℝ (tailGapHeight r) tailEnd) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  have hKseq : IsSeqCompact K := by
    intro nodes hnodes
    exact exists_convergent_subsequence_of_tailHeightSlab hd
      r.admissibleInterval hhomeomorph hlocal hsegment 1 T nodes hnodes
  have hloc := tailGapHeight_isLocalHomeomorph_of_localOrientation hlocal hd
  have hgamma : Continuous gamma := continuous_decreasingTailRay _
  have hzero : tailGapHeight r = gamma 0 := by
    funext i
    simp [gamma, decreasingTailRay]
  have hendpoint : ∀ {u : ℝ}, u ∈ Set.Icc 0 T →
      ∀ L : PrefixLift
        (tailGapHeight : EndpointArray d A B → Fin d → ℝ)
        gamma r u, L u ∈ K := by
    intro u hu L
    have htail : tailGapHeight (L u) = gamma u :=
      L.map_eq ⟨hu.1, le_rfl⟩
    have hdiff : gapDifference (L u) i0 =
        tailGapHeight (L u) i0 -
          (L u).height (0 : Fin (d + 1)) := by
      rw [gapDifference, tailGapHeight, hi0cast]
    have hdiffGt : c < gapDifference (L u) i0 := by
      by_contra hleDiff
      have hstopped := exists_stopped_decreasingRay_of_prefix_endpoint_le
        hd hhomeomorph r c hc hu.1 L (le_of_not_gt hleDiff)
      obtain ⟨alpha, halpha, g, hg0, hgtail, hgend⟩ := hstopped
      exact hno alpha halpha g hg0 hgtail hgend
    constructor
    · rw [htail]
      rw [segment_eq_image_lineMap]
      refine ⟨u / T, ?_, ?_⟩
      · constructor
        · exact div_nonneg hu.1 hT.le
        · exact (div_le_one hT).2 hu.2
      · funext i
        simp only [tailEnd, gamma, decreasingTailRay,
          AffineMap.lineMap_apply_module, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        field_simp
        ring
    · constructor
      · exact one_le_height (L u) (0 : Fin (d + 1))
      · rw [hdiff, htail] at hdiffGt
        have hgammaUi : gamma u i0 = tailGapHeight r i0 - u := rfl
        rw [hgammaUi] at hdiffGt
        dsimp only [T]
        have hu0 := hu.1
        linarith
  obtain ⟨L⟩ := exists_prefixLift_of_isLocalHomeomorph_of_seqCompact
    hloc hgamma hT.le hzero hKseq hendpoint
  have htailFinal : tailGapHeight (L T) = gamma T :=
    L.map_eq ⟨hT.le, le_rfl⟩
  have hdiffFinal : gapDifference (L T) i0 =
      tailGapHeight (L T) i0 -
        (L T).height (0 : Fin (d + 1)) := by
    rw [gapDifference, tailGapHeight, hi0cast]
  have honeFinal : 1 ≤ (L T).height (0 : Fin (d + 1)) :=
    one_le_height (L T) (0 : Fin (d + 1))
  have hfinalLe : gapDifference (L T) i0 ≤ c := by
    rw [hdiffFinal, htailFinal]
    dsimp only [gamma, decreasingTailRay, T]
    linarith
  obtain ⟨alpha, halpha, g, hg0, hgtail, hgend⟩ :=
    exists_stopped_decreasingRay_of_prefix_endpoint_le
      hd hhomeomorph r c hc hT.le L hfinalLe
  exact hno alpha halpha g hg0 hgtail hgend

/-- The complete source path/ray orientation interface, derived from the
global gap-difference homeomorphism and the single local coherent-orientation
input.  No global path or ray is included among the assumptions. -/
theorem gapHeightPathRayOrientation_of_homeomorphism_of_localOrientation
    {d : ℕ} {A B : ℝ}
    (hhomeomorph : GapDifferenceHomeomorphismStatement d A B)
    (hlocal : TailHeightLocalOrientationStatement d A B) :
    GapHeightPathRayOrientationStatement d A B where
  lift_increasingSegment hd s y hle hne :=
    exists_increasingSegment_lift_of_homeomorphism_of_localOrientation
      hd hhomeomorph hlocal s y hle hne
  lift_decreasingRay_to_firstDifference hd r c hc :=
    exists_decreasingRay_to_firstDifference_of_homeomorphism_of_localOrientation
      hd hhomeomorph hlocal r c hc

end

end Randy1153.DeBoorPinkus
