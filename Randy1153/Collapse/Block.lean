import Randy1153.Collapse.ExteriorGrowth
import Randy1153.DeBoorPinkus.Statement

/-!
# Conditional localization for a collapsed consecutive block

This file consumes, but does not inhabit, the source-backed
`ComparisonPackage`.  It first transports its endpoint-array rigidity to two
ordered arrays with common extreme nodes.  It then combines the checked
internal-gap lower limit and exterior-gap growth estimates with a genuinely
moving comparison array.
-/

namespace Randy1153.Collapse

open Set
open Randy1153.DeBoorPinkus

noncomputable section

/-- Finite conjunction of punctured-right-neighborhood estimates, retaining
an explicit positive radius. -/
private theorem eventually_all_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → ℝ → Prop)
    (hP : ∀ i ∈ s, ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ < η → P i δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η → ∀ i ∈ s, P i δ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨1, by norm_num, ?_⟩
      intro δ hδ hδone i hi
      simp at hi
  | @insert a s ha ih =>
      obtain ⟨ηa, hηa, hPa⟩ := hP a (by simp)
      obtain ⟨ηs, hηs, hPs⟩ := ih (by
        intro i hi
        exact hP i (by simp [hi]))
      refine ⟨min ηa ηs, lt_min hηa hηs, ?_⟩
      intro δ hδ hδmin i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hPa δ hδ (hδmin.trans_le (min_le_left _ _))
      · exact hPs δ hδ (hδmin.trans_le (min_le_right _ _)) i hi

/-- Regard an ordered `(q+2)`-node array as an endpoint-fixed array. -/
def endpointArrayOfOrdered {q : ℕ} (nodes : OrderedNodes (q + 2)) :
    EndpointArray q
      (nodes.point (endpointLeftIndex q))
      (nodes.point (endpointRightIndex q)) where
  toOrderedNodes := nodes
  left_endpoint := rfl
  right_endpoint := rfl

/-- Regard an ordered array as endpoint-fixed at propositionally equal
prescribed endpoints. -/
def endpointArrayOfCommonEndpoints {q : ℕ} (nodes : OrderedNodes (q + 2))
    (A B : ℝ)
    (hA : nodes.point (endpointLeftIndex q) = A)
    (hB : nodes.point (endpointRightIndex q) = B) : EndpointArray q A B where
  toOrderedNodes := nodes
  left_endpoint := hA
  right_endpoint := hB

@[simp]
lemma endpointArrayOfOrdered_toOrdered {q : ℕ}
    (nodes : OrderedNodes (q + 2)) :
    (endpointArrayOfOrdered nodes).toOrderedNodes = nodes :=
  rfl

@[simp]
lemma endpointArrayOfCommonEndpoints_toOrdered {q : ℕ}
    (nodes : OrderedNodes (q + 2)) (A B : ℝ)
    (hA : nodes.point (endpointLeftIndex q) = A)
    (hB : nodes.point (endpointRightIndex q) = B) :
    (endpointArrayOfCommonEndpoints nodes A B hA hB).toOrderedNodes = nodes :=
  rfl

/-- Exact transport of the de Boor--Pinkus coordinatewise rigidity interface
to ordered arrays with common endpoint values. -/
theorem orderedNodes_eq_of_gapHeight_le
    {q : ℕ} {A B : ℝ} (pkg : ComparisonPackage q A B)
    (s t : OrderedNodes (q + 2))
    (hsA : s.point (endpointLeftIndex q) = A)
    (hsB : s.point (endpointRightIndex q) = B)
    (htA : t.point (endpointLeftIndex q) = A)
    (htB : t.point (endpointRightIndex q) = B)
    (hle : ∀ g : Fin (q + 1), gapHeight s g ≤ gapHeight t g) :
    s = t := by
  let s' := endpointArrayOfCommonEndpoints s A B hsA hsB
  let t' := endpointArrayOfCommonEndpoints t A B htA htB
  have heq : s' = t' := pkg.gapHeight_le_rigidity s' t' (by
    intro g
    exact hle g)
  exact congrArg EndpointArray.toOrderedNodes heq

namespace Spec

variable {q d : ℕ} (spec : Spec (q + 2) d)

lemma globalLeft_eq_endpointLeft : spec.globalLeft = endpointLeftIndex q := by
  apply Fin.ext
  simp

lemma globalRight_eq_endpointRight : spec.globalRight = endpointRightIndex q := by
  apply Fin.ext
  simp

/-- The original full-array left endpoint used by the rigidity package. -/
def sourceLeft : ℝ := spec.nodes.point (endpointLeftIndex q)

/-- The original full-array right endpoint used by the rigidity package. -/
def sourceRight : ℝ := spec.nodes.point (endpointRightIndex q)

lemma collapsed_left_endpoint_of_not_full (δ : ℝ)
    (hnotfull : spec.placement ≠ .full) :
    spec.point δ (endpointLeftIndex q) = spec.sourceLeft := by
  have hfix := (spec.extreme_points_fixed_of_not_full δ hnotfull).1
  rw [spec.globalLeft_eq_endpointLeft] at hfix
  exact hfix

lemma collapsed_right_endpoint_of_not_full (δ : ℝ)
    (hnotfull : spec.placement ≠ .full) :
    spec.point δ (endpointRightIndex q) = spec.sourceRight := by
  have hfix := (spec.extreme_points_fixed_of_not_full δ hnotfull).2
  rw [spec.globalRight_eq_endpointRight] at hfix
  exact hfix

/-- The admissible collapsed array, packaged with the original extreme
endpoints so the exact rigidity theorem applies. -/
def collapsedEndpointArray (δ : ℝ) (hδ : spec.Admissible δ)
    (hnotfull : spec.placement ≠ .full) :
    EndpointArray q spec.sourceLeft spec.sourceRight :=
  endpointArrayOfCommonEndpoints (spec.orderedNodes δ hδ)
    spec.sourceLeft spec.sourceRight
    (spec.collapsed_left_endpoint_of_not_full δ hnotfull)
    (spec.collapsed_right_endpoint_of_not_full δ hnotfull)

@[simp]
lemma collapsedEndpointArray_toOrdered (δ : ℝ)
    (hδ : spec.Admissible δ) (hnotfull : spec.placement ≠ .full) :
    (spec.collapsedEndpointArray δ hδ hnotfull).toOrderedNodes =
      spec.orderedNodes δ hδ :=
  rfl

/-- The gaps internal to the consecutive block. -/
def IsInternalGap (g : Fin (q + 1)) : Prop :=
  spec.block.start ≤ g.val ∧ g.val < spec.block.start + d + 1

/-- Recover the local pattern gap from a global internal gap. -/
def localGapIndex (g : Fin (q + 1)) (hg : spec.IsInternalGap g) : Fin (d + 1) :=
  ⟨g.val - spec.block.start, by
    rcases hg with ⟨hleft, hright⟩
    omega⟩

lemma gapIndex_localGapIndex (g : Fin (q + 1)) (hg : spec.IsInternalGap g) :
    spec.gapIndex (spec.localGapIndex g hg) = g := by
  apply Fin.ext
  simp only [gapIndex_val, localGapIndex]
  rcases hg with ⟨hleft, hright⟩
  omega

lemma internal_or_exterior_gap (g : Fin (q + 1)) :
    spec.IsInternalGap g ∨ spec.IsExteriorGap g := by
  by_cases hleft : g.val < spec.block.start
  · exact Or.inr (Or.inl hleft)
  by_cases hright : g.val < spec.block.start + d + 1
  · exact Or.inl ⟨by omega, hright⟩
  · exact Or.inr (Or.inr (by omega))

/-- A convenient name for the common target height, represented by the first
pattern gap. -/
def patternHeight : ℝ := spec.pattern.height (0 : Fin (d + 1))

lemma pattern_height_eq (hequi : Equioscillates spec.pattern)
    (g : Fin (d + 1)) :
    spec.pattern.height g = spec.patternHeight :=
  hequi g 0

/-- If an original internal gap is strictly below the common pattern height,
the corresponding collapsed cluster gap is eventually strictly higher. -/
lemma eventually_internal_gapHeight_gt
    (hequi : Equioscillates spec.pattern) (g : Fin (d + 1))
    (hbelow : gapHeight spec.nodes (spec.gapIndex g) < spec.patternHeight) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        gapHeight spec.nodes (spec.gapIndex g) <
          gapHeight (spec.orderedNodes δ hδ) (spec.gapIndex g) := by
  let ε := (spec.patternHeight - gapHeight spec.nodes (spec.gapIndex g)) / 2
  have hε : 0 < ε := div_pos (sub_pos.mpr hbelow) (by norm_num)
  obtain ⟨η, hη, hconv⟩ := spec.eventually_pattern_gapHeight_sub_lt g ε hε
  refine ⟨η, hη, ?_⟩
  intro δ hδpos hδη hAdm
  have h := hconv δ hδpos hδη hAdm
  rw [spec.pattern_height_eq hequi g] at h
  dsimp only [ε] at h
  linarith

/-- Under the negation of the desired localization conclusion, every global
gap of the collapsed comparison array is eventually strictly higher than the
corresponding original gap.  Internal and exterior/bridge gaps use different
checked estimates. -/
theorem eventually_all_gapHeight_gt
    (hnotfull : spec.placement ≠ .full)
    (hequi : Equioscillates spec.pattern)
    (hbelow : ∀ g : Fin (d + 1),
      gapHeight spec.nodes (spec.gapIndex g) < spec.patternHeight) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ, ∀ g : Fin (q + 1),
        gapHeight spec.nodes g < gapHeight (spec.orderedNodes δ hδ) g := by
  let P : Fin (q + 1) → ℝ → Prop := fun g δ =>
    ∀ hδ : spec.Admissible δ,
      gapHeight spec.nodes g < gapHeight (spec.orderedNodes δ hδ) g
  have hP : ∀ g ∈ (Finset.univ : Finset (Fin (q + 1))),
      ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η → P g δ := by
    intro g hg
    rcases spec.internal_or_exterior_gap g with hint | hext
    · let lgap := spec.localGapIndex g hint
      have hglobal : spec.gapIndex lgap = g := spec.gapIndex_localGapIndex g hint
      obtain ⟨η, hη, hbound⟩ := spec.eventually_internal_gapHeight_gt hequi lgap
        (by simpa only [hglobal] using hbelow lgap)
      refine ⟨η, hη, ?_⟩
      intro δ hδpos hδη hAdm
      simpa only [P, hglobal] using hbound δ hδpos hδη hAdm
    · obtain ⟨η, hη, hbound⟩ :=
        spec.eventually_exteriorGap_gapHeight_gt hnotfull hext
          (0 : Fin (d + 2)) (gapHeight spec.nodes g)
      refine ⟨η, hη, ?_⟩
      intro δ hδpos hδη hAdm
      exact hbound δ hδpos hδη hAdm
  obtain ⟨η, hη, hall⟩ := eventually_all_finset
    (Finset.univ : Finset (Fin (q + 1))) P hP
  refine ⟨η, hη, ?_⟩
  intro δ hδpos hδη hAdm g
  exact hall δ hδpos hδη g (Finset.mem_univ g) hAdm

lemma point_lastIndex_eq_anchor_add (δ : ℝ)
    (hplace : spec.placement ≠ .rightEndpoint) :
    spec.point δ spec.lastIndex = spec.anchor + δ := by
  rw [show spec.lastIndex = spec.block.index spec.localRight by rfl,
    spec.point_index, clusterPoint, spec.offset_localRight, if_neg hplace]
  ring

lemma point_firstIndex_eq_anchor_sub (δ : ℝ)
    (hplace : spec.placement = .rightEndpoint) :
    spec.point δ spec.firstIndex = spec.anchor - δ := by
  rw [show spec.firstIndex = spec.block.index spec.localLeft by rfl,
    spec.point_index, clusterPoint, spec.offset_localLeft, if_pos hplace]
  ring

/-- In every non-full placement the collapsed comparison genuinely differs
from the original array at all sufficiently small positive scales.  The
moving endpoint is the block's right endpoint in the left/interior cases and
its left endpoint in the right-endpoint case. -/
theorem eventually_collapsed_ne_source
    (hnotfull : spec.placement ≠ .full) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ, spec.orderedNodes δ hδ ≠ spec.nodes := by
  cases hp : spec.placement
  · exact (hnotfull hp).elim
  · let η := spec.nodes.point spec.lastIndex - spec.anchor
    have hanchor : spec.anchor = spec.nodes.point spec.firstIndex := by simp [anchor, hp]
    have hη : 0 < η := by
      dsimp only [η]
      rw [hanchor]
      exact sub_pos.mpr (spec.nodes.strictMono (by
        simp only [Fin.lt_def, spec.firstIndex_val, spec.lastIndex_val]
        omega))
    refine ⟨η, hη, ?_⟩
    intro δ hδpos hδη hAdm heq
    have hpoint := congrArg
      (fun nodes : OrderedNodes (q + 2) => nodes.point spec.lastIndex) heq
    change spec.point δ spec.lastIndex = spec.nodes.point spec.lastIndex at hpoint
    rw [spec.point_lastIndex_eq_anchor_add δ (by simp [hp])] at hpoint
    dsimp only [η] at hδη
    linarith
  · let η := spec.anchor - spec.nodes.point spec.firstIndex
    have hanchor : spec.anchor = spec.nodes.point spec.lastIndex := by simp [anchor, hp]
    have hη : 0 < η := by
      dsimp only [η]
      rw [hanchor]
      exact sub_pos.mpr (spec.nodes.strictMono (by
        simp only [Fin.lt_def, spec.firstIndex_val, spec.lastIndex_val]
        omega))
    refine ⟨η, hη, ?_⟩
    intro δ hδpos hδη hAdm heq
    have hpoint := congrArg
      (fun nodes : OrderedNodes (q + 2) => nodes.point spec.firstIndex) heq
    change spec.point δ spec.firstIndex = spec.nodes.point spec.firstIndex at hpoint
    rw [spec.point_firstIndex_eq_anchor_sub δ hp] at hpoint
    dsimp only [η] at hδη
    linarith
  · let η := spec.nodes.point spec.lastIndex - spec.anchor
    have hanchor : spec.anchor = spec.nodes.point spec.firstIndex := by simp [anchor, hp]
    have hη : 0 < η := by
      dsimp only [η]
      rw [hanchor]
      exact sub_pos.mpr (spec.nodes.strictMono (by
        simp only [Fin.lt_def, spec.firstIndex_val, spec.lastIndex_val]
        omega))
    refine ⟨η, hη, ?_⟩
    intro δ hδpos hδη hAdm heq
    have hpoint := congrArg
      (fun nodes : OrderedNodes (q + 2) => nodes.point spec.lastIndex) heq
    change spec.point δ spec.lastIndex = spec.nodes.point spec.lastIndex at hpoint
    rw [spec.point_lastIndex_eq_anchor_add δ (by simp [hp])] at hpoint
    dsimp only [η] at hδη
    linarith

/-- Every non-full placement supplies admissible arrays at all sufficiently
small positive scales.  This restates the placement split in the common
shape used by the localization proof. -/
theorem eventually_admissible_of_not_full
    (hnotfull : spec.placement ≠ .full) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η → spec.Admissible δ := by
  cases hp : spec.placement
  · exact (hnotfull hp).elim
  · have hv : Placement.Valid .leftEndpoint spec.block := by
      simpa [hp] using spec.placement_valid
    change spec.block.start = 0 ∧ spec.block.start + (d + 2) < q + 2 at hv
    exact spec.exists_small_admissible_of_not_right (by simp [hp]) hv.2
  · have hv : Placement.Valid .rightEndpoint spec.block := by
      simpa [hp] using spec.placement_valid
    change 0 < spec.block.start ∧ spec.block.start + (d + 2) = q + 2 at hv
    exact spec.exists_small_admissible_of_right hp hv.1 hv.2
  · have hv : Placement.Valid .interior spec.block := by
      simpa [hp] using spec.placement_valid
    change 0 < spec.block.start ∧ spec.block.start + (d + 2) < q + 2 at hv
    exact spec.exists_small_admissible_of_not_right (by simp [hp]) hv.2

/-- Conditional block localization for each genuine small-scale placement.
No comparison theorem is postulated here: `pkg` is the explicit unproved
source package supplied by the caller. -/
theorem exists_internal_gap_ge_patternHeight_of_not_full
    (pkg : ComparisonPackage q spec.sourceLeft spec.sourceRight)
    (hnotfull : spec.placement ≠ .full)
    (hequi : Equioscillates spec.pattern) :
    ∃ g : Fin (d + 1),
      spec.patternHeight ≤ gapHeight spec.nodes (spec.gapIndex g) := by
  by_contra hloc
  push_neg at hloc
  obtain ⟨ηh, hηh, hheight⟩ := spec.eventually_all_gapHeight_gt
    hnotfull hequi hloc
  obtain ⟨ηm, hηm, hmove⟩ := spec.eventually_collapsed_ne_source hnotfull
  obtain ⟨ηa, hηa, hadm⟩ := spec.eventually_admissible_of_not_full hnotfull
  let η := min ηh (min ηm ηa)
  let δ := η / 2
  have hη : 0 < η := lt_min hηh (lt_min hηm hηa)
  have hδpos : 0 < δ := div_pos hη (by norm_num)
  have hδη : δ < η := by dsimp only [δ]; linarith
  have hδηh : δ < ηh := hδη.trans_le (min_le_left _ _)
  have hδηm : δ < ηm := hδη.trans_le
    ((min_le_right ηh (min ηm ηa)).trans (min_le_left ηm ηa))
  have hδηa : δ < ηa := hδη.trans_le
    ((min_le_right ηh (min ηm ηa)).trans (min_le_right ηm ηa))
  have hAdm : spec.Admissible δ := hadm δ hδpos hδηa
  have hle : ∀ g : Fin (q + 1),
      gapHeight spec.nodes g ≤ gapHeight (spec.orderedNodes δ hAdm) g :=
    fun g => (hheight δ hδpos hδηh hAdm g).le
  have heq : spec.nodes = spec.orderedNodes δ hAdm :=
    orderedNodes_eq_of_gapHeight_le pkg spec.nodes (spec.orderedNodes δ hAdm)
      rfl rfl
      (spec.collapsed_left_endpoint_of_not_full δ hnotfull)
      (spec.collapsed_right_endpoint_of_not_full δ hnotfull) hle
  exact hmove δ hδpos hδηm hAdm heq.symm

/-- Every global index belongs to a full block. -/
lemma block_mem_of_full (hfull : spec.placement = .full) (i : Fin (q + 2)) :
    spec.block.Mem i := by
  have hv : Placement.Valid .full spec.block := by
    simpa [hfull] using spec.placement_valid
  change spec.block.start ≤ i.val ∧ i.val < spec.block.start + (d + 2)
  rcases hv with ⟨hstart, hend⟩
  omega

/-- For a full placement the local-to-global block map is an equivalence. -/
def fullBlockIndexEquiv (hfull : spec.placement = .full) :
    Fin (d + 2) ≃ Fin (q + 2) :=
  Equiv.ofBijective spec.block.index
    ⟨spec.block.index_injective, fun i =>
      ⟨spec.block.localIndex i (spec.block_mem_of_full hfull i),
        spec.block.index_localIndex i (spec.block_mem_of_full hfull i)⟩⟩

@[simp]
lemma fullBlockIndexEquiv_apply (hfull : spec.placement = .full)
    (k : Fin (d + 2)) :
    spec.fullBlockIndexEquiv hfull k = spec.block.index k :=
  rfl

lemma exterior_eq_empty_of_full (hfull : spec.placement = .full) :
    spec.block.exterior = ∅ := by
  ext i
  simp [spec.block_mem_of_full hfull i]

lemma exteriorRatio_eq_one_of_full (hfull : spec.placement = .full)
    (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) :
    spec.exteriorRatio δ k x = 1 := by
  simp [exteriorRatio, exteriorPolynomial, spec.exterior_eq_empty_of_full hfull]

lemma fullCardinal_rescale_of_full (hfull : spec.placement = .full)
    (δ z : ℝ) (hδ : δ ≠ 0) (k : Fin (d + 2)) :
    spec.fullCardinal δ k (spec.anchor + δ * spec.patternOffset z) =
      lagrangeFundamental spec.pattern.toNodeFamily k z := by
  rw [spec.fullCardinal_factorization,
    spec.exteriorRatio_eq_one_of_full hfull,
    one_mul, spec.clusterCardinal_rescale δ z hδ]

/-- On a full block, affine rescaling identifies the entire collapsed
Lebesgue function with the supplied pattern Lebesgue function exactly. -/
lemma lebesgueFunction_rescale_of_full
    (hfull : spec.placement = .full) (δ z : ℝ) (hδ : spec.Admissible δ) :
    lebesgueFunction (spec.orderedNodes δ hδ).toNodeFamily
        (spec.anchor + δ * spec.patternOffset z) =
      lebesgueFunction spec.pattern.toNodeFamily z := by
  unfold lebesgueFunction
  let e := spec.fullBlockIndexEquiv hfull
  calc
    (∑ i : Fin (q + 2),
        |lagrangeFundamental (spec.orderedNodes δ hδ).toNodeFamily i
          (spec.anchor + δ * spec.patternOffset z)|) =
      ∑ k : Fin (d + 2),
        |lagrangeFundamental (spec.orderedNodes δ hδ).toNodeFamily (e k)
          (spec.anchor + δ * spec.patternOffset z)| := by
            exact (Fintype.sum_equiv e _ _ fun k => rfl).symm
    _ = ∑ k : Fin (d + 2),
        |spec.fullCardinal δ k
          (spec.anchor + δ * spec.patternOffset z)| := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [show e k = spec.block.index k by rfl,
              spec.fullCardinal_eq_lagrangeFundamental]
    _ = ∑ k : Fin (d + 2),
        |lagrangeFundamental spec.pattern.toNodeFamily k z| := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [spec.fullCardinal_rescale_of_full hfull δ z hδ.scale_pos.ne']

/-- Inverse affine coordinates on a full collapsed pattern gap. -/
lemma pattern_closedGap_of_full {g : Fin (d + 1)}
    (hfull : spec.placement = .full) (δ : ℝ) (hδ : spec.Admissible δ)
    {x : ℝ} (hx : x ∈ closedGap (spec.orderedNodes δ hδ) (spec.gapIndex g)) :
    let z := (x - spec.anchor) / δ
    z ∈ closedGap spec.pattern.toOrderedNodes g ∧
      spec.anchor + δ * spec.patternOffset z = x := by
  have hδpos := hδ.scale_pos
  rw [closedGap, spec.gapLeftIndex_gapIndex, spec.gapRightIndex_gapIndex,
    orderedNodes_point, orderedNodes_point, spec.point_index, spec.point_index,
    clusterPoint, clusterPoint] at hx
  simp only [offset, hfull] at hx
  dsimp only
  constructor
  · change spec.pattern.point (gapLeftIndex g) ≤ (x - spec.anchor) / δ ∧
      (x - spec.anchor) / δ ≤ spec.pattern.point (gapRightIndex g)
    constructor
    · apply (le_div_iff₀ hδpos).2
      linarith [hx.1]
    · apply (div_le_iff₀ hδpos).2
      linarith [hx.2]
  · simp [patternOffset, hfull]
    field_simp
    ring

/-- Exact affine invariance of each gap height in the full-block replacement.
Unlike the three genuine collapse placements, this uses the single
endpoint-preserving scale rather than a limit as `δ → 0`. -/
theorem full_gapHeight_eq_pattern_height
    (hfull : spec.placement = .full) (g : Fin (d + 1)) :
    gapHeight
        (spec.orderedNodes spec.fullScale (spec.admissible_full hfull))
        (spec.gapIndex g) = spec.pattern.height g := by
  let hAdm := spec.admissible_full hfull
  obtain ⟨x, hx, hcol, hcolmax⟩ := exists_lebesgueOn_eq_and_ge
    (spec.orderedNodes spec.fullScale hAdm).toNodeFamily
    (gap_left_lt_right (spec.orderedNodes spec.fullScale hAdm)
      (spec.gapIndex g)).le
  obtain ⟨z, hz, hpat, hpatmax⟩ := exists_lebesgueOn_eq_and_ge
    spec.pattern.toNodeFamily (gap_left_lt_right spec.pattern.toOrderedNodes g).le
  let z' := (x - spec.anchor) / spec.fullScale
  have hz' := spec.pattern_closedGap_of_full (g := g)
    hfull spec.fullScale hAdm hx
  have hscale := spec.fullScale_pos hfull
  have hforward := spec.rescaled_mem_closedGap spec.fullScale hAdm g hz
  apply le_antisymm
  · calc
      gapHeight (spec.orderedNodes spec.fullScale hAdm) (spec.gapIndex g) =
          lebesgueFunction (spec.orderedNodes spec.fullScale hAdm).toNodeFamily x := by
            rw [gapHeight, hcol]
      _ = lebesgueFunction spec.pattern.toNodeFamily z' := by
            rw [← hz'.2]
            exact spec.lebesgueFunction_rescale_of_full hfull spec.fullScale z' hAdm
      _ ≤ lebesgueFunction spec.pattern.toNodeFamily z := hpatmax z' hz'.1
      _ = spec.pattern.height g := by
            rw [EndpointArray.height, gapHeight, hpat]
  · calc
      spec.pattern.height g = lebesgueFunction spec.pattern.toNodeFamily z := by
            rw [EndpointArray.height, gapHeight, hpat]
      _ = lebesgueFunction (spec.orderedNodes spec.fullScale hAdm).toNodeFamily
          (spec.anchor + spec.fullScale * spec.patternOffset z) := by
            exact (spec.lebesgueFunction_rescale_of_full hfull spec.fullScale z hAdm).symm
      _ ≤ lebesgueFunction (spec.orderedNodes spec.fullScale hAdm).toNodeFamily x :=
            hcolmax _ hforward
      _ = gapHeight (spec.orderedNodes spec.fullScale hAdm) (spec.gapIndex g) := by
            rw [gapHeight, hcol]

/-- In a full placement, local pattern gaps enumerate all global gaps. -/
def fullGapIndexEquiv (hfull : spec.placement = .full) :
    Fin (d + 1) ≃ Fin (q + 1) :=
  Equiv.ofBijective spec.gapIndex ⟨by
    intro i j hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    simpa only [gapIndex_val] using Nat.add_left_cancel hval,
    by
      intro g
      have hv : Placement.Valid .full spec.block := by
        simpa [hfull] using spec.placement_valid
      have hint : spec.IsInternalGap g := by
        change spec.block.start ≤ g.val ∧
          g.val < spec.block.start + d + 1
        rcases hv with ⟨hstart, hend⟩
        have hglt := g.isLt
        omega
      exact ⟨spec.localGapIndex g hint,
        spec.gapIndex_localGapIndex g hint⟩⟩

@[simp]
lemma fullGapIndexEquiv_apply (hfull : spec.placement = .full)
    (g : Fin (d + 1)) :
    spec.fullGapIndexEquiv hfull g = spec.gapIndex g :=
  rfl

lemma collapsed_left_endpoint_full (hfull : spec.placement = .full) :
    spec.point spec.fullScale (endpointLeftIndex q) = spec.sourceLeft := by
  have hfix := (spec.extreme_points_fixed_full hfull).1
  rw [spec.globalLeft_eq_endpointLeft] at hfix
  exact hfix

lemma collapsed_right_endpoint_full (hfull : spec.placement = .full) :
    spec.point spec.fullScale (endpointRightIndex q) = spec.sourceRight := by
  have hfix := (spec.extreme_points_fixed_full hfull).2
  rw [spec.globalRight_eq_endpointRight] at hfix
  exact hfix

/-- Under the contradictory assumption that all original full-block gaps lie
below the common pattern height, the endpoint-preserving full replacement is
genuinely a different ordered array. -/
lemma full_collapsed_ne_source_of_below
    (hfull : spec.placement = .full)
    (hequi : Equioscillates spec.pattern)
    (hbelow : ∀ g : Fin (d + 1),
      gapHeight spec.nodes (spec.gapIndex g) < spec.patternHeight) :
    spec.orderedNodes spec.fullScale (spec.admissible_full hfull) ≠ spec.nodes := by
  intro heq
  let g : Fin (d + 1) := 0
  have hheight := spec.full_gapHeight_eq_pattern_height hfull g
  rw [heq, spec.pattern_height_eq hequi g] at hheight
  exact (ne_of_lt (hbelow g)) hheight

/-- Conditional localization in the exceptional full-block placement.  Its
comparison scale is the unique endpoint-preserving `fullScale`, and affine
invariance replaces the small-scale convergence argument. -/
theorem exists_internal_gap_ge_patternHeight_of_full
    (pkg : ComparisonPackage q spec.sourceLeft spec.sourceRight)
    (hfull : spec.placement = .full)
    (hequi : Equioscillates spec.pattern) :
    ∃ g : Fin (d + 1),
      spec.patternHeight ≤ gapHeight spec.nodes (spec.gapIndex g) := by
  by_contra hloc
  push_neg at hloc
  let hAdm := spec.admissible_full hfull
  have hle : ∀ g : Fin (q + 1),
      gapHeight spec.nodes g ≤
        gapHeight (spec.orderedNodes spec.fullScale hAdm) g := by
    intro g
    let lgap := (spec.fullGapIndexEquiv hfull).symm g
    have hindex : spec.gapIndex lgap = g :=
      (spec.fullGapIndexEquiv hfull).apply_symm_apply g
    have horig : gapHeight spec.nodes g < spec.patternHeight := by
      simpa only [hindex] using hloc lgap
    have hcollapsed :
        gapHeight (spec.orderedNodes spec.fullScale hAdm) g =
          spec.patternHeight := by
      rw [← hindex, spec.full_gapHeight_eq_pattern_height hfull lgap,
        spec.pattern_height_eq hequi lgap]
    linarith
  have heq : spec.nodes = spec.orderedNodes spec.fullScale hAdm :=
    orderedNodes_eq_of_gapHeight_le pkg spec.nodes
      (spec.orderedNodes spec.fullScale hAdm) rfl rfl
      (spec.collapsed_left_endpoint_full hfull)
      (spec.collapsed_right_endpoint_full hfull) hle
  exact spec.full_collapsed_ne_source_of_below hfull hequi hloc heq.symm

/-- Strong conditional block-localization theorem, with all four placements
dispatched explicitly.  The only hard external input is the caller-supplied
`ComparisonPackage`; no inhabitant is asserted in this file. -/
theorem exists_internal_gap_ge_patternHeight
    (pkg : ComparisonPackage q spec.sourceLeft spec.sourceRight)
    (hequi : Equioscillates spec.pattern) :
    ∃ g : Fin (d + 1),
      spec.patternHeight ≤ gapHeight spec.nodes (spec.gapIndex g) := by
  cases hp : spec.placement
  · exact spec.exists_internal_gap_ge_patternHeight_of_full pkg hp hequi
  · exact spec.exists_internal_gap_ge_patternHeight_of_not_full pkg
      (by simp [hp]) hequi
  · exact spec.exists_internal_gap_ge_patternHeight_of_not_full pkg
      (by simp [hp]) hequi
  · exact spec.exists_internal_gap_ge_patternHeight_of_not_full pkg
      (by simp [hp]) hequi

/-- Plan-facing spelling of the conditional block theorem. -/
theorem exists_block_gap_ge_equioscHeight
    (pkg : ComparisonPackage q spec.sourceLeft spec.sourceRight)
    (hequi : Equioscillates spec.pattern) :
    ∃ g : Fin (d + 1),
      spec.pattern.height (0 : Fin (d + 1)) ≤
        gapHeight spec.nodes (spec.gapIndex g) := by
  simpa only [patternHeight] using
    spec.exists_internal_gap_ge_patternHeight pkg hequi

end Spec

end

end Randy1153.Collapse
