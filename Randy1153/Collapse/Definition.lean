import Randy1153.DeBoorPinkus.NodeSpace

/-!
# Consecutive block collapses

This file isolates the four pieces of index geometry used by the block
comparison: a full block, a block touching only the left endpoint, a block
touching only the right endpoint, and an interior block.  A supplied
`EndpointArray d 0 1` is inserted as an affine copy in a consecutive block
of `d + 2` nodes.  No equioscillation theorem is assumed here.

The full-block case is deliberately exceptional: preserving both extreme
nodes fixes the affine scale, so it is a replacement by the supplied pattern
rather than a small-scale limit.  In the other three cases the lemmas below
give explicit positive small-scale conditions.
-/

namespace Randy1153.Collapse

open Set
open Randy1153.DeBoorPinkus

noncomputable section

/-- A consecutive block of `r` indices in `Fin n`, starting at `start`. -/
structure ConsecutiveBlock (n r : ℕ) where
  start : ℕ
  fits : start + r ≤ n

namespace ConsecutiveBlock

variable {n r : ℕ} (block : ConsecutiveBlock n r)

/-- The global index of a local block index. -/
def index (k : Fin r) : Fin n :=
  ⟨block.start + k.val, by
    have hk := k.isLt
    have hfit := block.fits
    omega⟩

@[simp]
lemma index_val (k : Fin r) : (block.index k).val = block.start + k.val :=
  rfl

lemma index_strictMono : StrictMono block.index := by
  intro i j hij
  simpa only [Fin.lt_def, index_val] using Nat.add_lt_add_left hij block.start

lemma index_injective : Function.Injective block.index :=
  block.index_strictMono.injective

/-- Membership in the consecutive global index interval. -/
def Mem (i : Fin n) : Prop :=
  block.start ≤ i.val ∧ i.val < block.start + r

instance memDecidable (i : Fin n) : Decidable (block.Mem i) :=
  by
    unfold Mem
    infer_instance

@[simp]
lemma mem_index (k : Fin r) : block.Mem (block.index k) := by
  simp [Mem]

/-- The local index associated to a global index known to lie in the block. -/
def localIndex (i : Fin n) (hi : block.Mem i) : Fin r :=
  ⟨i.val - block.start, by
    rcases hi with ⟨hile, hilt⟩
    omega⟩

@[simp]
lemma localIndex_val (i : Fin n) (hi : block.Mem i) :
    (block.localIndex i hi).val = i.val - block.start :=
  rfl

@[simp]
lemma localIndex_index (k : Fin r) :
    block.localIndex (block.index k) (block.mem_index k) = k := by
  apply Fin.ext
  simp

@[simp]
lemma index_localIndex (i : Fin n) (hi : block.Mem i) :
    block.index (block.localIndex i hi) = i := by
  apply Fin.ext
  simp only [index_val, localIndex_val]
  rcases hi with ⟨hile, hilt⟩
  omega

lemma localIndex_lt_localIndex {i j : Fin n} (hi : block.Mem i)
    (hj : block.Mem j) (hij : i < j) :
    block.localIndex i hi < block.localIndex j hj := by
  simp only [Fin.lt_def, localIndex_val]
  have hij' : i.val < j.val := hij
  rcases hi with ⟨hile, _⟩
  rcases hj with ⟨hjle, _⟩
  omega

/-- The fixed exterior indices. -/
def exterior : Finset (Fin n) :=
  Finset.univ.filter fun i => ¬ block.Mem i

@[simp]
lemma mem_exterior (i : Fin n) : i ∈ block.exterior ↔ ¬ block.Mem i := by
  simp [exterior]

end ConsecutiveBlock

/-- The four geometrically distinct positions of a consecutive block. -/
inductive Placement where
  | full
  | leftEndpoint
  | rightEndpoint
  | interior
  deriving DecidableEq

/-- The endpoint equations and strict inequalities belonging to a placement. -/
def Placement.Valid {n r : ℕ} (place : Placement)
    (block : ConsecutiveBlock n r) : Prop :=
  match place with
  | .full => block.start = 0 ∧ block.start + r = n
  | .leftEndpoint => block.start = 0 ∧ block.start + r < n
  | .rightEndpoint => 0 < block.start ∧ block.start + r = n
  | .interior => 0 < block.start ∧ block.start + r < n

/-- Every fitted nonempty block lies in exactly one of the four endpoint
configurations. -/
lemma placement_classification {n r : ℕ} (block : ConsecutiveBlock n r) :
    Placement.Valid .full block ∨
      Placement.Valid .leftEndpoint block ∨
      Placement.Valid .rightEndpoint block ∨
      Placement.Valid .interior block := by
  by_cases hs : block.start = 0
  · by_cases he : block.start + r = n
    · exact Or.inl ⟨hs, he⟩
    · exact Or.inr (Or.inl ⟨hs, lt_of_le_of_ne block.fits he⟩)
  · have hspos : 0 < block.start := Nat.pos_of_ne_zero hs
    by_cases he : block.start + r = n
    · exact Or.inr (Or.inr (Or.inl ⟨hspos, he⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨hspos, lt_of_le_of_ne block.fits he⟩))

/-- A block collapse with a supplied endpoint-containing pattern. -/
structure Spec (n d : ℕ) where
  nodes : OrderedNodes n
  block : ConsecutiveBlock n (d + 2)
  pattern : EndpointArray d 0 1
  placement : Placement
  placement_valid : placement.Valid block

namespace Spec

variable {n d : ℕ} (spec : Spec n d)

/-- The local left endpoint index. -/
def localLeft (_spec : Spec n d) : Fin (d + 2) := endpointLeftIndex d

/-- The local right endpoint index. -/
def localRight (_spec : Spec n d) : Fin (d + 2) := endpointRightIndex d

/-- The first global index of the block. -/
def firstIndex : Fin n := spec.block.index spec.localLeft

/-- The last global index of the block. -/
def lastIndex : Fin n := spec.block.index spec.localRight

/-- First index of the full array (well-defined because the block has at
least two nodes). -/
def globalLeft : Fin n :=
  ⟨0, by have hfit := spec.block.fits; omega⟩

/-- Last index of the full array. -/
def globalRight : Fin n :=
  ⟨n - 1, by have hfit := spec.block.fits; omega⟩

/-- The global gap belonging to a local pattern gap. -/
def gapIndex (g : Fin (d + 1)) : Fin (n - 1) :=
  ⟨spec.block.start + g.val, by
    have hg := g.isLt
    have hfit := spec.block.fits
    omega⟩

@[simp]
lemma localLeft_val : spec.localLeft.val = 0 := rfl

@[simp]
lemma localRight_val : spec.localRight.val = d + 1 := rfl

@[simp]
lemma firstIndex_val : spec.firstIndex.val = spec.block.start := by
  simp [firstIndex, localLeft]

@[simp]
lemma lastIndex_val : spec.lastIndex.val = spec.block.start + d + 1 := by
  simp [lastIndex, localRight, add_assoc]

@[simp]
lemma globalLeft_val : spec.globalLeft.val = 0 := rfl

@[simp]
lemma globalRight_val : spec.globalRight.val = n - 1 := rfl

@[simp]
lemma gapIndex_val (g : Fin (d + 1)) :
    (spec.gapIndex g).val = spec.block.start + g.val :=
  rfl

lemma gapLeftIndex_gapIndex (g : Fin (d + 1)) :
    gapLeftIndex (spec.gapIndex g) =
      spec.block.index (gapLeftIndex g) := by
  apply Fin.ext
  simp

lemma gapRightIndex_gapIndex (g : Fin (d + 1)) :
    gapRightIndex (spec.gapIndex g) =
      spec.block.index (gapRightIndex g) := by
  apply Fin.ext
  simp [add_assoc, add_left_comm, add_comm]

/-- The fixed point about which the affine pattern contracts.  Right-endpoint
blocks contract from their right endpoint; the other cases contract from the
left endpoint. -/
def anchor : ℝ :=
  match spec.placement with
  | .rightEndpoint => spec.nodes.point spec.lastIndex
  | _ => spec.nodes.point spec.firstIndex

/-- Pattern coordinates relative to the chosen anchor. -/
def offset (k : Fin (d + 2)) : ℝ :=
  match spec.placement with
  | .rightEndpoint => spec.pattern.point k - 1
  | _ => spec.pattern.point k

/-- The affine copy of the supplied pattern at positive scale `δ`. -/
def clusterPoint (δ : ℝ) (k : Fin (d + 2)) : ℝ :=
  spec.anchor + δ * spec.offset k

lemma pattern_point_nonneg (k : Fin (d + 2)) : 0 ≤ spec.pattern.point k := by
  calc
    0 = spec.pattern.point (endpointLeftIndex d) := spec.pattern.left_endpoint.symm
    _ ≤ spec.pattern.point k := spec.pattern.strictMono.monotone (Fin.zero_le k)

lemma pattern_point_le_one (k : Fin (d + 2)) : spec.pattern.point k ≤ 1 := by
  calc
    spec.pattern.point k ≤ spec.pattern.point (endpointRightIndex d) :=
      spec.pattern.strictMono.monotone (Fin.le_last k)
    _ = 1 := spec.pattern.right_endpoint

lemma offset_mem_Icc (k : Fin (d + 2)) : spec.offset k ∈ Set.Icc (-1 : ℝ) 1 := by
  have h0 := spec.pattern_point_nonneg k
  have h1 := spec.pattern_point_le_one k
  constructor
  · cases hplace : spec.placement <;> simp [offset, hplace] <;> linarith
  · cases hplace : spec.placement <;> simp [offset, hplace] <;> linarith

lemma offset_strictMono : StrictMono spec.offset := by
  intro i j hij
  cases hplace : spec.placement <;> simp only [offset, hplace]
  · exact spec.pattern.strictMono hij
  · exact spec.pattern.strictMono hij
  · exact sub_lt_sub_right (spec.pattern.strictMono hij) 1
  · exact spec.pattern.strictMono hij

lemma clusterPoint_strictMono {δ : ℝ} (hδ : 0 < δ) :
    StrictMono (spec.clusterPoint δ) := by
  intro i j hij
  simp only [clusterPoint]
  simpa only [add_comm] using
    add_lt_add_left (mul_lt_mul_of_pos_left (spec.offset_strictMono hij) hδ) spec.anchor

@[simp]
lemma offset_localLeft :
    spec.offset spec.localLeft =
      if spec.placement = .rightEndpoint then -1 else 0 := by
  cases hplace : spec.placement <;>
    simp [offset, hplace, localLeft, spec.pattern.left_endpoint]

@[simp]
lemma offset_localRight : spec.offset spec.localRight =
    if spec.placement = .rightEndpoint then 0 else 1 := by
  cases hplace : spec.placement <;>
    simp [offset, hplace, localRight, spec.pattern.right_endpoint]

/-- Pointwise definition of the comparison array: exterior nodes are fixed
and block nodes are replaced by the affine pattern. -/
def point (δ : ℝ) (i : Fin n) : ℝ :=
  if hi : spec.block.Mem i then
    spec.clusterPoint δ (spec.block.localIndex i hi)
  else
    spec.nodes.point i

@[simp]
lemma point_index (δ : ℝ) (k : Fin (d + 2)) :
    spec.point δ (spec.block.index k) = spec.clusterPoint δ k := by
  simp [point]

lemma point_of_not_mem (δ : ℝ) {i : Fin n} (hi : ¬ spec.block.Mem i) :
    spec.point δ i = spec.nodes.point i := by
  simp [point, hi]

/-- Precisely the hypotheses needed to make the piecewise point function an
ordered node family.  The two separation clauses explicitly include the
moving bridge endpoints. -/
structure Admissible (δ : ℝ) : Prop where
  scale_pos : 0 < δ
  mem_Icc : ∀ k, spec.clusterPoint δ k ∈ Set.Icc (-1 : ℝ) 1
  left_separated : ∀ i : Fin n, i.val < spec.block.start →
    spec.nodes.point i < spec.clusterPoint δ spec.localLeft
  right_separated : ∀ i : Fin n, spec.block.start + d + 2 ≤ i.val →
    spec.clusterPoint δ spec.localRight < spec.nodes.point i

/-- The first fixed node to the right of a non-right-endpoint block. -/
def rightExteriorIndex (hright : spec.block.start + d + 2 < n) : Fin n :=
  ⟨spec.block.start + d + 2, hright⟩

/-- The last fixed node to the left of a block not touching the left endpoint. -/
def leftExteriorIndex (hleft : 0 < spec.block.start) : Fin n :=
  ⟨spec.block.start - 1, by
    have hfit := spec.block.fits
    omega⟩

@[simp]
lemma rightExteriorIndex_val (hright : spec.block.start + d + 2 < n) :
    (spec.rightExteriorIndex hright).val = spec.block.start + d + 2 :=
  rfl

@[simp]
lemma leftExteriorIndex_val (hleft : 0 < spec.block.start) :
    (spec.leftExteriorIndex hleft).val = spec.block.start - 1 :=
  rfl

/-- Explicit small-scale criterion for a left-anchored block (left endpoint
or interior). -/
lemma admissible_of_not_right {δ : ℝ}
    (hplace : spec.placement ≠ .rightEndpoint)
    (hright : spec.block.start + d + 2 < n)
    (hδ : 0 < δ)
    (hsmall : spec.anchor + δ < spec.nodes.point (spec.rightExteriorIndex hright)) :
    spec.Admissible δ := by
  have hanchor : spec.anchor = spec.nodes.point spec.firstIndex := by
    cases hp : spec.placement <;> simp_all [anchor]
  have hoff_nonneg : ∀ k, 0 ≤ spec.offset k := by
    intro k
    cases hp : spec.placement <;> simp_all [offset, spec.pattern_point_nonneg k]
  have hoff_le : ∀ k, spec.offset k ≤ 1 := by
    intro k
    cases hp : spec.placement <;> simp_all [offset, spec.pattern_point_le_one k]
  refine ⟨hδ, ?_, ?_, ?_⟩
  · intro k
    have hlower : spec.anchor ≤ spec.clusterPoint δ k := by
      simp only [clusterPoint]
      nlinarith [mul_nonneg hδ.le (hoff_nonneg k)]
    have hupper : spec.clusterPoint δ k ≤ spec.anchor + δ := by
      simp only [clusterPoint]
      nlinarith [mul_le_mul_of_nonneg_left (hoff_le k) hδ.le]
    constructor
    · exact (spec.nodes.neg_one_le spec.firstIndex).trans
        (by simpa only [hanchor] using hlower)
    · exact hupper.trans hsmall.le |>.trans (spec.nodes.le_one _)
  · intro i hi
    rw [clusterPoint, spec.offset_localLeft, if_neg hplace, mul_zero, add_zero,
      hanchor]
    exact spec.nodes.strictMono (by simpa only [Fin.lt_def, spec.firstIndex_val] using hi)
  · intro i hi
    rw [clusterPoint, spec.offset_localRight, if_neg hplace, mul_one]
    exact hsmall.trans_le (spec.nodes.strictMono.monotone (by
      simpa only [Fin.le_iff_val_le_val, spec.rightExteriorIndex_val] using hi))

/-- Every left-anchored nonterminal block is admissible at all sufficiently
small positive scales. -/
theorem exists_small_admissible_of_not_right
    (hplace : spec.placement ≠ .rightEndpoint)
    (hright : spec.block.start + d + 2 < n) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η → spec.Admissible δ := by
  let η := spec.nodes.point (spec.rightExteriorIndex hright) - spec.anchor
  have hη : 0 < η := by
    dsimp only [η]
    rw [show spec.anchor = spec.nodes.point spec.firstIndex by
      cases hp : spec.placement <;> simp_all [anchor]]
    exact sub_pos.mpr (spec.nodes.strictMono (by
      simp only [Fin.lt_def, spec.firstIndex_val, spec.rightExteriorIndex_val]
      omega))
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  apply spec.admissible_of_not_right hplace hright hδ
  dsimp only [η] at hδη ⊢
  linarith

/-- Explicit small-scale criterion for a right-endpoint block. -/
lemma admissible_of_right {δ : ℝ}
    (hplace : spec.placement = .rightEndpoint)
    (hleft : 0 < spec.block.start)
    (hend : spec.block.start + d + 2 = n)
    (hδ : 0 < δ)
    (hsmall : spec.nodes.point (spec.leftExteriorIndex hleft) < spec.anchor - δ) :
    spec.Admissible δ := by
  have hanchor : spec.anchor = spec.nodes.point spec.lastIndex := by simp [anchor, hplace]
  have hoff_nonneg : ∀ k, -1 ≤ spec.offset k := fun k => (spec.offset_mem_Icc k).1
  have hoff_le : ∀ k, spec.offset k ≤ 0 := by
    intro k
    simp [offset, hplace]
    exact spec.pattern_point_le_one k
  refine ⟨hδ, ?_, ?_, ?_⟩
  · intro k
    have hlower : spec.anchor - δ ≤ spec.clusterPoint δ k := by
      simp only [clusterPoint]
      nlinarith [mul_le_mul_of_nonneg_left (hoff_nonneg k) hδ.le]
    have hupper : spec.clusterPoint δ k ≤ spec.anchor := by
      simp only [clusterPoint]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hδ.le (hoff_le k)]
    constructor
    · exact (spec.nodes.neg_one_le _).trans hsmall.le |>.trans hlower
    · exact hupper.trans (by simpa only [hanchor] using spec.nodes.le_one spec.lastIndex)
  · intro i hi
    rw [clusterPoint, spec.offset_localLeft, if_pos hplace, mul_neg, mul_one]
    simpa only [sub_eq_add_neg] using
      (spec.nodes.strictMono.monotone (by
      simpa only [Fin.le_iff_val_le_val, spec.leftExteriorIndex_val] using
        (show i.val ≤ spec.block.start - 1 by omega))).trans_lt hsmall
  · intro i hi
    have : n ≤ i.val := by omega
    exact (Nat.not_lt_of_ge this i.isLt).elim

/-- Every right-endpoint block is admissible at all sufficiently small
positive scales. -/
theorem exists_small_admissible_of_right
    (hplace : spec.placement = .rightEndpoint)
    (hleft : 0 < spec.block.start)
    (hend : spec.block.start + d + 2 = n) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η → spec.Admissible δ := by
  let η := spec.anchor - spec.nodes.point (spec.leftExteriorIndex hleft)
  have hη : 0 < η := by
    dsimp only [η]
    rw [show spec.anchor = spec.nodes.point spec.lastIndex by simp [anchor, hplace]]
    exact sub_pos.mpr (spec.nodes.strictMono (by
      simp only [Fin.lt_def, spec.leftExteriorIndex_val, spec.lastIndex_val]
      omega))
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη
  apply spec.admissible_of_right hplace hleft hend hδ
  dsimp only [η] at hδη ⊢
  linarith

lemma point_strictMono {δ : ℝ} (hδ : spec.Admissible δ) :
    StrictMono (spec.point δ) := by
  intro i j hij
  by_cases hi : spec.block.Mem i
  · by_cases hj : spec.block.Mem j
    · rw [show spec.point δ i = spec.clusterPoint δ (spec.block.localIndex i hi) by
          simp [point, hi],
        show spec.point δ j = spec.clusterPoint δ (spec.block.localIndex j hj) by
          simp [point, hj]]
      exact spec.clusterPoint_strictMono hδ.scale_pos
        (spec.block.localIndex_lt_localIndex hi hj hij)
    · have hjright : spec.block.start + d + 2 ≤ j.val := by
        simp only [ConsecutiveBlock.Mem] at hi hj
        omega
      rw [spec.point_of_not_mem δ hj]
      calc
        spec.point δ i =
            spec.clusterPoint δ (spec.block.localIndex i hi) := by simp [point, hi]
        _ ≤ spec.clusterPoint δ spec.localRight :=
          (spec.clusterPoint_strictMono hδ.scale_pos).monotone (Fin.le_last _)
        _ < spec.nodes.point j := hδ.right_separated j hjright
  · by_cases hj : spec.block.Mem j
    · have hileft : i.val < spec.block.start := by
        simp only [ConsecutiveBlock.Mem] at hi hj
        omega
      rw [spec.point_of_not_mem δ hi]
      calc
        spec.nodes.point i < spec.clusterPoint δ spec.localLeft :=
          hδ.left_separated i hileft
        _ ≤ spec.clusterPoint δ (spec.block.localIndex j hj) :=
          (spec.clusterPoint_strictMono hδ.scale_pos).monotone (Fin.zero_le _)
        _ = spec.point δ j := by simp [point, hj]
    · rw [spec.point_of_not_mem δ hi, spec.point_of_not_mem δ hj]
      exact spec.nodes.strictMono hij

/-- The resulting strictly ordered comparison array. -/
def orderedNodes (δ : ℝ) (hδ : spec.Admissible δ) : OrderedNodes n where
  point := spec.point δ
  injective := (spec.point_strictMono hδ).injective
  mem_Icc i := by
    by_cases hi : spec.block.Mem i
    · simpa [point, hi] using hδ.mem_Icc (spec.block.localIndex i hi)
    · simpa [point, hi] using spec.nodes.mem_Icc i
  strictMono := spec.point_strictMono hδ

@[simp]
lemma orderedNodes_point (δ : ℝ) (hδ : spec.Admissible δ) (i : Fin n) :
    (spec.orderedNodes δ hδ).point i = spec.point δ i :=
  rfl

lemma exterior_fixed (δ : ℝ) (hδ : spec.Admissible δ) {i : Fin n}
    (hi : i ∈ spec.block.exterior) :
    (spec.orderedNodes δ hδ).point i = spec.nodes.point i := by
  rw [orderedNodes_point, spec.point_of_not_mem]
  simpa using hi

/-- A left-anchored collapse fixes the first node of its block. -/
lemma first_point_fixed_of_not_right (δ : ℝ)
    (hplace : spec.placement ≠ .rightEndpoint) :
    spec.point δ spec.firstIndex = spec.nodes.point spec.firstIndex := by
  rw [show spec.firstIndex = spec.block.index spec.localLeft by rfl,
    spec.point_index]
  simp [clusterPoint, anchor, offset, firstIndex, localLeft,
    spec.pattern.left_endpoint]

/-- A right-endpoint collapse fixes the last node of its block. -/
lemma last_point_fixed_of_right (δ : ℝ)
    (hplace : spec.placement = .rightEndpoint) :
    spec.point δ spec.lastIndex = spec.nodes.point spec.lastIndex := by
  rw [show spec.lastIndex = spec.block.index spec.localRight by rfl,
    spec.point_index]
  simp [clusterPoint, anchor, offset, hplace, lastIndex, localRight,
    spec.pattern.right_endpoint]

/-- In each of the three genuinely collapsible cases, both extreme nodes of
the full array remain fixed for every scale. -/
lemma extreme_points_fixed_of_not_full (δ : ℝ)
    (hplace : spec.placement ≠ .full) :
    spec.point δ spec.globalLeft = spec.nodes.point spec.globalLeft ∧
      spec.point δ spec.globalRight = spec.nodes.point spec.globalRight := by
  cases hp : spec.placement
  · exact (hplace hp).elim
  · have hv : spec.block.start = 0 ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp] using spec.placement_valid
    have hleft : spec.globalLeft = spec.firstIndex := by
      apply Fin.ext
      simp [hv.1]
    constructor
    · rw [hleft]
      exact spec.first_point_fixed_of_not_right δ (by simp [hp])
    · apply spec.point_of_not_mem
      simp only [ConsecutiveBlock.Mem, spec.globalRight_val]
      omega
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 = n := by
      simpa [Placement.Valid, hp] using spec.placement_valid
    have hright : spec.globalRight = spec.lastIndex := by
      apply Fin.ext
      simp only [spec.globalRight_val, spec.lastIndex_val]
      omega
    constructor
    · apply spec.point_of_not_mem
      simp only [ConsecutiveBlock.Mem, spec.globalLeft_val]
      omega
    · rw [hright]
      exact spec.last_point_fixed_of_right δ hp
  · have hv : 0 < spec.block.start ∧ spec.block.start + d + 2 < n := by
      simpa [Placement.Valid, hp] using spec.placement_valid
    constructor <;> apply spec.point_of_not_mem
    · simp only [ConsecutiveBlock.Mem, spec.globalLeft_val]
      omega
    · simp only [ConsecutiveBlock.Mem, spec.globalRight_val]
      omega

/-- In the full-block case, preserving both endpoints forces the unique
scale equal to the original endpoint distance. -/
def fullScale : ℝ := spec.nodes.point spec.lastIndex - spec.nodes.point spec.firstIndex

lemma fullScale_pos (_hfull : spec.placement = .full) : 0 < spec.fullScale := by
  unfold fullScale
  exact sub_pos.mpr (spec.nodes.strictMono (by simp [Fin.lt_def, firstIndex_val, lastIndex_val]))

lemma last_point_fixed_full (hfull : spec.placement = .full) :
    spec.point spec.fullScale spec.lastIndex = spec.nodes.point spec.lastIndex := by
  rw [show spec.lastIndex = spec.block.index spec.localRight by rfl,
    spec.point_index]
  simp [clusterPoint, anchor, offset, hfull, fullScale, firstIndex, lastIndex, localRight,
    spec.pattern.right_endpoint]

/-- The full block has one endpoint-preserving admissible scale, namely the
original endpoint distance.  It is not a small-scale family. -/
lemma admissible_full (hfull : spec.placement = .full) :
    spec.Admissible spec.fullScale := by
  have hv : spec.block.start = 0 ∧ spec.block.start + d + 2 = n := by
    simpa [Placement.Valid, hfull] using spec.placement_valid
  have hscale := spec.fullScale_pos hfull
  have hleft : spec.clusterPoint spec.fullScale spec.localLeft =
      spec.nodes.point spec.firstIndex := by
    rw [← spec.point_index]
    exact spec.first_point_fixed_of_not_right spec.fullScale (by simp [hfull])
  have hright : spec.clusterPoint spec.fullScale spec.localRight =
      spec.nodes.point spec.lastIndex := by
    rw [← spec.point_index]
    exact spec.last_point_fixed_full hfull
  refine ⟨hscale, ?_, ?_, ?_⟩
  · intro k
    have hkleft : spec.clusterPoint spec.fullScale spec.localLeft ≤
        spec.clusterPoint spec.fullScale k :=
      (spec.clusterPoint_strictMono hscale).monotone (Fin.zero_le k)
    have hkright : spec.clusterPoint spec.fullScale k ≤
        spec.clusterPoint spec.fullScale spec.localRight :=
      (spec.clusterPoint_strictMono hscale).monotone (Fin.le_last k)
    exact ⟨(spec.nodes.neg_one_le spec.firstIndex).trans (by rwa [hleft] at hkleft),
      hkright.trans (by rw [hright]; exact spec.nodes.le_one spec.lastIndex)⟩
  · intro i hi
    omega
  · intro i hi
    have : n ≤ i.val := by omega
    exact (Nat.not_lt_of_ge this i.isLt).elim

lemma extreme_points_fixed_full (hfull : spec.placement = .full) :
    spec.point spec.fullScale spec.globalLeft = spec.nodes.point spec.globalLeft ∧
      spec.point spec.fullScale spec.globalRight = spec.nodes.point spec.globalRight := by
  have hv : spec.block.start = 0 ∧ spec.block.start + d + 2 = n := by
    simpa [Placement.Valid, hfull] using spec.placement_valid
  have hleft : spec.globalLeft = spec.firstIndex := by
    apply Fin.ext
    simp [hv.1]
  have hright : spec.globalRight = spec.lastIndex := by
    apply Fin.ext
    simp only [spec.globalRight_val, spec.lastIndex_val]
    omega
  constructor
  · rw [hleft]
    exact spec.first_point_fixed_of_not_right spec.fullScale (by simp [hfull])
  · rw [hright]
    exact spec.last_point_fixed_full hfull

end Spec

end

end Randy1153.Collapse
