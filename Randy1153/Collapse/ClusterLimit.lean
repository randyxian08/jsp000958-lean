import Randy1153.Collapse.Definition
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Algebra and internal limits for a collapsed block

The factorization here is the literal one from the block-collapse proof.
For a clustered cardinal function, the factors over fixed exterior nodes
form `E(X) / E(yₖ)` and the remaining factors form the cardinal function of
the affine cluster.  Rescaling by the cluster diameter identifies the latter
factor exactly with the supplied endpoint pattern.
-/

namespace Randy1153.Collapse

open Polynomial Set
open Randy1153.DeBoorPinkus
open scoped BigOperators

noncomputable section

namespace Spec

variable {n d : ℕ} (spec : Spec n d)

/-- Product over the fixed exterior nodes. -/
def exteriorPolynomial : ℝ[X] :=
  ∏ j ∈ spec.block.exterior, (Polynomial.X - Polynomial.C (spec.nodes.point j))

lemma exteriorPolynomial_eval (x : ℝ) :
    spec.exteriorPolynomial.eval x =
      ∏ j ∈ spec.block.exterior, (x - spec.nodes.point j) := by
  rw [exteriorPolynomial, Polynomial.eval_prod]
  apply Finset.prod_congr rfl
  intro j hj
  simp

/-- The exterior factor in a clustered cardinal function. -/
def exteriorRatio (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  spec.exteriorPolynomial.eval x /
    spec.exteriorPolynomial.eval (spec.clusterPoint δ k)

/-- The product of normalized linear factors contributed by the cluster. -/
def clusterCardinal (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  ∏ l ∈ Finset.univ.erase k,
    (x - spec.clusterPoint δ l) /
      (spec.clusterPoint δ k - spec.clusterPoint δ l)

/-- The literal cardinal product of the full collapsed point family.  This
definition does not require ordering; `fullCardinal_eq_lagrangeFundamental`
below identifies it with the project Lebesgue interface once admissibility is
supplied. -/
def fullCardinal (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase (spec.block.index k),
    (x - spec.point δ j) /
      (spec.point δ (spec.block.index k) - spec.point δ j)

lemma exteriorRatio_eq_product (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) :
    spec.exteriorRatio δ k x =
      ∏ j ∈ spec.block.exterior,
        (x - spec.nodes.point j) /
          (spec.clusterPoint δ k - spec.nodes.point j) := by
  simp only [exteriorRatio, spec.exteriorPolynomial_eval, Finset.prod_div_distrib]

private lemma filter_not_mem_erase_index (k : Fin (d + 2)) :
    (Finset.univ.erase (spec.block.index k)).filter
        (fun j => ¬ spec.block.Mem j) = spec.block.exterior := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    ConsecutiveBlock.mem_exterior]
  constructor
  · exact fun h => h.2
  · intro hjnot
    refine ⟨?_, hjnot⟩
    intro hj
    apply hjnot
    rw [hj]
    exact spec.block.mem_index k

private lemma inside_filter_eq_image (k : Fin (d + 2)) :
    (Finset.univ.erase (spec.block.index k)).filter spec.block.Mem =
      (Finset.univ.erase k).image spec.block.index := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
    Finset.mem_image]
  constructor
  · rintro ⟨hjk, hjmem⟩
    refine ⟨spec.block.localIndex j hjmem, ?_, spec.block.index_localIndex j hjmem⟩
    intro hlocal
    apply hjk
    rw [← spec.block.index_localIndex j hjmem, hlocal]
  · rintro ⟨l, hlk, rfl⟩
    exact ⟨fun h => hlk (spec.block.index_injective h), spec.block.mem_index l⟩

private lemma inside_product_eq_clusterCardinal
    (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) :
    (∏ j ∈ (Finset.univ.erase (spec.block.index k)).filter spec.block.Mem,
      (x - spec.point δ j) /
        (spec.point δ (spec.block.index k) - spec.point δ j)) =
      spec.clusterCardinal δ k x := by
  classical
  unfold clusterCardinal
  rw [spec.inside_filter_eq_image k,
    Finset.prod_image spec.block.index_injective.injOn]
  apply Finset.prod_congr rfl
  intro l hl
  simp only [spec.point_index]

/-- Exact algebraic factorization of every clustered cardinal function into
the exterior ratio and the affine-cluster cardinal function. -/
theorem fullCardinal_factorization (δ : ℝ) (k : Fin (d + 2)) (x : ℝ) :
    spec.fullCardinal δ k x =
      spec.exteriorRatio δ k x * spec.clusterCardinal δ k x := by
  classical
  let s := Finset.univ.erase (spec.block.index k)
  let p : Fin n → Prop := spec.block.Mem
  let f : Fin n → ℝ := fun j =>
    (x - spec.point δ j) /
      (spec.point δ (spec.block.index k) - spec.point δ j)
  rw [fullCardinal]
  change (∏ j ∈ s, f j) = _
  rw [← Finset.prod_filter_not_mul_prod_filter s p f]
  congr 1
  · rw [show s.filter (fun j => ¬p j) = spec.block.exterior by
        exact spec.filter_not_mem_erase_index k]
    rw [spec.exteriorRatio_eq_product]
    apply Finset.prod_congr rfl
    intro j hj
    have hjnot : ¬ spec.block.Mem j := by simpa using hj
    simp only [f]
    rw [spec.point_of_not_mem δ hjnot, spec.point_index]
  · exact spec.inside_product_eq_clusterCardinal δ k x

/-- The full product is the project fundamental function for every admissible
collapsed ordered array. -/
lemma fullCardinal_eq_lagrangeFundamental (δ : ℝ) (hδ : spec.Admissible δ)
    (k : Fin (d + 2)) (x : ℝ) :
    spec.fullCardinal δ k x =
      lagrangeFundamental (spec.orderedNodes δ hδ).toNodeFamily
        (spec.block.index k) x := by
  rfl

private lemma offset_sub_offset (k l : Fin (d + 2)) :
    spec.offset k - spec.offset l = spec.pattern.point k - spec.pattern.point l := by
  cases hplace : spec.placement <;> simp [offset, hplace]

/-- The real rescaled coordinate corresponding to a pattern coordinate.
Right-endpoint clusters use coordinates in `[-1,0]`; all other clusters use
coordinates in `[0,1]`. -/
def patternOffset (z : ℝ) : ℝ :=
  if spec.placement = .rightEndpoint then z - 1 else z

lemma patternOffset_monotone : Monotone spec.patternOffset := by
  intro x y hxy
  cases hplace : spec.placement <;> simp [patternOffset, hplace] <;> linarith

private lemma patternOffset_sub_offset (z : ℝ) (l : Fin (d + 2)) :
    spec.patternOffset z - spec.offset l = z - spec.pattern.point l := by
  cases hplace : spec.placement <;> simp [patternOffset, offset, hplace]

lemma patternOffset_mem_Icc {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    spec.patternOffset z ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · cases hplace : spec.placement <;> simp [patternOffset, hplace] <;>
      linarith [hz.1, hz.2]
  · cases hplace : spec.placement <;> simp [patternOffset, hplace] <;>
      linarith [hz.1, hz.2]

/-- Rescaling the cluster interval removes the affine transformation exactly:
the cluster factor is the cardinal function of the supplied pattern. -/
theorem clusterCardinal_rescale (δ z : ℝ) (hδ : δ ≠ 0)
    (k : Fin (d + 2)) :
    spec.clusterCardinal δ k (spec.anchor + δ * spec.patternOffset z) =
      lagrangeFundamental spec.pattern.toNodeFamily k z := by
  classical
  unfold clusterCardinal lagrangeFundamental
  apply Finset.prod_congr rfl
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  have hkl : k ≠ l := fun h => hlk h.symm
  have hpat : spec.pattern.point k - spec.pattern.point l ≠ 0 := by
    intro h
    apply hkl
    apply spec.pattern.injective
    linarith
  rw [clusterPoint, clusterPoint]
  have hoff := spec.offset_sub_offset k l
  have hoffz := spec.patternOffset_sub_offset z l
  rw [show (spec.anchor + δ * spec.patternOffset z -
        (spec.anchor + δ * spec.offset l)) =
      δ * (spec.patternOffset z - spec.offset l) by ring,
    show (spec.anchor + δ * spec.offset k -
        (spec.anchor + δ * spec.offset l)) =
      δ * (spec.offset k - spec.offset l) by ring,
    hoffz, hoff, mul_div_mul_left _ _ hδ]

lemma anchor_ne_exterior {j : Fin n} (hj : j ∈ spec.block.exterior) :
    spec.anchor ≠ spec.nodes.point j := by
  have hjnot : ¬ spec.block.Mem j := by simpa using hj
  intro heq
  cases hplace : spec.placement
  · have hindex : spec.firstIndex = j := spec.nodes.injective (by
      simpa [anchor, hplace] using heq)
    apply hjnot
    rw [← hindex]
    exact spec.block.mem_index spec.localLeft
  · have hindex : spec.firstIndex = j := spec.nodes.injective (by
      simpa [anchor, hplace] using heq)
    apply hjnot
    rw [← hindex]
    exact spec.block.mem_index spec.localLeft
  · have hindex : spec.lastIndex = j := spec.nodes.injective (by
      simpa [anchor, hplace] using heq)
    apply hjnot
    rw [← hindex]
    exact spec.block.mem_index spec.localRight
  · have hindex : spec.firstIndex = j := spec.nodes.injective (by
      simpa [anchor, hplace] using heq)
    apply hjnot
    rw [← hindex]
    exact spec.block.mem_index spec.localLeft

lemma exteriorPolynomial_eval_anchor_ne_zero :
    spec.exteriorPolynomial.eval spec.anchor ≠ 0 := by
  rw [spec.exteriorPolynomial_eval, Finset.prod_ne_zero_iff]
  intro j hj
  exact sub_ne_zero.mpr (spec.anchor_ne_exterior hj)

/-- The exterior ratio tends to one uniformly in the pattern coordinate and
in the finitely many clustered cardinal functions.  This is an explicit
epsilon estimate, not a postulated compact-convergence principle. -/
theorem uniform_exteriorRatio_tendsto_one :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, |δ| < η → ∀ z ∈ Set.Icc (0 : ℝ) 1,
        ∀ k : Fin (d + 2),
          |spec.exteriorRatio δ k
              (spec.anchor + δ * spec.patternOffset z) - 1| < ε := by
  intro ε hε
  let F : ℝ × ℝ → ℝ := fun q =>
    spec.exteriorPolynomial.eval (spec.anchor + q.1) /
      spec.exteriorPolynomial.eval (spec.anchor + q.2)
  have hnum : ContinuousAt
      (fun q : ℝ × ℝ => spec.exteriorPolynomial.eval (spec.anchor + q.1)) (0, 0) :=
    (spec.exteriorPolynomial.continuous.comp
      (continuous_const.add continuous_fst)).continuousAt
  have hden : ContinuousAt
      (fun q : ℝ × ℝ => spec.exteriorPolynomial.eval (spec.anchor + q.2)) (0, 0) :=
    (spec.exteriorPolynomial.continuous.comp
      (continuous_const.add continuous_snd)).continuousAt
  have hF : ContinuousAt F (0, 0) :=
    hnum.div hden (by simpa using spec.exteriorPolynomial_eval_anchor_ne_zero)
  obtain ⟨η, hη, hnear⟩ := (Metric.continuousAt_iff.mp hF) ε hε
  refine ⟨η, hη, ?_⟩
  intro δ hδ z hz k
  have hzoff := spec.patternOffset_mem_Icc hz
  have hkoff := spec.offset_mem_Icc k
  have hzabs : |spec.patternOffset z| ≤ 1 := by
    rw [abs_le]
    exact hzoff
  have hkabs : |spec.offset k| ≤ 1 := by
    rw [abs_le]
    exact hkoff
  have hpair : dist (δ * spec.patternOffset z, δ * spec.offset k) (0, 0) < η := by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
    constructor
    · have h := (mul_le_mul_of_nonneg_left hzabs (abs_nonneg δ)).trans_lt
          (by simpa using hδ)
      simpa only [sub_zero, abs_mul] using h
    · have h := (mul_le_mul_of_nonneg_left hkabs (abs_nonneg δ)).trans_lt
          (by simpa using hδ)
      simpa only [sub_zero, abs_mul] using h
  have hout := hnear hpair
  have hFzero : F (0, 0) = 1 := by
    simp [F, spec.exteriorPolynomial_eval_anchor_ne_zero]
  simpa only [F, exteriorRatio, clusterPoint, hFzero, Real.dist_eq] using hout

/-- Uniform convergence of each clustered cardinal function to its supplied
pattern cardinal function, on the whole rescaled pattern interval. -/
theorem uniform_fullCardinal_tendsto_pattern (k : Fin (d + 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ < η → ∀ z ∈ Set.Icc (0 : ℝ) 1,
        |spec.fullCardinal δ k
            (spec.anchor + δ * spec.patternOffset z) -
          lagrangeFundamental spec.pattern.toNodeFamily k z| < ε := by
  intro ε hε
  obtain ⟨t, ht, hheight, hmax⟩ :=
    exists_lebesgueOn_eq_and_ge spec.pattern.toNodeFamily (by norm_num : (0 : ℝ) ≤ 1)
  let M : ℝ := max 1 (lebesgueFunction spec.pattern.toNodeFamily t)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨η, hη, hratio⟩ := spec.uniform_exteriorRatio_tendsto_one
    (ε / M) (div_pos hε hM)
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη z hz
  have hδabs : |δ| < η := by simpa [abs_of_pos hδ]
  have hR := hratio δ hδabs z hz k
  have hterm_le_fun :
      |lagrangeFundamental spec.pattern.toNodeFamily k z| ≤
        lebesgueFunction spec.pattern.toNodeFamily z := by
    unfold lebesgueFunction
    exact Finset.single_le_sum (fun i _ => abs_nonneg (lagrangeFundamental
      spec.pattern.toNodeFamily i z)) (Finset.mem_univ k)
  have htermM : |lagrangeFundamental spec.pattern.toNodeFamily k z| ≤ M :=
    hterm_le_fun.trans ((hmax z hz).trans (le_max_right _ _))
  rw [spec.fullCardinal_factorization,
    spec.clusterCardinal_rescale δ z hδ.ne']
  rw [show spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) *
      lagrangeFundamental spec.pattern.toNodeFamily k z -
      lagrangeFundamental spec.pattern.toNodeFamily k z =
      (spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) - 1) *
        lagrangeFundamental spec.pattern.toNodeFamily k z by ring,
    abs_mul]
  calc
    |spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) - 1| *
        |lagrangeFundamental spec.pattern.toNodeFamily k z| ≤
      |spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) - 1| * M :=
        mul_le_mul_of_nonneg_left htermM (abs_nonneg _)
    _ < (ε / M) * M := mul_lt_mul_of_pos_right hR hM
    _ = ε := div_mul_cancel₀ ε hM.ne'

/-- A fixed positive bound for every pattern cardinal function on `[0,1]`. -/
def patternBound : ℝ :=
  max 1 (lebesgueOn spec.pattern.toNodeFamily 0 1)

lemma patternBound_pos : 0 < spec.patternBound :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma abs_patternCardinal_le_patternBound (k : Fin (d + 2))
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    |lagrangeFundamental spec.pattern.toNodeFamily k z| ≤ spec.patternBound := by
  have hterm : |lagrangeFundamental spec.pattern.toNodeFamily k z| ≤
      lebesgueFunction spec.pattern.toNodeFamily z := by
    unfold lebesgueFunction
    exact Finset.single_le_sum
      (fun i _ => abs_nonneg (lagrangeFundamental spec.pattern.toNodeFamily i z))
      (Finset.mem_univ k)
  obtain ⟨t, ht, heq, hmax⟩ :=
    exists_lebesgueOn_eq_and_ge spec.pattern.toNodeFamily (by norm_num : (0 : ℝ) ≤ 1)
  exact hterm.trans ((hmax z hz).trans (by rw [← heq]; exact le_max_right _ _))

/-- Sum of the absolute values of only the clustered cardinal functions. -/
def clusterContribution (δ z : ℝ) : ℝ :=
  ∑ k : Fin (d + 2),
    |spec.fullCardinal δ k (spec.anchor + δ * spec.patternOffset z)|

/-- The clustered part of the full Lebesgue function converges uniformly to
the pattern Lebesgue function throughout the rescaled cluster. -/
theorem uniform_clusterContribution_tendsto_pattern :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ δ : ℝ, 0 < δ → δ < η → ∀ z ∈ Set.Icc (0 : ℝ) 1,
        |spec.clusterContribution δ z -
          lebesgueFunction spec.pattern.toNodeFamily z| < ε := by
  intro ε hε
  have hr : (0 : ℝ) < d + 2 := by positivity
  have hM := spec.patternBound_pos
  obtain ⟨η, hη, hratio⟩ := spec.uniform_exteriorRatio_tendsto_one
    (ε / ((d + 2 : ℝ) * spec.patternBound))
    (div_pos hε (mul_pos hr hM))
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη z hz
  have hδabs : |δ| < η := by simpa [abs_of_pos hδ]
  have hterm (k : Fin (d + 2)) :
      |spec.fullCardinal δ k (spec.anchor + δ * spec.patternOffset z) -
          lagrangeFundamental spec.pattern.toNodeFamily k z| <
        ε / (d + 2 : ℝ) := by
    have hR := hratio δ hδabs z hz k
    have hL := spec.abs_patternCardinal_le_patternBound k hz
    rw [spec.fullCardinal_factorization,
      spec.clusterCardinal_rescale δ z hδ.ne']
    rw [show spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) *
        lagrangeFundamental spec.pattern.toNodeFamily k z -
        lagrangeFundamental spec.pattern.toNodeFamily k z =
        (spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) - 1) *
          lagrangeFundamental spec.pattern.toNodeFamily k z by ring,
      abs_mul]
    calc
      |spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) - 1| *
          |lagrangeFundamental spec.pattern.toNodeFamily k z| ≤
        |spec.exteriorRatio δ k (spec.anchor + δ * spec.patternOffset z) - 1| *
          spec.patternBound :=
        mul_le_mul_of_nonneg_left hL (abs_nonneg _)
      _ < (ε / ((d + 2 : ℝ) * spec.patternBound)) * spec.patternBound :=
        mul_lt_mul_of_pos_right hR hM
      _ = ε / (d + 2 : ℝ) := by field_simp
  rw [clusterContribution, lebesgueFunction, ← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin (d + 2),
        (|spec.fullCardinal δ k (spec.anchor + δ * spec.patternOffset z)| -
          |lagrangeFundamental spec.pattern.toNodeFamily k z|)| ≤
        ∑ k : Fin (d + 2),
          abs (|spec.fullCardinal δ k (spec.anchor + δ * spec.patternOffset z)| -
            |lagrangeFundamental spec.pattern.toNodeFamily k z|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ < ∑ _k : Fin (d + 2), ε / (d + 2 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ =>
        (abs_abs_sub_abs_le_abs_sub _ _).trans_lt (hterm k)
    _ = ε := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_ofNat]
      field_simp

lemma patternOffset_point (k : Fin (d + 2)) :
    spec.patternOffset (spec.pattern.point k) = spec.offset k := by
  cases hplace : spec.placement <;> simp [patternOffset, offset, hplace]

/-- A rescaled point of a pattern gap lies in the corresponding global
cluster gap. -/
lemma rescaled_mem_closedGap (δ : ℝ) (hδ : spec.Admissible δ)
    (g : Fin (d + 1)) {z : ℝ}
    (hz : z ∈ closedGap spec.pattern.toOrderedNodes g) :
    spec.anchor + δ * spec.patternOffset z ∈
      closedGap (spec.orderedNodes δ hδ) (spec.gapIndex g) := by
  rw [closedGap, spec.gapLeftIndex_gapIndex, spec.gapRightIndex_gapIndex,
    orderedNodes_point, orderedNodes_point, spec.point_index, spec.point_index]
  constructor
  · rw [clusterPoint, ← spec.patternOffset_point (gapLeftIndex g)]
    simpa only [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left (spec.patternOffset_monotone hz.1)
        hδ.scale_pos.le) spec.anchor
  · rw [clusterPoint, ← spec.patternOffset_point (gapRightIndex g)]
    simpa only [add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_left (spec.patternOffset_monotone hz.2)
        hδ.scale_pos.le) spec.anchor

/-- Clustered cardinal functions form a nonnegative subsum of the full
Lebesgue function. -/
lemma clusterContribution_le_lebesgueFunction (δ : ℝ)
    (hδ : spec.Admissible δ) (z : ℝ) :
    spec.clusterContribution δ z ≤
      lebesgueFunction (spec.orderedNodes δ hδ).toNodeFamily
        (spec.anchor + δ * spec.patternOffset z) := by
  classical
  let x := spec.anchor + δ * spec.patternOffset z
  let s := Finset.univ.image spec.block.index
  have hsum :
      (∑ i ∈ s,
        |lagrangeFundamental (spec.orderedNodes δ hδ).toNodeFamily i x|) =
        spec.clusterContribution δ z := by
    rw [Finset.sum_image spec.block.index_injective.injOn]
    simp only [clusterContribution, x]
    apply Finset.sum_congr rfl
    intro k hk
    rw [spec.fullCardinal_eq_lagrangeFundamental]
  rw [← hsum, lebesgueFunction]
  exact Finset.sum_le_sum_of_subset_of_nonneg (by intro i hi; simp)
    (fun i hi _ => abs_nonneg _)

/-- Any cluster contribution evaluated in a local pattern gap is bounded by
the corresponding global collapsed gap height. -/
lemma clusterContribution_le_gapHeight (δ : ℝ) (hδ : spec.Admissible δ)
    (g : Fin (d + 1)) {z : ℝ}
    (hz : z ∈ closedGap spec.pattern.toOrderedNodes g) :
    spec.clusterContribution δ z ≤
      gapHeight (spec.orderedNodes δ hδ) (spec.gapIndex g) := by
  let x := spec.anchor + δ * spec.patternOffset z
  have hx := spec.rescaled_mem_closedGap δ hδ g hz
  obtain ⟨t, ht, heq, hmax⟩ := exists_lebesgueOn_eq_and_ge
    (spec.orderedNodes δ hδ).toNodeFamily (gap_left_lt_right _ _).le
  calc
    spec.clusterContribution δ z ≤
        lebesgueFunction (spec.orderedNodes δ hδ).toNodeFamily x :=
      spec.clusterContribution_le_lebesgueFunction δ hδ z
    _ ≤ lebesgueFunction (spec.orderedNodes δ hδ).toNodeFamily t := hmax x hx
    _ = gapHeight (spec.orderedNodes δ hδ) (spec.gapIndex g) := by
      rw [gapHeight, heq]

/-- Checked internal-gap limit in the direction needed by block comparison:
every collapsed cluster gap is eventually at least the corresponding pattern
gap height minus an arbitrary positive error. -/
theorem eventually_pattern_gapHeight_sub_lt (g : Fin (d + 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ hδ : spec.Admissible δ,
        spec.pattern.height g - ε <
          gapHeight (spec.orderedNodes δ hδ) (spec.gapIndex g) := by
  obtain ⟨η, hη, hconv⟩ :=
    spec.uniform_clusterContribution_tendsto_pattern ε hε
  obtain ⟨z, hz, hheight, _⟩ :=
    exists_gapHeight_eq_eval_gapPolynomial spec.pattern.toOrderedNodes g
  have hleb : spec.pattern.height g =
      lebesgueFunction spec.pattern.toNodeFamily z := by
    rw [EndpointArray.height, hheight,
      ← lebesgueFunction_eq_eval_gapPolynomial spec.pattern.toOrderedNodes g hz]
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδη hAdm
  have hclose := hconv δ hδ hδη z (by
    exact ⟨(spec.pattern_point_nonneg _).trans hz.1,
      hz.2.trans (spec.pattern_point_le_one _)⟩)
  have hlower : spec.pattern.height g - ε < spec.clusterContribution δ z := by
    rw [hleb]
    have := (abs_lt.mp hclose).1
    linarith
  exact hlower.trans_le (spec.clusterContribution_le_gapHeight δ hAdm g hz)

end Spec

end

end Randy1153.Collapse
