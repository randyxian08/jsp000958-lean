import Randy1153.DeBoorPinkus.Simplex
import Randy1153.DeBoorPinkus.Statement
import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# The de Boor--Pinkus boundary kernel

Lemma 4 of de Boor--Pinkus (1978) considers two consecutive nodal gaps, the
upper of which collapses while the lower stays nondegenerate.  At the midpoint
of the lower gap, every cardinal function dominates its value throughout the
collapsing gap by one common factor tending to infinity.  Summing absolute
values compares the two gap heights and forces the corresponding coordinate
of `gapDifference` to tend to minus infinity.

This file isolates the exact, source-faithful implication from common-point
cardinal domination to gap-height divergence.  In particular, it does **not**
use the tempting but false shortcut that the ratio of the two cardinal
polynomials belonging to colliding nodes must diverge; that ratio can tend to
`-1`.
-/

namespace Randy1153.DeBoorPinkus

open scoped BigOperators Topology
open Filter

noncomputable section

/-! ## Transport and summation -/

/-- Exact product transport of a cardinal function between two nonnodal
points.  This is the algebraic identity used in the displayed estimate in
source Lemma 4; importantly, it transports one cardinal function between two
points, rather than comparing two cardinal functions at colliding nodes. -/
lemma lagrangeFundamental_eval_transport {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {x y : ℝ}
    (hx : ∀ j : Fin n, j ≠ k → x ≠ nodes.point j) :
    lagrangeFundamental nodes k y =
      lagrangeFundamental nodes k x *
        ∏ j ∈ Finset.univ.erase k,
          ((y - nodes.point j) / (x - nodes.point j)) := by
  classical
  unfold lagrangeFundamental
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hxj : x - nodes.point j ≠ 0 := sub_ne_zero.mpr (hx j hjk)
  field_simp

/-- Absolute-value form of `lagrangeFundamental_eval_transport`. -/
lemma abs_lagrangeFundamental_eval_transport {n : ℕ} (nodes : NodeFamily n)
    (k : Fin n) {x y : ℝ}
    (hx : ∀ j : Fin n, j ≠ k → x ≠ nodes.point j) :
    |lagrangeFundamental nodes k y| =
      |lagrangeFundamental nodes k x| *
        ∏ j ∈ Finset.univ.erase k,
          |(y - nodes.point j) / (x - nodes.point j)| := by
  rw [lagrangeFundamental_eval_transport nodes k hx, abs_mul,
    Finset.abs_prod]

/-- A common pointwise cardinal amplification survives summation and hence
amplifies the whole Lebesgue function. -/
lemma mul_le_lebesgueFunction_of_cardinal_domination {n : ℕ}
    (nodes : NodeFamily n) {K x y : ℝ}
    (hdom : ∀ k : Fin n,
      K * |lagrangeFundamental nodes k x| ≤
        |lagrangeFundamental nodes k y|) :
    K * lebesgueFunction nodes x ≤ lebesgueFunction nodes y := by
  classical
  simp only [lebesgueFunction, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ ↦ hdom k

/-! ## Compact gap maxima -/

/-- Every endpoint-array Lebesgue function is at least one. -/
lemma one_le_lebesgueFunction_endpointArray {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (x : ℝ) :
    1 ≤ lebesgueFunction nodes.toNodeFamily x := by
  have hsum :
      ∑ k : Fin (d + 2),
        lagrangeFundamental nodes.toNodeFamily k x = 1 :=
    sum_lagrangeFundamental_eq_one nodes.toOrderedNodes (by omega) x
  calc
    1 = |∑ k : Fin (d + 2),
        lagrangeFundamental nodes.toNodeFamily k x| := by rw [hsum, abs_one]
    _ ≤ ∑ k : Fin (d + 2),
        |lagrangeFundamental nodes.toNodeFamily k x| := Finset.abs_sum_le_sum_abs _ _
    _ = lebesgueFunction nodes.toNodeFamily x := rfl

/-- A gap height bounds the Lebesgue function at every point of its closed
gap. -/
lemma lebesgueFunction_le_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) {x : ℝ}
    (hx : x ∈ closedGap nodes.toOrderedNodes g) :
    lebesgueFunction nodes.toNodeFamily x ≤ nodes.height g := by
  obtain ⟨t, ht, heq, hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes g).le
  exact (hmax x hx).trans_eq heq.symm

/-- Every compact gap height is at least one. -/
lemma one_le_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) :
    1 ≤ nodes.height g := by
  exact (one_le_lebesgueFunction_endpointArray nodes
    (nodes.point (gapLeftIndex g))).trans
      (lebesgueFunction_le_height nodes g
      ⟨le_rfl, (gap_left_lt_right nodes.toOrderedNodes g).le⟩)

/-- With at least three nodes, every gap height is strictly greater than one.
This ensures that a maximizer cannot be either nodal endpoint. -/
lemma one_lt_height {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    1 < nodes.height g := by
  obtain ⟨x, hx⟩ := openGap_nonempty nodes.toOrderedNodes g
  have hxClosed : x ∈ closedGap nodes.toOrderedNodes g := ⟨hx.1.le, hx.2.le⟩
  have hpoly := one_lt_eval_gapPolynomial_of_mem_openGap
    nodes.toOrderedNodes (by omega) g hx
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hxClosed] at hpoly
  exact hpoly.trans_le (lebesgueFunction_le_height nodes g hxClosed)

/-- For an endpoint array with an interior node, the compact maximum on each
gap is attained in its open interior. -/
lemma exists_height_eq_lebesgueFunction_mem_openGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    ∃ x ∈ openGap nodes.toOrderedNodes g,
      nodes.height g = lebesgueFunction nodes.toNodeFamily x := by
  obtain ⟨x, hx, heq, _hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes g).le
  have hheight : 1 < nodes.height g := one_lt_height nodes hd g
  have hleft : x ≠ nodes.point (gapLeftIndex g) := by
    intro h
    subst x
    have hclosed : nodes.point (gapLeftIndex g) ∈ closedGap nodes.toOrderedNodes g :=
      ⟨le_rfl, (gap_left_lt_right nodes.toOrderedNodes g).le⟩
    have hvalue : lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapLeftIndex g)) = 1 := by
      rw [lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hclosed,
        gapPolynomial_eval_left]
    have heq' : nodes.height g = lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapLeftIndex g)) := heq
    rw [heq', hvalue] at hheight
    exact (lt_irrefl 1 hheight)
  have hright : x ≠ nodes.point (gapRightIndex g) := by
    intro h
    subst x
    have hclosed : nodes.point (gapRightIndex g) ∈ closedGap nodes.toOrderedNodes g :=
      ⟨(gap_left_lt_right nodes.toOrderedNodes g).le, le_rfl⟩
    have hvalue : lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapRightIndex g)) = 1 := by
      rw [lebesgueFunction_eq_eval_gapPolynomial nodes.toOrderedNodes g hclosed,
        gapPolynomial_eval_right]
    have heq' : nodes.height g = lebesgueFunction nodes.toNodeFamily
        (nodes.point (gapRightIndex g)) := heq
    rw [heq', hvalue] at hheight
    exact (lt_irrefl 1 hheight)
  refine ⟨x, ⟨lt_of_le_of_ne hx.1 hleft.symm,
    lt_of_le_of_ne hx.2 hright⟩, heq⟩

/-! ## The finite-radius boundary estimate -/

/-- The exact cardinal-domination premise extracted from source Lemma 4 for
two consecutive gaps.  `y` is the source's fixed point `t-hat` in the lower
gap; the quantifier over `x` is uniform over the collapsing upper gap.

This is a definition, not an assertion that the source's product estimate has
already been discharged. -/
def AdjacentCardinalAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (K : ℝ) : Prop :=
  ∃ y ∈ closedGap nodes.toOrderedNodes q.castSucc,
    ∀ x ∈ openGap nodes.toOrderedNodes q.succ,
      ∀ k : Fin (d + 2),
        K * |lagrangeFundamental nodes.toNodeFamily k x| ≤
          |lagrangeFundamental nodes.toNodeFamily k y|

/-- Midpoint of the noncollapsing lower neighbor used in source Lemma 4. -/
def boundaryMidpoint {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (nodes.point (gapLeftIndex q.castSucc) +
    nodes.point (gapRightIndex q.castSucc)) / 2

/-- The explicit finite-radius amplification obtained from the source product
argument.  We use the fixed interval length `B - A` in the harmless bounded
factors, rather than the slightly sharper local two-gap length printed in the
paper. -/
def boundaryAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (endpointSpacing nodes q.castSucc /
      (2 * endpointSpacing nodes q.succ)) *
    (endpointSpacing nodes q.castSucc / (2 * (B - A))) ^ d

lemma boundary_common_index {d : ℕ} (q : Fin d) :
    gapRightIndex (n := d + 2) q.castSucc =
      gapLeftIndex (n := d + 2) q.succ := by
  apply Fin.ext
  rfl

lemma boundaryMidpoint_mem_lowerGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) :
    boundaryMidpoint nodes q ∈ closedGap nodes.toOrderedNodes q.castSucc := by
  have h := gap_left_lt_right nodes.toOrderedNodes q.castSucc
  constructor <;> unfold boundaryMidpoint <;> linarith

/-- A point in the open upper gap is not any interpolation node. -/
lemma upperGap_point_ne_node {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    x ≠ nodes.point j := by
  intro heq
  by_cases hj : j.val ≤ q.val + 1
  · have hjCommon : j ≤ gapLeftIndex q.succ := by
      change j.val ≤ q.val + 1
      exact hj
    have := (nodes.strictMono.monotone hjCommon).trans_lt hx.1
    rw [heq] at this
    exact (lt_irrefl _ this)
  · have hrightj : gapRightIndex q.succ ≤ j := by
      change q.val + 2 ≤ j.val
      omega
    have := hx.2.trans_le (nodes.strictMono.monotone hrightj)
    rw [heq] at this
    exact (lt_irrefl _ this)

/-- Every node is at least half of the lower-gap length away from its
midpoint.  Adjacency is what makes this uniform in the node index. -/
lemma half_lowerSpacing_le_midpoint_distance {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (j : Fin (d + 2)) :
    endpointSpacing nodes q.castSucc / 2 ≤
      |boundaryMidpoint nodes q - nodes.point j| := by
  have hgap := gap_left_lt_right nodes.toOrderedNodes q.castSucc
  by_cases hj : j.val ≤ q.val
  · have hjleft : j ≤ gapLeftIndex q.castSucc := by
      change j.val ≤ q.val
      exact hj
    have hpoint := nodes.strictMono.monotone hjleft
    have hnonneg : 0 ≤ boundaryMidpoint nodes q - nodes.point j := by
      unfold boundaryMidpoint
      linarith
    rw [abs_of_nonneg hnonneg]
    unfold endpointSpacing boundaryMidpoint
    linarith
  · have hcommonj : gapRightIndex q.castSucc ≤ j := by
      change q.val + 1 ≤ j.val
      omega
    have hpoint := nodes.strictMono.monotone hcommonj
    have hnonpos : boundaryMidpoint nodes q - nodes.point j ≤ 0 := by
      unfold boundaryMidpoint
      linarith
    rw [abs_of_nonpos hnonpos]
    unfold endpointSpacing boundaryMidpoint
    linarith

/-- Distances between an upper-gap point and any endpoint-array node are
bounded by the fixed interval length. -/
lemma upperGap_distance_le_intervalLength {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    |x - nodes.point j| ≤ B - A := by
  have hAj : A ≤ nodes.point j := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point j := nodes.strictMono.monotone (by
        simp [Fin.le_iff_val_le_val, endpointLeftIndex])
  have hjB : nodes.point j ≤ B := by
    calc
      nodes.point j ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          change j.val ≤ d + 1
          omega)
      _ = B := nodes.right_endpoint
  have hAx : A < x := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point (gapLeftIndex q.succ) :=
        nodes.strictMono.monotone (by simp [Fin.le_iff_val_le_val, endpointLeftIndex])
      _ < x := hx.1
  have hxB : x < B := by
    calc
      x < nodes.point (gapRightIndex q.succ) := hx.2
      _ ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          simp [Fin.le_iff_val_le_val, endpointRightIndex])
      _ = B := nodes.right_endpoint
  rw [abs_le]
  constructor <;> linarith

private lemma half_div_le_div_of_bounds {L D a b : ℝ}
    (hL : 0 ≤ L) (hD : 0 < D) (hb : 0 < b)
    (ha : L / 2 ≤ a) (hbD : b ≤ D) :
    L / (2 * D) ≤ a / b := by
  rw [div_le_div_iff₀ (mul_pos (by norm_num) hD) hb]
  have h₁ : L * b ≤ L * D := mul_le_mul_of_nonneg_left hbD hL
  have h₂ : (2 * D) * (L / 2) ≤ (2 * D) * a :=
    mul_le_mul_of_nonneg_left ha (mul_pos (by norm_num) hD).le
  nlinarith

/-- Uniform bounded-factor estimate in the source product. -/
lemma boundary_base_le_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (j : Fin (d + 2)) :
    endpointSpacing nodes q.castSucc / (2 * (B - A)) ≤
      |(boundaryMidpoint nodes q - nodes.point j) /
        (x - nodes.point j)| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact sub_pos.mpr nodes.endpoints_lt
  · exact abs_pos.mpr (sub_ne_zero.mpr (upperGap_point_ne_node nodes q hx j))
  · exact half_lowerSpacing_le_midpoint_distance nodes q j
  · exact upperGap_distance_le_intervalLength nodes q hx j

/-- The factor belonging to the common node contains the full reciprocal
collapsing-spacing growth. -/
lemma boundary_ratio_le_common_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) :
    endpointSpacing nodes q.castSucc /
        (2 * endpointSpacing nodes q.succ) ≤
      |(boundaryMidpoint nodes q -
          nodes.point (gapRightIndex q.castSucc)) /
        (x - nodes.point (gapRightIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact endpointSpacing_pos nodes q.succ
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (upperGap_point_ne_node nodes q hx (gapRightIndex q.castSucc)))
  · exact half_lowerSpacing_le_midpoint_distance nodes q
      (gapRightIndex q.castSucc)
  · rw [boundary_common_index q]
    rw [abs_of_pos (sub_pos.mpr hx.1)]
    unfold endpointSpacing
    linarith [hx.2]

/-- The factor belonging to the right endpoint of the collapsing gap has the
same reciprocal-spacing lower bound. -/
lemma boundary_ratio_le_upperRight_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) :
    endpointSpacing nodes q.castSucc /
        (2 * endpointSpacing nodes q.succ) ≤
      |(boundaryMidpoint nodes q - nodes.point (gapRightIndex q.succ)) /
        (x - nodes.point (gapRightIndex q.succ))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.castSucc).le
  · exact endpointSpacing_pos nodes q.succ
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (upperGap_point_ne_node nodes q hx (gapRightIndex q.succ)))
  · exact half_lowerSpacing_le_midpoint_distance nodes q (gapRightIndex q.succ)
  · rw [abs_of_neg (sub_neg.mpr hx.2)]
    unfold endpointSpacing
    linarith [hx.1]

/-- For every cardinal row, at least one of the two factors adjacent to the
collapsing gap survives deletion of that cardinal's own node. -/
lemma exists_boundary_ratio_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (k : Fin (d + 2)) :
    ∃ r ∈ Finset.univ.erase k,
      endpointSpacing nodes q.castSucc /
          (2 * endpointSpacing nodes q.succ) ≤
        |(boundaryMidpoint nodes q - nodes.point r) /
          (x - nodes.point r)| := by
  by_cases hk : gapRightIndex q.castSucc = k
  · refine ⟨gapRightIndex q.succ, ?_,
      boundary_ratio_le_upperRight_factor nodes q hx⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply (gapLeftIndex_lt_rightIndex (n := d + 2) q.succ).ne
    rw [← boundary_common_index q, hk, h]
  · exact ⟨gapRightIndex q.castSucc, by simp [hk],
      boundary_ratio_le_common_factor nodes q hx⟩

/-- Product form of the displayed estimate in source Lemma 4.  One of the
two collision factors supplies the reciprocal upper spacing; the other `d`
factors are bounded below using the fixed interval length. -/
lemma boundaryAmplification_le_factorProduct {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.succ) (k : Fin (d + 2)) :
    boundaryAmplification nodes q ≤
      ∏ j ∈ Finset.univ.erase k,
        |(boundaryMidpoint nodes q - nodes.point j) /
          (x - nodes.point j)| := by
  classical
  let s : Finset (Fin (d + 2)) := Finset.univ.erase k
  let f : Fin (d + 2) → ℝ := fun j ↦
    |(boundaryMidpoint nodes q - nodes.point j) / (x - nodes.point j)|
  let c : ℝ := endpointSpacing nodes q.castSucc / (2 * (B - A))
  let R : ℝ := endpointSpacing nodes q.castSucc /
    (2 * endpointSpacing nodes q.succ)
  obtain ⟨r, hrs, hrR⟩ := exists_boundary_ratio_factor nodes q hx k
  have hc : ∀ j ∈ s, c ≤ f j := by
    intro j _hj
    exact boundary_base_le_factor nodes q hx j
  have hc0 : 0 ≤ c := by
    exact div_nonneg (endpointSpacing_pos nodes q.castSucc).le
      (mul_nonneg (by norm_num) (sub_pos.mpr nodes.endpoints_lt).le)
  have hpow : c ^ (s.erase r).card ≤ ∏ j ∈ s.erase r, f j := by
    have h := Finset.prod_le_prod (s := s.erase r)
      (f := fun _ ↦ c) (g := f)
      (fun _ _ ↦ hc0)
      (fun j hj ↦ hc j (Finset.mem_of_mem_erase hj))
    simpa using h
  have hcard : (s.erase r).card = d := by
    have hrs' : r ∈ s := hrs
    simp only [s, Finset.card_erase_of_mem hrs', Finset.card_erase_of_mem
      (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hpow' : c ^ d ≤ ∏ j ∈ s.erase r, f j := by
    rwa [hcard] at hpow
  have hrR' : R ≤ f r := hrR
  have hprod : R * c ^ d ≤ ∏ j ∈ s, f j := by
    calc
      R * c ^ d ≤ f r * c ^ d :=
        mul_le_mul_of_nonneg_right hrR' (pow_nonneg hc0 d)
      _ ≤ f r * ∏ j ∈ s.erase r, f j :=
        mul_le_mul_of_nonneg_left hpow' (abs_nonneg _)
      _ = ∏ j ∈ s, f j := Finset.mul_prod_erase s f hrs
  simpa only [boundaryAmplification, s, f, c, R] using hprod

/-- The explicit source product estimate supplies the precise common
cardinal amplification premise needed by the finite-radius height lemma. -/
theorem adjacentCardinalAmplification_boundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) :
    AdjacentCardinalAmplification nodes q (boundaryAmplification nodes q) := by
  refine ⟨boundaryMidpoint nodes q, boundaryMidpoint_mem_lowerGap nodes q, ?_⟩
  intro x hx k
  have hxnodes : ∀ j : Fin (d + 2), j ≠ k → x ≠ nodes.point j := by
    intro j _hjk
    exact upperGap_point_ne_node nodes q hx j
  have htransport := abs_lagrangeFundamental_eval_transport nodes.toNodeFamily k
    (x := x) (y := boundaryMidpoint nodes q) hxnodes
  rw [htransport]
  have hprod := boundaryAmplification_le_factorProduct nodes q hx k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (lagrangeFundamental nodes.toNodeFamily k x))

/-- Quantitative amplification tends to infinity when the upper spacing
collapses and its lower neighbor is eventually bounded below. -/
theorem tendsto_boundaryAmplification_atTop_of_upperSpacing
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (hzero : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
      atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta)
    (hlower : ∀ᶠ m in atTop,
      delta ≤ endpointSpacing (nodes m) q.castSucc) :
    Tendsto (fun m ↦ boundaryAmplification (nodes m) q) atTop atTop := by
  let C : ℝ := (delta / 2) * (delta / (2 * (B - A))) ^ d
  have hD : 0 < B - A := sub_pos.mpr (nodes 0).endpoints_lt
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hpositive : ∀ᶠ m in atTop,
      endpointSpacing (nodes m) q.succ ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun m ↦ endpointSpacing_pos (nodes m) q.succ
  have hGT : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hinv : Tendsto
      (fun m ↦ (endpointSpacing (nodes m) q.succ)⁻¹) atTop atTop :=
    hGT.inv_tendsto_nhdsGT_zero
  have hCinv : Tendsto
      (fun m ↦ C * (endpointSpacing (nodes m) q.succ)⁻¹) atTop atTop :=
    hinv.const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hCinv
  filter_upwards [hlower] with m hm
  have hLowerPos : 0 < endpointSpacing (nodes m) q.castSucc :=
    endpointSpacing_pos (nodes m) q.castSucc
  have hUpperPos : 0 < endpointSpacing (nodes m) q.succ :=
    endpointSpacing_pos (nodes m) q.succ
  have hbase : delta / (2 * (B - A)) ≤
      endpointSpacing (nodes m) q.castSucc / (2 * (B - A)) := by
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hD.le)
  have hpow : (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hbase d
  have hhalf : delta / 2 ≤ endpointSpacing (nodes m) q.castSucc / 2 := by
    linarith
  have hinner : (delta / 2) * (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.castSucc / 2) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
    exact mul_le_mul hhalf hpow (by positivity) (by positivity)
  dsimp only [C]
  rw [boundaryAmplification, div_eq_mul_inv]
  calc
    (delta / 2 * (delta / (2 * (B - A))) ^ d) *
        (endpointSpacing (nodes m) q.succ)⁻¹ ≤
      ((endpointSpacing (nodes m) q.castSucc / 2) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d) *
          (endpointSpacing (nodes m) q.succ)⁻¹ :=
      mul_le_mul_of_nonneg_right hinner (inv_nonneg.mpr hUpperPos.le)
    _ = (endpointSpacing (nodes m) q.castSucc *
          (2 * endpointSpacing (nodes m) q.succ)⁻¹) *
        (endpointSpacing (nodes m) q.castSucc / (2 * (B - A))) ^ d := by
      field_simp

/-- Source Lemma 4's analytic heart in finite-radius form: a common cardinal
amplification `K ≥ 1` forces the upper-minus-lower gap-height coordinate to
be at most `1 - K`. -/
theorem gapDifference_le_one_sub_of_adjacentCardinalAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) {K : ℝ}
    (hK : 1 ≤ K) (hamp : AdjacentCardinalAmplification nodes q K) :
    gapDifference nodes q ≤ 1 - K := by
  rcases hamp with ⟨y, hy, hdom⟩
  obtain ⟨x, hx, heq⟩ :=
    exists_height_eq_lebesgueFunction_mem_openGap nodes (by
      have := q.isLt
      omega) q.succ
  have hsum :
      K * lebesgueFunction nodes.toNodeFamily x ≤
        lebesgueFunction nodes.toNodeFamily y :=
    mul_le_lebesgueFunction_of_cardinal_domination nodes.toNodeFamily
      (hdom x hx)
  have hlower :
      lebesgueFunction nodes.toNodeFamily y ≤ nodes.height q.castSucc :=
    lebesgueFunction_le_height nodes q.castSucc hy
  have hupper : nodes.height q.succ = lebesgueFunction nodes.toNodeFamily x := by
    exact heq
  have hone : 1 ≤ nodes.height q.succ := one_le_height nodes q.succ
  unfold gapDifference
  rw [hupper] at hone ⊢
  nlinarith

/-- Fully explicit finite-radius gap-height estimate from the source product
argument. -/
theorem gapDifference_le_one_sub_boundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d)
    (hK : 1 ≤ boundaryAmplification nodes q) :
    gapDifference nodes q ≤ 1 - boundaryAmplification nodes q := by
  exact gapDifference_le_one_sub_of_adjacentCardinalAmplification nodes q hK
    (adjacentCardinalAmplification_boundaryAmplification nodes q)

/-- A sequence-level finite-radius form of the source boundary argument.
Once amplifications tend to infinity, the norm of the selected coordinate of
the gap-difference map tends to infinity. -/
theorem tendsto_norm_gapDifference_atTop_of_amplification
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hamp : ∀ m, AdjacentCardinalAmplification (nodes m) q (K m)) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hK.eventually (eventually_ge_atTop (max 1 (R + 1)))] with m hm
  have hKm : 1 ≤ K m := le_trans (le_max_left _ _) hm
  have hgap := gapDifference_le_one_sub_of_adjacentCardinalAmplification
    (nodes m) q hKm (hamp m)
  rw [Real.norm_eq_abs]
  have hneg : gapDifference (nodes m) q ≤ 0 := by linarith
  rw [abs_of_nonpos hneg]
  have hR : R + 1 ≤ K m := le_trans (le_max_right _ _) hm
  linarith

/-! ## The reflected, right-neighbor estimate -/

/-- Cardinal amplification when the lower gap collapses and the upper gap is
the surviving neighbor. -/
def RightAdjacentCardinalAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (K : ℝ) : Prop :=
  ∃ y ∈ closedGap nodes.toOrderedNodes q.succ,
    ∀ x ∈ openGap nodes.toOrderedNodes q.castSucc,
      ∀ k : Fin (d + 2),
        K * |lagrangeFundamental nodes.toNodeFamily k x| ≤
          |lagrangeFundamental nodes.toNodeFamily k y|

/-- Midpoint of the surviving upper neighbor. -/
def rightBoundaryMidpoint {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (nodes.point (gapLeftIndex q.succ) +
    nodes.point (gapRightIndex q.succ)) / 2

/-- Reflected amplification factor. -/
def rightBoundaryAmplification {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) : ℝ :=
  (endpointSpacing nodes q.succ /
      (2 * endpointSpacing nodes q.castSucc)) *
    (endpointSpacing nodes q.succ / (2 * (B - A))) ^ d

lemma rightBoundaryMidpoint_mem_upperGap {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) :
    rightBoundaryMidpoint nodes q ∈ closedGap nodes.toOrderedNodes q.succ := by
  have h := gap_left_lt_right nodes.toOrderedNodes q.succ
  constructor <;> unfold rightBoundaryMidpoint <;> linarith

lemma lowerGap_point_ne_node {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    x ≠ nodes.point j := by
  intro heq
  by_cases hj : j.val ≤ q.val
  · have hjleft : j ≤ gapLeftIndex q.castSucc := by
      change j.val ≤ q.val
      exact hj
    have := (nodes.strictMono.monotone hjleft).trans_lt hx.1
    rw [heq] at this
    exact (lt_irrefl _ this)
  · have hrightj : gapRightIndex q.castSucc ≤ j := by
      change q.val + 1 ≤ j.val
      omega
    have := hx.2.trans_le (nodes.strictMono.monotone hrightj)
    rw [heq] at this
    exact (lt_irrefl _ this)

lemma half_upperSpacing_le_rightMidpoint_distance {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) (j : Fin (d + 2)) :
    endpointSpacing nodes q.succ / 2 ≤
      |rightBoundaryMidpoint nodes q - nodes.point j| := by
  have hgap := gap_left_lt_right nodes.toOrderedNodes q.succ
  by_cases hj : j.val ≤ q.val + 1
  · have hjleft : j ≤ gapLeftIndex q.succ := by
      change j.val ≤ q.val + 1
      exact hj
    have hpoint := nodes.strictMono.monotone hjleft
    have hnonneg : 0 ≤ rightBoundaryMidpoint nodes q - nodes.point j := by
      unfold rightBoundaryMidpoint
      linarith
    rw [abs_of_nonneg hnonneg]
    unfold endpointSpacing rightBoundaryMidpoint
    linarith
  · have hrightj : gapRightIndex q.succ ≤ j := by
      change q.val + 2 ≤ j.val
      omega
    have hpoint := nodes.strictMono.monotone hrightj
    have hnonpos : rightBoundaryMidpoint nodes q - nodes.point j ≤ 0 := by
      unfold rightBoundaryMidpoint
      linarith
    rw [abs_of_nonpos hnonpos]
    unfold endpointSpacing rightBoundaryMidpoint
    linarith

lemma lowerGap_distance_le_intervalLength {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    |x - nodes.point j| ≤ B - A := by
  have hAj : A ≤ nodes.point j := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point j := nodes.strictMono.monotone (by
        simp [Fin.le_iff_val_le_val, endpointLeftIndex])
  have hjB : nodes.point j ≤ B := by
    calc
      nodes.point j ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          change j.val ≤ d + 1
          omega)
      _ = B := nodes.right_endpoint
  have hAx : A < x := by
    calc
      A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point (gapLeftIndex q.castSucc) :=
        nodes.strictMono.monotone (by simp [Fin.le_iff_val_le_val, endpointLeftIndex])
      _ < x := hx.1
  have hxB : x < B := by
    calc
      x < nodes.point (gapRightIndex q.castSucc) := hx.2
      _ ≤ nodes.point (endpointRightIndex d) :=
        nodes.strictMono.monotone (by
          simp [Fin.le_iff_val_le_val, endpointRightIndex])
      _ = B := nodes.right_endpoint
  rw [abs_le]
  constructor <;> linarith

lemma rightBoundary_base_le_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (j : Fin (d + 2)) :
    endpointSpacing nodes q.succ / (2 * (B - A)) ≤
      |(rightBoundaryMidpoint nodes q - nodes.point j) /
        (x - nodes.point j)| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact sub_pos.mpr nodes.endpoints_lt
  · exact abs_pos.mpr (sub_ne_zero.mpr (lowerGap_point_ne_node nodes q hx j))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q j
  · exact lowerGap_distance_le_intervalLength nodes q hx j

lemma rightBoundary_ratio_le_common_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) :
    endpointSpacing nodes q.succ /
        (2 * endpointSpacing nodes q.castSucc) ≤
      |(rightBoundaryMidpoint nodes q -
          nodes.point (gapRightIndex q.castSucc)) /
        (x - nodes.point (gapRightIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact endpointSpacing_pos nodes q.castSucc
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (lowerGap_point_ne_node nodes q hx (gapRightIndex q.castSucc)))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q
      (gapRightIndex q.castSucc)
  · rw [abs_of_neg (sub_neg.mpr hx.2)]
    unfold endpointSpacing
    linarith [hx.1]

lemma rightBoundary_ratio_le_lowerLeft_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) :
    endpointSpacing nodes q.succ /
        (2 * endpointSpacing nodes q.castSucc) ≤
      |(rightBoundaryMidpoint nodes q -
          nodes.point (gapLeftIndex q.castSucc)) /
        (x - nodes.point (gapLeftIndex q.castSucc))| := by
  rw [abs_div]
  apply half_div_le_div_of_bounds
  · exact (endpointSpacing_pos nodes q.succ).le
  · exact endpointSpacing_pos nodes q.castSucc
  · exact abs_pos.mpr (sub_ne_zero.mpr
      (lowerGap_point_ne_node nodes q hx (gapLeftIndex q.castSucc)))
  · exact half_upperSpacing_le_rightMidpoint_distance nodes q
      (gapLeftIndex q.castSucc)
  · rw [abs_of_pos (sub_pos.mpr hx.1)]
    unfold endpointSpacing
    linarith [hx.2]

lemma exists_rightBoundary_ratio_factor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (k : Fin (d + 2)) :
    ∃ r ∈ Finset.univ.erase k,
      endpointSpacing nodes q.succ /
          (2 * endpointSpacing nodes q.castSucc) ≤
        |(rightBoundaryMidpoint nodes q - nodes.point r) /
          (x - nodes.point r)| := by
  by_cases hk : gapRightIndex q.castSucc = k
  · refine ⟨gapLeftIndex q.castSucc, ?_,
      rightBoundary_ratio_le_lowerLeft_factor nodes q hx⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h
    apply (gapLeftIndex_lt_rightIndex (n := d + 2) q.castSucc).ne
    rw [h, hk]
  · exact ⟨gapRightIndex q.castSucc, by simp [hk],
      rightBoundary_ratio_le_common_factor nodes q hx⟩

lemma rightBoundaryAmplification_le_factorProduct {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (q : Fin d) {x : ℝ}
    (hx : x ∈ openGap nodes.toOrderedNodes q.castSucc) (k : Fin (d + 2)) :
    rightBoundaryAmplification nodes q ≤
      ∏ j ∈ Finset.univ.erase k,
        |(rightBoundaryMidpoint nodes q - nodes.point j) /
          (x - nodes.point j)| := by
  classical
  let s : Finset (Fin (d + 2)) := Finset.univ.erase k
  let f : Fin (d + 2) → ℝ := fun j ↦
    |(rightBoundaryMidpoint nodes q - nodes.point j) / (x - nodes.point j)|
  let c : ℝ := endpointSpacing nodes q.succ / (2 * (B - A))
  let R : ℝ := endpointSpacing nodes q.succ /
    (2 * endpointSpacing nodes q.castSucc)
  obtain ⟨r, hrs, hrR⟩ := exists_rightBoundary_ratio_factor nodes q hx k
  have hc : ∀ j ∈ s, c ≤ f j := by
    intro j _hj
    exact rightBoundary_base_le_factor nodes q hx j
  have hc0 : 0 ≤ c := by
    exact div_nonneg (endpointSpacing_pos nodes q.succ).le
      (mul_nonneg (by norm_num) (sub_pos.mpr nodes.endpoints_lt).le)
  have hpow : c ^ (s.erase r).card ≤ ∏ j ∈ s.erase r, f j := by
    have h := Finset.prod_le_prod (s := s.erase r)
      (f := fun _ ↦ c) (g := f)
      (fun _ _ ↦ hc0)
      (fun j hj ↦ hc j (Finset.mem_of_mem_erase hj))
    simpa using h
  have hcard : (s.erase r).card = d := by
    have hrs' : r ∈ s := hrs
    simp only [s, Finset.card_erase_of_mem hrs', Finset.card_erase_of_mem
      (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
    omega
  have hpow' : c ^ d ≤ ∏ j ∈ s.erase r, f j := by rwa [hcard] at hpow
  have hprod : R * c ^ d ≤ ∏ j ∈ s, f j := by
    calc
      R * c ^ d ≤ f r * c ^ d :=
        mul_le_mul_of_nonneg_right hrR (pow_nonneg hc0 d)
      _ ≤ f r * ∏ j ∈ s.erase r, f j :=
        mul_le_mul_of_nonneg_left hpow' (abs_nonneg _)
      _ = ∏ j ∈ s, f j := Finset.mul_prod_erase s f hrs
  simpa only [rightBoundaryAmplification, s, f, c, R] using hprod

theorem rightAdjacentCardinalAmplification_rightBoundaryAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) :
    RightAdjacentCardinalAmplification nodes q
      (rightBoundaryAmplification nodes q) := by
  refine ⟨rightBoundaryMidpoint nodes q, rightBoundaryMidpoint_mem_upperGap nodes q, ?_⟩
  intro x hx k
  have hxnodes : ∀ j : Fin (d + 2), j ≠ k → x ≠ nodes.point j := by
    intro j _hjk
    exact lowerGap_point_ne_node nodes q hx j
  have htransport := abs_lagrangeFundamental_eval_transport nodes.toNodeFamily k
    (x := x) (y := rightBoundaryMidpoint nodes q) hxnodes
  rw [htransport]
  have hprod := rightBoundaryAmplification_le_factorProduct nodes q hx k
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hprod
    (abs_nonneg (lagrangeFundamental nodes.toNodeFamily k x))

/-- Reflected finite-radius height separation. -/
theorem gapDifference_ge_sub_one_of_rightAdjacentCardinalAmplification
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (q : Fin d) {K : ℝ}
    (hK : 1 ≤ K) (hamp : RightAdjacentCardinalAmplification nodes q K) :
    K - 1 ≤ gapDifference nodes q := by
  rcases hamp with ⟨y, hy, hdom⟩
  obtain ⟨x, hx, heq⟩ :=
    exists_height_eq_lebesgueFunction_mem_openGap nodes (by
      have := q.isLt
      omega) q.castSucc
  have hsum : K * lebesgueFunction nodes.toNodeFamily x ≤
      lebesgueFunction nodes.toNodeFamily y :=
    mul_le_lebesgueFunction_of_cardinal_domination nodes.toNodeFamily (hdom x hx)
  have hupp : lebesgueFunction nodes.toNodeFamily y ≤ nodes.height q.succ :=
    lebesgueFunction_le_height nodes q.succ hy
  have hlower : nodes.height q.castSucc = lebesgueFunction nodes.toNodeFamily x := heq
  have hone : 1 ≤ nodes.height q.castSucc := one_le_height nodes q.castSucc
  unfold gapDifference
  rw [hlower] at hone ⊢
  nlinarith

theorem tendsto_rightBoundaryAmplification_atTop_of_lowerSpacing
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (hzero : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
      atTop (nhds 0))
    {delta : ℝ} (hdelta : 0 < delta)
    (hupper : ∀ᶠ m in atTop, delta ≤ endpointSpacing (nodes m) q.succ) :
    Tendsto (fun m ↦ rightBoundaryAmplification (nodes m) q) atTop atTop := by
  let C : ℝ := (delta / 2) * (delta / (2 * (B - A))) ^ d
  have hD : 0 < B - A := sub_pos.mpr (nodes 0).endpoints_lt
  have hC : 0 < C := by dsimp [C]; positivity
  have hpositive : ∀ᶠ m in atTop,
      endpointSpacing (nodes m) q.castSucc ∈ Set.Ioi (0 : ℝ) :=
    Eventually.of_forall fun m ↦ endpointSpacing_pos (nodes m) q.castSucc
  have hGT : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
      atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpositive⟩
  have hinv : Tendsto (fun m ↦ (endpointSpacing (nodes m) q.castSucc)⁻¹)
      atTop atTop := hGT.inv_tendsto_nhdsGT_zero
  have hCinv : Tendsto
      (fun m ↦ C * (endpointSpacing (nodes m) q.castSucc)⁻¹) atTop atTop :=
    hinv.const_mul_atTop hC
  apply tendsto_atTop_mono' atTop _ hCinv
  filter_upwards [hupper] with m hm
  have hLowerPos : 0 < endpointSpacing (nodes m) q.castSucc :=
    endpointSpacing_pos (nodes m) q.castSucc
  have hUpperPos : 0 < endpointSpacing (nodes m) q.succ :=
    endpointSpacing_pos (nodes m) q.succ
  have hbase : delta / (2 * (B - A)) ≤
      endpointSpacing (nodes m) q.succ / (2 * (B - A)) := by
    exact div_le_div_of_nonneg_right hm (mul_nonneg (by norm_num) hD.le)
  have hpow : (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
    exact pow_le_pow_left₀ (by positivity) hbase d
  have hhalf : delta / 2 ≤ endpointSpacing (nodes m) q.succ / 2 := by linarith
  have hinner : (delta / 2) * (delta / (2 * (B - A))) ^ d ≤
      (endpointSpacing (nodes m) q.succ / 2) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
    exact mul_le_mul hhalf hpow (by positivity) (by positivity)
  dsimp only [C]
  rw [rightBoundaryAmplification, div_eq_mul_inv]
  calc
    (delta / 2 * (delta / (2 * (B - A))) ^ d) *
        (endpointSpacing (nodes m) q.castSucc)⁻¹ ≤
      ((endpointSpacing (nodes m) q.succ / 2) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d) *
          (endpointSpacing (nodes m) q.castSucc)⁻¹ :=
      mul_le_mul_of_nonneg_right hinner (inv_nonneg.mpr hLowerPos.le)
    _ = (endpointSpacing (nodes m) q.succ *
          (2 * endpointSpacing (nodes m) q.castSucc)⁻¹) *
        (endpointSpacing (nodes m) q.succ / (2 * (B - A))) ^ d := by
      field_simp

theorem tendsto_norm_gapDifference_atTop_of_rightAmplification
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) (q : Fin d)
    (K : ℕ → ℝ) (hK : Tendsto K atTop atTop)
    (hamp : ∀ m, RightAdjacentCardinalAmplification (nodes m) q (K m)) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  refine tendsto_atTop.2 fun R ↦ ?_
  filter_upwards [hK.eventually (eventually_ge_atTop (max 1 (R + 1)))] with m hm
  have hKm : 1 ≤ K m := le_trans (le_max_left _ _) hm
  have hgap := gapDifference_ge_sub_one_of_rightAdjacentCardinalAmplification
    (nodes m) q hKm (hamp m)
  rw [Real.norm_eq_abs]
  have hpos : 0 ≤ gapDifference (nodes m) q := by linarith
  rw [abs_of_nonneg hpos]
  have hR : R + 1 ≤ K m := le_trans (le_max_right _ _) hm
  linarith

/-! ## Boundary/properness interfaces -/

/-- Sequential escape when an upper gap collapses while its immediate lower
neighbor remains nondegenerate. -/
def LeftNeighborBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ (nodes : ℕ → EndpointArray d A B) (q : Fin d),
    Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ) atTop (nhds 0) →
    (∃ δ > 0, ∀ᶠ m in atTop, δ ≤ endpointSpacing (nodes m) q.castSucc) →
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop

/-- Reflected sequential escape: the lower gap collapses while its immediate
upper neighbor remains nondegenerate.  This is deliberately a proposition,
not an asserted theorem; it is the exact remaining mirror estimate. -/
def RightNeighborBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ (nodes : ℕ → EndpointArray d A B) (q : Fin d),
    Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc) atTop (nhds 0) →
    (∃ δ > 0, ∀ᶠ m in atTop, δ ≤ endpointSpacing (nodes m) q.succ) →
    Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop

/-- The adjacent-pair boundary kernel required before the finite-dimensional
compactness/pigeonhole reduction to global properness. -/
def AdjacentBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  LeftNeighborBoundaryEscapeStatement d A B ∧
    RightNeighborBoundaryEscapeStatement d A B

/-- The left-neighbor boundary escape statement is completely discharged by
the explicit product estimate.  This includes collapse of the right endpoint
gap; the reflected right-neighbor case is the remaining ingredient for an
all-faces properness theorem. -/
theorem boundaryEscape_leftNeighbor (d : ℕ) (A B : ℝ) :
    LeftNeighborBoundaryEscapeStatement d A B := by
  intro nodes q hzero hdelta
  rcases hdelta with ⟨delta, hdelta, hlower⟩
  have hK := tendsto_boundaryAmplification_atTop_of_upperSpacing
    nodes q hzero hdelta hlower
  exact tendsto_norm_gapDifference_atTop_of_amplification nodes q
    (fun m ↦ boundaryAmplification (nodes m) q) hK
    (fun m ↦ adjacentCardinalAmplification_boundaryAmplification (nodes m) q)

/-- Reflected right-neighbor escape, proved by transporting every cardinal
function from the collapsing lower gap to the midpoint of the surviving upper
gap. -/
theorem boundaryEscape_rightNeighbor (d : ℕ) (A B : ℝ) :
    RightNeighborBoundaryEscapeStatement d A B := by
  intro nodes q hzero hdelta
  rcases hdelta with ⟨delta, hdelta, hupper⟩
  have hK := tendsto_rightBoundaryAmplification_atTop_of_lowerSpacing
    nodes q hzero hdelta hupper
  exact tendsto_norm_gapDifference_atTop_of_rightAmplification nodes q
    (fun m ↦ rightBoundaryAmplification (nodes m) q) hK
    (fun m ↦ rightAdjacentCardinalAmplification_rightBoundaryAmplification
      (nodes m) q)

/-- Both orientations of the adjacent boundary kernel. -/
theorem adjacentBoundaryEscape (d : ℕ) (A B : ℝ) :
    AdjacentBoundaryEscapeStatement d A B :=
  ⟨boundaryEscape_leftNeighbor d A B, boundaryEscape_rightNeighbor d A B⟩

/-! ## Selection from a limiting boundary spacing profile -/

/-- A nonnegative finite chain containing both a zero and a positive entry
has an adjacent zero/positive transition. -/
lemma exists_adjacent_zero_positive {d : ℕ} (s : Fin (d + 1) → ℝ)
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    ∃ q : Fin d,
      (0 < s q.castSucc ∧ s q.succ = 0) ∨
        (s q.castSucc = 0 ∧ 0 < s q.succ) := by
  induction d with
  | zero =>
      obtain ⟨z, hz⟩ := hzero
      obtain ⟨p, hp⟩ := hpos
      have hz0 : z = 0 := Fin.eq_zero z
      have hp0 : p = 0 := Fin.eq_zero p
      rw [hz0] at hz
      rw [hp0, hz] at hp
      exact (lt_irrefl 0 hp).elim
  | succ d ih =>
      let tail : Fin (d + 1) → ℝ := fun i ↦ s i.succ
      by_cases h0 : s 0 = 0
      · by_cases h1 : s (Fin.succ 0) = 0
        · have htailZero : ∃ g, tail g = 0 := ⟨0, h1⟩
          obtain ⟨p, hp⟩ := hpos
          have hp0 : p ≠ 0 := by
            intro hpzero
            subst p
            rw [h0] at hp
            exact (lt_irrefl 0 hp)
          obtain ⟨p', rfl⟩ := Fin.exists_succ_eq.mpr hp0
          have htailPos : ∃ g, 0 < tail g := ⟨p', hp⟩
          obtain ⟨q, hq⟩ := ih tail (fun g ↦ hs g.succ) htailZero htailPos
          refine ⟨q.succ, ?_⟩
          simpa [tail] using hq
        · refine ⟨0, Or.inr ⟨h0, ?_⟩⟩
          exact lt_of_le_of_ne (hs (Fin.succ 0)) (Ne.symm h1)
      · have h0pos : 0 < s 0 := lt_of_le_of_ne (hs 0) (Ne.symm h0)
        by_cases h1 : s (Fin.succ 0) = 0
        · exact ⟨0, Or.inl ⟨h0pos, h1⟩⟩
        · have htailPos : ∃ g, 0 < tail g :=
            ⟨0, lt_of_le_of_ne (hs (Fin.succ 0)) (Ne.symm h1)⟩
          obtain ⟨z, hz⟩ := hzero
          have hz0 : z ≠ 0 := by
            intro hzzero
            subst z
            exact h0 hz
          obtain ⟨z', rfl⟩ := Fin.exists_succ_eq.mpr hz0
          have htailZero : ∃ g, tail g = 0 := ⟨z', hz⟩
          obtain ⟨q, hq⟩ := ih tail (fun g ↦ hs g.succ) htailZero htailPos
          refine ⟨q.succ, ?_⟩
          simpa [tail] using hq

/-- Coordinatewise convergence of the positive spacing vectors to a genuine
boundary profile forces one fixed adjacent coordinate of `gapDifference` to
escape.  This is a whole-sequence result because the boundary profile itself
is assumed to be the whole-sequence limit. -/
theorem exists_coordinate_escape_of_boundarySpacingProfile
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (s : Fin (d + 1) → ℝ)
    (hconv : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes m) g) atTop (nhds (s g)))
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    ∃ q : Fin d,
      Tendsto (fun m ↦ ‖gapDifference (nodes m) q‖) atTop atTop := by
  obtain ⟨q, hq⟩ := exists_adjacent_zero_positive s hs hzero hpos
  refine ⟨q, ?_⟩
  rcases hq with hleft | hright
  · have hzero' : Tendsto (fun m ↦ endpointSpacing (nodes m) q.succ)
        atTop (nhds 0) := by simpa [hleft.2] using hconv q.succ
    have hevent : ∀ᶠ m in atTop,
        s q.castSucc / 2 ≤ endpointSpacing (nodes m) q.castSucc :=
      ((hconv q.castSucc).eventually_const_lt (half_lt_self hleft.1)).mono
        fun _ h ↦ h.le
    exact boundaryEscape_leftNeighbor d A B nodes q hzero'
      ⟨s q.castSucc / 2, half_pos hleft.1, hevent⟩
  · have hzero' : Tendsto (fun m ↦ endpointSpacing (nodes m) q.castSucc)
        atTop (nhds 0) := by simpa [hright.1] using hconv q.castSucc
    have hevent : ∀ᶠ m in atTop,
        s q.succ / 2 ≤ endpointSpacing (nodes m) q.succ :=
      ((hconv q.succ).eventually_const_lt (half_lt_self hright.2)).mono
        fun _ h ↦ h.le
    exact boundaryEscape_rightNeighbor d A B nodes q hzero'
      ⟨s q.succ / 2, half_pos hright.2, hevent⟩

/-- The norm of the full finite gap-difference vector escapes whenever one
fixed coordinate does. -/
theorem tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (s : Fin (d + 1) → ℝ)
    (hconv : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes m) g) atTop (nhds (s g)))
    (hs : ∀ g, 0 ≤ s g) (hzero : ∃ g, s g = 0) (hpos : ∃ g, 0 < s g) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop := by
  obtain ⟨q, hq⟩ := exists_coordinate_escape_of_boundarySpacingProfile
    nodes s hconv hs hzero hpos
  exact tendsto_atTop_mono
    (fun m ↦ norm_le_pi_norm (gapDifference (nodes m)) q) hq

/-- Exact subsequential boundary-escape interface.  It is intentionally
weaker than whole-sequence sequential properness: an arbitrary sequence may
have several boundary cluster profiles and require passage to a subsequence. -/
def SubsequenceBoundaryEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ nodes : ℕ → EndpointArray d A B,
    ∀ φ : ℕ → ℕ, StrictMono φ →
    ∀ s : Fin (d + 1) → ℝ,
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) →
      (∀ g, 0 ≤ s g) → (∃ g, s g = 0) → (∃ g, 0 < s g) →
      Tendsto (fun m ↦ ‖gapDifference (nodes (φ m))‖) atTop atTop

theorem subsequenceBoundaryEscape (d : ℕ) (A B : ℝ) :
    SubsequenceBoundaryEscapeStatement d A B := by
  intro nodes φ _hφ s hconv hs hzero hpos
  exact tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
    (fun m ↦ nodes (φ m)) s hconv hs hzero hpos

/-! ## Compact spacing extraction and the precise sequential residue -/

/-- Closed coordinate box containing every spacing vector. -/
def closedSpacingBox (d : ℕ) (A B : ℝ) : Set (Fin (d + 1) → ℝ) :=
  Set.univ.pi fun _ ↦ Set.Icc 0 (B - A)

lemma isCompact_closedSpacingBox (d : ℕ) (A B : ℝ) :
    IsCompact (closedSpacingBox d A B) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

lemma endpointSpacing_mem_closedSpacingBox {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    endpointSpacing nodes ∈ closedSpacingBox d A B := by
  intro g _hg
  constructor
  · exact (endpointSpacing_pos nodes g).le
  · calc
      endpointSpacing nodes g ≤ ∑ i, endpointSpacing nodes i :=
        Finset.single_le_sum
          (fun i _ ↦ (endpointSpacing_pos nodes i).le) (Finset.mem_univ g)
      _ = B - A := sum_endpointSpacing nodes

/-- Every endpoint-array sequence has a subsequence whose complete spacing
vector converges in the closed simplex. -/
theorem exists_convergent_spacing_subsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B) :
    ∃ (s : Fin (d + 1) → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) ∧
      (∀ g, 0 ≤ s g) ∧
      ∑ g, s g = B - A := by
  obtain ⟨s, hsbox, φ, hφ, hlim⟩ :=
    (isCompact_closedSpacingBox d A B).tendsto_subseq
      (fun m ↦ endpointSpacing_mem_closedSpacingBox (nodes m))
  have hcoord : ∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
      atTop (nhds (s g)) := by
    intro g
    have h := (tendsto_pi_nhds.mp hlim) g
    simpa only [Function.comp_apply] using h
  have hsumlim : Tendsto
      (fun m ↦ ∑ g, endpointSpacing (nodes (φ m)) g)
      atTop (nhds (∑ g, s g)) :=
    tendsto_finset_sum Finset.univ fun g _ ↦ hcoord g
  have hsumlim' : Tendsto (fun _ : ℕ ↦ B - A)
      atTop (nhds (∑ g, s g)) := by
    simpa only [sum_endpointSpacing] using hsumlim
  have hsum : ∑ g, s g = B - A :=
    tendsto_nhds_unique hsumlim' tendsto_const_nhds
  exact ⟨s, φ, hφ, hcoord, fun g ↦ (hsbox g (Set.mem_univ g)).1, hsum⟩

/-- A sequence has no convergent subsequence in the open endpoint-array
space.  This is a sequential escape hypothesis, not yet a topological
properness assertion. -/
def HasNoConvergentEndpointSubsequence {d : ℕ} {A B : ℝ}
    (nodes : ℕ → EndpointArray d A B) : Prop :=
  ∀ (φ : ℕ → ℕ), StrictMono φ → ∀ limit : EndpointArray d A B,
    ¬ Tendsto (fun m ↦ nodes (φ m)) atTop (nhds limit)

/-- Under sequential escape from the open simplex, compact spacing
extraction necessarily lands on its boundary.  If every limiting spacing
were positive, the committed spacing homeomorphism would reconstruct a
convergent endpoint-array subsequence. -/
theorem exists_boundary_spacing_subsequence_of_noConvergentEndpointSubsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    ∃ (s : Fin (d + 1) → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ g, Tendsto (fun m ↦ endpointSpacing (nodes (φ m)) g)
        atTop (nhds (s g))) ∧
      (∀ g, 0 ≤ s g) ∧ (∃ g, s g = 0) ∧ (∃ g, 0 < s g) := by
  obtain ⟨s, φ, hφ, hconv, hs, hsum⟩ := exists_convergent_spacing_subsequence nodes
  have hzero : ∃ g, s g = 0 := by
    by_contra h
    push_neg at h
    have hspos : ∀ g, 0 < s g := fun g ↦ lt_of_le_of_ne (hs g) (Ne.symm (h g))
    let σ : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} :=
      ⟨s, hspos, hsum⟩
    have hsub : Tendsto
        (fun m ↦ ⟨endpointSpacing (nodes (φ m)),
          endpointSpacing_mem_positiveSpacingSimplex (nodes (φ m))⟩)
        atTop (nhds σ) := by
      apply tendsto_subtype_rng.mpr
      exact tendsto_pi_nhds.mpr hconv
    have hAB : AdmissibleInterval A B := (nodes 0).admissibleInterval
    have hnodes :=
      ((endpointArraySpacingHomeomorph hAB).continuous_invFun.tendsto σ).comp hsub
    have hnodes' : Tendsto (fun m ↦ nodes (φ m)) atTop
        (nhds (endpointArrayOfSpacings hAB σ)) := by
      change Tendsto
        (fun m ↦ endpointArrayOfSpacings hAB
          ⟨endpointSpacing (nodes (φ m)),
            endpointSpacing_mem_positiveSpacingSimplex (nodes (φ m))⟩)
        atTop (nhds (endpointArrayOfSpacings hAB σ)) at hnodes
      simpa only [endpointArrayOfSpacings_endpointSpacing] using hnodes
    exact hno φ hφ (endpointArrayOfSpacings hAB σ) hnodes'
  have hpos : ∃ g, 0 < s g := by
    have hp := (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (fun g _ ↦ hs g)).mp (by
        rw [hsum]
        exact sub_pos.mpr (nodes 0).endpoints_lt)
    obtain ⟨g, _hgmem, hg⟩ := hp
    exact ⟨g, hg⟩
  exact ⟨s, φ, hφ, hconv, hs, hzero, hpos⟩

/-- What the compactness reduction proves without any further uniformity
argument: every endpoint-array sequence with no convergent open-simplex
subsequence has a subsequence along which the full gap-difference norm tends
to infinity. -/
theorem exists_subsequence_tendsto_norm_gapDifference_atTop
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun m ↦ ‖gapDifference (nodes (φ m))‖) atTop atTop := by
  obtain ⟨s, φ, hφ, hconv, hs, hzero, hpos⟩ :=
    exists_boundary_spacing_subsequence_of_noConvergentEndpointSubsequence nodes hno
  exact ⟨φ, hφ,
    tendsto_norm_gapDifference_atTop_of_boundarySpacingProfile
      (fun m ↦ nodes (φ m)) s hconv hs hzero hpos⟩

/-- Sequential properness kernel: if a sequence has no convergent subsequence
in the open endpoint-array simplex, then the norm of its full gap-difference
vector tends to infinity along the whole sequence.  The proof upgrades the
subsequential boundary result by applying it to any hypothetical frequently
bounded subsequence. -/
theorem tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence
    {d : ℕ} {A B : ℝ} (nodes : ℕ → EndpointArray d A B)
    (hno : HasNoConvergentEndpointSubsequence nodes) :
    Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop := by
  rw [tendsto_atTop]
  intro R
  by_contra hR
  have hfreq : ∃ᶠ m in atTop, ¬ R ≤ ‖gapDifference (nodes m)‖ := by
    exact Filter.not_eventually.mp hR
  obtain ⟨φ, hφ, hbound⟩ := Filter.extraction_of_frequently_atTop hfreq
  have hnoφ : HasNoConvergentEndpointSubsequence (fun m ↦ nodes (φ m)) := by
    intro ψ hψ limit hlim
    apply hno (φ ∘ ψ) (hφ.comp hψ) limit
    simpa only [Function.comp_apply] using hlim
  obtain ⟨ψ, _hψ, hescape⟩ :=
    exists_subsequence_tendsto_norm_gapDifference_atTop
      (fun m ↦ nodes (φ m)) hnoφ
  have hevent := hescape.eventually_ge_atTop R
  obtain ⟨m, hm⟩ := hevent.exists
  exact hbound (ψ m) hm

/-- The sequential escape result proved in this file, packaged separately
from topological properness. -/
def GapDifferenceSequentialEscapeStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ nodes : ℕ → EndpointArray d A B,
    HasNoConvergentEndpointSubsequence nodes →
      Tendsto (fun m ↦ ‖gapDifference (nodes m)‖) atTop atTop

theorem gapDifference_sequentialEscape (d : ℕ) (A B : ℝ) :
    GapDifferenceSequentialEscapeStatement d A B :=
  fun nodes ↦ tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence nodes

/-- The genuine topological properness target.  It is kept as a proposition:
upgrading the checked sequential escape theorem to `IsProperMap` additionally
requires the continuity of the gap-height map and the appropriate
metrizable/locally compact properness bridge. -/
def GapDifferenceTopologicalPropernessStatement (d : ℕ) (A B : ℝ) : Prop :=
  IsProperMap (gapDifference : EndpointArray d A B → Fin d → ℝ)

end

end Randy1153.DeBoorPinkus
