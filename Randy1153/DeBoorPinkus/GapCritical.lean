import Randy1153.GapPolynomial
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Attained gap maxima and interior critical points

The compact maximum supplied by `gapHeight` is made into a named point here.
For at least three nodes, the strict interior inequality for the signed gap
polynomial forces every such chosen maximum away from the two endpoints.
Fermat's theorem then makes it a genuine derivative root.

For `n ≥ 4`, a private root in each other gap factors the polynomial into
real linear factors, with at most one final linear quotient.  Its logarithmic
derivative is therefore strictly decreasing on the root-free owning gap.
This proves the required uniqueness without assuming the downstream
cross-interlacing target.  The two-node case remains explicitly exceptional:
there the only gap polynomial is identically one, so every point is critical.
-/

namespace Randy1153.DeBoorPinkus

open Polynomial
open scoped Topology

noncomputable section

/-- A compact maximizer of the signed polynomial on its own closed gap. -/
def gapArgmax {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  Classical.choose (exists_gapHeight_eq_eval_gapPolynomial nodes g)

/-- Being a global maximizer of the signed polynomial on its own closed
nodal gap. -/
def IsGapMaximizer {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1))
    (r : ℝ) : Prop :=
  r ∈ closedGap nodes g ∧ ∀ u ∈ closedGap nodes g,
    (gapPolynomial nodes g).eval u ≤ (gapPolynomial nodes g).eval r

lemma gapArgmax_mem_closedGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ closedGap nodes g :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).1

lemma gapHeight_eq_eval_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    gapHeight nodes g = (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).2.1

lemma gapPolynomial_eval_le_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) {t : ℝ} (ht : t ∈ closedGap nodes g) :
    (gapPolynomial nodes g).eval t ≤
      (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
  (Classical.choose_spec (exists_gapHeight_eq_eval_gapPolynomial nodes g)).2.2 t ht

lemma isGapMaximizer_gapArgmax {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    IsGapMaximizer nodes g (gapArgmax nodes g) :=
  ⟨gapArgmax_mem_closedGap nodes g, fun _ ht =>
    gapPolynomial_eval_le_gapArgmax nodes g ht⟩

/-- For at least three nodes, the compact maximum lies strictly inside its
gap.  The cardinality hypothesis is sharp; see
`gapPolynomial_eq_one_of_two_nodes`. -/
lemma gapArgmax_mem_openGap {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n)
    (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ openGap nodes g := by
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  have htgt : 1 < (gapPolynomial nodes g).eval t :=
    one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht
  have hmaxgt : 1 < (gapPolynomial nodes g).eval (gapArgmax nodes g) :=
    htgt.trans_le (gapPolynomial_eval_le_gapArgmax nodes g ⟨ht.1.le, ht.2.le⟩)
  have hclosed := gapArgmax_mem_closedGap nodes g
  refine ⟨lt_of_le_of_ne hclosed.1 ?_, lt_of_le_of_ne hclosed.2 ?_⟩
  · intro heq
    rw [← heq, gapPolynomial_eval_left] at hmaxgt
    exact (lt_irrefl 1) hmaxgt
  · intro heq
    rw [heq, gapPolynomial_eval_right] at hmaxgt
    exact (lt_irrefl 1) hmaxgt

/-- Every chosen gap maximum is a derivative root once the gap has a genuine
interior maximum. -/
lemma gapPolynomial_derivative_eval_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.eval (gapArgmax nodes g) = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  have hopen := gapArgmax_mem_openGap nodes hn g
  have hmaxOn : IsMaxOn (fun t : ℝ => p.eval t) (closedGap nodes g)
      (gapArgmax nodes g) := by
    intro t ht
    exact gapPolynomial_eval_le_gapArgmax nodes g ht
  have hlocal : IsLocalMax (fun t : ℝ => p.eval t) (gapArgmax nodes g) :=
    hmaxOn.isLocalMax (Icc_mem_nhds hopen.1 hopen.2)
  simpa only [p] using hlocal.hasDerivAt_eq_zero (p.hasDerivAt (gapArgmax nodes g))

lemma one_lt_gapHeight {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n)
    (g : Fin (n - 1)) :
    1 < gapHeight nodes g := by
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  rw [gapHeight_eq_eval_gapArgmax]
  exact (one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht).trans_le
    (gapPolynomial_eval_le_gapArgmax nodes g ⟨ht.1.le, ht.2.le⟩)

/-- In every nondegenerate (`n ≥ 3`) case the derivative polynomial itself
is nonzero.  This keeps membership in its finite real-root multiset honest. -/
lemma gapPolynomial_derivative_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative ≠ 0 := by
  intro hderiv
  obtain ⟨t, ht⟩ := openGap_nonempty nodes g
  have htgt := one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g ht
  have hconst := Polynomial.eq_C_of_derivative_eq_zero hderiv
  have heq := congrArg (Polynomial.eval t) hconst
  have heqLeft := congrArg
    (Polynomial.eval (nodes.point (gapLeftIndex g))) hconst
  simp only [Polynomial.eval_C] at heq heqLeft
  rw [gapPolynomial_eval_left] at heqLeft
  linarith

lemma gapArgmax_mem_derivative_roots {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) (g : Fin (n - 1)) :
    gapArgmax nodes g ∈ (gapPolynomial nodes g).derivative.roots := by
  rw [Polynomial.mem_roots (gapPolynomial_derivative_ne_zero nodes hn g)]
  exact gapPolynomial_derivative_eval_gapArgmax nodes hn g

/-! ### Real splitting and strict logarithmic concavity

This section is deliberately upstream of `Interlacing.lean`: that module
imports this one.  We therefore use private chosen roots in the other gaps,
rather than importing or assuming the later public root-placement API.
-/

private lemma gapPolynomial_ne_zero_critical {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapPolynomial nodes g ≠ 0 := by
  intro hzero
  have h := gapPolynomial_eval_left nodes g
  rw [hzero, Polynomial.eval_zero] at h
  norm_num at h

private abbrev CriticalOtherGapIndex {n : ℕ} (g : Fin (n - 1)) :=
  {h : Fin (n - 1) // h ≠ g}

@[simp]
private lemma card_criticalOtherGapIndex {n : ℕ} (g : Fin (n - 1)) :
    Fintype.card (CriticalOtherGapIndex g) = n - 2 := by
  classical
  change Fintype.card {h : Fin (n - 1) // ¬h = g} = n - 2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega

private theorem exists_criticalOtherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    ∃ r ∈ openGap nodes h, (gapPolynomial nodes g).eval r = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  let a : ℝ := nodes.point (gapLeftIndex h)
  let b : ℝ := nodes.point (gapRightIndex h)
  have hab : a ≤ b := (gap_left_lt_right nodes h).le
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuous.continuousOn
  have ha : p.eval a = gapCoefficient g (gapLeftIndex h) := by
    exact gapPolynomial_eval_node nodes g (gapLeftIndex h)
  have hb : p.eval b = -gapCoefficient g (gapLeftIndex h) := by
    simp only [p, b]
    rw [gapPolynomial_eval_node, gapCoefficient_right_eq_neg_left_of_ne g h hhg]
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex h) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz

private def criticalOtherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : CriticalOtherGapIndex g) : ℝ :=
  Classical.choose (exists_criticalOtherGapRoot nodes g h.1 h.property)

private lemma criticalOtherGapRoot_mem_openGap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : CriticalOtherGapIndex g) :
    criticalOtherGapRoot nodes g h ∈ openGap nodes h.1 :=
  (Classical.choose_spec
    (exists_criticalOtherGapRoot nodes g h.1 h.property)).1

private lemma gapPolynomial_eval_criticalOtherGapRoot {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : CriticalOtherGapIndex g) :
    (gapPolynomial nodes g).eval (criticalOtherGapRoot nodes g h) = 0 :=
  (Classical.choose_spec
    (exists_criticalOtherGapRoot nodes g h.1 h.property)).2

private lemma criticalOtherGapRoot_strictMono {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    StrictMono (criticalOtherGapRoot nodes g) := by
  intro h k hhk
  have hindex : gapRightIndex h.1 ≤ gapLeftIndex k.1 := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [gapRightIndex_val, gapLeftIndex_val]
    have hval : h.1.val < k.1.val := hhk
    omega
  calc
    criticalOtherGapRoot nodes g h < nodes.point (gapRightIndex h.1) :=
      (criticalOtherGapRoot_mem_openGap nodes g h).2
    _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
    _ < criticalOtherGapRoot nodes g k :=
      (criticalOtherGapRoot_mem_openGap nodes g k).1

/-- Every gap polynomial splits over `ℝ`.  The proof uses one root in each
other nodal gap; after their product is divided out, the interpolation degree
budget leaves a quotient of degree at most one. -/
theorem gapPolynomial_splits {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : (gapPolynomial nodes g).Splits := by
  classical
  let p : ℝ[X] := gapPolynomial nodes g
  let root : CriticalOtherGapIndex g → ℝ := criticalOtherGapRoot nodes g
  let D : ℝ[X] := ∏ h : CriticalOtherGapIndex g, (X - C (root h))
  have hrootInjective : Function.Injective root :=
    (criticalOtherGapRoot_strictMono nodes g).injective
  have hDvd : D ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro h
      rw [Polynomial.dvd_iff_isRoot]
      exact gapPolynomial_eval_criticalOtherGapRoot nodes g h
  obtain ⟨q, hq⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).Monic
    exact monic_prod_of_monic _ _ fun h _hh => monic_X_sub_C (root h)
  have hDsplits : D.Splits := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).Splits
    exact Polynomial.Splits.prod fun h _hh => Polynomial.Splits.X_sub_C (root h)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hp : p ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hqne : q ≠ 0 := by
    intro hzero
    apply hp
    rw [hzero, mul_zero] at hq
    exact hq
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ h ∈ (Finset.univ : Finset (CriticalOtherGapIndex g)),
      (X - C (root h))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_criticalOtherGapIndex]
  have hpdegree : p.natDegree ≤ n - 1 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  have hqdegree : q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hDne hqne, hDdegree] at hnat
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  change p.Splits
  rw [hq]
  exact hDsplits.mul (Polynomial.Splits.of_natDegree_le_one hqdegree)

private lemma gapPolynomial_root_not_mem_closedGap {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hr : r ∈ (gapPolynomial nodes g).roots) :
    r ∉ closedGap nodes g := by
  intro hrclosed
  have hroot : (gapPolynomial nodes g).eval r = 0 := by
    rw [← Polynomial.IsRoot]
    exact (Polynomial.mem_roots (gapPolynomial_ne_zero_critical nodes g)).mp hr
  by_cases hleft : r = nodes.point (gapLeftIndex g)
  · rw [hleft, gapPolynomial_eval_left] at hroot
    norm_num at hroot
  by_cases hright : r = nodes.point (gapRightIndex g)
  · rw [hright, gapPolynomial_eval_right] at hroot
    norm_num at hroot
  have hopen : r ∈ openGap nodes g :=
    ⟨lt_of_le_of_ne hrclosed.1 (Ne.symm hleft),
      lt_of_le_of_ne hrclosed.2 hright⟩
  have hpos := one_lt_eval_gapPolynomial_of_mem_openGap nodes hn g hopen
  linarith

private lemma reciprocal_sub_strictAnti {a b x y r : ℝ}
    (hxy : x < y) (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hr : r < a ∨ b < r) :
    1 / (y - r) < 1 / (x - r) := by
  have hxr : x - r ≠ 0 := by
    rcases hr with hr | hr
    · exact ne_of_gt (sub_pos.mpr (hr.trans hx.1))
    · exact ne_of_lt (sub_neg.mpr (hx.2.trans hr))
  have hyr : y - r ≠ 0 := by
    rcases hr with hr | hr
    · exact ne_of_gt (sub_pos.mpr (hr.trans (hx.1.trans hxy)))
    · exact ne_of_lt (sub_neg.mpr (hy.2.trans hr))
  have hprod : 0 < (x - r) * (y - r) := by
    rcases hr with hr | hr
    · exact mul_pos (sub_pos.mpr (hr.trans hx.1))
        (sub_pos.mpr (hr.trans hy.1))
    · exact mul_pos_of_neg_of_neg (sub_neg.mpr (hx.2.trans hr))
        (sub_neg.mpr (hy.2.trans hr))
  rw [← sub_pos]
  rw [show 1 / (x - r) - 1 / (y - r) =
      (y - x) / ((x - r) * (y - r)) by field_simp; ring]
  exact div_pos (sub_pos.mpr hxy) hprod

private lemma hasDerivAt_reciprocal_sub (x r : ℝ) (hxr : x ≠ r) :
    HasDerivAt (fun y : ℝ => 1 / (y - r)) (-1 / (x - r) ^ 2) x := by
  have hne : x - r ≠ 0 := sub_ne_zero.mpr hxr
  simpa only [one_div, id_eq, sub_eq_add_neg, add_comm] using
    ((hasDerivAt_id x).sub_const r).inv hne

private lemma hasDerivAt_rootReciprocalSum (roots : Multiset ℝ) (x : ℝ)
    (hx : ∀ r ∈ roots, x ≠ r) :
    HasDerivAt
      (fun y : ℝ => (roots.map fun r => 1 / (y - r)).sum)
      ((roots.map fun r => -1 / (x - r) ^ 2).sum) x := by
  induction roots using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const x (0 : ℝ)
  | cons r roots ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (hasDerivAt_reciprocal_sub x r (hx r (by simp))).add
        (ih fun s hs => hx s (by simp [hs]))

/-- The logarithmic derivative `F'_g/F_g` is strictly decreasing throughout
the polynomial's own gap.  This is the root-budget form of the source's
critical-point argument. -/
theorem gapLogDerivative_strictAntiOn {n : ℕ} (nodes : OrderedNodes n)
    (hn : 4 ≤ n) (g : Fin (n - 1)) :
    StrictAntiOn
      (fun x => (gapPolynomial nodes g).derivative.eval x /
        (gapPolynomial nodes g).eval x)
      (openGap nodes g) := by
  intro x hx y hy hxy
  let p : ℝ[X] := gapPolynomial nodes g
  have hp : p ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hsplit : p.Splits := gapPolynomial_splits nodes g
  have hpx : p.eval x ≠ 0 := ne_of_gt
    (zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap nodes
      (by omega) g hx))
  have hpy : p.eval y ≠ 0 := ne_of_gt
    (zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap nodes
      (by omega) g hy))
  change p.derivative.eval y / p.eval y < p.derivative.eval x / p.eval x
  rw [hsplit.eval_derivative_div_eval_of_ne_zero hpx,
    hsplit.eval_derivative_div_eval_of_ne_zero hpy]
  apply Multiset.sum_lt_sum
  · intro r hr
    apply (reciprocal_sub_strictAnti hxy hx hy ?_).le
    have hrout := gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    simp only [closedGap, Set.mem_Icc, not_and_or, not_le] at hrout
    exact hrout
  · have hnat : p.natDegree ≠ 0 := by
      intro hzero
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hzero
      have hderiv : p.derivative = 0 := by rw [← hc]; simp
      exact (gapPolynomial_derivative_ne_zero nodes (by omega) g) hderiv
    obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero (hsplit.roots_ne_zero hnat)
    refine ⟨r, hr, reciprocal_sub_strictAnti hxy hx hy ?_⟩
    have hrout := gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    simp only [closedGap, Set.mem_Icc, not_and_or, not_le] at hrout
    exact hrout

/-- For `n ≥ 4`, every derivative zero in the polynomial's own open gap is
the chosen compact maximizer. -/
lemma eq_gapArgmax_of_derivative_eval_eq_zero {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hrgap : r ∈ openGap nodes g)
    (hr : (gapPolynomial nodes g).derivative.eval r = 0) :
    r = gapArgmax nodes g := by
  have harggap := gapArgmax_mem_openGap nodes (by omega) g
  have harg := gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hanti := gapLogDerivative_strictAntiOn nodes hn g
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict := hanti hrgap harggap hlt
    simp only [hr, harg, zero_div] at hstrict
    exact (lt_irrefl 0) hstrict
  · have hstrict := hanti harggap hrgap hgt
    simp only [hr, harg, zero_div] at hstrict
    exact (lt_irrefl 0) hstrict

/-- The source-critical-point statement for `n ≥ 4`: the derivative has
exactly one zero in its own gap, namely `gapArgmax`. -/
theorem existsUnique_gapPolynomial_derivative_root_in_gap {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    ∃! r : ℝ, r ∈ openGap nodes g ∧
      (gapPolynomial nodes g).derivative.eval r = 0 := by
  refine ⟨gapArgmax nodes g,
    ⟨gapArgmax_mem_openGap nodes (by omega) g,
      gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g⟩, ?_⟩
  intro r hr
  exact eq_gapArgmax_of_derivative_eval_eq_zero nodes hn g hr.1 hr.2

/-- Pointwise critical-root characterization on the owning open gap. -/
lemma derivative_eval_eq_zero_iff_eq_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hrgap : r ∈ openGap nodes g) :
    (gapPolynomial nodes g).derivative.eval r = 0 ↔
      r = gapArgmax nodes g := by
  constructor
  · exact eq_gapArgmax_of_derivative_eval_eq_zero nodes hn g hrgap
  · rintro rfl
    exact gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g

/-- Hence the compact maximizer on the gap is unique for `n ≥ 4`. -/
lemma isGapMaximizer_iff_eq_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) {r : ℝ} :
    IsGapMaximizer nodes g r ↔ r = gapArgmax nodes g := by
  constructor
  · intro hrmax
    obtain ⟨t, ht⟩ := openGap_nonempty nodes g
    have htgt := one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g ht
    have hrgt : 1 < (gapPolynomial nodes g).eval r :=
      htgt.trans_le (hrmax.2 t ⟨ht.1.le, ht.2.le⟩)
    have hropen : r ∈ openGap nodes g := by
      refine ⟨lt_of_le_of_ne hrmax.1.1 ?_, lt_of_le_of_ne hrmax.1.2 ?_⟩
      · intro heq
        rw [← heq, gapPolynomial_eval_left] at hrgt
        exact (lt_irrefl 1) hrgt
      · intro heq
        rw [heq, gapPolynomial_eval_right] at hrgt
        exact (lt_irrefl 1) hrgt
    have hlocal : IsLocalMax (fun x : ℝ => (gapPolynomial nodes g).eval x) r :=
      (show IsMaxOn (fun x : ℝ => (gapPolynomial nodes g).eval x)
          (closedGap nodes g) r from hrmax.2).isLocalMax
        (Icc_mem_nhds hropen.1 hropen.2)
    have hderiv : (gapPolynomial nodes g).derivative.eval r = 0 :=
      hlocal.hasDerivAt_eq_zero ((gapPolynomial nodes g).hasDerivAt r)
    exact eq_gapArgmax_of_derivative_eval_eq_zero nodes hn g hropen hderiv
  · rintro rfl
    exact isGapMaximizer_gapArgmax nodes g

lemma gapPolynomial_derivative_pos_of_lt_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {x : ℝ} (hx : x ∈ openGap nodes g) (hxt : x < gapArgmax nodes g) :
    0 < (gapPolynomial nodes g).derivative.eval x := by
  have hτgap := gapArgmax_mem_openGap nodes (by omega) g
  have hstrict := gapLogDerivative_strictAntiOn nodes hn g hx hτgap hxt
  change (gapPolynomial nodes g).derivative.eval (gapArgmax nodes g) /
      (gapPolynomial nodes g).eval (gapArgmax nodes g) <
    (gapPolynomial nodes g).derivative.eval x /
      (gapPolynomial nodes g).eval x at hstrict
  rw [gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g, zero_div] at hstrict
  have hden : 0 < (gapPolynomial nodes g).eval x := zero_lt_one.trans
    (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hx)
  rcases div_pos_iff.mp hstrict with hgood | hbad
  · exact hgood.1
  · exact (not_lt_of_ge hden.le hbad.2).elim

lemma gapPolynomial_derivative_neg_of_gapArgmax_lt {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {x : ℝ} (hx : x ∈ openGap nodes g) (htx : gapArgmax nodes g < x) :
    (gapPolynomial nodes g).derivative.eval x < 0 := by
  have hτgap := gapArgmax_mem_openGap nodes (by omega) g
  have hstrict := gapLogDerivative_strictAntiOn nodes hn g hτgap hx htx
  change (gapPolynomial nodes g).derivative.eval x /
      (gapPolynomial nodes g).eval x <
    (gapPolynomial nodes g).derivative.eval (gapArgmax nodes g) /
      (gapPolynomial nodes g).eval (gapArgmax nodes g) at hstrict
  rw [gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g, zero_div] at hstrict
  have hden : 0 < (gapPolynomial nodes g).eval x := zero_lt_one.trans
    (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hx)
  rcases div_neg_iff.mp hstrict with hbad | hgood
  · exact (not_lt_of_ge hden.le hbad.2).elim
  · exact hgood.1

/-- Strict logarithmic concavity makes the critical point nondegenerate:
`F''_g(τ_g) < 0`.  This is stronger than uniqueness as a set-theoretic root
and is what makes division by `(X-τ_g)` retain a nonzero value at `τ_g`. -/
lemma gapPolynomial_secondDerivative_eval_gapArgmax_neg {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.derivative.eval (gapArgmax nodes g) < 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  let τ : ℝ := gapArgmax nodes g
  have hτgap : τ ∈ openGap nodes g := gapArgmax_mem_openGap nodes (by omega) g
  have hpτpos : 0 < p.eval τ := zero_lt_one.trans
    (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hτgap)
  have hpτ : p.eval τ ≠ 0 := hpτpos.ne'
  have hcrit : p.derivative.eval τ = 0 := by
    exact gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hsplit : p.Splits := gapPolynomial_splits nodes g
  have hrootNe : ∀ r ∈ p.roots, τ ≠ r := by
    intro r hr heq
    apply gapPolynomial_root_not_mem_closedGap nodes (by omega) g hr
    rw [← heq]
    exact gapArgmax_mem_closedGap nodes g
  have hsumDeriv := hasDerivAt_rootReciprocalSum p.roots τ hrootNe
  have hevent :
      (fun x : ℝ => p.derivative.eval x / p.eval x) =ᶠ[𝓝 τ]
        (fun x : ℝ => (p.roots.map fun r => 1 / (x - r)).sum) := by
    filter_upwards [Ioo_mem_nhds hτgap.1 hτgap.2] with x hx
    exact hsplit.eval_derivative_div_eval_of_ne_zero
      (ne_of_gt (zero_lt_one.trans
        (one_lt_eval_gapPolynomial_of_mem_openGap nodes (by omega) g hx)))
  have hquotDeriv : HasDerivAt
      (fun x : ℝ => p.derivative.eval x / p.eval x)
      (p.derivative.derivative.eval τ / p.eval τ) τ := by
    have hraw := (p.derivative.hasDerivAt τ).div (p.hasDerivAt τ) hpτ
    apply hraw.congr_deriv
    rw [hcrit]
    field_simp
    ring
  have hcoeff :
      p.derivative.derivative.eval τ / p.eval τ =
        (p.roots.map fun r => -1 / (τ - r) ^ 2).sum :=
    hquotDeriv.unique (hsumDeriv.congr_of_eventuallyEq hevent)
  have hroots : p.roots ≠ 0 := by
    have hnat : p.natDegree ≠ 0 := by
      intro hzero
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hzero
      have hderiv : p.derivative = 0 := by rw [← hc]; simp
      exact (gapPolynomial_derivative_ne_zero nodes (by omega) g) hderiv
    exact hsplit.roots_ne_zero hnat
  have hterm (r : ℝ) (hr : r ∈ p.roots) : -1 / (τ - r) ^ 2 < 0 :=
    div_neg_of_neg_of_pos (by norm_num)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr (hrootNe r hr)))
  have hsumneg : (p.roots.map fun r => -1 / (τ - r) ^ 2).sum < 0 := by
    have hlt : (p.roots.map fun r => -1 / (τ - r) ^ 2).sum <
        (p.roots.map fun _r => (0 : ℝ)).sum := by
      apply Multiset.sum_lt_sum
      · intro r hr
        exact (hterm r hr).le
      · obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero hroots
        exact ⟨r, hr, hterm r hr⟩
    simpa using hlt
  have hratio : p.derivative.derivative.eval τ / p.eval τ < 0 := by
    rw [hcoeff]
    exact hsumneg
  rcases (div_neg_iff.mp hratio) with hbad | hneg
  · exact (not_lt_of_ge hpτpos.le hbad.2).elim
  · exact hneg.1

/-- Quotient of `F'_g` by the unique critical factor `(X - τ_g)`. -/
def gapDerivativeQuotient {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : ℝ[X] :=
  (gapPolynomial nodes g).derivative /ₘ (X - C (gapArgmax nodes g))

/-- Exact factorization consumed by the source Lemma 2 sign table and the
Jacobian evaluation matrix. -/
lemma X_sub_C_gapArgmax_mul_gapDerivativeQuotient {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    (X - C (gapArgmax nodes g)) * gapDerivativeQuotient nodes g =
      (gapPolynomial nodes g).derivative := by
  exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr
    (gapPolynomial_derivative_eval_gapArgmax nodes hn g)

lemma gapDerivativeQuotient_eval_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).eval (gapArgmax nodes g) =
      (gapPolynomial nodes g).derivative.derivative.eval (gapArgmax nodes g) := by
  have h := congrArg (Polynomial.eval (gapArgmax nodes g))
    (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative
      (gapPolynomial nodes g).derivative (gapArgmax nodes g))
  simpa [gapDerivativeQuotient] using h

lemma gapDerivativeQuotient_eval_gapArgmax_neg {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).eval (gapArgmax nodes g) < 0 := by
  rw [gapDerivativeQuotient_eval_gapArgmax]
  exact gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes hn g

/-- The removed-critical-factor quotient is strictly negative throughout its
own open gap, including at the removed root. -/
lemma gapDerivativeQuotient_eval_neg_of_mem_openGap {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {x : ℝ} (hx : x ∈ openGap nodes g) :
    (gapDerivativeQuotient nodes g).eval x < 0 := by
  by_cases heq : x = gapArgmax nodes g
  · rw [heq]
    exact gapDerivativeQuotient_eval_gapArgmax_neg nodes hn g
  have hfactor := congrArg (Polynomial.eval x)
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes (by omega) g)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  rcases lt_or_gt_of_ne heq with hlt | hgt
  · have hderiv := gapPolynomial_derivative_pos_of_lt_gapArgmax nodes hn g hx hlt
    have hmul : 0 < (x - gapArgmax nodes g) *
        (gapDerivativeQuotient nodes g).eval x := by rwa [hfactor]
    rcases mul_pos_iff.mp hmul with hbad | hgood
    · exact (not_lt_of_ge hbad.1.le (sub_neg.mpr hlt)).elim
    · exact hgood.2
  · have hderiv := gapPolynomial_derivative_neg_of_gapArgmax_lt nodes hn g hx hgt
    have hmul : (x - gapArgmax nodes g) *
        (gapDerivativeQuotient nodes g).eval x < 0 := by rwa [hfactor]
    rcases mul_neg_iff.mp hmul with hgood | hbad
    · exact hgood.2
    · exact (not_lt_of_ge (sub_pos.mpr hgt).le hbad.1).elim

/-- The unique critical root is simple, so the quotient sign does not vanish
at the removed root. -/
lemma rootMultiplicity_gapPolynomial_derivative_gapArgmax {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.rootMultiplicity (gapArgmax nodes g) = 1 := by
  let dp : ℝ[X] := (gapPolynomial nodes g).derivative
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero nodes (by omega) g
  have hroot : dp.IsRoot (gapArgmax nodes g) :=
    gapPolynomial_derivative_eval_gapArgmax nodes (by omega) g
  have hpos : 0 < dp.rootMultiplicity (gapArgmax nodes g) :=
    (Polynomial.rootMultiplicity_pos hdp).2 hroot
  have hnotgt : ¬1 < dp.rootMultiplicity (gapArgmax nodes g) := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hdp]
    push_neg
    intro hroot'
    exact ne_of_lt (gapPolynomial_secondDerivative_eval_gapArgmax_neg nodes hn g)
  have hle : dp.rootMultiplicity (gapArgmax nodes g) ≤ 1 :=
    Nat.le_of_not_gt hnotgt
  change dp.rootMultiplicity (gapArgmax nodes g) = 1
  omega

lemma gapDerivativeQuotient_ne_zero {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (g : Fin (n - 1)) :
    gapDerivativeQuotient nodes g ≠ 0 := by
  intro hzero
  have hfactor := X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes hn g
  rw [hzero, mul_zero] at hfactor
  exact (gapPolynomial_derivative_ne_zero nodes hn g) hfactor.symm

/-- The critical quotient has the `≤ n-3` degree required by the source
Lemma 2/Jacobian matrix. -/
lemma natDegree_gapDerivativeQuotient_le_sub_three {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1)) :
    (gapDerivativeQuotient nodes g).natDegree ≤ n - 3 := by
  have hp : gapPolynomial nodes g ≠ 0 := gapPolynomial_ne_zero_critical nodes g
  have hpdegree : (gapPolynomial nodes g).natDegree ≤ n - 1 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  have hderivative :
      (gapPolynomial nodes g).derivative.natDegree ≤ n - 2 := by
    calc
      (gapPolynomial nodes g).derivative.natDegree ≤
          (gapPolynomial nodes g).natDegree - 1 :=
        Polynomial.natDegree_derivative_le _
      _ ≤ (n - 1) - 1 := Nat.sub_le_sub_right hpdegree 1
      _ = n - 2 := by omega
  rw [gapDerivativeQuotient,
    Polynomial.natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  calc
    (gapPolynomial nodes g).derivative.natDegree - 1 ≤ (n - 2) - 1 :=
      Nat.sub_le_sub_right hderivative 1
    _ = n - 3 := by omega

/-- Away from `τ_g`, the critical quotient has no zero in the owning gap. -/
lemma gapDerivativeQuotient_eval_ne_zero_of_mem_openGap {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (g : Fin (n - 1))
    {r : ℝ} (hrgap : r ∈ openGap nodes g)
    (hrne : r ≠ gapArgmax nodes g) :
    (gapDerivativeQuotient nodes g).eval r ≠ 0 := by
  intro hq
  have hfactor := congrArg (Polynomial.eval r)
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes (by omega) g)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, hq, mul_zero] at hfactor
  exact hrne (eq_gapArgmax_of_derivative_eval_eq_zero nodes hn g hrgap hfactor.symm)

/-- With exactly three nodes the derivative is at most linear. -/
lemma natDegree_gapPolynomial_derivative_le_one_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) :
    (gapPolynomial nodes g).derivative.natDegree ≤ 1 := by
  have hp : gapPolynomial nodes g ≠ 0 := by
    intro hzero
    have h := gapPolynomial_eval_left nodes g
    rw [hzero, Polynomial.eval_zero] at h
    norm_num at h
  have hpdegree : (gapPolynomial nodes g).natDegree ≤ 2 := by
    have hdegree := degree_gapPolynomial_le nodes g
    rw [Polynomial.degree_eq_natDegree hp] at hdegree
    exact_mod_cast hdegree
  exact (Polynomial.natDegree_derivative_le _).trans <| by omega

/-- The three-node case of the unique-critical-point claim: the chosen gap
maximizer is the derivative polynomial's unique real root, globally. -/
lemma eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) {r : ℝ}
    (hr : (gapPolynomial nodes g).derivative.eval r = 0) :
    r = gapArgmax nodes g := by
  let dp : ℝ[X] := (gapPolynomial nodes g).derivative
  have hdp : dp ≠ 0 := gapPolynomial_derivative_ne_zero nodes (by norm_num) g
  have hrmem : r ∈ dp.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdp]
    exact hr
  have hamem : gapArgmax nodes g ∈ dp.roots.toFinset := by
    rw [Multiset.mem_toFinset]
    exact gapArgmax_mem_derivative_roots nodes (by norm_num) g
  by_contra hne
  have hpair : ({r, gapArgmax nodes g} : Finset ℝ) ⊆ dp.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hrmem
    · exact hamem
  have hcard : 2 ≤ dp.roots.toFinset.card := by
    have := Finset.card_le_card hpair
    simpa [hne] using this
  have hdegree : dp.roots.toFinset.card ≤ 1 :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' dp).trans
        (natDegree_gapPolynomial_derivative_le_one_of_three_nodes nodes g)
  omega

theorem existsUnique_gapPolynomial_derivative_root_in_gap_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) :
    ∃! r : ℝ, r ∈ openGap nodes g ∧
      (gapPolynomial nodes g).derivative.eval r = 0 := by
  refine ⟨gapArgmax nodes g,
    ⟨gapArgmax_mem_openGap nodes (by norm_num) g,
      gapPolynomial_derivative_eval_gapArgmax nodes (by norm_num) g⟩, ?_⟩
  intro r hr
  exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes nodes g hr.2

/-- Hence the three-node compact maximizer itself is unique. -/
lemma isGapMaximizer_iff_eq_gapArgmax_of_three_nodes
    (nodes : OrderedNodes 3) (g : Fin 2) {r : ℝ} :
    IsGapMaximizer nodes g r ↔ r = gapArgmax nodes g := by
  constructor
  · intro hrmax
    obtain ⟨t, ht⟩ := openGap_nonempty nodes g
    have htgt := one_lt_eval_gapPolynomial_of_mem_openGap nodes (by norm_num) g ht
    have hrgt : 1 < (gapPolynomial nodes g).eval r :=
      htgt.trans_le (hrmax.2 t ⟨ht.1.le, ht.2.le⟩)
    have hropen : r ∈ openGap nodes g := by
      refine ⟨lt_of_le_of_ne hrmax.1.1 ?_, lt_of_le_of_ne hrmax.1.2 ?_⟩
      · intro heq
        rw [← heq, gapPolynomial_eval_left] at hrgt
        exact (lt_irrefl 1) hrgt
      · intro heq
        rw [heq, gapPolynomial_eval_right] at hrgt
        exact (lt_irrefl 1) hrgt
    have hlocal : IsLocalMax (fun x : ℝ => (gapPolynomial nodes g).eval x) r :=
      (show IsMaxOn (fun x : ℝ => (gapPolynomial nodes g).eval x)
          (closedGap nodes g) r from hrmax.2).isLocalMax
        (Icc_mem_nhds hropen.1 hropen.2)
    have hderiv : (gapPolynomial nodes g).derivative.eval r = 0 :=
      hlocal.hasDerivAt_eq_zero ((gapPolynomial nodes g).hasDerivAt r)
    exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes nodes g hderiv
  · rintro rfl
    exact isGapMaximizer_gapArgmax nodes g

/-- In the two-node case the unique gap coefficient vector is constantly
one, hence the gap polynomial is the constant polynomial one. -/
lemma gapPolynomial_eq_one_of_two_nodes (nodes : OrderedNodes 2) (g : Fin 1) :
    gapPolynomial nodes g = 1 := by
  have hg : g = 0 := Subsingleton.elim _ _
  subst g
  have hcoeff : (gapCoefficient (0 : Fin 1) : Fin 2 → ℝ) = 1 := by
    funext k
    fin_cases k <;> simp [gapCoefficient_of_le, gapCoefficient_of_lt]
  rw [gapPolynomial, hcoeff]
  exact Lagrange.interpolate_one nodes.injective.injOn
    ⟨(0 : Fin 2), Finset.mem_univ _⟩

@[simp]
lemma gapPolynomial_derivative_eq_zero_of_two_nodes (nodes : OrderedNodes 2)
    (g : Fin 1) :
    (gapPolynomial nodes g).derivative = 0 := by
  rw [gapPolynomial_eq_one_of_two_nodes]
  simp

end

end Randy1153.DeBoorPinkus
