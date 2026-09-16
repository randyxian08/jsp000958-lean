import Randy1153.DeBoorPinkus.GapCritical
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Order.IntermediateValue

/-!
# First root-separation lemmas for the de Boor--Pinkus source kernel

Section 2 of de Boor--Pinkus begins its interlacing argument with the facts
that the signed polynomial for one gap changes sign across every other nodal
gap and its derivative vanishes in its own gap.  This file proves those
facts, strictly orders one root in every other gap, proves those selected
roots simple by making the source's implicit multiplicity/parity argument
explicit, and isolates the one remaining degree slot.  Exhaustion in the
degree-`n-2` branch is proved exactly; the degree-`n-1` branch and cross-
polynomial strict interlacing remain for the full source Lemmas 1 and 2.
-/

namespace Randy1153.DeBoorPinkus

open Polynomial

noncomputable section

/-- The signed gap polynomial is nonzero, witnessed by either endpoint of
its own gap. -/
lemma gapPolynomial_ne_zero {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    gapPolynomial nodes g ≠ 0 := by
  intro hzero
  have h := gapPolynomial_eval_left nodes g
  rw [hzero, Polynomial.eval_zero] at h
  norm_num at h

/-- The partition of unity makes the signed polynomial at least one on its
own closed gap. -/
lemma one_le_eval_gapPolynomial_of_mem_closedGap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    1 ≤ (gapPolynomial nodes g).eval t := by
  have hsub : 0 < n - 1 :=
    lt_of_le_of_lt (Nat.zero_le _) g.isLt
  have hn : 0 < n := by omega
  have hsum := sum_lagrangeFundamental_eq_one nodes hn t
  have habs := Finset.abs_sum_le_sum_abs
    (fun k : Fin n => lagrangeFundamental nodes.toNodeFamily k t) Finset.univ
  rw [hsum, abs_one] at habs
  rw [← lebesgueFunction_eq_eval_gapPolynomial nodes g ht, lebesgueFunction]
  simpa using habs

/-- There is no zero of `F_g` in its own closed nodal gap. -/
lemma not_isRoot_gapPolynomial_of_mem_closedGap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) {t : ℝ}
    (ht : t ∈ closedGap nodes g) :
    ¬(gapPolynomial nodes g).IsRoot t := by
  rw [Polynomial.IsRoot]
  exact ne_of_gt (zero_lt_one.trans_le
    (one_le_eval_gapPolynomial_of_mem_closedGap nodes g ht))

/-- Every point in an earlier open nodal gap lies before every point in a
later open nodal gap. -/
lemma openGap_point_lt_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    {g h : Fin (n - 1)} (hgh : g < h) {x y : ℝ}
    (hx : x ∈ openGap nodes g) (hy : y ∈ openGap nodes h) :
    x < y := by
  have hindex : gapRightIndex g ≤ gapLeftIndex h := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [gapRightIndex_val, gapLeftIndex_val]
    omega
  calc
    x < nodes.point (gapRightIndex g) := hx.2
    _ ≤ nodes.point (gapLeftIndex h) := nodes.strictMono.monotone hindex
    _ < y := hy.1

/-- Indices of all nodal gaps other than `g`. -/
abbrev OtherGapIndex {n : ℕ} (g : Fin (n - 1)) :=
  {h : Fin (n - 1) // h ≠ g}

@[simp]
lemma card_otherGapIndex {n : ℕ} (g : Fin (n - 1)) :
    Fintype.card (OtherGapIndex g) = n - 2 := by
  classical
  change Fintype.card {h : Fin (n - 1) // ¬h = g} = n - 2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_fin, Fintype.card_unique]
  omega

/-- A gap polynomial takes opposite, nonzero values at the endpoints of every
other nodal gap. -/
lemma gapPolynomial_endpoint_values_opposite {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hhg : h ≠ g) :
    (gapPolynomial nodes g).eval (nodes.point (gapRightIndex h)) =
      -(gapPolynomial nodes g).eval (nodes.point (gapLeftIndex h)) := by
  rw [gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapCoefficient_right_eq_neg_left_of_ne g h hhg]

lemma gapPolynomial_endpoint_value_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapPolynomial nodes g).eval (nodes.point (gapLeftIndex h)) ≠ 0 := by
  rw [gapPolynomial_eval_node]
  exact gapCoefficient_ne_zero g (gapLeftIndex h)

/-- The initial root-existence step in source Lemma 1: `F_g` has a real root
strictly inside every nodal gap other than `g`. -/
theorem exists_gapPolynomial_root_in_other_gap {n : ℕ} (nodes : OrderedNodes n)
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
    rcases intermediate_value_Ioo' hab hcont hz with ⟨r, hr, hpr⟩
    exact ⟨r, hr, hpr⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) := by
      rw [ha, hb, hc]
      norm_num
    rcases intermediate_value_Ioo hab hcont hz with ⟨r, hr, hpr⟩
    exact ⟨r, hr, hpr⟩

/-- A chosen real zero of `F_g` in every other nodal gap. -/
def otherGapRoot {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h : OtherGapIndex g) : ℝ :=
  Classical.choose (exists_gapPolynomial_root_in_other_gap nodes g h.1 h.property)

lemma otherGapRoot_mem_openGap {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : OtherGapIndex g) :
    otherGapRoot nodes g h ∈ openGap nodes h.1 :=
  (Classical.choose_spec
    (exists_gapPolynomial_root_in_other_gap nodes g h.1 h.property)).1

lemma gapPolynomial_eval_otherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : OtherGapIndex g) :
    (gapPolynomial nodes g).eval (otherGapRoot nodes g h) = 0 :=
  (Classical.choose_spec
    (exists_gapPolynomial_root_in_other_gap nodes g h.1 h.property)).2

lemma otherGapRoot_isRoot {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : OtherGapIndex g) :
    (gapPolynomial nodes g).IsRoot (otherGapRoot nodes g h) :=
  gapPolynomial_eval_otherGapRoot nodes g h

/-- The chosen internal roots occur in strict nodal-gap order. -/
lemma otherGapRoot_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    StrictMono (otherGapRoot nodes g) := by
  intro h k hhk
  exact openGap_point_lt_of_gap_lt nodes hhk
    (otherGapRoot_mem_openGap nodes g h)
    (otherGapRoot_mem_openGap nodes g k)

/-- The paper's first root count, made explicit: `F_g` has at least `n-2`
distinct real roots, one in every other nodal gap. -/
lemma sub_two_le_card_gapPolynomial_roots_toFinset {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    n - 2 ≤ (gapPolynomial nodes g).roots.toFinset.card := by
  let p : ℝ[X] := gapPolynomial nodes g
  let f : OtherGapIndex g → p.roots.toFinset := fun h =>
    ⟨otherGapRoot nodes g h, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (gapPolynomial_ne_zero nodes g)]
      exact otherGapRoot_isRoot nodes g h⟩
  rw [← card_otherGapIndex g]
  simpa only [Fintype.card_coe] using
    (Fintype.card_le_of_injective f fun h k heq =>
      (otherGapRoot_strictMono nodes g).injective (congrArg Subtype.val heq))

/-- Consequently the natural degree is at least `n-2`.  Together with the
interpolation upper bound, only one degree/multiplicity slot remains; closing
that slot is precisely where the source's parity/interlacing argument enters. -/
lemma sub_two_le_natDegree_gapPolynomial {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    n - 2 ≤ (gapPolynomial nodes g).natDegree :=
  (sub_two_le_card_gapPolynomial_roots_toFinset nodes g).trans <|
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _)

lemma natDegree_gapPolynomial_le_sub_one {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    (gapPolynomial nodes g).natDegree ≤ n - 1 := by
  have hdegree := degree_gapPolynomial_le nodes g
  rw [Polynomial.degree_eq_natDegree (gapPolynomial_ne_zero nodes g)] at hdegree
  exact_mod_cast hdegree

/-- Exact degree dichotomy left by the first root count.  The source's full
Lemma 1 must decide this final slot while controlling real-root
multiplicities; it cannot be discarded by a distinct-root count alone. -/
lemma natDegree_gapPolynomial_eq_sub_two_or_sub_one {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).natDegree = n - 2 ∨
      (gapPolynomial nodes g).natDegree = n - 1 := by
  have hn : 2 ≤ n := by
    have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
    omega
  have hlo := sub_two_le_natDegree_gapPolynomial nodes g
  have hhi := natDegree_gapPolynomial_le_sub_one nodes g
  omega

/-- Counting multiplicity, the real-root multiset has at most one slot more
than the already separated `n-2` roots.  This is the precise budget used by
the paper's implicit parity argument. -/
lemma card_gapPolynomial_roots_le_toFinset_card_add_one {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).roots.card ≤
      (gapPolynomial nodes g).roots.toFinset.card + 1 := by
  have hn : 2 ≤ n := by
    have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
    omega
  have hdistinct := sub_two_le_card_gapPolynomial_roots_toFinset nodes g
  have hmulti : (gapPolynomial nodes g).roots.card ≤ n - 1 :=
    (Polynomial.card_roots' _).trans (natDegree_gapPolynomial_le_sub_one nodes g)
  omega

private lemma toFinset_card_add_count_sub_one_le_card {α : Type*}
    [DecidableEq α] (s : Multiset α) {a : α} (ha : a ∈ s) :
    s.toFinset.card + (s.count a - 1) ≤ s.card := by
  have haS : a ∈ s.toFinset := Multiset.mem_toFinset.mpr ha
  have hrest : (s.toFinset.erase a).card ≤
      ∑ x ∈ s.toFinset.erase a, s.count x := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun x hx => by
      rw [Nat.one_le_iff_ne_zero, Multiset.count_ne_zero]
      exact Multiset.mem_toFinset.mp (Finset.mem_of_mem_erase hx)
  have hsplit : s.card = s.count a +
      ∑ x ∈ s.toFinset.erase a, s.count x := by
    rw [← Multiset.toFinset_sum_count_eq]
    exact (Finset.add_sum_erase s.toFinset (fun x => s.count x) haS).symm
  have hcardSplit : s.toFinset.card = (s.toFinset.erase a).card + 1 := by
    exact (Finset.card_erase_add_one haS).symm
  have hcount : 1 ≤ s.count a := by
    rwa [Nat.one_le_iff_ne_zero, Multiset.count_ne_zero]
  rw [hcardSplit, hsplit]
  omega

/-- Each selected sign-changing root is simple.  The proof makes explicit
the parity argument compressed into the sentence preceding source Lemma 1:
a double root consumes the only spare multiplicity slot, so it would be the
only root in that gap; after factoring out its square, IVT forces another
root because the endpoint values of `F_g` are opposite. -/
lemma rootMultiplicity_otherGapRoot {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (h : OtherGapIndex g) :
    (gapPolynomial nodes g).rootMultiplicity (otherGapRoot nodes g h) = 1 := by
  classical
  let p : ℝ[X] := gapPolynomial nodes g
  let r : ℝ := otherGapRoot nodes g h
  have hp : p ≠ 0 := gapPolynomial_ne_zero nodes g
  have hrroot : p.IsRoot r := otherGapRoot_isRoot nodes g h
  have hrmem : r ∈ p.roots := (Polynomial.mem_roots hp).mpr hrroot
  have hcountPos : 0 < p.roots.count r := Multiset.count_pos.mpr hrmem
  have hcountEq : p.roots.count r = p.rootMultiplicity r :=
    Polynomial.count_roots p
  have hcountUpper : p.roots.count r ≤ 2 := by
    have hbudget := toFinset_card_add_count_sub_one_le_card p.roots hrmem
    have hdistinct : n - 2 ≤ p.roots.toFinset.card := by
      simpa only [p] using sub_two_le_card_gapPolynomial_roots_toFinset nodes g
    have hcardUpper : p.roots.card ≤ n - 1 :=
      (Polynomial.card_roots' p).trans (natDegree_gapPolynomial_le_sub_one nodes g)
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  by_contra hnotone
  have hnotone' : p.rootMultiplicity r ≠ 1 := by
    simpa only [p, r] using hnotone
  have hmult : p.rootMultiplicity r = 2 := by omega

  have hunique : ∀ {x : ℝ}, x ∈ openGap nodes h.1 → p.IsRoot x → x = r := by
    intro x hx hxp
    by_contra hxr
    let rootImage : Finset ℝ :=
      Finset.univ.image (otherGapRoot nodes g : OtherGapIndex g → ℝ)
    have hrootImageCard : rootImage.card = n - 2 := by
      rw [Finset.card_image_of_injOn
        (otherGapRoot_strictMono nodes g).injective.injOn,
        Finset.card_univ, card_otherGapIndex]
    have hrootImageSubset : rootImage ⊆ p.roots.toFinset := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨k, _hk, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
      exact otherGapRoot_isRoot nodes g k
    have hxNotImage : x ∉ rootImage := by
      intro hxImage
      rcases Finset.mem_image.mp hxImage with ⟨k, _hk, hkx⟩
      have hkval : k.1 = h.1 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := openGap_point_lt_of_gap_lt nodes hlt
            (otherGapRoot_mem_openGap nodes g k) hx
          exact this.ne hkx
        · have := openGap_point_lt_of_gap_lt nodes hgt hx
            (otherGapRoot_mem_openGap nodes g k)
          exact this.ne hkx.symm
      have hkeq : k = h := Subtype.ext hkval
      subst k
      exact hxr hkx.symm
    have hxmem : x ∈ p.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
      exact hxp
    have hlargeDistinct : n - 1 ≤ p.roots.toFinset.card := by
      have hinsert : insert x rootImage ⊆ p.roots.toFinset := by
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxmem
        · exact hrootImageSubset hy
      have hcardInsert : (insert x rootImage).card = n - 1 := by
        rw [Finset.card_insert_of_notMem hxNotImage, hrootImageCard]
        omega
      rw [← hcardInsert]
      exact Finset.card_le_card hinsert
    have hbudget := toFinset_card_add_count_sub_one_le_card p.roots hrmem
    have hcardUpper : p.roots.card ≤ n - 1 :=
      (Polynomial.card_roots' p).trans (natDegree_gapPolynomial_le_sub_one nodes g)
    omega

  let q : ℝ[X] := p /ₘ (X - C r) ^ 2
  have hpFactor : (X - C r) ^ 2 * q = p := by
    simpa only [q, hmult] using p.pow_mul_divByMonic_rootMultiplicity_eq r
  have hqr : q.eval r ≠ 0 := by
    simpa only [q, hmult] using
      (Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero r hp)
  let a : ℝ := nodes.point (gapLeftIndex h.1)
  let b : ℝ := nodes.point (gapRightIndex h.1)
  have hra : r - a > 0 := by
    simpa only [r, a, sub_pos] using (otherGapRoot_mem_openGap nodes g h).1
  have hrb : b - r > 0 := by
    simpa only [r, b, sub_pos] using (otherGapRoot_mem_openGap nodes g h).2
  have hpa : p.eval a = gapCoefficient g (gapLeftIndex h.1) := by
    exact gapPolynomial_eval_node nodes g (gapLeftIndex h.1)
  have hpb : p.eval b = -gapCoefficient g (gapLeftIndex h.1) := by
    calc
      p.eval b = -p.eval a := by
        simpa only [p, a, b] using
          gapPolynomial_endpoint_values_opposite nodes g h.1 h.property
      _ = -gapCoefficient g (gapLeftIndex h.1) := by rw [hpa]
  have hpaFactor : p.eval a = (a - r) ^ 2 * q.eval a := by
    rw [← hpFactor]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hpbFactor : p.eval b = (b - r) ^ 2 * q.eval b := by
    rw [← hpFactor]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  have hqprod : q.eval a * q.eval b < 0 := by
    have hcoeff := gapCoefficient_ne_zero g (gapLeftIndex h.1)
    have hasq : 0 < (a - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
    have hbsq : 0 < (b - r) ^ 2 := sq_pos_of_ne_zero (by linarith)
    have hpProdNeg : p.eval a * p.eval b < 0 := by
      rw [hpa, hpb]
      nlinarith [sq_pos_of_ne_zero hcoeff]
    by_contra hnot
    have hqnonneg : 0 ≤ q.eval a * q.eval b := le_of_not_gt hnot
    have hpProdNonneg : 0 ≤ p.eval a * p.eval b := by
      rw [hpaFactor, hpbFactor]
      calc
        0 ≤ ((a - r) ^ 2 * (b - r) ^ 2) * (q.eval a * q.eval b) :=
          mul_nonneg (mul_nonneg hasq.le hbsq.le) hqnonneg
        _ = ((a - r) ^ 2 * q.eval a) * ((b - r) ^ 2 * q.eval b) := by ring
    exact (not_lt_of_ge hpProdNonneg) hpProdNeg
  have hab : a ≤ b := (gap_left_lt_right nodes h.1).le
  have hcont : ContinuousOn (fun x => q.eval x) (Set.Icc a b) :=
    q.continuous.continuousOn
  obtain ⟨x, hx, hqx⟩ : ∃ x ∈ Set.Ioo a b, q.eval x = 0 := by
    rcases (mul_neg_iff.mp hqprod) with hsign | hsign
    · have hz : (0 : ℝ) ∈ Set.Ioo (q.eval b) (q.eval a) :=
        ⟨hsign.2, hsign.1⟩
      exact intermediate_value_Ioo' hab hcont hz
    · have hz : (0 : ℝ) ∈ Set.Ioo (q.eval a) (q.eval b) := hsign
      exact intermediate_value_Ioo hab hcont hz
  have hxp : p.IsRoot x := by
    rw [← hpFactor, Polynomial.IsRoot, Polynomial.eval_mul,
      Polynomial.eval_pow, hqx, mul_zero]
  have hxrEq : x = r := hunique hx hxp
  exact hqr (hxrEq ▸ hqx)

/-- If the final degree slot vanishes, the selected roots exhaust the whole
real-root multiset.  Thus all unresolved root placement is confined to the
source's genuine degree-`n-1` branch. -/
lemma roots_gapPolynomial_eq_otherGapRoots_of_natDegree_eq_sub_two {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (hdegree : (gapPolynomial nodes g).natDegree = n - 2) :
    (gapPolynomial nodes g).roots =
      (Finset.univ.image
        (otherGapRoot nodes g : OtherGapIndex g → ℝ)).val := by
  let rootImage : Finset ℝ :=
    Finset.univ.image (otherGapRoot nodes g : OtherGapIndex g → ℝ)
  have hrootImageCard : rootImage.card = n - 2 := by
    rw [Finset.card_image_of_injOn
      (otherGapRoot_strictMono nodes g).injective.injOn,
      Finset.card_univ, card_otherGapIndex]
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨h, _hh, rfl⟩
    exact gapPolynomial_eval_otherGapRoot nodes g h
  · rw [hdegree, hrootImageCard]
  · exact gapPolynomial_ne_zero nodes g

/-- The selected root is the only root in its nodal gap.  Factoring the
`n-2` simple selected roots leaves a quotient of degree at most one.  On a
fixed other gap both the selected-root product and `F_g` change sign, so the
linear quotient has equal endpoint sign and cannot vanish inside. -/
lemma isRoot_in_other_gap_iff_eq_otherGapRoot {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (h : OtherGapIndex g)
    {x : ℝ} (hx : x ∈ openGap nodes h.1) :
    (gapPolynomial nodes g).IsRoot x ↔ x = otherGapRoot nodes g h := by
  classical
  let p : ℝ[X] := gapPolynomial nodes g
  let root : OtherGapIndex g → ℝ := otherGapRoot nodes g
  let D : ℝ[X] := ∏ k : OtherGapIndex g, (X - C (root k))
  have hp : p ≠ 0 := gapPolynomial_ne_zero nodes g
  have hrootInjective : Function.Injective root :=
    (otherGapRoot_strictMono nodes g).injective
  have hDvd : D ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro k
      rw [Polynomial.dvd_iff_isRoot]
      exact otherGapRoot_isRoot nodes g k
  obtain ⟨q, hq⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex g)),
      (X - C (root k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (root k)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hqne : q ≠ 0 := by
    intro hzero
    apply hp
    rw [hzero, mul_zero] at hq
    exact hq
  have hn : 2 ≤ n := by
    have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
    omega
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex g)),
      (X - C (root k))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_otherGapIndex]
  have hqdegree : q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hq
    rw [Polynomial.natDegree_mul hDne hqne, hDdegree] at hnat
    have hpdegree : p.natDegree ≤ n - 1 :=
      natDegree_gapPolynomial_le_sub_one nodes g
    omega

  let a : ℝ := nodes.point (gapLeftIndex h.1)
  let b : ℝ := nodes.point (gapRightIndex h.1)
  let pairValue : OtherGapIndex g → ℝ := fun k =>
    (a - root k) * (b - root k)
  have hpairSelf : pairValue h < 0 := by
    have hrmem := otherGapRoot_mem_openGap nodes g h
    have hal : a < root h := by simpa only [a, root] using hrmem.1
    have hrb : root h < b := by simpa only [b, root] using hrmem.2
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hal) (sub_pos.mpr hrb)
  have hpairOther : ∀ k : OtherGapIndex g, k ≠ h → 0 < pairValue k := by
    intro k hkh
    rcases lt_or_gt_of_ne hkh with hlt | hgt
    · have hrlt : root k < a := by
        have hrmem := otherGapRoot_mem_openGap nodes g k
        have hltval : k.1.val < h.1.val := hlt
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex h.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hrmem.2
          _ ≤ nodes.point (gapLeftIndex h.1) := nodes.strictMono.monotone hindex
          _ = a := rfl
      have hab : a < b := gap_left_lt_right nodes h.1
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hrlt) (sub_pos.mpr (hrlt.trans hab))
    · have hbrt : b < root k := by
        have hrmem := otherGapRoot_mem_openGap nodes g k
        have hgtval : h.1.val < k.1.val := hgt
        have hindex : gapRightIndex h.1 ≤ gapLeftIndex k.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          b = nodes.point (gapRightIndex h.1) := rfl
          _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
          _ < root k := by simpa only [root] using hrmem.1
      have hab : a < b := gap_left_lt_right nodes h.1
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans hbrt)) (sub_neg.mpr hbrt)
  have hpairProduct : (∏ k : OtherGapIndex g, pairValue k) < 0 := by
    rw [Fintype.prod_eq_mul_prod_compl h]
    exact mul_neg_of_neg_of_pos hpairSelf <| by
      exact Finset.prod_pos fun k hk => hpairOther k (by simpa using hk)
  have hDevalProduct : D.eval a * D.eval b < 0 := by
    have heq : D.eval a * D.eval b = ∏ k : OtherGapIndex g, pairValue k := by
      simp only [D, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, pairValue]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    exact hpairProduct
  have hpevalProduct : p.eval a * p.eval b < 0 := by
    have hpa : p.eval a = gapCoefficient g (gapLeftIndex h.1) := by
      simpa only [p, a] using gapPolynomial_eval_node nodes g (gapLeftIndex h.1)
    have hpb : p.eval b = -gapCoefficient g (gapLeftIndex h.1) := by
      calc
        p.eval b = -p.eval a := by
          simpa only [p, a, b] using
            gapPolynomial_endpoint_values_opposite nodes g h.1 h.property
        _ = -gapCoefficient g (gapLeftIndex h.1) := by rw [hpa]
    rw [hpa, hpb]
    nlinarith [sq_pos_of_ne_zero (gapCoefficient_ne_zero g (gapLeftIndex h.1))]
  have hqevalProduct : 0 < q.eval a * q.eval b := by
    have hfactor : p.eval a * p.eval b =
        (D.eval a * D.eval b) * (q.eval a * q.eval b) := by
      rw [hq]
      simp only [Polynomial.eval_mul]
      ring
    have hmulneg : (D.eval a * D.eval b) * (q.eval a * q.eval b) < 0 := by
      rwa [← hfactor]
    rcases mul_neg_iff.mp hmulneg with hbad | hgood
    · exact (hDevalProduct.not_gt hbad.1).elim
    · exact hgood.2
  have hqNoRoot : ∀ {y : ℝ}, y ∈ Set.Ioo a b → ¬q.IsRoot y := by
    intro y hy hyroot
    obtain ⟨s, hs⟩ := Polynomial.dvd_iff_isRoot.mpr hyroot
    have hsne : s ≠ 0 := by
      intro hzero
      apply hqne
      rw [hzero, mul_zero] at hs
      exact hs
    have hsdegree : s.natDegree = 0 := by
      have hnat := congrArg Polynomial.natDegree hs
      rw [Polynomial.natDegree_mul (X_sub_C_ne_zero y) hsne,
        natDegree_X_sub_C] at hnat
      omega
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hsdegree
    have hc : c ≠ 0 := by
      intro hc
      apply hqne
      simpa [hc] using hs
    have hqprodneg : q.eval a * q.eval b < 0 := by
      rw [hs]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      calc
        (a - y) * c * ((b - y) * c) =
            ((a - y) * (b - y)) * c ^ 2 := by ring
        _ < 0 := mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos (sub_neg.mpr hy.1) (sub_pos.mpr hy.2))
          (sq_pos_of_ne_zero hc)
    exact (not_lt_of_ge hqevalProduct.le) hqprodneg

  constructor
  · intro hxroot
    have hqnx : q.eval x ≠ 0 := by
      intro hzero
      exact hqNoRoot hx hzero
    have hDevalx : D.eval x = 0 := by
      have hpx : p.eval x = 0 := hxroot
      rw [hq, Polynomial.eval_mul] at hpx
      exact (mul_eq_zero.mp hpx).resolve_right hqnx
    have hprod : ∏ k : OtherGapIndex g, (x - root k) = 0 := by
      simpa only [D, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] using hDevalx
    rcases Finset.prod_eq_zero_iff.mp hprod with ⟨k, _hk, hkzero⟩
    have hxrootk : x = root k := sub_eq_zero.mp hkzero
    have hkval : k.1 = h.1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have horder := openGap_point_lt_of_gap_lt nodes hlt
          (otherGapRoot_mem_openGap nodes g k) hx
        exact horder.ne hxrootk.symm
      · have horder := openGap_point_lt_of_gap_lt nodes hgt hx
          (otherGapRoot_mem_openGap nodes g k)
        exact horder.ne hxrootk
    have hkeq : k = h := Subtype.ext hkval
    simpa only [root, hkeq] using hxrootk
  · rintro rfl
    exact otherGapRoot_isRoot nodes g h

/-- Exact simple root placement on every gap other than `g`. -/
theorem existsUnique_gapPolynomial_root_in_other_gap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (h : OtherGapIndex g) :
    ∃! r : ℝ, r ∈ openGap nodes h.1 ∧ (gapPolynomial nodes g).IsRoot r := by
  refine ⟨otherGapRoot nodes g h,
    ⟨otherGapRoot_mem_openGap nodes g h, otherGapRoot_isRoot nodes g h⟩, ?_⟩
  intro r hr
  exact (isRoot_in_other_gap_iff_eq_otherGapRoot nodes g h hr.1).mp hr.2

lemma rootMultiplicity_eq_one_of_mem_other_gap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) (h : OtherGapIndex g)
    {r : ℝ} (hr : r ∈ openGap nodes h.1) (hroot : (gapPolynomial nodes g).IsRoot r) :
    (gapPolynomial nodes g).rootMultiplicity r = 1 := by
  rw [(isRoot_in_other_gap_iff_eq_otherGapRoot nodes g h hr).mp hroot]
  exact rootMultiplicity_otherGapRoot nodes g h

/-- Rolle separation between any two ordered selected roots.  Full source
Lemma 2 must sharpen these existentials into an exhaustive, strictly
interlacing derivative-root list. -/
theorem exists_derivative_root_between_otherGapRoots {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1))
    (h k : OtherGapIndex g) (hhk : h < k) :
    ∃ r ∈ Set.Ioo (otherGapRoot nodes g h) (otherGapRoot nodes g k),
      (gapPolynomial nodes g).derivative.eval r = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  have hlt : otherGapRoot nodes g h < otherGapRoot nodes g k :=
    otherGapRoot_strictMono nodes g hhk
  have heq : p.eval (otherGapRoot nodes g h) =
      p.eval (otherGapRoot nodes g k) := by
    rw [gapPolynomial_eval_otherGapRoot, gapPolynomial_eval_otherGapRoot]
  obtain ⟨r, hr, hderiv⟩ := exists_deriv_eq_zero hlt p.continuous.continuousOn heq
  refine ⟨r, hr, ?_⟩
  simpa only [p, Polynomial.deriv] using hderiv

lemma natDegree_gapPolynomial_derivative_le_sub_two {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    (gapPolynomial nodes g).derivative.natDegree ≤ n - 2 := by
  calc
    (gapPolynomial nodes g).derivative.natDegree ≤
        (gapPolynomial nodes g).natDegree - 1 :=
      Polynomial.natDegree_derivative_le _
    _ ≤ (n - 1) - 1 := Nat.sub_le_sub_right
      (natDegree_gapPolynomial_le_sub_one nodes g) 1
    _ = n - 2 := by omega

/-- Rolle's theorem supplies at least one critical point of `F_g` in its own
gap.  The de Boor--Pinkus/Kilgore kernel later strengthens this to a unique
critical point and identifies it as the unique gap maximum. -/
theorem exists_gapPolynomial_derivative_root_in_gap {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    ∃ r ∈ openGap nodes g, (gapPolynomial nodes g).derivative.eval r = 0 := by
  let p : ℝ[X] := gapPolynomial nodes g
  have hend : p.eval (nodes.point (gapLeftIndex g)) =
      p.eval (nodes.point (gapRightIndex g)) := by
    simp [p]
  obtain ⟨r, hr, hderiv⟩ := exists_deriv_eq_zero (gap_left_lt_right nodes g)
    p.continuous.continuousOn hend
  refine ⟨r, hr, ?_⟩
  simpa only [p, Polynomial.deriv] using hderiv

end

end Randy1153.DeBoorPinkus
