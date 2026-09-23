import Randy1153.DeBoorPinkus.Interlacing

/-!
# Cross-polynomial root separation

This file follows the proof of de Boor--Pinkus, Section 2, Lemma 1.  For two
gap polynomials `F_g,F_h` with `g<h`, the source uses the two combinations

`F_g - (-1)^(h-g) F_h` and `F_g + (-1)^(h-g) F_h`.

The first vanishes at all nodal points outside the block and alternates at
the nodes inside it; the second has the complementary nodal pattern.  The
root counts, quotient parity, and resulting signs below prove equations
`(5a--f)` and their strict common-gap root order.
-/

namespace Randy1153.DeBoorPinkus

open Polynomial
open scoped BigOperators

noncomputable section

/-- The parity factor used by the source for a pair of gap indices. -/
def gapPairParity {n : ℕ} (g h : Fin (n - 1)) : ℝ :=
  (-1 : ℝ) ^ (h.val - g.val)

lemma gapPairParity_eq_one_or_neg_one {n : ℕ} (g h : Fin (n - 1)) :
    gapPairParity g h = 1 ∨ gapPairParity g h = -1 := by
  rw [gapPairParity]
  generalize h.val - g.val = m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      rcases ih with ih | ih <;> simp [ih]

@[simp]
lemma sq_gapPairParity {n : ℕ} (g h : Fin (n - 1)) :
    gapPairParity g h ^ 2 = 1 := by
  rcases gapPairParity_eq_one_or_neg_one g h with hp | hp <;> simp [hp]

/-- Coefficient relation underlying both source combinations. -/
lemma gapPairParity_mul_gapCoefficient {n : ℕ} (g h : Fin (n - 1))
    (hgh : g < h) (k : Fin n) :
    gapPairParity g h * gapCoefficient h k =
      if k.val ≤ g.val ∨ h.val < k.val then
        gapCoefficient g k
      else
        -gapCoefficient g k := by
  by_cases hkg : k.val ≤ g.val
  · have hkh : k.val ≤ h.val := hkg.trans hgh.le
    rw [if_pos (Or.inl hkg), gapPairParity, gapCoefficient_of_le g k hkg,
      gapCoefficient_of_le h k hkh]
    have hexp : (h.val - g.val) + (h.val - k.val) =
        (g.val - k.val) + 2 * (h.val - g.val) := by omega
    rw [← pow_add, hexp, pow_add, pow_mul]
    norm_num
  · have hgk : g.val < k.val := Nat.lt_of_not_ge hkg
    by_cases hhk : h.val < k.val
    · rw [if_pos (Or.inr hhk), gapPairParity,
        gapCoefficient_of_lt g k hgk, gapCoefficient_of_lt h k hhk]
      have hexp : (h.val - g.val) + (k.val - h.val - 1) =
          k.val - g.val - 1 := by omega
      rw [← pow_add, hexp]
    · have hkle : k.val ≤ h.val := Nat.le_of_not_gt hhk
      rw [if_neg (by simp [hkg, hhk]), gapPairParity,
        gapCoefficient_of_lt g k hgk, gapCoefficient_of_le h k hkle]
      have hexp : (h.val - g.val) + (h.val - k.val) =
          (k.val - g.val - 1) + (2 * (h.val - k.val) + 1) := by omega
      rw [← pow_add, hexp, pow_add]
      have hodd : (-1 : ℝ) ^ (2 * (h.val - k.val) + 1) = -1 := by
        rw [pow_add, pow_mul]
        norm_num
      rw [hodd]
      ring

/-- Source `G₁`: difference combination, zero outside the index block. -/
def gapDifferenceCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : ℝ[X] :=
  gapPolynomial nodes g - C (gapPairParity g h) * gapPolynomial nodes h

/-- Source `G₂`: sum combination, zero inside the index block. -/
def gapSumCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : ℝ[X] :=
  gapPolynomial nodes g + C (gapPairParity g h) * gapPolynomial nodes h

lemma gapDifferenceCombination_eval_node {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (k : Fin n) :
    (gapDifferenceCombination nodes g h).eval (nodes.point k) =
      if k.val ≤ g.val ∨ h.val < k.val then 0
      else 2 * gapCoefficient g k := by
  rw [gapDifferenceCombination, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapPairParity_mul_gapCoefficient g h hgh k]
  split_ifs <;> ring

lemma gapSumCombination_eval_node {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (k : Fin n) :
    (gapSumCombination nodes g h).eval (nodes.point k) =
      if k.val ≤ g.val ∨ h.val < k.val then 2 * gapCoefficient g k
      else 0 := by
  rw [gapSumCombination, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, gapPolynomial_eval_node, gapPolynomial_eval_node,
    gapPairParity_mul_gapCoefficient g h hgh k]
  split_ifs <;> ring

lemma degree_gapDifferenceCombination_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapDifferenceCombination nodes g h).degree ≤ (n - 1 : ℕ) := by
  apply (degree_sub_le _ _).trans
  apply max_le
  · exact degree_gapPolynomial_le nodes g
  · exact (degree_mul_le _ _).trans <| by
      simpa using add_le_add degree_C_le (degree_gapPolynomial_le nodes h)

lemma degree_gapSumCombination_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) :
    (gapSumCombination nodes g h).degree ≤ (n - 1 : ℕ) := by
  apply (degree_add_le _ _).trans
  apply max_le
  · exact degree_gapPolynomial_le nodes g
  · exact (degree_mul_le _ _).trans <| by
      simpa using add_le_add degree_C_le (degree_gapPolynomial_le nodes h)

lemma gapDifferenceCombination_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    gapDifferenceCombination nodes g h ≠ 0 := by
  let k : Fin n := gapRightIndex g
  have hinside : ¬(k.val ≤ g.val ∨ h.val < k.val) := by
    simp only [k, gapRightIndex_val]
    omega
  have heval := gapDifferenceCombination_eval_node nodes g h hgh k
  rw [if_neg hinside] at heval
  intro hzero
  rw [hzero, Polynomial.eval_zero] at heval
  have hcoeff := gapCoefficient_ne_zero g k
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hcoeff) heval.symm

/-- The difference combination has a root in every gap strictly between
`g` and `h`; these are the non-nodal roots in the source count for `G₁`. -/
theorem exists_gapDifferenceCombination_root_in_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1))
    (hgh : g < h) (hgq : g < q) (hqh : q < h) :
    ∃ r ∈ openGap nodes q, (gapDifferenceCombination nodes g h).eval r = 0 := by
  let P : ℝ[X] := gapDifferenceCombination nodes g h
  let a : ℝ := nodes.point (gapLeftIndex q)
  let b : ℝ := nodes.point (gapRightIndex q)
  have hleftInside : ¬((gapLeftIndex q).val ≤ g.val ∨
      h.val < (gapLeftIndex q).val) := by
    simp only [gapLeftIndex_val]
    omega
  have hrightInside : ¬((gapRightIndex q).val ≤ g.val ∨
      h.val < (gapRightIndex q).val) := by
    simp only [gapRightIndex_val]
    omega
  have ha : P.eval a = 2 * gapCoefficient g (gapLeftIndex q) := by
    simpa only [P, a, if_neg hleftInside] using
      gapDifferenceCombination_eval_node nodes g h hgh (gapLeftIndex q)
  have hb : P.eval b = -(2 * gapCoefficient g (gapLeftIndex q)) := by
    have hqg : q ≠ g := ne_of_gt hgq
    calc
      P.eval b = 2 * gapCoefficient g (gapRightIndex q) := by
        simpa only [P, b, if_neg hrightInside] using
          gapDifferenceCombination_eval_node nodes g h hgh (gapRightIndex q)
      _ = -(2 * gapCoefficient g (gapLeftIndex q)) := by
        rw [gapCoefficient_right_eq_neg_left_of_ne g q hqg]
        ring
  have hab : a ≤ b := (gap_left_lt_right nodes q).le
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) :=
    P.continuous.continuousOn
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex q) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz

/-- The complete `n-1`-point root list for the difference combination:
outside the block use its nodal roots; inside use the IVT root in that gap. -/
def gapDifferenceRootPoint {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1)) : ℝ :=
  if hqg : q.val ≤ g.val then
    nodes.point (gapLeftIndex q)
  else if hhq : h.val ≤ q.val then
    nodes.point (gapRightIndex q)
  else
    Classical.choose (exists_gapDifferenceCombination_root_in_middleGap
      nodes g h q hgh (by omega) (by omega))

lemma gapDifferenceRootPoint_eq_left_of_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hqg : q.val ≤ g.val) :
    gapDifferenceRootPoint nodes g h hgh q = nodes.point (gapLeftIndex q) := by
  simp [gapDifferenceRootPoint, hqg]

lemma gapDifferenceRootPoint_eq_right_of_le {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hhq : h.val ≤ q.val) :
    gapDifferenceRootPoint nodes g h hgh q = nodes.point (gapRightIndex q) := by
  have hnqg : ¬q.val ≤ g.val := by omega
  simp [gapDifferenceRootPoint, hnqg, hhq]

lemma gapDifferenceRootPoint_mem_openGap_of_between {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) (hgq : g < q) (hqh : q < h) :
    gapDifferenceRootPoint nodes g h hgh q ∈ openGap nodes q := by
  have hnqg : ¬q.val ≤ g.val := by omega
  have hnhq : ¬h.val ≤ q.val := by omega
  simp only [gapDifferenceRootPoint, dif_neg hnqg, dif_neg hnhq]
  exact (Classical.choose_spec (exists_gapDifferenceCombination_root_in_middleGap
    nodes g h q hgh hgq hqh)).1

lemma gapDifferenceCombination_eval_rootPoint {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) :
    (gapDifferenceCombination nodes g h).eval
      (gapDifferenceRootPoint nodes g h hgh q) = 0 := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg,
      gapDifferenceCombination_eval_node nodes g h hgh]
    simp [hqg]
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq,
        gapDifferenceCombination_eval_node nodes g h hgh]
      simp [hhq]
    · have hgq : g < q := by exact Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
      have hqh : q < h := by exact Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
      simp only [gapDifferenceRootPoint, dif_neg hqg, dif_neg hhq]
      exact (Classical.choose_spec (exists_gapDifferenceCombination_root_in_middleGap
        nodes g h q hgh hgq hqh)).2

lemma gapDifferenceRootPoint_mem_closedGap {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1)) :
    gapDifferenceRootPoint nodes g h hgh q ∈ closedGap nodes q := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg]
    exact ⟨le_rfl, (gap_left_lt_right nodes q).le⟩
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq]
      exact ⟨(gap_left_lt_right nodes q).le, le_rfl⟩
    · have hgq : g < q := Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
      have hqh : q < h := Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
      have hopen := gapDifferenceRootPoint_mem_openGap_of_between
        nodes g h hgh q hgq hqh
      exact ⟨hopen.1.le, hopen.2.le⟩

lemma gapDifferenceRootPoint_lt_right_of_lt {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hqh : q < h) :
    gapDifferenceRootPoint nodes g h hgh q < nodes.point (gapRightIndex q) := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg]
    exact gap_left_lt_right nodes q
  · have hgq : g < q := Fin.lt_def.mpr (Nat.lt_of_not_ge hqg)
    exact (gapDifferenceRootPoint_mem_openGap_of_between nodes g h hgh q hgq hqh).2

lemma left_lt_gapDifferenceRootPoint_of_lt {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : Fin (n - 1))
    (hgq : g < q) :
    nodes.point (gapLeftIndex q) < gapDifferenceRootPoint nodes g h hgh q := by
  by_cases hhq : h.val ≤ q.val
  · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq]
    exact gap_left_lt_right nodes q
  · have hqh : q < h := Fin.lt_def.mpr (Nat.lt_of_not_ge hhq)
    exact (gapDifferenceRootPoint_mem_openGap_of_between nodes g h hgh q hgq hqh).1

lemma gapDifferenceRootPoint_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictMono (gapDifferenceRootPoint nodes g h hgh) := by
  intro q r hqr
  by_cases hqh : q < h
  · calc
      gapDifferenceRootPoint nodes g h hgh q < nodes.point (gapRightIndex q) :=
        gapDifferenceRootPoint_lt_right_of_lt nodes g h hgh q hqh
      _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ ≤ gapDifferenceRootPoint nodes g h hgh r :=
        (gapDifferenceRootPoint_mem_closedGap nodes g h hgh r).1
  · have hhq : h ≤ q := le_of_not_gt hqh
    have hgr : g < r := hgh.trans_le (hhq.trans hqr.le)
    calc
      gapDifferenceRootPoint nodes g h hgh q ≤ nodes.point (gapRightIndex q) :=
        (gapDifferenceRootPoint_mem_closedGap nodes g h hgh q).2
      _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ < gapDifferenceRootPoint nodes g h hgh r :=
        left_lt_gapDifferenceRootPoint_of_lt nodes g h hgh r hgr

/-- Sharp root count for the source difference combination: its `n-1`
listed roots exhaust the multiset, so all are simple. -/
lemma roots_gapDifferenceCombination {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    (gapDifferenceCombination nodes g h).roots =
      (Finset.univ.image (gapDifferenceRootPoint nodes g h hgh)).val := by
  let S : Finset ℝ :=
    Finset.univ.image (gapDifferenceRootPoint nodes g h hgh)
  have hScard : S.card = n - 1 := by
    rw [Finset.card_image_of_injOn
      (gapDifferenceRootPoint_strictMono nodes g h hgh).injective.injOn,
      Finset.card_univ, Fintype.card_fin]
  have hnatDegree : (gapDifferenceCombination nodes g h).natDegree ≤ n - 1 := by
    have hdegree := degree_gapDifferenceCombination_le nodes g h
    rw [Polynomial.degree_eq_natDegree
      (gapDifferenceCombination_ne_zero nodes g h hgh)] at hdegree
    exact_mod_cast hdegree
  apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨q, _hq, rfl⟩
    exact gapDifferenceCombination_eval_rootPoint nodes g h hgh q
  · rw [hScard]
    exact hnatDegree
  · exact gapDifferenceCombination_ne_zero nodes g h hgh

lemma gapSumCombination_ne_zero {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    gapSumCombination nodes g h ≠ 0 := by
  let k : Fin n := gapLeftIndex g
  have houtside : k.val ≤ g.val ∨ h.val < k.val := by
    exact Or.inl (by simp only [k, gapLeftIndex_val]; exact le_rfl)
  have heval := gapSumCombination_eval_node nodes g h hgh k
  rw [if_pos houtside] at heval
  intro hzero
  rw [hzero, Polynomial.eval_zero] at heval
  have hcoeff := gapCoefficient_ne_zero g k
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_ne_zero htwo hcoeff) heval.symm

/-- The sum combination has a root in every nodal gap outside the closed
index block from `g` through `h`. -/
theorem exists_gapSumCombination_root_in_outerGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1))
    (hgh : g < h) (hq : q < g ∨ h < q) :
    ∃ r ∈ openGap nodes q, (gapSumCombination nodes g h).eval r = 0 := by
  let P : ℝ[X] := gapSumCombination nodes g h
  let a : ℝ := nodes.point (gapLeftIndex q)
  let b : ℝ := nodes.point (gapRightIndex q)
  have hleftOutside : (gapLeftIndex q).val ≤ g.val ∨
      h.val < (gapLeftIndex q).val := by
    rcases hq with hqg | hhq
    · exact Or.inl (by simp only [gapLeftIndex_val]; omega)
    · exact Or.inr (by simp only [gapLeftIndex_val]; omega)
  have hrightOutside : (gapRightIndex q).val ≤ g.val ∨
      h.val < (gapRightIndex q).val := by
    rcases hq with hqg | hhq
    · exact Or.inl (by simp only [gapRightIndex_val]; omega)
    · exact Or.inr (by simp only [gapRightIndex_val]; omega)
  have ha : P.eval a = 2 * gapCoefficient g (gapLeftIndex q) := by
    simpa only [P, a, if_pos hleftOutside] using
      gapSumCombination_eval_node nodes g h hgh (gapLeftIndex q)
  have hb : P.eval b = -(2 * gapCoefficient g (gapLeftIndex q)) := by
    have hqg : q ≠ g := by rcases hq with hqg | hhq <;> omega
    calc
      P.eval b = 2 * gapCoefficient g (gapRightIndex q) := by
        simpa only [P, b, if_pos hrightOutside] using
          gapSumCombination_eval_node nodes g h hgh (gapRightIndex q)
      _ = -(2 * gapCoefficient g (gapLeftIndex q)) := by
        rw [gapCoefficient_right_eq_neg_left_of_ne g q hqg]
        ring
  have hab : a ≤ b := (gap_left_lt_right nodes q).le
  have hcont : ContinuousOn (fun x => P.eval x) (Set.Icc a b) :=
    P.continuous.continuousOn
  rcases gapCoefficient_eq_one_or_neg_one g (gapLeftIndex q) with hc | hc
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo' hab hcont hz
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := by
      rw [ha, hb, hc]
      norm_num
    exact intermediate_value_Ioo hab hcont hz

/-- A complete source-count list of `n-2` distinct roots of the sum
combination.  The omitted gap index is `h`: outside the block the entry is
an IVT root, while inside the block it is the right nodal endpoint. -/
def gapSumRootPoint {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : OtherGapIndex h) : ℝ :=
  if hqg : q.1 < g then
    Classical.choose (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))
  else if hhq : h < q.1 then
    Classical.choose (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inr hhq))
  else
    nodes.point (gapRightIndex q.1)

lemma gapSumRootPoint_mem_openGap_of_outer {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hq : q.1 < g ∨ h < q.1) :
    gapSumRootPoint nodes g h hgh q ∈ openGap nodes q.1 := by
  rcases hq with hqg | hhq
  · simp only [gapSumRootPoint, dif_pos hqg]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))).1
  · have hnqg : ¬q.1 < g := by omega
    simp only [gapSumRootPoint, dif_neg hnqg, dif_pos hhq]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inr hhq))).1

lemma gapSumRootPoint_eq_right_of_between {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hgq : g ≤ q.1) (hqh : q.1 < h) :
    gapSumRootPoint nodes g h hgh q = nodes.point (gapRightIndex q.1) := by
  have hnqg : ¬q.1 < g := not_lt.mpr hgq
  have hnhq : ¬h < q.1 := not_lt.mpr hqh.le
  simp [gapSumRootPoint, hnqg, hnhq]

lemma gapSumCombination_eval_rootPoint {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) :
    (gapSumCombination nodes g h).eval
      (gapSumRootPoint nodes g h hgh q) = 0 := by
  by_cases hqg : q.1 < g
  · simp only [gapSumRootPoint, dif_pos hqg]
    exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
      nodes g h q.1 hgh (Or.inl hqg))).2
  · by_cases hhq : h < q.1
    · simp only [gapSumRootPoint, dif_neg hqg, dif_pos hhq]
      exact (Classical.choose_spec (exists_gapSumCombination_root_in_outerGap
        nodes g h q.1 hgh (Or.inr hhq))).2
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh,
        gapSumCombination_eval_node nodes g h hgh]
      simp only [gapRightIndex_val]
      split_ifs with houtside
      · rcases houtside with houtside | houtside <;> omega
      · simp [houtside]
        intro h
        rcases h with h | h <;> omega

lemma gapSumRootPoint_mem_closedGap {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (q : OtherGapIndex h) :
    gapSumRootPoint nodes g h hgh q ∈ closedGap nodes q.1 := by
  by_cases hqg : q.1 < g
  · have hopen := gapSumRootPoint_mem_openGap_of_outer
      nodes g h hgh q (Or.inl hqg)
    exact ⟨hopen.1.le, hopen.2.le⟩
  · by_cases hhq : h < q.1
    · have hopen := gapSumRootPoint_mem_openGap_of_outer
        nodes g h hgh q (Or.inr hhq)
      exact ⟨hopen.1.le, hopen.2.le⟩
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
      exact ⟨(gap_left_lt_right nodes q.1).le, le_rfl⟩

lemma gapSumRootPoint_lt_right_of_outer {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hq : q.1 < g ∨ h < q.1) :
    gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
  (gapSumRootPoint_mem_openGap_of_outer nodes g h hgh q hq).2

lemma left_lt_gapSumRootPoint_of_g_le {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : OtherGapIndex h) (hgq : g ≤ q.1) :
    nodes.point (gapLeftIndex q.1) < gapSumRootPoint nodes g h hgh q := by
  by_cases hhq : h < q.1
  · exact (gapSumRootPoint_mem_openGap_of_outer
      nodes g h hgh q (Or.inr hhq)).1
  · have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
    rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
    exact gap_left_lt_right nodes q.1

lemma gapSumRootPoint_strictMono {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictMono (gapSumRootPoint nodes g h hgh) := by
  intro q r hqr
  have hqrval : q.1 < r.1 := hqr
  by_cases hqg : q.1 < g
  · calc
      gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
        gapSumRootPoint_lt_right_of_outer nodes g h hgh q (Or.inl hqg)
      _ ≤ nodes.point (gapLeftIndex r.1) := nodes.strictMono.monotone <| by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      _ ≤ gapSumRootPoint nodes g h hgh r :=
        (gapSumRootPoint_mem_closedGap nodes g h hgh r).1
  · by_cases hhq : h < q.1
    · calc
        gapSumRootPoint nodes g h hgh q < nodes.point (gapRightIndex q.1) :=
          gapSumRootPoint_lt_right_of_outer nodes g h hgh q (Or.inr hhq)
        _ ≤ nodes.point (gapLeftIndex r.1) := nodes.strictMono.monotone <| by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        _ ≤ gapSumRootPoint nodes g h hgh r :=
          (gapSumRootPoint_mem_closedGap nodes g h hgh r).1
    · have hgq : g ≤ q.1 := le_of_not_gt hqg
      have hqh : q.1 < h := lt_of_le_of_ne (le_of_not_gt hhq) q.property
      have hgr : g ≤ r.1 := hgq.trans hqrval.le
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh q hgq hqh]
      calc
        nodes.point (gapRightIndex q.1) ≤ nodes.point (gapLeftIndex r.1) :=
          nodes.strictMono.monotone <| by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val, gapLeftIndex_val]
            omega
        _ < gapSumRootPoint nodes g h hgh r :=
          left_lt_gapSumRootPoint_of_g_le nodes g h hgh r hgr

/-- The source sum combination has at least `n-2` distinct real roots.
Together with its degree bound, this leaves exactly one possible additional
degree/multiplicity slot. -/
lemma sub_two_le_card_gapSumCombination_roots_toFinset {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    n - 2 ≤ (gapSumCombination nodes g h).roots.toFinset.card := by
  let P : ℝ[X] := gapSumCombination nodes g h
  let f : OtherGapIndex h → P.roots.toFinset := fun q =>
    ⟨gapSumRootPoint nodes g h hgh q, by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots
        (gapSumCombination_ne_zero nodes g h hgh)]
      exact gapSumCombination_eval_rootPoint nodes g h hgh q⟩
  rw [← card_otherGapIndex h]
  simpa only [Fintype.card_coe] using
    (Fintype.card_le_of_injective f fun q r heq =>
      (gapSumRootPoint_strictMono nodes g h hgh).injective
        (congrArg Subtype.val heq))

lemma natDegree_gapSumCombination_le_sub_one {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    (gapSumCombination nodes g h).natDegree ≤ n - 1 := by
  have hdegree := degree_gapSumCombination_le nodes g h
  rw [Polynomial.degree_eq_natDegree
    (gapSumCombination_ne_zero nodes g h hgh)] at hdegree
  exact_mod_cast hdegree

/-- Exact one-slot budget for the source sum polynomial's real roots. -/
lemma card_gapSumCombination_roots_le_toFinset_card_add_one {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    (gapSumCombination nodes g h).roots.card ≤
      (gapSumCombination nodes g h).roots.toFinset.card + 1 := by
  have hn : 2 ≤ n := by
    have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
    omega
  have hdistinct := sub_two_le_card_gapSumCombination_roots_toFinset
    nodes g h hgh
  have hmulti : (gapSumCombination nodes g h).roots.card ≤ n - 1 :=
    (Polynomial.card_roots' _).trans
      (natDegree_gapSumCombination_le_sub_one nodes g h hgh)
  omega

private lemma neg_one_pow_card_filter_mul_prod_pos {α : Type*}
    [DecidableEq α] (s : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → ℝ) (hneg : ∀ x ∈ s, p x → f x < 0)
    (hpos : ∀ x ∈ s, ¬p x → 0 < f x) :
    0 < (-1 : ℝ) ^ (s.filter p).card * ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
      have ih' := ih (fun y hy => hneg y (Finset.mem_insert_of_mem hy))
        (fun y hy => hpos y (Finset.mem_insert_of_mem hy))
      by_cases hpx : p x
      · have hfx : f x < 0 := hneg x (Finset.mem_insert_self x s) hpx
        have hxfilter : x ∉ s.filter p := by simp [hxs]
        rw [Finset.filter_insert, if_pos hpx,
          Finset.card_insert_of_notMem hxfilter, pow_succ,
          Finset.prod_insert hxs]
        nlinarith
      · have hfx : 0 < f x := hpos x (Finset.mem_insert_self x s) hpx
        rw [Finset.filter_insert, if_neg hpx, Finset.prod_insert hxs]
        calc
          0 < ((-1 : ℝ) ^ (s.filter p).card * ∏ y ∈ s, f y) * f x :=
            mul_pos ih' hfx
          _ = (-1 : ℝ) ^ (s.filter p).card * (f x * ∏ y ∈ s, f y) := by ring

private lemma card_filter_middle_otherGapIndex {n : ℕ}
    (g h : Fin (n - 1)) :
    ((Finset.univ : Finset (OtherGapIndex h)).filter
      (fun q => g ≤ q.1 ∧ q.1 < h)).card = h.val - g.val := by
  let S := (Finset.univ : Finset (OtherGapIndex h)).filter
    (fun q => g ≤ q.1 ∧ q.1 < h)
  have himage : S.image (fun q => q.1) = Finset.Ico g h := by
    ext q
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨r, ⟨hgr, hrh⟩, rfl⟩
      exact ⟨hgr, hrh⟩
    · intro hq
      exact ⟨⟨q, ne_of_lt hq.2⟩, ⟨hq.1, hq.2⟩, rfl⟩
  calc
    S.card = (S.image (fun q => q.1)).card := by
      rw [Finset.card_image_of_injective S Subtype.val_injective]
    _ = (Finset.Ico g h).card := congrArg Finset.card himage
    _ = h.val - g.val := by simp

private lemma ne_gapSumRootPoint_of_mem_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (q : Fin (n - 1)) (hgq : g ≤ q) (hqh : q < h) {x : ℝ}
    (hx : x ∈ openGap nodes q) (k : OtherGapIndex h) :
    x ≠ gapSumRootPoint nodes g h hgh k := by
  by_cases hkg : k.1 < g
  · have hkq : k.1 < q := hkg.trans_le hgq
    exact (openGap_point_lt_of_gap_lt nodes hkq
      (gapSumRootPoint_mem_openGap_of_outer nodes g h hgh k (Or.inl hkg)) hx).ne'
  · by_cases hhk : h < k.1
    · have hqk : q < k.1 := hqh.trans hhk
      exact (openGap_point_lt_of_gap_lt nodes hqk hx
        (gapSumRootPoint_mem_openGap_of_outer nodes g h hgh k (Or.inr hhk))).ne
    · have hgk : g ≤ k.1 := le_of_not_gt hkg
      have hkh : k.1 < h := lt_of_le_of_ne (le_of_not_gt hhk) k.property
      rw [gapSumRootPoint_eq_right_of_between nodes g h hgh k hgk hkh]
      rcases lt_trichotomy k.1 q with hkq | hkq | hqk
      · have hindex : gapRightIndex k.1 ≤ gapLeftIndex q := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        exact (lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1).ne'
      · rw [hkq]
        exact hx.2.ne
      · have hindex : gapRightIndex q ≤ gapRightIndex k.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val]
          omega
        exact (hx.2.trans_le (nodes.strictMono.monotone hindex)).ne

/-- The parity step in the source proof of `(5f)`: after factoring the
`n-2` listed roots from the sum combination, its remaining linear-or-
constant quotient has no root in the middle block.  Consequently the sum
combination has no root in any open nodal gap strictly inside that block. -/
theorem not_isRoot_gapSumCombination_of_mem_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hgq : g ≤ q) (hqh : q < h) {x : ℝ} (hx : x ∈ openGap nodes q) :
    ¬(gapSumCombination nodes g h).IsRoot x := by
  classical
  let P : ℝ[X] := gapSumCombination nodes g h
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let D : ℝ[X] := ∏ k : OtherGapIndex h, (X - C (root k))
  have hP : P ≠ 0 := gapSumCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapSumRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro k
      rw [Polynomial.dvd_iff_isRoot]
      exact gapSumCombination_eval_rootPoint nodes g h hgh k
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (root k)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_otherGapIndex]
  have hQdegree : Q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      simpa only [P] using natDegree_gapSumCombination_le_sub_one nodes g h hgh
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega

  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (b - root k)
  let middle : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < h
  have hpairNeg : ∀ k : OtherGapIndex h, middle k → pairValue k < 0 := by
    intro k hk
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk.2
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootb : root k < b := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapRightIndex_val]
      omega
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootb)
  have hpairPos : ∀ k : OtherGapIndex h, ¬middle k → 0 < pairValue k := by
    intro k hk
    have hkouter : k.1 < g ∨ h < k.1 := by
      by_cases hkg : k.1 < g
      · exact Or.inl hkg
      · right
        have hgk : g ≤ k.1 := le_of_not_gt hkg
        have hnotlt : ¬k.1 < h := fun hlt => hk ⟨hgk, hlt⟩
        exact lt_of_le_of_ne (le_of_not_gt hnotlt) k.property.symm
    rcases hkouter with hkg | hhk
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hab))
    · have hbroot : b < root k := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inr hhk)
        have hindex : gapRightIndex h ≤ gapLeftIndex k.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          b = nodes.point (gapRightIndex h) := rfl
          _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
          _ < root k := by simpa only [root] using hmem.1
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans hbroot))
        (sub_neg.mpr hbroot)
  have hpairProduct :
      0 < gapPairParity g h * ∏ k : OtherGapIndex h, pairValue k := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) middle pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_middle_otherGapIndex g h] at hsign
    simpa [gapPairParity] using hsign
  have hDevalProduct :
      0 < gapPairParity g h * (D.eval a * D.eval b) := by
    have heq : D.eval a * D.eval b = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, pairValue]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    exact hpairProduct
  have hPa : P.eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hPb : P.eval b = 2 * gapPairParity g h := by
    have houtside : (gapRightIndex h).val ≤ g.val ∨
        h.val < (gapRightIndex h).val := Or.inr (by simp)
    have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapRightIndex h)
    have hhval : h.val < (gapRightIndex h).val := by simp
    rw [if_pos houtside,
      gapCoefficient_of_lt h (gapRightIndex h) hhval] at hrel
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside, hrel.symm]
    simp only [gapRightIndex_val]
    norm_num
  have hPevalProduct : 0 < gapPairParity g h * (P.eval a * P.eval b) := by
    rw [hPa, hPb]
    nlinarith [sq_gapPairParity g h]
  have hQevalProduct : 0 < Q.eval a * Q.eval b := by
    have hfactor : gapPairParity g h * (P.eval a * P.eval b) =
        (gapPairParity g h * (D.eval a * D.eval b)) * (Q.eval a * Q.eval b) := by
      rw [hQ]
      simp only [Polynomial.eval_mul]
      ring
    have hmul : 0 < (gapPairParity g h * (D.eval a * D.eval b)) *
        (Q.eval a * Q.eval b) := by rwa [← hfactor]
    rcases mul_pos_iff.mp hmul with hgood | hbad
    · exact hgood.2
    · exact (hDevalProduct.not_gt hbad.1).elim
  have hax : a < x := by
    have hindex : gapLeftIndex g ≤ gapLeftIndex q := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapLeftIndex_val]
      omega
    exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
  have hxb : x < b := by
    have hindex : gapRightIndex q ≤ gapRightIndex h := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val]
      omega
    exact hx.2.trans_le (nodes.strictMono.monotone hindex)
  have hQNoRoot : ¬Q.IsRoot x := by
    intro hxroot
    obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hxroot
    have hRne : R ≠ 0 := by
      intro hzero
      apply hQne
      rw [hzero, mul_zero] at hR
      exact hR
    have hRdegree : R.natDegree = 0 := by
      have hnat := congrArg Polynomial.natDegree hR
      rw [Polynomial.natDegree_mul (X_sub_C_ne_zero x) hRne,
        natDegree_X_sub_C] at hnat
      omega
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hRdegree
    have hc : c ≠ 0 := by
      intro hc
      apply hQne
      simpa [hc] using hR
    have hQprodNeg : Q.eval a * Q.eval b < 0 := by
      rw [hR]
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      calc
        (a - x) * c * ((b - x) * c) =
            ((a - x) * (b - x)) * c ^ 2 := by ring
        _ < 0 := mul_neg_of_neg_of_pos
          (mul_neg_of_neg_of_pos (sub_neg.mpr hax) (sub_pos.mpr hxb))
          (sq_pos_of_ne_zero hc)
    exact hQevalProduct.not_gt hQprodNeg
  intro hxP
  have hQx : Q.eval x ≠ 0 := hQNoRoot
  have hDx : D.eval x = 0 := by
    have hxzero : P.eval x = 0 := by
      simpa only [P, Polynomial.IsRoot] using hxP
    rw [hQ, Polynomial.eval_mul] at hxzero
    exact (mul_eq_zero.mp hxzero).resolve_right hQx
  have hprod : ∏ k : OtherGapIndex h, (x - root k) = 0 := by
    simpa only [D, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] using hDx
  rcases Finset.prod_eq_zero_iff.mp hprod with ⟨k, _hk, hkzero⟩
  exact ne_gapSumRootPoint_of_mem_middleGap nodes g h hgh q hgq hqh hx k
    (by simpa only [root] using sub_eq_zero.mp hkzero)

private lemma ne_gapDifferenceRootPoint_of_mem_outerGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hq : q < g ∨ h < q) {x : ℝ} (hx : x ∈ openGap nodes q)
    (r : Fin (n - 1)) :
    x ≠ gapDifferenceRootPoint nodes g h hgh r := by
  rcases lt_trichotomy r q with hrq | hrq | hqr
  · have hindex : gapRightIndex r ≤ gapLeftIndex q := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val, gapLeftIndex_val]
      omega
    exact (lt_of_le_of_lt
      ((gapDifferenceRootPoint_mem_closedGap nodes g h hgh r).2.trans
        (nodes.strictMono.monotone hindex)) hx.1).ne'
  · subst r
    rcases hq with hqg | hhq
    · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg.le]
      exact hx.1.ne'
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq.le]
      exact hx.2.ne
  · have hindex : gapRightIndex q ≤ gapLeftIndex r := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val, gapLeftIndex_val]
      omega
    exact (hx.2.trans_le <| (nodes.strictMono.monotone hindex).trans <|
      (gapDifferenceRootPoint_mem_closedGap nodes g h hgh r).1).ne

/-- The exact `n-1` root count for the difference combination rules out any
interior root in an outer shared nodal gap.  These are precisely the gaps
used for source `(5a--e)`. -/
theorem not_isRoot_gapDifferenceCombination_of_mem_outerGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hq : q < g ∨ h < q) {x : ℝ} (hx : x ∈ openGap nodes q) :
    ¬(gapDifferenceCombination nodes g h).IsRoot x := by
  intro hxroot
  have hxmem : x ∈ (gapDifferenceCombination nodes g h).roots :=
    (Polynomial.mem_roots (gapDifferenceCombination_ne_zero nodes g h hgh)).mpr hxroot
  rw [roots_gapDifferenceCombination nodes g h hgh] at hxmem
  have hximage : x ∈ Finset.univ.image
      (gapDifferenceRootPoint nodes g h hgh) := by
    exact hxmem
  rcases Finset.mem_image.mp hximage with ⟨r, _hr, hrx⟩
  exact ne_gapDifferenceRootPoint_of_mem_outerGap nodes g h q hgh hq hx r hrx.symm

private lemma eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos
    (Q : ℝ[X]) {a b x : ℝ} (hdegree : Q.natDegree ≤ 1)
    (hprod : 0 < Q.eval a * Q.eval b) (hx : x ∈ Set.Ioo a b) :
    Q.eval x ≠ 0 := by
  intro hxzero
  have hxroot : Q.IsRoot x := hxzero
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hxroot
  have hQne : Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hprod
    norm_num at hprod
  have hRne : R ≠ 0 := by
    intro hzero
    apply hQne
    rw [hzero, mul_zero] at hR
    exact hR
  have hRdegree : R.natDegree = 0 := by
    have hnat := congrArg Polynomial.natDegree hR
    rw [Polynomial.natDegree_mul (X_sub_C_ne_zero x) hRne,
      natDegree_X_sub_C] at hnat
    omega
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hRdegree
  have hc : c ≠ 0 := by
    intro hc
    apply hQne
    simpa [hc] using hR
  have hQprodNeg : Q.eval a * Q.eval b < 0 := by
    rw [hR]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    calc
      (a - x) * c * ((b - x) * c) =
          ((a - x) * (b - x)) * c ^ 2 := by ring
      _ < 0 := mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (sub_neg.mpr hx.1) (sub_pos.mpr hx.2))
        (sq_pos_of_ne_zero hc)
  exact hprod.not_gt hQprodNeg

private lemma eval_mul_eval_pos_of_no_root_between (P : ℝ[X])
    {a b : ℝ} (hab : a < b) (ha : P.eval a ≠ 0) (hb : P.eval b ≠ 0)
    (hroot : ∀ {x : ℝ}, x ∈ Set.Ioo a b → ¬P.IsRoot x) :
    0 < P.eval a * P.eval b := by
  have hprodne : P.eval a * P.eval b ≠ 0 := mul_ne_zero ha hb
  apply lt_of_le_of_ne (le_of_not_gt fun hneg => ?_) hprodne.symm
  rcases mul_neg_iff.mp hneg with hsign | hsign
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval b) (P.eval a) :=
      ⟨hsign.2, hsign.1⟩
    obtain ⟨x, hx, hxzero⟩ := intermediate_value_Ioo' hab.le
      P.continuous.continuousOn hz
    exact hroot hx hxzero
  · have hz : (0 : ℝ) ∈ Set.Ioo (P.eval a) (P.eval b) := hsign
    obtain ⟨x, hx, hxzero⟩ := intermediate_value_Ioo hab.le
      P.continuous.continuousOn hz
    exact hroot hx hxzero

/-- Product of the `n-2` explicitly listed roots of the sum combination. -/
def gapSumRootProduct {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : ℝ[X] :=
  ∏ k : OtherGapIndex h, (X - C (gapSumRootPoint nodes g h hgh k))

/-- Reusable checked factor data behind the source's parity argument. -/
structure GapSumFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) where
  quotient : ℝ[X]
  factor : gapSumCombination nodes g h =
    gapSumRootProduct nodes g h hgh * quotient
  quotient_ne_zero : quotient ≠ 0
  quotient_natDegree_le_one : quotient.natDegree ≤ 1
  quotient_endpoint_product_pos :
    0 < quotient.eval (nodes.point (gapLeftIndex g)) *
      quotient.eval (nodes.point (gapRightIndex h))

private theorem exists_gapSumFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    Nonempty (GapSumFactorData nodes g h hgh) := by
  classical
  let P : ℝ[X] := gapSumCombination nodes g h
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let D : ℝ[X] := gapSumRootProduct nodes g h hgh
  have hP : P ≠ 0 := gapSumCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapSumRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro k
      rw [Polynomial.dvd_iff_isRoot]
      exact gapSumCombination_eval_rootPoint nodes g h hgh k
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (root k)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 2 := by
    change (∏ k ∈ (Finset.univ : Finset (OtherGapIndex h)),
      (X - C (root k))).natDegree = n - 2
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      card_otherGapIndex]
  have hQdegree : Q.natDegree ≤ 1 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      simpa only [P] using natDegree_gapSumCombination_le_sub_one nodes g h hgh
    have hn : 2 ≤ n := by
      have hsub : 0 < n - 1 := lt_of_le_of_lt (Nat.zero_le _) g.isLt
      omega
    omega
  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (b - root k)
  let middle : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < h
  have hpairNeg : ∀ k : OtherGapIndex h, middle k → pairValue k < 0 := by
    intro k hk
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk.2
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootb : root k < b := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapRightIndex_val]
      omega
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootb)
  have hpairPos : ∀ k : OtherGapIndex h, ¬middle k → 0 < pairValue k := by
    intro k hk
    have hkouter : k.1 < g ∨ h < k.1 := by
      by_cases hkg : k.1 < g
      · exact Or.inl hkg
      · right
        have hgk : g ≤ k.1 := le_of_not_gt hkg
        have hnotlt : ¬k.1 < h := fun hlt => hk ⟨hgk, hlt⟩
        exact lt_of_le_of_ne (le_of_not_gt hnotlt) k.property.symm
    rcases hkouter with hkg | hhk
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hab))
    · have hbroot : b < root k := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inr hhk)
        have hindex : gapRightIndex h ≤ gapLeftIndex k.1 := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          b = nodes.point (gapRightIndex h) := rfl
          _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
          _ < root k := by simpa only [root] using hmem.1
      have hab : a < b := by
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hab.trans hbroot))
        (sub_neg.mpr hbroot)
  have hpairProduct :
      0 < gapPairParity g h * ∏ k : OtherGapIndex h, pairValue k := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) middle pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_middle_otherGapIndex g h] at hsign
    simpa [gapPairParity] using hsign
  have hDevalProduct : 0 < gapPairParity g h * (D.eval a * D.eval b) := by
    have heq : D.eval a * D.eval b = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, gapSumRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    exact hpairProduct
  have hPa : P.eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hPb : P.eval b = 2 * gapPairParity g h := by
    have houtside : (gapRightIndex h).val ≤ g.val ∨
        h.val < (gapRightIndex h).val := Or.inr (by simp)
    have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapRightIndex h)
    have hhval : h.val < (gapRightIndex h).val := by simp
    rw [if_pos houtside,
      gapCoefficient_of_lt h (gapRightIndex h) hhval] at hrel
    rw [show P = gapSumCombination nodes g h from rfl,
      gapSumCombination_eval_node nodes g h hgh, if_pos houtside, hrel.symm]
    simp only [gapRightIndex_val]
    norm_num
  have hPevalProduct : 0 < gapPairParity g h * (P.eval a * P.eval b) := by
    rw [hPa, hPb]
    nlinarith [sq_gapPairParity g h]
  have hQevalProduct : 0 < Q.eval a * Q.eval b := by
    have hfactor : gapPairParity g h * (P.eval a * P.eval b) =
        (gapPairParity g h * (D.eval a * D.eval b)) * (Q.eval a * Q.eval b) := by
      rw [hQ]
      simp only [Polynomial.eval_mul]
      ring
    have hmul : 0 < (gapPairParity g h * (D.eval a * D.eval b)) *
        (Q.eval a * Q.eval b) := by rwa [← hfactor]
    rcases mul_pos_iff.mp hmul with hgood | hbad
    · exact hgood.2
    · exact (hDevalProduct.not_gt hbad.1).elim
  refine ⟨⟨Q, ?_, hQne, hQdegree, ?_⟩⟩
  · simpa only [P, D] using hQ
  · simpa only [a, b] using hQevalProduct

/-- Every internal nodal root listed for the sum combination is simple. -/
theorem rootMultiplicity_gapSumCombination_internal_node {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hgq : g ≤ q) (hqh : q < h) :
    (gapSumCombination nodes g h).rootMultiplicity
      (nodes.point (gapRightIndex q)) = 1 := by
  classical
  let k : OtherGapIndex h := ⟨q, ne_of_lt hqh⟩
  let r : ℝ := nodes.point (gapRightIndex q)
  let data := Classical.choice (exists_gapSumFactorData nodes g h hgh)
  let Q : ℝ[X] := data.quotient
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let rest : ℝ[X] := ∏ j ∈ ({k}ᶜ : Finset (OtherGapIndex h)),
    (X - C (root j))
  have hrootk : root k = r := by
    simpa only [root, k, r] using gapSumRootPoint_eq_right_of_between
      nodes g h hgh k hgq hqh
  have ha_r : nodes.point (gapLeftIndex g) < r := by
    apply nodes.strictMono
    apply Fin.lt_def.mpr
    simp only [gapLeftIndex_val, gapRightIndex_val]
    omega
  have hr_b : r < nodes.point (gapRightIndex h) := by
    apply nodes.strictMono
    apply Fin.lt_def.mpr
    simp only [gapRightIndex_val]
    omega
  have hQr : Q.eval r ≠ 0 := by
    exact eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨ha_r, hr_b⟩
  have hrootInjective : Function.Injective root :=
    (gapSumRootPoint_strictMono nodes g h hgh).injective
  have hrestEval : rest.eval r ≠ 0 := by
    simp only [rest, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjne : j ≠ k := by simpa using hj
    rw [← hrootk]
    exact sub_ne_zero.mpr (hrootInjective.ne hjne).symm
  have hfactor : gapSumCombination nodes g h = (X - C r) * (rest * Q) := by
    rw [data.factor, gapSumRootProduct,
      Fintype.prod_eq_mul_prod_compl k]
    change ((X - C (root k)) * ∏ j ∈ ({k}ᶜ : Finset (OtherGapIndex h)),
      (X - C (root j))) * Q = (X - C r) * (rest * Q)
    rw [hrootk]
    dsimp only [rest]
    ring
  have hrestQeval : (rest * Q).eval r ≠ 0 := by
    simp only [Polynomial.eval_mul]
    exact mul_ne_zero hrestEval hQr
  have hrestQne : rest * Q ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.eval_zero] at hrestQeval
    exact hrestQeval rfl
  have hmultRest : (rest * Q).rootMultiplicity r = 0 := by
    apply Polynomial.rootMultiplicity_eq_zero
    rw [Polynomial.IsRoot]
    exact hrestQeval
  rw [hfactor, Polynomial.rootMultiplicity_mul
    (mul_ne_zero (X_sub_C_ne_zero r) hrestQne),
    Polynomial.rootMultiplicity_X_sub_C_self, hmultRest]

private lemma card_filter_between_otherGapIndex {n : ℕ}
    (h g u : Fin (n - 1)) (huh : u < h) :
    ((Finset.univ : Finset (OtherGapIndex h)).filter
      (fun k => g ≤ k.1 ∧ k.1 < u)).card = u.val - g.val := by
  let S := (Finset.univ : Finset (OtherGapIndex h)).filter
    (fun k => g ≤ k.1 ∧ k.1 < u)
  have himage : S.image (fun k => k.1) = Finset.Ico g u := by
    ext k
    simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hgj, hju⟩, rfl⟩
      exact ⟨hgj, hju⟩
    · intro hk
      exact ⟨⟨k, ne_of_lt (hk.2.trans huh)⟩, ⟨hk.1, hk.2⟩, rfl⟩
  calc
    S.card = (S.image (fun k => k.1)).card := by
      rw [Finset.card_image_of_injective S Subtype.val_injective]
    _ = (Finset.Ico g u).card := congrArg Finset.card himage
    _ = u.val - g.val := by simp

/-- Source `(5f)` sign on every middle gap. -/
theorem gapSumCombination_sign_middleGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hgq : g ≤ q) (hqh : q < h) {x : ℝ} (hx : x ∈ openGap nodes q) :
    0 < (-1 : ℝ) ^ (q.val - g.val) *
      (gapSumCombination nodes g h).eval x := by
  classical
  let data := Classical.choice (exists_gapSumFactorData nodes g h hgh)
  let Q : ℝ[X] := data.quotient
  let D : ℝ[X] := gapSumRootProduct nodes g h hgh
  let root : OtherGapIndex h → ℝ := gapSumRootPoint nodes g h hgh
  let a : ℝ := nodes.point (gapLeftIndex g)
  let b : ℝ := nodes.point (gapRightIndex h)
  have hax : a < x := by
    have hindex : gapLeftIndex g ≤ gapLeftIndex q := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapLeftIndex_val]
      omega
    exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
  have hxb : x < b := by
    have hindex : gapRightIndex q ≤ gapRightIndex h := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val]
      omega
    exact hx.2.trans_le (nodes.strictMono.monotone hindex)
  have hQa : Q.eval a ≠ 0 :=
    left_ne_zero_of_mul (ne_of_gt data.quotient_endpoint_product_pos)
  have hQx : Q.eval x ≠ 0 :=
    eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨hax, hxb⟩
  have hQax : 0 < Q.eval a * Q.eval x := by
    apply eval_mul_eval_pos_of_no_root_between Q hax hQa hQx
    intro z hz hzroot
    have hzne := eval_ne_zero_of_natDegree_le_one_of_endpoint_product_pos Q
      data.quotient_natDegree_le_one data.quotient_endpoint_product_pos
      ⟨hz.1, hz.2.trans hxb⟩
    exact hzne hzroot
  let pairValue : OtherGapIndex h → ℝ := fun k =>
    (a - root k) * (x - root k)
  let before : OtherGapIndex h → Prop := fun k => g ≤ k.1 ∧ k.1 < q
  have hpairNeg : ∀ k : OtherGapIndex h, before k → pairValue k < 0 := by
    intro k hk
    have hk_h : k.1 < h := hk.2.trans hqh
    have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
      simpa only [root] using gapSumRootPoint_eq_right_of_between
        nodes g h hgh k hk.1 hk_h
    have haroot : a < root k := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    have hrootx : root k < x := by
      rw [hrootEq]
      have hindex : gapRightIndex k.1 ≤ gapLeftIndex q := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      exact lt_of_le_of_lt (nodes.strictMono.monotone hindex) hx.1
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr haroot) (sub_pos.mpr hrootx)
  have hpairPos : ∀ k : OtherGapIndex h, ¬before k → 0 < pairValue k := by
    intro k hk
    by_cases hkg : k.1 < g
    · have hroota : root k < a := by
        have hmem := gapSumRootPoint_mem_openGap_of_outer
          nodes g h hgh k (Or.inl hkg)
        have hindex : gapRightIndex k.1 ≤ gapLeftIndex g := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          root k < nodes.point (gapRightIndex k.1) := by simpa only [root] using hmem.2
          _ ≤ nodes.point (gapLeftIndex g) := nodes.strictMono.monotone hindex
          _ = a := rfl
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hroota) (sub_pos.mpr (hroota.trans hax))
    · have hgk : g ≤ k.1 := le_of_not_gt hkg
      have hqk : q ≤ k.1 := by
        by_contra hnot
        exact hk ⟨hgk, lt_of_not_ge hnot⟩
      have hxroot : x < root k := by
        by_cases hhk : h < k.1
        · have hmem := gapSumRootPoint_mem_openGap_of_outer
            nodes g h hgh k (Or.inr hhk)
          have hindex : gapRightIndex q ≤ gapLeftIndex k.1 := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val, gapLeftIndex_val]
            omega
          calc
            x < nodes.point (gapRightIndex q) := hx.2
            _ ≤ nodes.point (gapLeftIndex k.1) := nodes.strictMono.monotone hindex
            _ < root k := by simpa only [root] using hmem.1
        · have hkh : k.1 < h :=
            lt_of_le_of_ne (le_of_not_gt hhk) k.property
          have hrootEq : root k = nodes.point (gapRightIndex k.1) := by
            simpa only [root] using gapSumRootPoint_eq_right_of_between
              nodes g h hgh k hgk hkh
          rw [hrootEq]
          have hindex : gapRightIndex q ≤ gapRightIndex k.1 := by
            apply Fin.le_iff_val_le_val.mpr
            simp only [gapRightIndex_val]
            omega
          exact hx.2.trans_le (nodes.strictMono.monotone hindex)
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hax.trans hxroot))
        (sub_neg.mpr hxroot)
  have hDax : 0 < (-1 : ℝ) ^ (q.val - g.val) * (D.eval a * D.eval x) := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (OtherGapIndex h)) before pairValue
      (fun k _hk => hpairNeg k) (fun k _hk => hpairPos k)
    rw [card_filter_between_otherGapIndex h g q hqh] at hsign
    have heq : D.eval a * D.eval x = ∏ k : OtherGapIndex h, pairValue k := by
      simp only [D, gapSumRootProduct, Polynomial.eval_prod, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    simpa using hsign
  have hPa : (gapSumCombination nodes g h).eval a = 2 := by
    have houtside : (gapLeftIndex g).val ≤ g.val ∨
        h.val < (gapLeftIndex g).val := Or.inl (by simp)
    rw [gapSumCombination_eval_node nodes g h hgh, if_pos houtside,
      gapCoefficient_of_le]
    · simp
    · simp
  have hfactor : gapSumCombination nodes g h = D * Q := by
    simpa only [D, Q] using data.factor
  have htotal : 0 < (-1 : ℝ) ^ (q.val - g.val) *
      ((gapSumCombination nodes g h).eval a *
        (gapSumCombination nodes g h).eval x) := by
    rw [hfactor]
    simp only [Polynomial.eval_mul]
    nlinarith [mul_pos hDax hQax]
  rw [hPa] at htotal
  nlinarith

/-- Monic product over the exhaustive root list of the difference
combination. -/
def gapDifferenceRootProduct {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : ℝ[X] :=
  ∏ q : Fin (n - 1), (X - C (gapDifferenceRootPoint nodes g h hgh q))

/-- Since the difference combination has exactly `n-1` roots and degree at
most `n-1`, it is a nonzero scalar multiple of its monic root product. -/
structure GapDifferenceFactorData {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) where
  scale : ℝ
  scale_ne_zero : scale ≠ 0
  factor : gapDifferenceCombination nodes g h =
    gapDifferenceRootProduct nodes g h hgh * C scale

private theorem exists_gapDifferenceFactorData {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h) :
    Nonempty (GapDifferenceFactorData nodes g h hgh) := by
  classical
  let P : ℝ[X] := gapDifferenceCombination nodes g h
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let D : ℝ[X] := gapDifferenceRootProduct nodes g h hgh
  have hP : P ≠ 0 := gapDifferenceCombination_ne_zero nodes g h hgh
  have hrootInjective : Function.Injective root :=
    (gapDifferenceRootPoint_strictMono nodes g h hgh).injective
  have hDvd : D ∣ P := by
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hrootInjective
    · intro q
      rw [Polynomial.dvd_iff_isRoot]
      exact gapDifferenceCombination_eval_rootPoint nodes g h hgh q
  obtain ⟨Q, hQ⟩ := hDvd
  have hDmonic : D.Monic := by
    change (∏ q ∈ (Finset.univ : Finset (Fin (n - 1))),
      (X - C (root q))).Monic
    exact monic_prod_of_monic _ _ fun q _hq => monic_X_sub_C (root q)
  have hDne : D ≠ 0 := hDmonic.ne_zero
  have hQne : Q ≠ 0 := by
    intro hzero
    apply hP
    rw [hzero, mul_zero] at hQ
    exact hQ
  have hDdegree : D.natDegree = n - 1 := by
    change (∏ q ∈ (Finset.univ : Finset (Fin (n - 1))),
      (X - C (root q))).natDegree = n - 1
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hQdegree : Q.natDegree = 0 := by
    have hnat := congrArg Polynomial.natDegree hQ
    rw [Polynomial.natDegree_mul hDne hQne, hDdegree] at hnat
    have hPdegree : P.natDegree ≤ n - 1 := by
      have hdegree := degree_gapDifferenceCombination_le nodes g h
      rw [Polynomial.degree_eq_natDegree hP] at hdegree
      exact_mod_cast hdegree
    omega
  obtain ⟨c, hcQ⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hc : c ≠ 0 := by
    intro hzero
    apply hQne
    rw [← hcQ, hzero, C_0]
  refine ⟨⟨c, hc, ?_⟩⟩
  calc
    gapDifferenceCombination nodes g h = P := rfl
    _ = D * Q := hQ
    _ = gapDifferenceRootProduct nodes g h hgh * C c := by
      rw [← hcQ]

private lemma card_filter_left_difference_roots {n : ℕ}
    (q g : Fin (n - 1)) :
    ((Finset.univ : Finset (Fin (n - 1))).filter
      (fun r => q < r ∧ r ≤ g)).card = g.val - q.val := by
  have heq : (Finset.univ : Finset (Fin (n - 1))).filter
      (fun r => q < r ∧ r ≤ g) = Finset.Ioc q g := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc]
  rw [heq]
  simp

private lemma card_filter_right_difference_roots {n : ℕ}
    (g q : Fin (n - 1)) :
    ((Finset.univ : Finset (Fin (n - 1))).filter
      (fun r => g < r ∧ r < q)).card = q.val - g.val - 1 := by
  have heq : (Finset.univ : Finset (Fin (n - 1))).filter
      (fun r => g < r ∧ r < q) = Finset.Ioo g q := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo]
  rw [heq]
  simp

/-- Source `(5a--b)` sign on every shared gap to the left of the block. -/
theorem gapDifferenceCombination_sign_leftGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hqg : q < g) {x : ℝ} (hx : x ∈ openGap nodes q) :
    0 < (-1 : ℝ) ^ (g.val - q.val) *
      (gapDifferenceCombination nodes g h).eval x := by
  classical
  let data := Classical.choice (exists_gapDifferenceFactorData nodes g h hgh)
  let c : ℝ := data.scale
  let D : ℝ[X] := gapDifferenceRootProduct nodes g h hgh
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let y : ℝ := nodes.point (gapRightIndex g)
  have hxy : x < y := by
    have hindex : gapRightIndex q ≤ gapRightIndex g := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val]
      omega
    exact hx.2.trans_le (nodes.strictMono.monotone hindex)
  let pairValue : Fin (n - 1) → ℝ := fun r =>
    (x - root r) * (y - root r)
  let between : Fin (n - 1) → Prop := fun r => q < r ∧ r ≤ g
  have hpairNeg : ∀ r : Fin (n - 1), between r → pairValue r < 0 := by
    intro r hr
    have hrootEq : root r = nodes.point (gapLeftIndex r) := by
      simpa only [root] using gapDifferenceRootPoint_eq_left_of_le
        nodes g h hgh r hr.2
    have hxroot : x < root r := by
      rw [hrootEq]
      have hindex : gapRightIndex q ≤ gapLeftIndex r := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      exact hx.2.trans_le (nodes.strictMono.monotone hindex)
    have hrooty : root r < y := by
      rw [hrootEq]
      apply nodes.strictMono
      apply Fin.lt_def.mpr
      simp only [gapLeftIndex_val, gapRightIndex_val]
      omega
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hxroot) (sub_pos.mpr hrooty)
  have hpairPos : ∀ r : Fin (n - 1), ¬between r → 0 < pairValue r := by
    intro r hr
    by_cases hrq : r ≤ q
    · have hrg : r.val ≤ g.val := hrq.trans hqg.le
      have hrootEq : root r = nodes.point (gapLeftIndex r) := by
        simpa only [root] using gapDifferenceRootPoint_eq_left_of_le
          nodes g h hgh r hrg
      have hrootx : root r < x := by
        rw [hrootEq]
        have hindex : gapLeftIndex r ≤ gapLeftIndex q := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapLeftIndex_val]
          omega
        exact (nodes.strictMono.monotone hindex).trans_lt hx.1
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hrootx) (sub_pos.mpr (hrootx.trans hxy))
    · have hgr : g < r := by
        by_contra hnot
        have hrg : r ≤ g := le_of_not_gt hnot
        exact hr ⟨lt_of_not_ge hrq, hrg⟩
      have hyroot : y < root r := by
        have hindex : gapRightIndex g ≤ gapLeftIndex r := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        calc
          y = nodes.point (gapRightIndex g) := rfl
          _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone hindex
          _ < root r := by
            simpa only [root] using left_lt_gapDifferenceRootPoint_of_lt
              nodes g h hgh r hgr
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hxy.trans hyroot))
        (sub_neg.mpr hyroot)
  have hDxy : 0 < (-1 : ℝ) ^ (g.val - q.val) * (D.eval x * D.eval y) := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (Fin (n - 1))) between pairValue
      (fun r _hr => hpairNeg r) (fun r _hr => hpairPos r)
    rw [card_filter_left_difference_roots q g] at hsign
    have heq : D.eval x * D.eval y = ∏ r : Fin (n - 1), pairValue r := by
      simp only [D, gapDifferenceRootProduct, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    simpa using hsign
  have hPy : (gapDifferenceCombination nodes g h).eval y = 2 := by
    have hinside : ¬((gapRightIndex g).val ≤ g.val ∨
        h.val < (gapRightIndex g).val) := by
      simp only [gapRightIndex_val]
      omega
    have hgval : g.val < (gapRightIndex g).val := by simp
    rw [gapDifferenceCombination_eval_node nodes g h hgh, if_neg hinside,
      gapCoefficient_of_lt g (gapRightIndex g) hgval]
    simp only [gapRightIndex_val]
    norm_num
  have hfactor : gapDifferenceCombination nodes g h = D * C c := by
    simpa only [D, c] using data.factor
  have hc : 0 < c ^ 2 := sq_pos_of_ne_zero data.scale_ne_zero
  have htotal : 0 < (-1 : ℝ) ^ (g.val - q.val) *
      ((gapDifferenceCombination nodes g h).eval x *
        (gapDifferenceCombination nodes g h).eval y) := by
    rw [hfactor]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    nlinarith [mul_pos hDxy hc]
  rw [hPy] at htotal
  nlinarith

/-- Source `(5c--e)` sign on every shared gap to the right of the block. -/
theorem gapDifferenceCombination_sign_rightGap {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (hhq : h < q) {x : ℝ} (hx : x ∈ openGap nodes q) :
    0 < (-1 : ℝ) ^ (q.val - g.val - 1) *
      (gapDifferenceCombination nodes g h).eval x := by
  classical
  let data := Classical.choice (exists_gapDifferenceFactorData nodes g h hgh)
  let c : ℝ := data.scale
  let D : ℝ[X] := gapDifferenceRootProduct nodes g h hgh
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let y : ℝ := nodes.point (gapRightIndex g)
  have hyx : y < x := by
    have hindex : gapRightIndex g ≤ gapLeftIndex q := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [gapRightIndex_val, gapLeftIndex_val]
      omega
    exact (nodes.strictMono.monotone hindex).trans_lt hx.1
  let pairValue : Fin (n - 1) → ℝ := fun r =>
    (y - root r) * (x - root r)
  let between : Fin (n - 1) → Prop := fun r => g < r ∧ r < q
  have hpairNeg : ∀ r : Fin (n - 1), between r → pairValue r < 0 := by
    intro r hr
    have hyroot : y < root r := by
      have hindex : gapRightIndex g ≤ gapLeftIndex r := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      calc
        y = nodes.point (gapRightIndex g) := rfl
        _ ≤ nodes.point (gapLeftIndex r) := nodes.strictMono.monotone hindex
        _ < root r := by
          simpa only [root] using left_lt_gapDifferenceRootPoint_of_lt
            nodes g h hgh r hr.1
    have hrootx : root r < x := by
      have hindex : gapRightIndex r ≤ gapLeftIndex q := by
        apply Fin.le_iff_val_le_val.mpr
        simp only [gapRightIndex_val, gapLeftIndex_val]
        omega
      exact ((gapDifferenceRootPoint_mem_closedGap nodes g h hgh r).2.trans
        (nodes.strictMono.monotone hindex)).trans_lt hx.1
    dsimp only [pairValue]
    exact mul_neg_of_neg_of_pos (sub_neg.mpr hyroot) (sub_pos.mpr hrootx)
  have hpairPos : ∀ r : Fin (n - 1), ¬between r → 0 < pairValue r := by
    intro r hr
    by_cases hrg : r ≤ g
    · have hrootEq : root r = nodes.point (gapLeftIndex r) := by
        simpa only [root] using gapDifferenceRootPoint_eq_left_of_le
          nodes g h hgh r hrg
      have hrooty : root r < y := by
        rw [hrootEq]
        apply nodes.strictMono
        apply Fin.lt_def.mpr
        simp only [gapLeftIndex_val, gapRightIndex_val]
        omega
      dsimp only [pairValue]
      exact mul_pos (sub_pos.mpr hrooty) (sub_pos.mpr (hrooty.trans hyx))
    · have hqr : q ≤ r := by
        by_contra hnot
        exact hr ⟨lt_of_not_ge hrg, lt_of_not_ge hnot⟩
      have hhr : h.val ≤ r.val := by omega
      have hrootEq : root r = nodes.point (gapRightIndex r) := by
        simpa only [root] using gapDifferenceRootPoint_eq_right_of_le
          nodes g h hgh r hhr
      have hxroot : x < root r := by
        rw [hrootEq]
        have hindex : gapRightIndex q ≤ gapRightIndex r := by
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val]
          omega
        exact hx.2.trans_le (nodes.strictMono.monotone hindex)
      dsimp only [pairValue]
      exact mul_pos_of_neg_of_neg (sub_neg.mpr (hyx.trans hxroot))
        (sub_neg.mpr hxroot)
  have hDyx : 0 < (-1 : ℝ) ^ (q.val - g.val - 1) * (D.eval y * D.eval x) := by
    have hsign := neg_one_pow_card_filter_mul_prod_pos
      (Finset.univ : Finset (Fin (n - 1))) between pairValue
      (fun r _hr => hpairNeg r) (fun r _hr => hpairPos r)
    rw [card_filter_right_difference_roots g q] at hsign
    have heq : D.eval y * D.eval x = ∏ r : Fin (n - 1), pairValue r := by
      simp only [D, gapDifferenceRootProduct, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        pairValue, root]
      rw [← Finset.prod_mul_distrib]
    rw [heq]
    simpa using hsign
  have hPy : (gapDifferenceCombination nodes g h).eval y = 2 := by
    have hinside : ¬((gapRightIndex g).val ≤ g.val ∨
        h.val < (gapRightIndex g).val) := by
      simp only [gapRightIndex_val]
      omega
    have hgval : g.val < (gapRightIndex g).val := by simp
    rw [gapDifferenceCombination_eval_node nodes g h hgh, if_neg hinside,
      gapCoefficient_of_lt g (gapRightIndex g) hgval]
    simp only [gapRightIndex_val]
    norm_num
  have hfactor : gapDifferenceCombination nodes g h = D * C c := by
    simpa only [D, c] using data.factor
  have hc : 0 < c ^ 2 := sq_pos_of_ne_zero data.scale_ne_zero
  have htotal : 0 < (-1 : ℝ) ^ (q.val - g.val - 1) *
      ((gapDifferenceCombination nodes g h).eval y *
        (gapDifferenceCombination nodes g h).eval x) := by
    rw [hfactor]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    nlinarith [mul_pos hDyx hc]
  rw [hPy] at htotal
  nlinarith

/-- Before its unique root in another gap, a gap polynomial has the sign of
its left endpoint value. -/
lemma gapPolynomial_sign_before_otherGapRoot {n : ℕ}
    (nodes : OrderedNodes n) (i : Fin (n - 1)) (q : OtherGapIndex i)
    {x : ℝ} (hx : x ∈ openGap nodes q.1)
    (hxr : x < otherGapRoot nodes i q) :
    0 < gapCoefficient i (gapLeftIndex q.1) *
      (gapPolynomial nodes i).eval x := by
  let a : ℝ := nodes.point (gapLeftIndex q.1)
  have hpa : (gapPolynomial nodes i).eval a =
      gapCoefficient i (gapLeftIndex q.1) := by
    simpa only [a] using gapPolynomial_eval_node nodes i (gapLeftIndex q.1)
  have hane : (gapPolynomial nodes i).eval a ≠ 0 := by
    rw [hpa]
    exact gapCoefficient_ne_zero i (gapLeftIndex q.1)
  have hxne : (gapPolynomial nodes i).eval x ≠ 0 := by
    intro hxzero
    have hxroot : (gapPolynomial nodes i).IsRoot x := hxzero
    have heq := (isRoot_in_other_gap_iff_eq_otherGapRoot nodes i q hx).mp hxroot
    exact hxr.ne heq
  have hprod : 0 < (gapPolynomial nodes i).eval a *
      (gapPolynomial nodes i).eval x := by
    apply eval_mul_eval_pos_of_no_root_between
      (gapPolynomial nodes i) hx.1 hane hxne
    intro z hz hzroot
    have hzmem : z ∈ openGap nodes q.1 :=
      ⟨hz.1, hz.2.trans (hxr.trans (otherGapRoot_mem_openGap nodes i q).2)⟩
    have heq := (isRoot_in_other_gap_iff_eq_otherGapRoot nodes i q hzmem).mp hzroot
    exact (hz.2.trans hxr).ne heq
  rwa [hpa] at hprod

/-- After its unique root in another gap, a gap polynomial has the sign of
its right endpoint value, the negative of its left endpoint value. -/
lemma gapPolynomial_sign_after_otherGapRoot {n : ℕ}
    (nodes : OrderedNodes n) (i : Fin (n - 1)) (q : OtherGapIndex i)
    {x : ℝ} (hx : x ∈ openGap nodes q.1)
    (hrx : otherGapRoot nodes i q < x) :
    0 < -gapCoefficient i (gapLeftIndex q.1) *
      (gapPolynomial nodes i).eval x := by
  let b : ℝ := nodes.point (gapRightIndex q.1)
  have hpb : (gapPolynomial nodes i).eval b =
      -gapCoefficient i (gapLeftIndex q.1) := by
    calc
      (gapPolynomial nodes i).eval b =
          -(gapPolynomial nodes i).eval (nodes.point (gapLeftIndex q.1)) := by
        simpa only [b] using gapPolynomial_endpoint_values_opposite
          nodes i q.1 q.property
      _ = -gapCoefficient i (gapLeftIndex q.1) := by
        rw [gapPolynomial_eval_node]
  have hbne : (gapPolynomial nodes i).eval b ≠ 0 := by
    rw [hpb]
    exact neg_ne_zero.mpr (gapCoefficient_ne_zero i (gapLeftIndex q.1))
  have hxne : (gapPolynomial nodes i).eval x ≠ 0 := by
    intro hxzero
    have hxroot : (gapPolynomial nodes i).IsRoot x := hxzero
    have heq := (isRoot_in_other_gap_iff_eq_otherGapRoot nodes i q hx).mp hxroot
    exact hrx.ne' heq
  have hprod : 0 < (gapPolynomial nodes i).eval x *
      (gapPolynomial nodes i).eval b := by
    apply eval_mul_eval_pos_of_no_root_between
      (gapPolynomial nodes i) hx.2 hxne hbne
    intro z hz hzroot
    have hzmem : z ∈ openGap nodes q.1 :=
      ⟨(otherGapRoot_mem_openGap nodes i q).1.trans (hrx.trans hz.1), hz.2⟩
    have heq := (isRoot_in_other_gap_iff_eq_otherGapRoot nodes i q hzmem).mp hzroot
    exact (hrx.trans hz.1).ne' heq
  rw [hpb] at hprod
  nlinarith

/-- The three sign families appearing in source equations `(5a--f)`. -/
def SourceCombinationSignTable {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) : Prop :=
  (∀ (q : Fin (n - 1)), q < g → ∀ x ∈ openGap nodes q,
    0 < (-1 : ℝ) ^ (g.val - q.val) *
      (gapDifferenceCombination nodes g h).eval x) ∧
  (∀ (q : Fin (n - 1)), h < q → ∀ x ∈ openGap nodes q,
    0 < (-1 : ℝ) ^ (q.val - g.val - 1) *
      (gapDifferenceCombination nodes g h).eval x) ∧
  (∀ (q : Fin (n - 1)), g ≤ q → q < h → ∀ x ∈ openGap nodes q,
    0 < (-1 : ℝ) ^ (q.val - g.val) *
      (gapSumCombination nodes g h).eval x)

/-- The source sign table is inhabited by the checked root-factor and parity
arguments above. -/
theorem sourceCombinationSignTable {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    SourceCombinationSignTable nodes g h := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hqg x hx
    exact gapDifferenceCombination_sign_leftGap nodes g h q hgh hqg hx
  · intro q hhq x hx
    exact gapDifferenceCombination_sign_rightGap nodes g h q hgh hhq hx
  · intro q hgq hqh x hx
    exact gapSumCombination_sign_middleGap nodes g h q hgh hgq hqh hx

/-- Stable common-gap formulation of the strict root order encoded by
source `(5a--f)`: outside the index block the `h`-polynomial root comes
first, while strictly between `g` and `h` the order reverses.  This too is a
target proposition, not an assumed result. -/
def StrictCrossRootOrder {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) : Prop :=
  (∀ (q : Fin (n - 1)) (hqg : q < g),
    otherGapRoot nodes h ⟨q, ne_of_lt (hqg.trans hgh)⟩ <
      otherGapRoot nodes g ⟨q, ne_of_lt hqg⟩) ∧
  (∀ (q : Fin (n - 1)) (hhq : h < q),
    otherGapRoot nodes h ⟨q, ne_of_gt hhq⟩ <
      otherGapRoot nodes g ⟨q, ne_of_gt (hgh.trans hhq)⟩) ∧
  (∀ (q : Fin (n - 1)) (hgq : g < q) (hqh : q < h),
    otherGapRoot nodes g ⟨q, ne_of_gt hgq⟩ <
      otherGapRoot nodes h ⟨q, ne_of_lt hqh⟩)

/-- Source Lemma 1 in stable common-gap form. -/
theorem strictCrossRootOrder {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) :
    StrictCrossRootOrder nodes g h hgh := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hqg
    let qg : OtherGapIndex g := ⟨q, ne_of_lt hqg⟩
    let qh : OtherGapIndex h := ⟨q, ne_of_lt (hqg.trans hgh)⟩
    let rg : ℝ := otherGapRoot nodes g qg
    let rh : ℝ := otherGapRoot nodes h qh
    have hrhmem : rh ∈ openGap nodes q := by
      simpa only [rh, qh] using otherGapRoot_mem_openGap nodes h qh
    have hrgmem : rg ∈ openGap nodes q := by
      simpa only [rg, qg] using otherGapRoot_mem_openGap nodes g qg
    have hrhne : rh ≠ rg := by
      intro heq
      have hFg : (gapPolynomial nodes g).eval rh = 0 := by
        rw [heq]
        exact gapPolynomial_eval_otherGapRoot nodes g qg
      have hFh : (gapPolynomial nodes h).eval rh = 0 :=
        gapPolynomial_eval_otherGapRoot nodes h qh
      have hroot : (gapDifferenceCombination nodes g h).IsRoot rh := by
        rw [Polynomial.IsRoot, gapDifferenceCombination, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_C, hFg, hFh]
        ring
      exact (not_isRoot_gapDifferenceCombination_of_mem_outerGap
        nodes g h q hgh (Or.inl hqg) hrhmem) hroot
    rcases lt_or_gt_of_ne hrhne with hgood | hbad
    · exact hgood
    · have hbefore : 0 < gapCoefficient h (gapLeftIndex q) *
          (gapPolynomial nodes h).eval rg := by
        simpa only [qh, rh] using gapPolynomial_sign_before_otherGapRoot
          nodes h qh hrgmem hbad
      have hsign := gapDifferenceCombination_sign_leftGap
        nodes g h q hgh hqg hrgmem
      have hGeval : (gapDifferenceCombination nodes g h).eval rg =
          -gapPairParity g h * (gapPolynomial nodes h).eval rg := by
        rw [gapDifferenceCombination, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C, show (gapPolynomial nodes g).eval rg = 0 by
            exact gapPolynomial_eval_otherGapRoot nodes g qg]
        ring
      have houtside : (gapLeftIndex q).val ≤ g.val ∨
          h.val < (gapLeftIndex q).val := Or.inl (by simp; omega)
      have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapLeftIndex q)
      rw [if_pos houtside,
        gapCoefficient_of_le g (gapLeftIndex q) (by simp; omega)] at hrel
      simp only [gapLeftIndex_val] at hrel
      rw [hGeval, ← hrel] at hsign
      nlinarith [sq_gapPairParity g h]
  · intro q hhq
    let qg : OtherGapIndex g := ⟨q, ne_of_gt (hgh.trans hhq)⟩
    let qh : OtherGapIndex h := ⟨q, ne_of_gt hhq⟩
    let rg : ℝ := otherGapRoot nodes g qg
    let rh : ℝ := otherGapRoot nodes h qh
    have hrhmem : rh ∈ openGap nodes q := by
      simpa only [rh, qh] using otherGapRoot_mem_openGap nodes h qh
    have hrgmem : rg ∈ openGap nodes q := by
      simpa only [rg, qg] using otherGapRoot_mem_openGap nodes g qg
    have hrhne : rh ≠ rg := by
      intro heq
      have hFg : (gapPolynomial nodes g).eval rh = 0 := by
        rw [heq]
        exact gapPolynomial_eval_otherGapRoot nodes g qg
      have hFh : (gapPolynomial nodes h).eval rh = 0 :=
        gapPolynomial_eval_otherGapRoot nodes h qh
      have hroot : (gapDifferenceCombination nodes g h).IsRoot rh := by
        rw [Polynomial.IsRoot, gapDifferenceCombination, Polynomial.eval_sub,
          Polynomial.eval_mul, Polynomial.eval_C, hFg, hFh]
        ring
      exact (not_isRoot_gapDifferenceCombination_of_mem_outerGap
        nodes g h q hgh (Or.inr hhq) hrhmem) hroot
    rcases lt_or_gt_of_ne hrhne with hgood | hbad
    · exact hgood
    · have hbefore : 0 < gapCoefficient h (gapLeftIndex q) *
          (gapPolynomial nodes h).eval rg := by
        simpa only [qh, rh] using gapPolynomial_sign_before_otherGapRoot
          nodes h qh hrgmem hbad
      have hsign := gapDifferenceCombination_sign_rightGap
        nodes g h q hgh hhq hrgmem
      have hGeval : (gapDifferenceCombination nodes g h).eval rg =
          -gapPairParity g h * (gapPolynomial nodes h).eval rg := by
        rw [gapDifferenceCombination, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_C, show (gapPolynomial nodes g).eval rg = 0 by
            exact gapPolynomial_eval_otherGapRoot nodes g qg]
        ring
      have houtside : (gapLeftIndex q).val ≤ g.val ∨
          h.val < (gapLeftIndex q).val := Or.inr (by simp; omega)
      have hgk : g.val < (gapLeftIndex q).val := by simp; omega
      have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapLeftIndex q)
      rw [if_pos houtside,
        gapCoefficient_of_lt g (gapLeftIndex q) hgk] at hrel
      simp only [gapLeftIndex_val] at hrel
      rw [hGeval, ← hrel] at hsign
      nlinarith [sq_gapPairParity g h]
  · intro q hgq hqh
    let qg : OtherGapIndex g := ⟨q, ne_of_gt hgq⟩
    let qh : OtherGapIndex h := ⟨q, ne_of_lt hqh⟩
    let rg : ℝ := otherGapRoot nodes g qg
    let rh : ℝ := otherGapRoot nodes h qh
    have hrhmem : rh ∈ openGap nodes q := by
      simpa only [rh, qh] using otherGapRoot_mem_openGap nodes h qh
    have hrgmem : rg ∈ openGap nodes q := by
      simpa only [rg, qg] using otherGapRoot_mem_openGap nodes g qg
    have hrhne : rh ≠ rg := by
      intro heq
      have hFg : (gapPolynomial nodes g).eval rh = 0 := by
        rw [heq]
        exact gapPolynomial_eval_otherGapRoot nodes g qg
      have hFh : (gapPolynomial nodes h).eval rh = 0 :=
        gapPolynomial_eval_otherGapRoot nodes h qh
      have hroot : (gapSumCombination nodes g h).IsRoot rh := by
        rw [Polynomial.IsRoot, gapSumCombination, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_C, hFg, hFh]
        ring
      exact (not_isRoot_gapSumCombination_of_mem_middleGap
        nodes g h q hgh hgq.le hqh hrhmem) hroot
    rcases lt_or_gt_of_ne hrhne with hbad | hgood
    · have hafter : 0 < -gapCoefficient h (gapLeftIndex q) *
          (gapPolynomial nodes h).eval rg := by
        simpa only [qh, rh] using gapPolynomial_sign_after_otherGapRoot
          nodes h qh hrgmem hbad
      have hsign := gapSumCombination_sign_middleGap
        nodes g h q hgh hgq.le hqh hrgmem
      have hGeval : (gapSumCombination nodes g h).eval rg =
          gapPairParity g h * (gapPolynomial nodes h).eval rg := by
        rw [gapSumCombination, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, show (gapPolynomial nodes g).eval rg = 0 by
            exact gapPolynomial_eval_otherGapRoot nodes g qg]
        ring
      have hinside : ¬((gapLeftIndex q).val ≤ g.val ∨
          h.val < (gapLeftIndex q).val) := by
        simp only [gapLeftIndex_val]
        omega
      have hgk : g.val < (gapLeftIndex q).val := by simp; omega
      have hrel := gapPairParity_mul_gapCoefficient g h hgh (gapLeftIndex q)
      rw [if_neg hinside,
        gapCoefficient_of_lt g (gapLeftIndex q) hgk] at hrel
      simp only [gapLeftIndex_val] at hrel
      have hrel' : gapPairParity g h * gapCoefficient h (gapLeftIndex q) =
          (-1 : ℝ) ^ (q.val - g.val) := by
        calc
          gapPairParity g h * gapCoefficient h (gapLeftIndex q) =
              -(-1 : ℝ) ^ (q.val - g.val - 1) := hrel
          _ = (-1 : ℝ) ^ ((q.val - g.val - 1) + 1) := by
            rw [pow_succ]
            ring
          _ = (-1 : ℝ) ^ (q.val - g.val) := by
            congr 1
            omega
      rw [hGeval, ← hrel'] at hsign
      nlinarith [sq_gapPairParity g h]
    · exact hgood

end

end Randy1153.DeBoorPinkus
