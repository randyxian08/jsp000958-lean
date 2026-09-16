import Randy1153.DeBoorPinkus.DerivativeInterlacing
import Randy1153.DeBoorPinkus.Jacobian
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Maximal quotient-evaluation minors

This file formalizes the last, genuinely linear-algebraic step in Lemma 2 of
de Boor--Pinkus.  The checkerboard signs of the critical quotients are not by
themselves a nonsingularity theorem.  The additional input used here is that
all quotient polynomials have degree at most `d - 1`: the source's alternating
sign construction would otherwise produce `d` distinct real zeros.
-/

namespace Randy1153.DeBoorPinkus

open Polynomial
open scoped BigOperators

noncomputable section

/-! ## The alternating-zero-count kernel -/

/-- A polynomial of degree strictly below `d` cannot change sign across all
`d` consecutive intervals cut out by `d+1` strictly ordered points. -/
private theorem eq_zero_of_eval_mul_next_neg {d : ℕ} (p : ℝ[X])
    (τ : Fin (d + 1) → ℝ) (hτ : StrictMono τ)
    (hdegree : p.natDegree < d)
    (hsign : ∀ j : Fin d,
      p.eval (τ j.castSucc) * p.eval (τ j.succ) < 0) :
    p = 0 := by
  classical
  have hexists (j : Fin d) :
      ∃ x ∈ Set.Ioo (τ j.castSucc) (τ j.succ), p.eval x = 0 := by
    have hab : τ j.castSucc ≤ τ j.succ :=
      (hτ Fin.castSucc_lt_succ).le
    have hcont : ContinuousOn (fun x => p.eval x)
        (Set.Icc (τ j.castSucc) (τ j.succ)) :=
      p.continuous.continuousOn
    rcases mul_neg_iff.mp (hsign j) with hj | hj
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (τ j.succ))
          (p.eval (τ j.castSucc)) := ⟨hj.2, hj.1⟩
      exact intermediate_value_Ioo' hab hcont hz
    · have hz : (0 : ℝ) ∈ Set.Ioo (p.eval (τ j.castSucc))
          (p.eval (τ j.succ)) := hj
      exact intermediate_value_Ioo hab hcont hz
  let r : Fin d → ℝ := fun j => Classical.choose (hexists j)
  have hr_mem (j : Fin d) : r j ∈ Set.Ioo (τ j.castSucc) (τ j.succ) :=
    (Classical.choose_spec (hexists j)).1
  have hr_eval (j : Fin d) : p.eval (r j) = 0 :=
    (Classical.choose_spec (hexists j)).2
  have hr_strictMono : StrictMono r := by
    intro i j hij
    have hij' : i.val + 1 ≤ j.val := by omega
    have hmiddle : τ i.succ ≤ τ j.castSucc := by
      apply hτ.monotone
      exact Fin.le_iff_val_le_val.mpr (by simpa using hij')
    exact ((hr_mem i).2.trans_le hmiddle).trans (hr_mem j).1
  let s : Finset ℝ := Finset.univ.image r
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hr_strictMono.injective,
      Finset.card_univ, Fintype.card_fin]
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
  · rw [hs_card]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr hdegree)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    exact hr_eval j

/-! ## Signs of ordered nodal products -/

private lemma sq_negOnePow (k : ℕ) : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
  rcases neg_one_pow_eq_or ℝ k with h | h <;> rw [h] <;> norm_num

private lemma ordered_gap_nodalProduct_sign {n : ℕ} (t : Fin n → ℝ)
    (ht : StrictMono t) (g : Fin (n - 1)) {x : ℝ}
    (hx : t (gapLeftIndex g) < x ∧ x < t (gapRightIndex g)) :
    0 < (-1 : ℝ) ^ (n - 1 - g.val) * ∏ k : Fin n, (x - t k) := by
  classical
  let L : Finset (Fin n) := Finset.Iic (gapLeftIndex g)
  let U : Finset (Fin n) := Finset.Ioi (gapLeftIndex g)
  have hdis : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkU
    have hkle : k ≤ gapLeftIndex g := by simpa [L] using hkL
    have hgk : gapLeftIndex g < k := by simpa [U] using hkU
    exact (not_lt_of_ge hkle) hgk
  have hunion : L ∪ U = Finset.univ := by
    ext k
    simp only [L, U, Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi,
      Finset.mem_univ, iff_true]
    exact le_or_gt k (gapLeftIndex g)
  have hleft : 0 < ∏ k ∈ L, (x - t k) := by
    apply Finset.prod_pos
    intro k hk
    have hkle : k ≤ gapLeftIndex g := by simpa [L] using hk
    exact sub_pos.mpr ((ht.monotone hkle).trans_lt hx.1)
  have hright : 0 < ∏ k ∈ U, (t k - x) := by
    apply Finset.prod_pos
    intro k hk
    have hgk : gapLeftIndex g < k := by simpa [U] using hk
    have hright_le : gapRightIndex g ≤ k := by
      apply Fin.le_iff_val_le_val.mpr
      change g.val + 1 ≤ k.val
      change g.val < k.val at hgk
      omega
    exact sub_pos.mpr (hx.2.trans_le (ht.monotone hright_le))
  have hprod : (∏ k : Fin n, (x - t k)) =
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (x - t k) := by
    rw [← Finset.prod_union hdis, hunion]
  have hright_sign : (∏ k ∈ U, (x - t k)) =
      (-1 : ℝ) ^ U.card * ∏ k ∈ U, (t k - x) := by
    simpa only [neg_sub] using
      (Finset.prod_neg (s := U) (fun k => t k - x))
  have hcard : U.card = n - 1 - g.val := by
    simp [U, gapLeftIndex_val]
  let s : ℝ := (-1 : ℝ) ^ (n - 1 - g.val)
  have hs : s ^ 2 = 1 := sq_negOnePow (n - 1 - g.val)
  have hboth : 0 <
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (t k - x) :=
    mul_pos hleft hright
  rw [hprod, hright_sign, hcard]
  change 0 < s * ((∏ k ∈ L, (x - t k)) *
    (s * ∏ k ∈ U, (t k - x)))
  rw [show s * ((∏ k ∈ L, (x - t k)) *
      (s * ∏ k ∈ U, (t k - x))) =
      (∏ k ∈ L, (x - t k)) * ∏ k ∈ U, (t k - x) by
    calc
      s * ((∏ k ∈ L, (x - t k)) *
          (s * ∏ k ∈ U, (t k - x))) =
          s ^ 2 * ((∏ k ∈ L, (x - t k)) *
            ∏ k ∈ U, (t k - x)) := by ring
      _ = _ := by rw [hs, one_mul]]
  exact hboth

private lemma ordered_basisDenominator_sign {n : ℕ} (t : Fin n → ℝ)
    (ht : StrictMono t) (r : Fin n) :
    0 < (-1 : ℝ) ^ (n - 1 - r.val) *
      ∏ k ∈ Finset.univ.erase r, (t r - t k) := by
  classical
  let L : Finset (Fin n) := Finset.Iio r
  let U : Finset (Fin n) := Finset.Ioi r
  have hdis : Disjoint L U := by
    apply Finset.disjoint_left.mpr
    intro k hkL hkU
    have hkr : k < r := by simpa [L] using hkL
    have hrk : r < k := by simpa [U] using hkU
    exact (not_lt_of_ge hkr.le) hrk
  have hunion : L ∪ U = Finset.univ.erase r := by
    ext k
    simp only [L, U, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi,
      Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro h
      rcases h with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h
    · intro h
      exact lt_or_gt_of_ne h
  have hleft : 0 < ∏ k ∈ L, (t r - t k) := by
    apply Finset.prod_pos
    intro k hk
    exact sub_pos.mpr (ht (by simpa [L] using hk))
  have hright : 0 < ∏ k ∈ U, (t k - t r) := by
    apply Finset.prod_pos
    intro k hk
    exact sub_pos.mpr (ht (by simpa [U] using hk))
  have hprod : (∏ k ∈ Finset.univ.erase r, (t r - t k)) =
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t r - t k) := by
    rw [← Finset.prod_union hdis, hunion]
  have hright_sign : (∏ k ∈ U, (t r - t k)) =
      (-1 : ℝ) ^ U.card * ∏ k ∈ U, (t k - t r) := by
    simpa only [neg_sub] using
      (Finset.prod_neg (s := U) (fun k => t k - t r))
  have hcard : U.card = n - 1 - r.val := by simp [U]
  let s : ℝ := (-1 : ℝ) ^ (n - 1 - r.val)
  have hs : s ^ 2 = 1 := sq_negOnePow (n - 1 - r.val)
  have hboth : 0 <
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t k - t r) :=
    mul_pos hleft hright
  rw [hprod, hright_sign, hcard]
  change 0 < s * ((∏ k ∈ L, (t r - t k)) *
    (s * ∏ k ∈ U, (t k - t r)))
  rw [show s * ((∏ k ∈ L, (t r - t k)) *
      (s * ∏ k ∈ U, (t k - t r))) =
      (∏ k ∈ L, (t r - t k)) * ∏ k ∈ U, (t k - t r) by
    calc
      s * ((∏ k ∈ L, (t r - t k)) *
          (s * ∏ k ∈ U, (t k - t r))) =
          s ^ 2 * ((∏ k ∈ L, (t r - t k)) *
            ∏ k ∈ U, (t k - t r)) := by ring
      _ = _ := by rw [hs, one_mul]]
  exact hboth

private lemma endpointPoint_eq_endpointArray_point {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (k : Fin (d + 2)) :
    endpointPoint A B nodes.interior k = nodes.point k := by
  let u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} :=
    ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  have harr := endpointArrayOfInterior_interior nodes.admissibleInterval nodes
  have hpoint := congrArg (fun z : EndpointArray d A B => z.point k) harr
  exact hpoint

/-- Exact row-factor sign: the nodal product at the `g`th gap maximum has
one negative factor for every node strictly to the right of that gap. -/
theorem gapJacobianRowFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (g : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ (d + 1 - g.val) * gapJacobianRowFactor nodes g := by
  rw [gapJacobianRowFactor, coordinateNodalValue]
  simp_rw [endpointPoint_eq_endpointArray_point nodes]
  have h := ordered_gap_nodalProduct_sign nodes.point nodes.strictMono g
    (gapArgmax_mem_openGap nodes.toOrderedNodes (by omega) g)
  simpa using h

/-- Exact column-factor sign.  The denominator at interior node `j` has one
negative factor for every node to its right, namely `d-j` factors; inversion
preserves that sign. -/
theorem gapJacobianColumnFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    0 < (-1 : ℝ) ^ (d - j.val) * gapJacobianColumnFactor nodes j := by
  have hden := ordered_basisDenominator_sign nodes.point nodes.strictMono
    (interiorNodeIndex j)
  have hden' : 0 < (-1 : ℝ) ^ (d - j.val) *
      coordinateBasisDenominator A B nodes.interior j := by
    rw [coordinateBasisDenominator]
    simp_rw [endpointPoint_eq_endpointArray_point nodes]
    have hexp : d + 2 - 1 - (interiorNodeIndex j).val = d - j.val := by
      simp only [interiorNodeIndex_val]
      omega
    rw [hexp] at hden
    exact hden
  rw [gapJacobianColumnFactor]
  rcases neg_one_pow_eq_or ℝ (d - j.val) with hs | hs
  · rw [hs] at hden' ⊢
    simp only [one_mul] at hden' ⊢
    exact inv_pos.mpr hden'
  · rw [hs] at hden' ⊢
    simp only [neg_one_mul] at hden' ⊢
    have hneg : coordinateBasisDenominator A B nodes.interior j < 0 := by
      linarith
    exact neg_pos.mpr (inv_lt_zero.mpr hneg)

/-- The total sign contributed to a height-Jacobian minor by all retained row
factors and all column factors. -/
def heightMinorFactorParity (d : ℕ) (omitted : Fin (d + 1)) : ℝ :=
  (∏ i : Fin d, (-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val)) *
    ∏ j : Fin d, (-1 : ℝ) ^ (d - j.val)

/-- The explicit row/column factor parity collapses to the ordinary
row-deletion parity `(-1)^omitted`.  Pairing the retained row indexed by
`omitted.succAbove i` with column `i` makes each factor `-1` exactly for
`i < omitted`. -/
lemma heightMinorFactorParity_eq_negOnePow (d : ℕ)
    (omitted : Fin (d + 1)) :
    heightMinorFactorParity d omitted = (-1 : ℝ) ^ omitted.val := by
  classical
  let S : Finset (Fin d) :=
    Finset.univ.filter fun i => i.castSucc < omitted
  have hcard : S.card = omitted.val := by
    calc
      S.card = (Finset.Iio omitted).card := by
        apply Finset.card_bij (fun i _hi => i.castSucc)
        · intro i hi
          simpa [S] using (Finset.mem_filter.mp hi).2
        · intro i _hi j _hj hij
          exact Fin.castSucc_inj.mp hij
        · intro k hk
          have hko : k < omitted := by simpa using hk
          let i : Fin d := ⟨k.val, by
            have ho : omitted.val ≤ d := by omega
            exact lt_of_lt_of_le (Fin.lt_def.mp hko) ho⟩
          refine ⟨i, ?_, ?_⟩
          · exact Finset.mem_filter.mpr
              ⟨Finset.mem_univ i, by simpa [i] using hko⟩
          · ext
            rfl
      _ = omitted.val := Fin.card_Iio omitted
  rw [heightMinorFactorParity, ← Finset.prod_mul_distrib]
  calc
    (∏ i : Fin d,
        (-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val) *
          (-1 : ℝ) ^ (d - i.val)) =
        ∏ i : Fin d, if i.castSucc < omitted then (-1 : ℝ) else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hio : i.castSucc < omitted
      · rw [if_pos hio, Fin.succAbove_of_castSucc_lt omitted i hio]
        simp only [Fin.val_castSucc]
        have hexp : d + 1 - i.val = (d - i.val) + 1 := by omega
        rw [hexp, pow_succ]
        have hs := sq_negOnePow (d - i.val)
        nlinarith
      · have hoi : omitted ≤ i.castSucc := le_of_not_gt hio
        rw [if_neg hio, Fin.succAbove_of_le_castSucc omitted i hoi]
        simp only [Fin.val_succ]
        have hexp : d + 1 - (i.val + 1) = d - i.val := by omega
        rw [hexp]
        simpa only [pow_two] using sq_negOnePow (d - i.val)
    _ = (-1 : ℝ) ^ S.card := by
      rw [← Finset.prod_filter (s := Finset.univ)
        (fun i : Fin d => i.castSucc < omitted) (fun _ => (-1 : ℝ))]
      change (∏ _i ∈ S, (-1 : ℝ)) = (-1 : ℝ) ^ S.card
      simp
    _ = (-1 : ℝ) ^ omitted.val := by rw [hcard]

/-! ## The source normalization and its sign table -/

/-- Row normalization used in the proof following source equations (6)--(7).
The first quotient is negated; every later quotient receives its alternating
row sign.  Consequently all normalized quotients are positive at `τ₀`. -/
def sourceQuotientNormalizer {m : ℕ} (i : Fin (m + 1)) : ℝ :=
  if i = 0 then -1 else (-1 : ℝ) ^ i.val

lemma sourceQuotientNormalizer_ne_zero {m : ℕ} (i : Fin (m + 1)) :
    sourceQuotientNormalizer i ≠ 0 := by
  rw [sourceQuotientNormalizer]
  split
  · norm_num
  · exact pow_ne_zero _ (by norm_num)

lemma sourceQuotientNormalizer_sq {m : ℕ} (i : Fin (m + 1)) :
    sourceQuotientNormalizer i ^ 2 = 1 := by
  rw [sourceQuotientNormalizer]
  split
  · norm_num
  · exact sq_negOnePow i.val

/-- The normalized critical quotient polynomial. -/
def sourceNormalizedQuotient {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (i : Fin (d + 1)) : ℝ[X] :=
  C (sourceQuotientNormalizer i) *
    gapDerivativeQuotient nodes.toOrderedNodes i

lemma natDegree_sourceNormalizedQuotient_le {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) (i : Fin (d + 1)) :
    (sourceNormalizedQuotient nodes i).natDegree ≤ d - 1 := by
  have hq := natDegree_gapDerivativeQuotient_le_sub_three
    (n := d + 2) nodes.toOrderedNodes (by omega) i
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by omega)

lemma sourceNormalizedQuotient_eval_first_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d) (i : Fin (d + 1)) :
    0 < (sourceNormalizedQuotient nodes i).eval
      (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  by_cases hi : i = 0
  · subst i
    simpa [sourceNormalizedQuotient, sourceQuotientNormalizer]
      using neg_pos.mpr (htable.1 ⟨0, by omega⟩)
  · have h := htable.2 i ⟨0, by omega⟩ hi
    simpa [sourceNormalizedQuotient, sourceQuotientNormalizer, hi,
      Polynomial.eval_mul, Polynomial.eval_C] using h

lemma sourceNormalizedQuotient_first_eval_later_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (j : Fin (d + 1)) (hj : j ≠ 0) :
    0 < (-1 : ℝ) ^ (j.val + 1) *
      (sourceNormalizedQuotient nodes 0).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  have h := htable.2 ⟨0, by omega⟩ j hj.symm
  simpa [sourceNormalizedQuotient, sourceQuotientNormalizer,
    Polynomial.eval_mul, Polynomial.eval_C, pow_succ] using h

lemma sourceNormalizedQuotient_offDiagonal_eval_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (i j : Fin (d + 1)) (hi : i ≠ 0) (hij : i ≠ j) :
    0 < (-1 : ℝ) ^ j.val *
      (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have htable := derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)
  have h := htable.2 i j hij
  simpa [sourceNormalizedQuotient, sourceQuotientNormalizer, hi,
    Polynomial.eval_mul, Polynomial.eval_C, pow_add, mul_assoc,
    mul_left_comm, mul_comm] using h

lemma sourceNormalizedQuotient_diagonal_eval_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (j : Fin (d + 1)) (hj : j ≠ 0) :
    0 < (-1 : ℝ) ^ (j.val + 1) *
      (sourceNormalizedQuotient nodes j).eval
        (gapArgmax nodes.toOrderedNodes j) := by
  have hdiag := (derivativeQuotientSignTable_of_three_le
    nodes.toOrderedNodes (by omega)).1 j
  have hsquare := sq_negOnePow j.val
  rw [sourceNormalizedQuotient, Polynomial.eval_mul, Polynomial.eval_C,
    sourceQuotientNormalizer, if_neg hj, pow_succ]
  nlinarith

/-! ## The de Boor--Pinkus sign-variation relation argument -/

private def negativeLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => a i < 0

private def positiveLaterIndices {d : ℕ} (a : Fin (d + 1) → ℝ) :
    Finset (Fin (d + 1)) :=
  (Finset.univ.erase 0).filter fun i => 0 < a i

private lemma sum_eq_first_add_negative_add_positive {d : ℕ}
    (a v : Fin (d + 1) → ℝ) :
    (∑ i, a i * v i) =
      a 0 * v 0 +
        ∑ i ∈ negativeLaterIndices a, a i * v i +
          ∑ i ∈ positiveLaterIndices a, a i * v i := by
  classical
  let I : Finset (Fin (d + 1)) := Finset.univ.erase 0
  let N := negativeLaterIndices a
  let P := positiveLaterIndices a
  have hNsub : N ⊆ I := Finset.filter_subset _ _
  have hPsub : P ⊆ I := Finset.filter_subset _ _
  have hdis : Disjoint N P := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiN hiP
    have hneg : a i < 0 := (Finset.mem_filter.mp hiN).2
    have hpos : 0 < a i := (Finset.mem_filter.mp hiP).2
    linarith
  have hcover :
      (∑ i ∈ N ∪ P, a i * v i) = ∑ i ∈ I, a i * v i := by
    apply Finset.sum_subset (Finset.union_subset hNsub hPsub)
    intro i hiI hiNP
    have hiN : i ∉ N := fun h => hiNP (Finset.mem_union_left P h)
    have hiP : i ∉ P := fun h => hiNP (Finset.mem_union_right N h)
    have hnneg : ¬a i < 0 := by
      intro h
      exact hiN (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hnpos : ¬0 < a i := by
      intro h
      exact hiP (Finset.mem_filter.mpr ⟨hiI, h⟩)
    have hai : a i = 0 := le_antisymm (le_of_not_gt hnpos) (le_of_not_gt hnneg)
    simp [hai]
  rw [Finset.sum_union hdis] at hcover
  have herase := Finset.sum_erase_add Finset.univ (fun i => a i * v i)
    (Finset.mem_univ (0 : Fin (d + 1)))
  change (∑ i ∈ I, a i * v i) + a 0 * v 0 = ∑ i, a i * v i at herase
  rw [← herase, ← hcover]
  dsimp only [N, P]
  ring

/-- In any nonzero polynomial relation among the normalized quotients, every
coefficient is nonzero.  This is the precise source conclusion needed for
all row-deleted families: a relation missing one row is therefore trivial. -/
theorem sourceNormalizedQuotient_relation_sign_pattern {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ)
    (hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0)
    (ha : a ≠ 0) :
    (0 < a 0 ∧ ∀ i, i ≠ 0 → a i < 0) ∨
      (a 0 < 0 ∧ ∀ i, i ≠ 0 → 0 < a i) := by
  classical
  let orient : ℝ := if 0 ≤ a 0 then 1 else -1
  let b : Fin (d + 1) → ℝ := fun i => orient * a i
  have horient : orient = 1 ∨ orient = -1 := by
    dsimp [orient]
    split <;> simp
  have horient_ne : orient ≠ 0 := by
    rcases horient with h | h <;> rw [h] <;> norm_num
  have hbfirst : 0 ≤ b 0 := by
    dsimp [b, orient]
    split_ifs with h
    · simpa using h
    · have hlt : a 0 < 0 := lt_of_not_ge h
      simp only [neg_one_mul]
      exact neg_nonneg.mpr hlt.le
  have hbne : b ≠ 0 := by
    intro hb
    apply ha
    funext i
    have hi := congrFun hb i
    dsimp [b] at hi
    exact (mul_eq_zero.mp hi).resolve_left horient_ne
  have hbrel : (∑ i, C (b i) * sourceNormalizedQuotient nodes i) = 0 := by
    calc
      (∑ i, C (b i) * sourceNormalizedQuotient nodes i) =
          C orient * (∑ i, C (a i) * sourceNormalizedQuotient nodes i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            simp only [b, map_mul]
            ring
      _ = 0 := by rw [hrel, mul_zero]
  have hbrel_eval (x : ℝ) :
      (∑ i, b i * (sourceNormalizedQuotient nodes i).eval x) = 0 := by
    have h := congrArg (Polynomial.eval x) hbrel
    simpa only [Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_zero] using h
  let N := negativeLaterIndices b
  let P := positiveLaterIndices b
  have hN : N.Nonempty := by
    by_contra hNempty
    rw [Finset.not_nonempty_iff_eq_empty] at hNempty
    have hbnonneg (i : Fin (d + 1)) : 0 ≤ b i := by
      by_cases hi : i = 0
      · simpa [hi] using hbfirst
      · apply le_of_not_gt
        intro hneg
        have hiN : i ∈ N := by
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hneg⟩
        rw [hNempty] at hiN
        simp at hiN
    obtain ⟨i, hbi⟩ := Function.ne_iff.mp hbne
    have hbipos : 0 < b i := lt_of_le_of_ne (hbnonneg i) (Ne.symm hbi)
    have hterm_nonneg (k : Fin (d + 1)) :
        0 ≤ b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) :=
      mul_nonneg (hbnonneg k)
        (sourceNormalizedQuotient_eval_first_pos nodes (by omega) k).le
    have hterm_pos :
        0 < b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) :=
      mul_pos hbipos
        (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
    have hsumpos : 0 <
        ∑ k, b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
      rw [Finset.sum_pos_iff_of_nonneg (fun k _hk => hterm_nonneg k)]
      exact ⟨i, Finset.mem_univ i, hterm_pos⟩
    rw [hbrel_eval] at hsumpos
    exact (lt_irrefl 0) hsumpos
  -- The source's auxiliary polynomial: first row plus all negatively
  -- weighted later rows.
  let f : ℝ[X] := C (b 0) * sourceNormalizedQuotient nodes 0 +
    ∑ i ∈ N, C (b i) * sourceNormalizedQuotient nodes i
  have hf_eval (x : ℝ) : f.eval x =
      b 0 * (sourceNormalizedQuotient nodes 0).eval x +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval x := by
    simp only [f, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_finset_sum]
  have hf_eval_eq_neg_pos (x : ℝ) : f.eval x =
      -∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval x := by
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => (sourceNormalizedQuotient nodes i).eval x)
    have hzero := hbrel_eval x
    change (∑ i, b i * (sourceNormalizedQuotient nodes i).eval x) =
      b 0 * (sourceNormalizedQuotient nodes 0).eval x +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval x +
          ∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval x at hsplit
    rw [hf_eval]
    linarith
  have hNmem {i : Fin (d + 1)} (hi : i ∈ N) : i ≠ 0 ∧ b i < 0 := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hPmem {i : Fin (d + 1)} (hi : i ∈ P) : i ≠ 0 ∧ 0 < b i := by
    exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hi).1).1,
      (Finset.mem_filter.mp hi).2⟩
  have hfzero : f = 0 := by
    by_cases hP : P.Nonempty
    · have hf_sign (j : Fin (d + 1)) :
          0 < (-1 : ℝ) ^ (j.val + 1) * f.eval
            (gapArgmax nodes.toOrderedNodes j) := by
        by_cases hj0 : j = 0
        · subst j
          have hsumpos : 0 < ∑ i ∈ P,
              b i * (sourceNormalizedQuotient nodes i).eval
                (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
            apply Finset.sum_pos
            · intro i hi
              exact mul_pos (hPmem hi).2
                (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
            · exact hP
          rw [hf_eval_eq_neg_pos]
          simpa using hsumpos
        · by_cases hjP : j ∈ P
          · have hfirst : 0 ≤
                b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                  (sourceNormalizedQuotient nodes 0).eval
                    (gapArgmax nodes.toOrderedNodes j)) :=
              mul_nonneg hbfirst
                (sourceNormalizedQuotient_first_eval_later_sign
                  nodes (by omega) j hj0).le
            have hNsum : 0 < ∑ i ∈ N,
                (-1 : ℝ) ^ (j.val + 1) *
                  (b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j)) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hNmem hi).1
                have hibneg := (hNmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  linarith [hibneg, (hPmem hjP).2]
                have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
                  nodes (by omega) i j hine hij
                calc
                  0 < (-b i) * ((-1 : ℝ) ^ j.val *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) :=
                    mul_pos (neg_pos.mpr hibneg) hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (b i * (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := by
                    rw [pow_succ]
                    ring
              · exact hN
            rw [hf_eval]
            calc
              0 < b 0 * ((-1 : ℝ) ^ (j.val + 1) *
                    (sourceNormalizedQuotient nodes 0).eval
                      (gapArgmax nodes.toOrderedNodes j)) +
                  ∑ i ∈ N, (-1 : ℝ) ^ (j.val + 1) *
                    (b i * (sourceNormalizedQuotient nodes i).eval
                      (gapArgmax nodes.toOrderedNodes j)) :=
                add_pos_of_nonneg_of_pos hfirst hNsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (b 0 * (sourceNormalizedQuotient nodes 0).eval
                      (gapArgmax nodes.toOrderedNodes j) +
                    ∑ i ∈ N, b i *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := by
                rw [← Finset.mul_sum]
                ring
          · have hjnotpos : ¬0 < b j := by
              intro hjpos
              exact hjP (Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hj0, Finset.mem_univ j⟩, hjpos⟩)
            have hPsum : 0 < ∑ i ∈ P,
                (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j))) := by
              apply Finset.sum_pos
              · intro i hi
                have hine := (hPmem hi).1
                have hibpos := (hPmem hi).2
                have hij : i ≠ j := by
                  intro hij
                  subst i
                  exact hjnotpos hibpos
                have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
                  nodes (by omega) i j hine hij
                calc
                  0 < b i * ((-1 : ℝ) ^ j.val *
                      (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j)) := mul_pos hibpos hq
                  _ = (-1 : ℝ) ^ (j.val + 1) *
                      (-(b i * (sourceNormalizedQuotient nodes i).eval
                        (gapArgmax nodes.toOrderedNodes j))) := by
                    rw [pow_succ]
                    ring
              · exact hP
            rw [hf_eval_eq_neg_pos]
            calc
              0 < ∑ i ∈ P, (-1 : ℝ) ^ (j.val + 1) *
                  (-(b i * (sourceNormalizedQuotient nodes i).eval
                    (gapArgmax nodes.toOrderedNodes j))) := hPsum
              _ = (-1 : ℝ) ^ (j.val + 1) *
                  (-∑ i ∈ P, b i *
                    (sourceNormalizedQuotient nodes i).eval
                      (gapArgmax nodes.toOrderedNodes j)) := by
                rw [← Finset.mul_sum]
                congr 1
                rw [← Finset.sum_neg_distrib]
      apply eq_zero_of_eval_mul_next_neg f
          (gapArgmax nodes.toOrderedNodes)
          (gapArgmax_strictMono nodes.toOrderedNodes (by omega))
      · have hfirstDegree :
            (C (b 0) * sourceNormalizedQuotient nodes 0).natDegree ≤ d - 1 :=
          (Polynomial.natDegree_C_mul_le _ _).trans
            (natDegree_sourceNormalizedQuotient_le nodes hd 0)
        have hsumDegree :
            (∑ i ∈ N, C (b i) * sourceNormalizedQuotient nodes i).natDegree ≤
              d - 1 := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro i hi
          exact (Polynomial.natDegree_C_mul_le _ _).trans
            (natDegree_sourceNormalizedQuotient_le nodes hd i)
        exact (Polynomial.natDegree_add_le _ _).trans_lt (by omega)
      · intro j
        have hleft := hf_sign j.castSucc
        have hright := hf_sign j.succ
        simp only [Fin.val_castSucc, Fin.val_succ] at hleft hright
        rw [show j.val + 1 + 1 = (j.val + 1) + 1 by omega, pow_succ] at hright
        nlinarith [sq_negOnePow (j.val + 1)]
    · apply Polynomial.funext
      have heval : ∀ x : ℝ, f.eval x = 0 := by
        intro x
        rw [hf_eval_eq_neg_pos]
        rw [Finset.not_nonempty_iff_eq_empty.mp hP]
        simp
      intro x
      simpa using heval x
  have hPempty : P = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro hP
    have hsumpos : 0 < ∑ i ∈ P,
        b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) := by
      apply Finset.sum_pos
      · intro i hi
        exact mul_pos (hPmem hi).2
          (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
      · exact hP
    have hf0 := congrArg
      (fun p : ℝ[X] => p.eval (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩)) hfzero
    have hf0' : f.eval (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) = 0 := by
      simpa only [Polynomial.eval_zero] using hf0
    rw [hf_eval_eq_neg_pos] at hf0'
    linarith
  have hblater (i : Fin (d + 1)) (hi0 : i ≠ 0) : b i ≠ 0 := by
    intro hbi
    have hiP : i ∉ P := by rw [hPempty]; simp
    have hibnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hiP (Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ i⟩, hpos⟩)
    have hiN : i ∉ N := by
      intro hiN
      exact (hNmem hiN).2.ne hbi
    have hfirst : 0 ≤ b 0 * ((-1 : ℝ) ^ (i.val + 1) *
        (sourceNormalizedQuotient nodes 0).eval
          (gapArgmax nodes.toOrderedNodes i)) :=
      mul_nonneg hbfirst
        (sourceNormalizedQuotient_first_eval_later_sign
          nodes (by omega) i hi0).le
    have hNsum : 0 < ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
        (b k * (sourceNormalizedQuotient nodes k).eval
          (gapArgmax nodes.toOrderedNodes i)) := by
      apply Finset.sum_pos
      · intro k hk
        have hk0 := (hNmem hk).1
        have hkbneg := (hNmem hk).2
        have hki : k ≠ i := by
          intro hki
          subst k
          exact hiN hk
        have hq := sourceNormalizedQuotient_offDiagonal_eval_sign
          nodes (by omega) k i hk0 hki
        calc
          0 < (-b k) * ((-1 : ℝ) ^ i.val *
              (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) :=
            mul_pos (neg_pos.mpr hkbneg) hq
          _ = (-1 : ℝ) ^ (i.val + 1) *
              (b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) := by
            rw [pow_succ]
            ring
      · exact hN
    have hfpos : 0 < (-1 : ℝ) ^ (i.val + 1) *
        f.eval (gapArgmax nodes.toOrderedNodes i) := by
      rw [hf_eval]
      calc
        0 < b 0 * ((-1 : ℝ) ^ (i.val + 1) *
              (sourceNormalizedQuotient nodes 0).eval
                (gapArgmax nodes.toOrderedNodes i)) +
            ∑ k ∈ N, (-1 : ℝ) ^ (i.val + 1) *
              (b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) :=
          add_pos_of_nonneg_of_pos hfirst hNsum
        _ = (-1 : ℝ) ^ (i.val + 1) *
            (b 0 * (sourceNormalizedQuotient nodes 0).eval
                (gapArgmax nodes.toOrderedNodes i) +
              ∑ k ∈ N, b k * (sourceNormalizedQuotient nodes k).eval
                (gapArgmax nodes.toOrderedNodes i)) := by
          rw [← Finset.mul_sum]
          ring
    rw [hfzero] at hfpos
    simp at hfpos
  have hbzero : b 0 ≠ 0 := by
    intro hb0
    have hNsumneg :
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) < 0 := by
      apply Finset.sum_neg
      · intro i hi
        exact mul_neg_of_neg_of_pos (hNmem hi).2
          (sourceNormalizedQuotient_eval_first_pos nodes (by omega) i)
      · exact hN
    have hsplit := sum_eq_first_add_negative_add_positive b
      (fun i => (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩))
    change (∑ i, b i * (sourceNormalizedQuotient nodes i).eval
        (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩)) =
      b 0 * (sourceNormalizedQuotient nodes 0).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) +
        ∑ i ∈ N, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) +
        ∑ i ∈ P, b i * (sourceNormalizedQuotient nodes i).eval
          (gapArgmax nodes.toOrderedNodes ⟨0, by omega⟩) at hsplit
    rw [hbrel_eval, hb0, hPempty] at hsplit
    simp at hsplit
    exact (ne_of_lt hNsumneg) hsplit.symm
  have hbfirstpos : 0 < b 0 := lt_of_le_of_ne hbfirst (Ne.symm hbzero)
  have hblaterneg (i : Fin (d + 1)) (hi : i ≠ 0) : b i < 0 := by
    have hnonpos : b i ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      have hiP : i ∈ P := Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩, hpos⟩
      rw [hPempty] at hiP
      simp at hiP
    exact lt_of_le_of_ne hnonpos (hblater i hi)
  rcases horient with horient | horient
  · left
    constructor
    · simpa [b, horient] using hbfirstpos
    · intro i hi
      simpa [b, horient] using hblaterneg i hi
  · right
    constructor
    · have := hbfirstpos
      simp only [b, horient, neg_one_mul] at this
      linarith
    · intro i hi
      have := hblaterneg i hi
      simp only [b, horient, neg_one_mul] at this
      linarith

theorem sourceNormalizedQuotient_relation_coeff_ne_zero {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ)
    (hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0)
    (ha : a ≠ 0) :
    ∀ i, a i ≠ 0 := by
  rcases sourceNormalizedQuotient_relation_sign_pattern nodes hd a hrel ha with
    h | h
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ne_of_gt h.1
    · exact ne_of_lt (h.2 i hi)
  · intro i
    by_cases hi : i = 0
    · subst i
      exact ne_of_lt h.1
    · exact ne_of_gt (h.2 i hi)

/-! ## From the relation theorem to maximal minors -/

/-- Transpose-oriented evaluation matrix for the normalized polynomials in
the row-deleted family.  Rows are interior nodes and columns are retained gap
quotients. -/
def normalizedDeletedQuotientEvaluationMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun j i => (sourceNormalizedQuotient nodes (omitted.succAbove i)).eval
    (nodes.point (interiorNodeIndex j))

theorem normalizedDeletedQuotientEvaluationMatrix_det_ne_zero {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (omitted : Fin (d + 1)) :
    (normalizedDeletedQuotientEvaluationMatrix nodes omitted).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let p : ℝ[X] := ∑ i : Fin d,
    C (c i) * sourceNormalizedQuotient nodes (omitted.succAbove i)
  have hpdegree : p.natDegree < d := by
    have hle : p.natDegree ≤ d - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (natDegree_sourceNormalizedQuotient_le nodes hd _)
    omega
  have hp_eval (j : Fin d) : p.eval (nodes.point (interiorNodeIndex j)) = 0 := by
    have hj := congrFun hc j
    simp only [normalizedDeletedQuotientEvaluationMatrix, Matrix.mulVec,
      dotProduct, p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Pi.zero_apply] at hj ⊢
    simpa only [mul_comm] using hj
  let s : Finset ℝ := Finset.univ.image
    (fun j : Fin d => nodes.point (interiorNodeIndex j))
  have hxinj : Function.Injective
      (fun j : Fin d => nodes.point (interiorNodeIndex j)) :=
    nodes.strictMono.injective.comp interiorNodeIndex_strictMono.injective
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ,
      Fintype.card_fin]
  have hpzero : p = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
    · rw [hs_card]
      exact Polynomial.degree_le_natDegree.trans_lt
        (WithBot.coe_lt_coe.mpr hpdegree)
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
      exact hp_eval j
  let a : Fin (d + 1) → ℝ :=
    Fin.succAboveCases (α := fun _ => ℝ) omitted 0 c
  have harel :
      (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0 := by
    rw [Fin.sum_univ_succAbove
      (fun i => C (a i) * sourceNormalizedQuotient nodes i) omitted]
    simp [a]
    exact hpzero
  have hane : a ≠ 0 := by
    intro ha
    apply hcne
    funext i
    have hi := congrFun ha (omitted.succAbove i)
    simpa [a] using hi
  have hall := sourceNormalizedQuotient_relation_coeff_ne_zero
    nodes hd a harel hane omitted
  exact hall (by simp [a])

/-- Row normalization is exactly diagonal scaling of the transposed deleted
quotient-evaluation matrix. -/
lemma normalizedDeletedQuotientEvaluationMatrix_transpose_factorization
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B)
    (omitted : Fin (d + 1)) :
    (normalizedDeletedQuotientEvaluationMatrix nodes omitted).transpose =
      Matrix.diagonal
        (fun i => sourceQuotientNormalizer (omitted.succAbove i)) *
      (gapQuotientEvaluationMatrix nodes).submatrix omitted.succAbove id := by
  ext i j
  simp [normalizedDeletedQuotientEvaluationMatrix, sourceNormalizedQuotient,
    gapQuotientEvaluationMatrix, Matrix.diagonal_mul]

theorem deletedRowMinor_gapQuotientEvaluationMatrix_ne_zero_of_two_le
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 2 ≤ d)
    (omitted : Fin (d + 1)) :
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted ≠ 0 := by
  have hnormalized :=
    normalizedDeletedQuotientEvaluationMatrix_det_ne_zero nodes hd omitted
  have hfactor := congrArg Matrix.det
    (normalizedDeletedQuotientEvaluationMatrix_transpose_factorization
      nodes omitted)
  rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal] at hfactor
  have hnormalizer :
      (∏ i : Fin d, sourceQuotientNormalizer (omitted.succAbove i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _hi => sourceQuotientNormalizer_ne_zero _
  rw [deletedRowMinor]
  intro hminor
  rw [hminor, mul_zero] at hfactor
  exact hnormalized hfactor

theorem quotientEvaluationMaximalMinorsNonzero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    QuotientEvaluationMaximalMinorsNonzero nodes := by
  intro omitted
  by_cases hd0 : d = 0
  · subst d
    simp [deletedRowMinor]
  by_cases hd1 : d = 1
  · subst d
    rw [deletedRowMinor]
    have hentry := gapDerivativeQuotient_eval_neg_of_three_nodes
      nodes.toOrderedNodes (omitted.succAbove 0)
        (nodes.point (interiorNodeIndex 0))
    simpa [gapQuotientEvaluationMatrix, Matrix.det_fin_one] using
      (ne_of_lt hentry)
  · exact deletedRowMinor_gapQuotientEvaluationMatrix_ne_zero_of_two_le
      nodes (by omega) omitted

theorem gapHeightJacobianModel_maximalMinors_nonzero_unconditional
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (hd : 1 ≤ d) :
    ∀ omitted : Fin (d + 1),
      deletedRowMinor (gapHeightJacobianModel nodes) omitted ≠ 0 :=
  gapHeightJacobianModel_maximalMinors_nonzero nodes hd
    (quotientEvaluationMaximalMinorsNonzero nodes)

/-! ## Coherent signs of all row-deleted minors -/

/-- The signed maximal minor which occurs in the usual left-kernel cofactor
vector of a `(d+1)×d` matrix. -/
def gapQuotientCofactor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (i : Fin (d + 1)) : ℝ :=
  (-1 : ℝ) ^ i.val *
    deletedRowMinor (gapQuotientEvaluationMatrix nodes) i

/-- Square augmentation of the quotient matrix by a duplicate of column
`j`.  Its determinant vanishes, and expansion down column zero gives the
cofactor relation. -/
private def duplicateQuotientColumnMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases (gapQuotientEvaluationMatrix nodes i j)
    (fun k' => gapQuotientEvaluationMatrix nodes i k') k

lemma gapQuotientCofactor_evaluation_sum_eq_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (j : Fin d) :
    ∑ i : Fin (d + 1), gapQuotientCofactor nodes i *
      gapQuotientEvaluationMatrix nodes i j = 0 := by
  let M := duplicateQuotientColumnMatrix nodes j
  have hcols : ∀ i, M i 0 = M i j.succ := by
    intro i
    simp [M, duplicateQuotientColumnMatrix]
  have hne : (0 : Fin (d + 1)) ≠ j.succ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hdet : M.det = 0 := Matrix.det_zero_of_column_eq hne hcols
  have hexpand := Matrix.det_succ_column M (0 : Fin (d + 1))
  rw [hdet] at hexpand
  have hminor (i : Fin (d + 1)) :
      (M.submatrix i.succAbove (0 : Fin (d + 1)).succAbove).det =
        deletedRowMinor (gapQuotientEvaluationMatrix nodes) i := by
    rw [deletedRowMinor]
    congr 1
  simp only [Fin.val_zero, Nat.add_zero, M, duplicateQuotientColumnMatrix,
    Fin.cases_zero, hminor] at hexpand
  simpa [gapQuotientCofactor, mul_assoc, mul_left_comm, mul_comm] using
    hexpand.symm

theorem gapQuotientCofactor_polynomial_relation {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) :
    (∑ i : Fin (d + 1), C (gapQuotientCofactor nodes i) *
      gapDerivativeQuotient nodes.toOrderedNodes i) = 0 := by
  let p : ℝ[X] := ∑ i : Fin (d + 1), C (gapQuotientCofactor nodes i) *
    gapDerivativeQuotient nodes.toOrderedNodes i
  have hpdegree : p.natDegree < d := by
    have hle : p.natDegree ≤ d - 1 := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro i hi
      exact (Polynomial.natDegree_C_mul_le _ _).trans
        (by
          have hq := natDegree_gapDerivativeQuotient_le_sub_three
            (n := d + 2) nodes.toOrderedNodes (by omega) i
          omega)
    omega
  let s : Finset ℝ := Finset.univ.image
    (fun j : Fin d => nodes.point (interiorNodeIndex j))
  have hxinj : Function.Injective
      (fun j : Fin d => nodes.point (interiorNodeIndex j)) :=
    nodes.strictMono.injective.comp interiorNodeIndex_strictMono.injective
  have hs_card : s.card = d := by
    rw [Finset.card_image_of_injective _ hxinj, Finset.card_univ,
      Fintype.card_fin]
  change p = 0
  apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
  · rw [hs_card]
    exact Polynomial.degree_le_natDegree.trans_lt
      (WithBot.coe_lt_coe.mpr hpdegree)
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨j, _hj, rfl⟩
    simp only [p, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C]
    exact gapQuotientCofactor_evaluation_sum_eq_zero nodes j

/-- The source relation theorem applied to the cofactor relation.  In raw
row convention, the cofactor coefficients alternate strictly. -/
theorem gapQuotientCofactor_alternating_sign {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 2 ≤ d) :
    (∀ i : Fin (d + 1),
      (-1 : ℝ) ^ i.val * gapQuotientCofactor nodes i < 0) ∨
    (∀ i : Fin (d + 1),
      0 < (-1 : ℝ) ^ i.val * gapQuotientCofactor nodes i) := by
  let a : Fin (d + 1) → ℝ := fun i =>
    sourceQuotientNormalizer i * gapQuotientCofactor nodes i
  have hrel : (∑ i, C (a i) * sourceNormalizedQuotient nodes i) = 0 := by
    calc
      (∑ i, C (a i) * sourceNormalizedQuotient nodes i) =
          ∑ i, C (gapQuotientCofactor nodes i) *
            gapDerivativeQuotient nodes.toOrderedNodes i := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [sourceNormalizedQuotient]
        have hs := sourceQuotientNormalizer_sq i
        change C (sourceQuotientNormalizer i * gapQuotientCofactor nodes i) *
            (C (sourceQuotientNormalizer i) *
              gapDerivativeQuotient nodes.toOrderedNodes i) = _
        rw [← mul_assoc, ← map_mul]
        congr 2
        calc
          sourceQuotientNormalizer i * gapQuotientCofactor nodes i *
              sourceQuotientNormalizer i =
              gapQuotientCofactor nodes i *
                sourceQuotientNormalizer i ^ 2 := by ring
          _ = gapQuotientCofactor nodes i := by rw [hs, mul_one]
      _ = 0 := gapQuotientCofactor_polynomial_relation nodes hd
  have hane : a ≠ 0 := by
    intro ha
    have h0 := congrFun ha (0 : Fin (d + 1))
    have hc0 := quotientEvaluationMaximalMinorsNonzero nodes (0 : Fin (d + 1))
    have hcofactor0 : gapQuotientCofactor nodes 0 ≠ 0 := by
      simpa [gapQuotientCofactor] using hc0
    dsimp [a] at h0
    exact hcofactor0 ((mul_eq_zero.mp h0).resolve_left
      (sourceQuotientNormalizer_ne_zero 0))
  rcases sourceNormalizedQuotient_relation_sign_pattern nodes hd a hrel hane with
    hneg | hpos
  · left
    intro i
    by_cases hi : i = 0
    · subst i
      dsimp [a, sourceQuotientNormalizer] at hneg
      simpa using hneg.1
    · have hi' := hneg.2 i hi
      dsimp [a, sourceQuotientNormalizer] at hi'
      rw [if_neg hi] at hi'
      exact hi'
  · right
    intro i
    by_cases hi : i = 0
    · subst i
      dsimp [a, sourceQuotientNormalizer] at hpos
      simpa using hpos.1
    · have hi' := hpos.2 i hi
      dsimp [a, sourceQuotientNormalizer] at hi'
      rw [if_neg hi] at hi'
      exact hi'

/-- All raw row-deleted quotient-evaluation minors have one coherent strict
sign.  This is stronger than pointwise nonvanishing and is the orientation
input needed by the consecutive-gap-difference Jacobian. -/
theorem gapQuotientEvaluation_deletedRowMinors_coherent_sign {d : ℕ}
    {A B : ℝ} (nodes : EndpointArray d A B) :
    (∀ omitted : Fin (d + 1),
      deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted < 0) ∨
    (∀ omitted : Fin (d + 1),
      0 < deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted) := by
  by_cases hd0 : d = 0
  · subst d
    right
    intro omitted
    simp [deletedRowMinor]
  by_cases hd1 : d = 1
  · subst d
    left
    intro omitted
    rw [deletedRowMinor]
    simpa [gapQuotientEvaluationMatrix, Matrix.det_fin_one] using
      gapDerivativeQuotient_eval_neg_of_three_nodes nodes.toOrderedNodes
        (omitted.succAbove 0) (nodes.point (interiorNodeIndex 0))
  · rcases gapQuotientCofactor_alternating_sign nodes (by omega) with
      hneg | hpos
    · left
      intro omitted
      have h := hneg omitted
      rw [gapQuotientCofactor] at h
      nlinarith [sq_negOnePow omitted.val]
    · right
      intro omitted
      have h := hpos omitted
      rw [gapQuotientCofactor] at h
      nlinarith [sq_negOnePow omitted.val]

/-! ## Transfer to the height Jacobian and consecutive differences -/

/-- The explicit diagonal row/column factor multiplying a quotient minor has
the row-deletion sign `(-1)^omitted`. -/
theorem gapHeightMinor_diagonalFactor_parity_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (hd : 1 ≤ d)
    (omitted : Fin (d + 1)) :
    0 < (-1 : ℝ) ^ omitted.val *
      ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
        ∏ j : Fin d, gapJacobianColumnFactor nodes j) := by
  have hrow : 0 < ∏ i : Fin d,
      ((-1 : ℝ) ^ (d + 1 - (omitted.succAbove i).val) *
        gapJacobianRowFactor nodes (omitted.succAbove i)) := by
    apply Finset.prod_pos
    intro i _hi
    exact gapJacobianRowFactor_parity_pos nodes hd _
  have hcol : 0 < ∏ j : Fin d,
      ((-1 : ℝ) ^ (d - j.val) * gapJacobianColumnFactor nodes j) := by
    apply Finset.prod_pos
    intro j _hj
    exact gapJacobianColumnFactor_parity_pos nodes j
  have hboth := mul_pos hrow hcol
  rw [← heightMinorFactorParity_eq_negOnePow d omitted]
  simpa [heightMinorFactorParity, Finset.prod_mul_distrib, mul_assoc,
    mul_left_comm, mul_comm] using hboth

/-- Coherent orientation of all height-Jacobian maximal minors.  The
row-deletion cofactor signs, rather than the bare minors, are equal: they are
all strictly negative or all strictly positive. -/
def AlternatingHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) : Prop :=
  (∀ omitted : Fin (d + 1),
      (-1 : ℝ) ^ omitted.val *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted < 0) ∨
  (∀ omitted : Fin (d + 1),
      0 < (-1 : ℝ) ^ omitted.val *
        deletedRowMinor (gapHeightJacobianModel nodes) omitted)

theorem alternatingHeightMaximalMinorSigns {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    AlternatingHeightMaximalMinorSigns nodes := by
  by_cases hd0 : d = 0
  · subst d
    right
    intro omitted
    simp [deletedRowMinor_zero_dim]
  have hd : 1 ≤ d := by omega
  rcases gapQuotientEvaluation_deletedRowMinors_coherent_sign nodes with
    hqneg | hqpos
  · left
    intro omitted
    rw [deletedRowMinor_gapHeightJacobianModel]
    have hfactor := gapHeightMinor_diagonalFactor_parity_pos nodes hd omitted
    have hq := hqneg omitted
    calc
      (-1 : ℝ) ^ omitted.val *
          ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j) =
          ((-1 : ℝ) ^ omitted.val *
            ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted := by ring
      _ < 0 := mul_neg_of_pos_of_neg hfactor hq
  · right
    intro omitted
    rw [deletedRowMinor_gapHeightJacobianModel]
    have hfactor := gapHeightMinor_diagonalFactor_parity_pos nodes hd omitted
    have hq := hqpos omitted
    calc
      0 < ((-1 : ℝ) ^ omitted.val *
            ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted :=
        mul_pos hfactor hq
      _ = (-1 : ℝ) ^ omitted.val *
          ((∏ i : Fin d, gapJacobianRowFactor nodes (omitted.succAbove i)) *
            deletedRowMinor (gapQuotientEvaluationMatrix nodes) omitted *
              ∏ j : Fin d, gapJacobianColumnFactor nodes j) := by ring

/-- Adjoin a leading column of ones to the rectangular height Jacobian.  Its
first-column cofactors are exactly the signed height maximal minors. -/
def augmentedGapHeightJacobianMatrix {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i k => Fin.cases 1 (fun j => gapHeightJacobianModel nodes i j) k

lemma augmentedGapHeightJacobianMatrix_minor {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (omitted : Fin (d + 1)) :
    ((augmentedGapHeightJacobianMatrix nodes).submatrix omitted.succAbove
      (0 : Fin (d + 1)).succAbove).det =
        deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
  rw [deletedRowMinor]
  congr 1

/-- The augmented determinant has the common strict cofactor sign. -/
theorem augmentedGapHeightJacobianMatrix_det_sign {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    (augmentedGapHeightJacobianMatrix nodes).det < 0 ∨
      0 < (augmentedGapHeightJacobianMatrix nodes).det := by
  have hexpand := Matrix.det_succ_column_zero
    (augmentedGapHeightJacobianMatrix nodes)
  simp only [augmentedGapHeightJacobianMatrix, Fin.cases_zero, mul_one] at hexpand
  rcases alternatingHeightMaximalMinorSigns nodes with hneg | hpos
  · left
    rw [hexpand]
    apply Finset.sum_neg
    · intro i _hi
      exact hneg i
    · exact Finset.univ_nonempty
  · right
    rw [hexpand]
    apply Finset.sum_pos
    · intro i _hi
      exact hpos i
    · exact Finset.univ_nonempty

theorem augmentedGapHeightJacobianMatrix_det_ne_zero {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    (augmentedGapHeightJacobianMatrix nodes).det ≠ 0 := by
  rcases augmentedGapHeightJacobianMatrix_det_sign nodes with h | h
  · exact ne_of_lt h
  · exact ne_of_gt h

/-- The actual consecutive-row-difference matrix is nonsingular.  The proof
uses the augmented determinant: a kernel vector for all consecutive
differences would make all height-row evaluations equal, hence extend to a
nonzero kernel vector of the augmented matrix. -/
theorem gapHeightJacobianModel_consecutiveDifference_det_ne_zero
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Matrix.det (fun i j : Fin d =>
      gapHeightJacobianModel nodes i.succ j -
        gapHeightJacobianModel nodes i.castSucc j) ≠ 0 := by
  classical
  intro hdet
  let D : Matrix (Fin d) (Fin d) ℝ := fun i j =>
    gapHeightJacobianModel nodes i.succ j -
      gapHeightJacobianModel nodes i.castSucc j
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr
    (show D.det = 0 from hdet)
  let rowValue : Fin (d + 1) → ℝ := fun i =>
    ∑ j : Fin d, gapHeightJacobianModel nodes i j * v j
  have hadj (i : Fin d) : rowValue i.succ = rowValue i.castSucc := by
    have hi := congrFun hv i
    simp only [D, Matrix.mulVec, dotProduct, Pi.zero_apply, rowValue] at hi ⊢
    simp_rw [sub_mul] at hi
    rw [Finset.sum_sub_distrib] at hi
    linarith
  have hconst (i : Fin (d + 1)) : rowValue i = rowValue 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hadj i).trans ih
  let w : Fin (d + 1) → ℝ :=
    Fin.cases (-(rowValue 0)) v
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    funext j
    have hj := congrFun hw j.succ
    simpa [w] using hj
  have hAw : (augmentedGapHeightJacobianMatrix nodes).mulVec w = 0 := by
    funext i
    rw [show (augmentedGapHeightJacobianMatrix nodes).mulVec w i =
        -(rowValue 0) + rowValue i by
      simp [Matrix.mulVec, dotProduct, augmentedGapHeightJacobianMatrix,
        w, Fin.sum_univ_succ, rowValue]]
    rw [hconst i]
    simp
  have hA0 : (augmentedGapHeightJacobianMatrix nodes).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hwne, hAw⟩
  exact (augmentedGapHeightJacobianMatrix_det_ne_zero nodes) hA0

end

end Randy1153.DeBoorPinkus
