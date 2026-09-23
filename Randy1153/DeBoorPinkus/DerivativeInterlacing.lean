import Randy1153.DeBoorPinkus.CrossInterlacing
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Derivative interlacing and the critical-quotient sign table

This file isolates source Lemma 2 of de Boor--Pinkus.  The critical points
`gapArgmax nodes g` are written in their actual nodal-gap order, and the
quotient `gapDerivativeQuotient nodes g = F'_g / (X - τ_g)` is kept in the
fixed sign convention of `GapCritical`.
-/

namespace Randy1153.DeBoorPinkus

open Polynomial
open scoped BigOperators

noncomputable section

/-- Critical points occur in strict nodal-gap order. -/
lemma gapArgmax_lt_of_gap_lt {n : ℕ} (nodes : OrderedNodes n)
    (hn : 3 ≤ n) {g h : Fin (n - 1)} (hgh : g < h) :
    gapArgmax nodes g < gapArgmax nodes h := by
  exact openGap_point_lt_of_gap_lt nodes hgh
    (gapArgmax_mem_openGap nodes hn g)
    (gapArgmax_mem_openGap nodes hn h)

lemma gapArgmax_strictMono {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    StrictMono (gapArgmax nodes) :=
  fun _g _h hgh => gapArgmax_lt_of_gap_lt nodes hn hgh

/-- Off the removed critical point, quotient evaluation is exactly derivative
evaluation divided by the ordered critical-point displacement. -/
lemma gapDerivativeQuotient_eval_eq_derivative_div {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) (i j : Fin (n - 1)) (hij : j ≠ i) :
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) =
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) /
        (gapArgmax nodes j - gapArgmax nodes i) := by
  have hargne : gapArgmax nodes j - gapArgmax nodes i ≠ 0 := by
    rw [sub_ne_zero]
    exact (gapArgmax_strictMono nodes hn).injective.ne hij
  have hfactor := congrArg (Polynomial.eval (gapArgmax nodes j))
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes hn i)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  rw [eq_div_iff hargne]
  calc
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) *
        (gapArgmax nodes j - gapArgmax nodes i) =
        (gapArgmax nodes j - gapArgmax nodes i) *
          (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j) := by ring
    _ = (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) := hfactor

/-- The raw quotient sign table used by the Jacobian evaluation matrix.
The committed sign convention makes every diagonal entry negative.  Every
off-diagonal entry has checkerboard sign `(-1)^(i+j)`.

The finite Markov/Wronskian argument below inhabits this proposition for
every `n ≥ 4`; the separate constant-quotient proof handles `n = 3`. -/
def DerivativeQuotientSignTable {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  (∀ i : Fin (n - 1),
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes i) < 0) ∧
  (∀ i j : Fin (n - 1), i ≠ j →
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (gapDerivativeQuotient nodes i).eval (gapArgmax nodes j))

/-- The derivative-evaluation form of the off-diagonal part of source
Lemma 2.  Splitting at `i<j` is intentional: the factor
`\tau_j-\tau_i` changes sign across the diagonal.

This is the exact finite Markov conclusion proved below from the source's
sum/difference root counts and a checked negative-squares Wronskian
identity. -/
def CrossDerivativeCriticalSignTable {n : ℕ}
    (nodes : OrderedNodes n) : Prop :=
  (∀ i j : Fin (n - 1), i < j →
    0 < (-1 : ℝ) ^ (i.val + j.val) *
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j)) ∧
  (∀ i j : Fin (n - 1), j < i →
    (-1 : ℝ) ^ (i.val + j.val) *
      (gapPolynomial nodes i).derivative.eval (gapArgmax nodes j) < 0)

/-- The quotient checkerboard signs imply precisely the two oriented
cross-derivative sign families.  This direction uses no root-interlacing
input beyond the strict order of the chosen critical points. -/
lemma crossDerivativeCriticalSignTable_of_derivativeQuotientSignTable
    {n : ℕ} (nodes : OrderedNodes n) (hn : 3 ≤ n)
    (htable : DerivativeQuotientSignTable nodes) :
    CrossDerivativeCriticalSignTable nodes := by
  constructor
  · intro i j hij
    have hq := htable.2 i j (ne_of_lt hij)
    have hfactor := congrArg (Polynomial.eval (gapArgmax nodes j))
      (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes hn i)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hfactor
    have hdisp : 0 < gapArgmax nodes j - gapArgmax nodes i :=
      sub_pos.mpr (gapArgmax_lt_of_gap_lt nodes hn hij)
    rw [← hfactor]
    nlinarith
  · intro i j hji
    have hq := htable.2 i j (ne_of_gt hji)
    have hfactor := congrArg (Polynomial.eval (gapArgmax nodes j))
      (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes hn i)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hfactor
    have hdisp : gapArgmax nodes j - gapArgmax nodes i < 0 :=
      sub_neg.mpr (gapArgmax_lt_of_gap_lt nodes hn hji)
    rw [← hfactor]
    nlinarith

/-- Conversely, once the finite Markov derivative signs are known, division
by the ordered critical displacement gives the paper's quotient sign table.
The diagonal is supplied independently by strict concavity on the owning
gap. -/
theorem derivativeQuotientSignTable_of_crossDerivativeCriticalSignTable
    {n : ℕ} (nodes : OrderedNodes n) (hn : 4 ≤ n)
    (hcross : CrossDerivativeCriticalSignTable nodes) :
    DerivativeQuotientSignTable nodes := by
  constructor
  · exact fun i => gapDerivativeQuotient_eval_gapArgmax_neg nodes hn i
  · intro i j hij
    rw [gapDerivativeQuotient_eval_eq_derivative_div nodes (by omega) i j hij.symm]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · simpa only [div_eq_mul_inv, mul_assoc] using
        div_pos (hcross.1 i j hijlt)
          (sub_pos.mpr (gapArgmax_lt_of_gap_lt nodes (by omega) hijlt))
    · simpa only [div_eq_mul_inv, mul_assoc] using
        div_pos_of_neg_of_neg (hcross.2 i j hjilt)
          (sub_neg.mpr (gapArgmax_lt_of_gap_lt nodes (by omega) hjilt))

/-- All of the common-nodal-gap root ordering furnished by source Lemma 1,
packaged as the checked internal input to the finite Markov step.  This does
not claim the possible exterior roots have been placed. -/
def CommonGapRootInterlacing {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  ∀ (g h : Fin (n - 1)) (hgh : g < h),
    StrictCrossRootOrder nodes g h hgh

theorem commonGapRootInterlacing {n : ℕ} (nodes : OrderedNodes n) :
    CommonGapRootInterlacing nodes :=
  fun g h hgh => strictCrossRootOrder nodes g h hgh

/-! ### A finite Markov kernel via the two source combinations

For `D = F_g - ε F_h` and `S = F_g + ε F_h`, the checked roots of
`D` are exhaustive and simple.  The source `S`-roots lie one in every
interval between consecutive `D`-roots.  The following elementary
Lagrange/Wronskian kernel is the finite specialization needed here: if the
residues `S(d_k) / D'(d_k)` are positive, then

`D S' - D' S < 0`

on the whole real line.  This is the sum-of-negative-squares proof of the
Markov monotonicity assertion, not an imported interlacing theorem. -/

private def finiteRootProduct {m : ℕ} (d : Fin m → ℝ) : ℝ[X] :=
  ∏ k : Fin m, (X - C (d k))

private def finiteRootComplement {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  ∏ l ∈ (Finset.univ.erase k : Finset (Fin m)), (X - C (d l))

private lemma finiteRootProduct_eq_mul_complement {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    finiteRootProduct d = (X - C (d k)) * finiteRootComplement d k := by
  classical
  rw [finiteRootProduct, Fintype.prod_eq_mul_prod_compl k]
  simp only [finiteRootComplement, Finset.compl_singleton]

private lemma finiteRootComplement_eval_self_ne_zero {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    (finiteRootComplement d k).eval (d k) ≠ 0 := by
  classical
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
  exact sub_ne_zero.mpr (hd.ne hlk.symm)

private lemma finiteRootProduct_derivative_eval_root {m : ℕ}
    (d : Fin m → ℝ) (k : Fin m) :
    (finiteRootProduct d).derivative.eval (d k) =
      (finiteRootComplement d k).eval (d k) := by
  rw [finiteRootProduct_eq_mul_complement d k, Polynomial.derivative_mul]
  simp

/-- Cardinal basis attached to a finite strictly ordered root list, written
in the unnormalized complement-product form needed by the Wronskian
calculation. -/
private def finiteRootBasis {m : ℕ} (d : Fin m → ℝ)
    (k : Fin m) : ℝ[X] :=
  C ((finiteRootComplement d k).eval (d k))⁻¹ *
    finiteRootComplement d k

private lemma finiteRootBasis_eval_self {m : ℕ} {d : Fin m → ℝ}
    (hd : Function.Injective d) (k : Fin m) :
    (finiteRootBasis d k).eval (d k) = 1 := by
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  exact inv_mul_cancel₀ (finiteRootComplement_eval_self_ne_zero hd k)

private lemma finiteRootBasis_eval_of_ne {m : ℕ} {d : Fin m → ℝ}
    (k l : Fin m) (hlk : l ≠ k) :
    (finiteRootBasis d k).eval (d l) = 0 := by
  classical
  rw [finiteRootBasis, Polynomial.eval_mul, Polynomial.eval_C]
  suffices (finiteRootComplement d k).eval (d l) = 0 by rw [this, mul_zero]
  simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩)
  simp

private lemma finiteRootBasis_eq_lagrangeBasis {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (k : Fin m) :
    finiteRootBasis d k = Lagrange.basis Finset.univ d k := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hd.injOn
  · have hEvalNe := finiteRootComplement_eval_self_ne_zero hd k
    have hComplementNe : finiteRootComplement d k ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.eval_zero] at hEvalNe
      exact hEvalNe rfl
    rw [finiteRootBasis, Polynomial.degree_mul,
      Polynomial.degree_C (inv_ne_zero hEvalNe), zero_add,
      Polynomial.degree_eq_natDegree hComplementNe,
      finiteRootComplement, natDegree_finset_prod_X_sub_C_eq_card,
      Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · have hdegree := Lagrange.degree_basis hd.injOn (Finset.mem_univ k)
    rw [hdegree, Finset.card_univ, Fintype.card_fin]
    exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one
  · intro l _hl
    by_cases hlk : l = k
    · subst l
      rw [finiteRootBasis_eval_self hd]
      exact (Lagrange.eval_basis_self hd.injOn (Finset.mem_univ k)).symm
    · rw [finiteRootBasis_eval_of_ne k l hlk]
      exact (Lagrange.eval_basis_of_ne (Ne.symm hlk) (Finset.mem_univ l)).symm

private lemma finiteRootBasis_wronskian {m : ℕ} (d : Fin m → ℝ)
    (scale : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (finiteRootBasis d k).eval x) =
      -(scale * ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  rw [finiteRootProduct_eq_mul_complement d k]
  simp only [finiteRootBasis, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_zero,
    Polynomial.eval_one]
  ring

private lemma finiteRootScaledBasis_wronskian {m : ℕ}
    (d : Fin m → ℝ) (scale value : ℝ) (k : Fin m) (x : ℝ) :
    ((finiteRootProduct d * C scale).eval x *
        (C value * finiteRootBasis d k).derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x *
        (C value * finiteRootBasis d k).eval x) =
      -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by
  have hbase := finiteRootBasis_wronskian d scale k x
  calc
    (finiteRootProduct d * C scale).eval x *
          (C value * finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (C value * finiteRootBasis d k).eval x =
        value * ((finiteRootProduct d * C scale).eval x *
          (finiteRootBasis d k).derivative.eval x -
        (finiteRootProduct d * C scale).derivative.eval x *
          (finiteRootBasis d k).eval x) := by
            simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
              zero_mul, zero_add, Polynomial.eval_mul, Polynomial.eval_C]
            ring
    _ = value * (-(scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2) := by rw [hbase]
    _ = -(value * scale *
          ((finiteRootComplement d k).eval (d k))⁻¹) *
        ((finiteRootComplement d k).eval x) ^ 2 := by ring

private def finiteRootInterpolant {m : ℕ} (d : Fin m → ℝ)
    (S : ℝ[X]) : ℝ[X] :=
  ∑ k : Fin m, C (S.eval (d k)) * finiteRootBasis d k

private lemma finiteRootInterpolant_eq_lagrange {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    finiteRootInterpolant d S =
      Lagrange.interpolate Finset.univ d (fun k => S.eval (d k)) := by
  classical
  rw [finiteRootInterpolant, Lagrange.interpolate_apply]
  simp only [finiteRootBasis_eq_lagrangeBasis hd]

private lemma finiteRootInterpolant_degree_lt {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X]) :
    (finiteRootInterpolant d S).degree < m := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := Finset.univ) (v := d)
      (fun k => S.eval (d k)) hd.injOn

private lemma finiteRootInterpolant_eval_root {m : ℕ}
    {d : Fin m → ℝ} (hd : Function.Injective d) (S : ℝ[X])
    (k : Fin m) :
    (finiteRootInterpolant d S).eval (d k) = S.eval (d k) := by
  rw [finiteRootInterpolant_eq_lagrange hd]
  exact Lagrange.eval_interpolate_at_node _ hd.injOn (Finset.mem_univ k)

private lemma exists_finiteRootComplement_eval_ne_zero {m : ℕ}
    (hm : 0 < m) {d : Fin m → ℝ} (hd : Function.Injective d) (x : ℝ) :
    ∃ k : Fin m, (finiteRootComplement d k).eval x ≠ 0 := by
  classical
  by_cases hx : ∃ k : Fin m, x = d k
  · obtain ⟨k, rfl⟩ := hx
    exact ⟨k, finiteRootComplement_eval_self_ne_zero hd k⟩
  · let k : Fin m := ⟨0, hm⟩
    refine ⟨k, ?_⟩
    simp only [finiteRootComplement, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro l _hl
    exact sub_ne_zero.mpr (fun heq => hx ⟨l, heq⟩)

/-- Finite V. A. Markov specialization in the form actually consumed below.
The proof is Lagrange interpolation modulo the exhaustive root product.
Every residue contributes a negative square, and at least one complementary
root product is nonzero at each real point. -/
private theorem finite_markov_wronskian_neg {m : ℕ} (hm : 0 < m)
    (d : Fin m → ℝ) (hd : Function.Injective d) (scale : ℝ)
    (hscale : scale ≠ 0) (S : ℝ[X]) (hSdegree : S.natDegree ≤ m)
    (hresidue : ∀ k : Fin m,
      0 < S.eval (d k) *
        (finiteRootProduct d * C scale).derivative.eval (d k))
    (x : ℝ) :
    (finiteRootProduct d * C scale).eval x * S.derivative.eval x -
      (finiteRootProduct d * C scale).derivative.eval x * S.eval x < 0 := by
  classical
  let M : ℝ[X] := finiteRootProduct d
  let D : ℝ[X] := M * C scale
  let R : ℝ[X] := finiteRootInterpolant d S
  have hMmonic : M.Monic := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)), (X - C (d k))).Monic
    exact monic_prod_of_monic _ _ fun k _hk => monic_X_sub_C (d k)
  have hMne : M ≠ 0 := hMmonic.ne_zero
  have hMdegree : M.natDegree = m := by
    change (∏ k ∈ (Finset.univ : Finset (Fin m)),
      (X - C (d k))).natDegree = m
    rw [natDegree_finset_prod_X_sub_C_eq_card, Finset.card_univ,
      Fintype.card_fin]
  have hRdegree : R.degree < m := by
    simpa only [R] using finiteRootInterpolant_degree_lt hd S
  have hRnatDegree : R.natDegree ≤ m := by
    rw [Polynomial.natDegree_le_iff_degree_le]
    exact hRdegree.le
  have hMdvd : M ∣ S - R := by
    change (∏ k : Fin m, (X - C (d k))) ∣ S - R
    apply Fintype.prod_dvd_of_coprime
    · exact pairwise_coprime_X_sub_C hd
    · intro k
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot,
        Polynomial.eval_sub]
      change S.eval (d k) - (finiteRootInterpolant d S).eval (d k) = 0
      rw [finiteRootInterpolant_eval_root hd S k, sub_self]
  obtain ⟨Q, hQ⟩ := hMdvd
  have hSRdegree : (S - R).natDegree ≤ m :=
    (Polynomial.natDegree_sub_le S R).trans (max_le hSdegree hRnatDegree)
  have hQdegree : Q.natDegree = 0 := by
    by_cases hQzero : Q = 0
    · simp [hQzero]
    · have hproduct : (M * Q).natDegree ≤ m := by
        rw [← hQ]
        exact hSRdegree
      rw [Polynomial.natDegree_mul hMne hQzero, hMdegree] at hproduct
      omega
  obtain ⟨q, hq⟩ := Polynomial.natDegree_eq_zero.mp hQdegree
  have hSfactor : S = R + M * C q := by
    rw [← hq] at hQ
    calc
      S = (S - R) + R := by ring
      _ = M * C q + R := by rw [hQ]
      _ = R + M * C q := by ring
  have hWinvariant :
      D.eval x * S.derivative.eval x - D.derivative.eval x * S.eval x =
        D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x := by
    rw [hSfactor]
    dsimp only [D]
    simp only [Polynomial.derivative_add, Polynomial.derivative_mul,
      Polynomial.derivative_C, mul_zero, add_zero,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  let coefficient : Fin m → ℝ := fun k =>
    S.eval (d k) * scale *
      ((finiteRootComplement d k).eval (d k))⁻¹
  have hcoefficient : ∀ k : Fin m, 0 < coefficient k := by
    intro k
    let e : ℝ := (finiteRootComplement d k).eval (d k)
    have he : e ≠ 0 := finiteRootComplement_eval_self_ne_zero hd k
    have hderivative : D.derivative.eval (d k) = e * scale := by
      simp only [D, M, Polynomial.derivative_mul, Polynomial.derivative_C,
        mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
      rw [finiteRootProduct_derivative_eval_root]
    have hpositive : 0 < S.eval (d k) * (e * scale) := by
      rw [← hderivative]
      simpa only [D, M] using hresidue k
    have he2 : 0 < e ^ 2 := sq_pos_of_ne_zero he
    have heq : coefficient k * e ^ 2 = S.eval (d k) * (e * scale) := by
      dsimp only [coefficient, e]
      field_simp
    nlinarith
  have hWsum :
      D.eval x * R.derivative.eval x - D.derivative.eval x * R.eval x =
        -∑ k : Fin m, coefficient k *
          ((finiteRootComplement d k).eval x) ^ 2 := by
    simp only [R, finiteRootInterpolant, Polynomial.derivative_sum,
      Polynomial.eval_finset_sum]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _hk
    rw [finiteRootScaledBasis_wronskian]
    simp only [coefficient]
    ring
  have hsumPos : 0 < ∑ k : Fin m, coefficient k *
      ((finiteRootComplement d k).eval x) ^ 2 := by
    apply Finset.sum_pos'
    · intro k _hk
      exact mul_nonneg (hcoefficient k).le (sq_nonneg _)
    · obtain ⟨k, hk⟩ := exists_finiteRootComplement_eval_ne_zero hm hd x
      exact ⟨k, Finset.mem_univ k,
        mul_pos (hcoefficient k) (sq_pos_of_ne_zero hk)⟩
  rw [hWinvariant, hWsum]
  exact neg_neg_of_pos hsumPos

private lemma negOnePowFilter_mul_prod_pos {α : Type*}
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
          _ = (-1 : ℝ) ^ (s.filter p).card *
              (f x * ∏ y ∈ s, f y) := by ring

private lemma card_filter_gt_erase_fin {m : ℕ} (k : Fin m) :
    (((Finset.univ.erase k : Finset (Fin m)).filter
      (fun l => k < l))).card = m - 1 - k.val := by
  have heq : (Finset.univ.erase k : Finset (Fin m)).filter
      (fun l => k < l) = Finset.Ioi k := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, Finset.mem_Ioi]
    omega
  rw [heq]
  simp

/-- Sign of the derivative of a monic product at its `k`th strictly ordered
root. -/
private lemma finiteRootComplement_checkerboard_sign {m : ℕ}
    {d : Fin m → ℝ} (hd : StrictMono d) (k : Fin m) :
    0 < (-1 : ℝ) ^ (m - 1 - k.val) *
      (finiteRootComplement d k).eval (d k) := by
  classical
  have hsign := negOnePowFilter_mul_prod_pos
    (Finset.univ.erase k : Finset (Fin m)) (fun l => k < l)
    (fun l => d k - d l)
    (fun l _hl hkl => sub_neg.mpr (hd hkl))
    (fun l hl hnkl => by
      have hlk : l ≠ k := (Finset.mem_erase.mp hl).1
      exact sub_pos.mpr (hd (lt_of_le_of_ne (le_of_not_gt hnkl) hlk)))
  rw [card_filter_gt_erase_fin k] at hsign
  simpa only [finiteRootComplement, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hsign

/-- Public `CrossInterlacing` exposes the factor-data structure but keeps its
choice private.  Reconstruct the witness here so the Markov kernel can use
the actual leading scale without assuming it. -/
private theorem exists_markovGapDifferenceFactorData {n : ℕ}
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

private lemma negOnePow_add_eq_sub {a b : ℕ} (hab : a ≤ b) :
    (-1 : ℝ) ^ (a + b) = (-1 : ℝ) ^ (b - a) := by
  have heq : a + b = (b - a) + 2 * a := by omega
  rw [heq, pow_add, pow_mul]
  norm_num

@[simp]
private lemma sq_negOnePow (a : ℕ) : ((-1 : ℝ) ^ a) ^ 2 = 1 := by
  rw [← pow_mul]
  have heq : a * 2 = 2 * a := by omega
  rw [heq, pow_mul]
  norm_num

/-- The source sum combination has the same checkerboard sign as the
derivative of the difference combination at every exhaustive difference
root. -/
private lemma gapSumCombination_eval_differenceRoot_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h) :
    0 < (-1 : ℝ) ^ (g.val + q.val) *
      (gapSumCombination nodes g h).eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  by_cases hqg : q.val ≤ g.val
  · rw [gapDifferenceRootPoint_eq_left_of_le nodes g h hgh q hqg,
      gapSumCombination_eval_node nodes g h hgh]
    have houtside : (gapLeftIndex q).val ≤ g.val ∨
        h.val < (gapLeftIndex q).val := Or.inl (by simpa using hqg)
    rw [if_pos houtside,
      gapCoefficient_of_le g (gapLeftIndex q) (by simpa using hqg)]
    simp only [gapLeftIndex_val]
    have hparity : (-1 : ℝ) ^ (g.val + q.val) =
        (-1 : ℝ) ^ (g.val - q.val) := by
      simpa only [Nat.add_comm] using negOnePow_add_eq_sub hqg
    rw [hparity]
    nlinarith [sq_negOnePow (g.val - q.val)]
  · by_cases hhq : h.val ≤ q.val
    · rw [gapDifferenceRootPoint_eq_right_of_le nodes g h hgh q hhq,
        gapSumCombination_eval_node nodes g h hgh]
      have houtside : (gapRightIndex q).val ≤ g.val ∨
          h.val < (gapRightIndex q).val := Or.inr (by simp; omega)
      have hgk : g.val < (gapRightIndex q).val := by simp; omega
      rw [if_pos houtside, gapCoefficient_of_lt g (gapRightIndex q) hgk]
      simp only [gapRightIndex_val]
      have hgq : g.val ≤ q.val := by omega
      have hexp : q.val + 1 - g.val - 1 = q.val - g.val := by omega
      rw [hexp]
      rw [negOnePow_add_eq_sub hgq]
      nlinarith [sq_negOnePow (q.val - g.val)]
    · have hgq : g < q := Fin.lt_def.mpr (by omega)
      have hqh : q < h := Fin.lt_def.mpr (by omega)
      have hmem := gapDifferenceRootPoint_mem_openGap_of_between
        nodes g h hgh q hgq hqh
      have hsign := gapSumCombination_sign_middleGap
        nodes g h q hgh hgq.le hqh hmem
      have hparity : (-1 : ℝ) ^ (g.val + q.val) =
          (-1 : ℝ) ^ (q.val - g.val) :=
        negOnePow_add_eq_sub hgq.le
      rwa [hparity]

private lemma card_filter_gt_fin {m : ℕ} (g : Fin m) :
    ((Finset.univ : Finset (Fin m)).filter (fun q => g < q)).card =
      m - 1 - g.val := by
  have heq : (Finset.univ : Finset (Fin m)).filter (fun q => g < q) =
      Finset.Ioi g := by
    ext q
    simp
  rw [heq]
  simp

private lemma negOnePow_two_complements_eq_add {m : ℕ}
    (g q : Fin m) :
    (-1 : ℝ) ^ (m - 1 - g.val) * (-1 : ℝ) ^ (m - 1 - q.val) =
      (-1 : ℝ) ^ (g.val + q.val) := by
  have heq : (m - 1 - g.val) + (m - 1 - q.val) +
      (g.val + q.val) = 2 * (m - 1) := by omega
  have hproduct :
      ((-1 : ℝ) ^ (m - 1 - g.val) *
        (-1 : ℝ) ^ (m - 1 - q.val)) *
          (-1 : ℝ) ^ (g.val + q.val) = 1 := by
    rw [← pow_add, ← pow_add, heq, pow_mul]
    norm_num
  calc
    (-1 : ℝ) ^ (m - 1 - g.val) * (-1 : ℝ) ^ (m - 1 - q.val) =
        ((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) * 1 := by ring
    _ = ((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) *
        (((-1 : ℝ) ^ (g.val + q.val)) ^ 2) := by
          rw [sq_negOnePow]
    _ = ((((-1 : ℝ) ^ (m - 1 - g.val) *
          (-1 : ℝ) ^ (m - 1 - q.val)) *
        (-1 : ℝ) ^ (g.val + q.val)) *
          (-1 : ℝ) ^ (g.val + q.val)) := by ring
    _ = (-1 : ℝ) ^ (g.val + q.val) := by rw [hproduct]; ring

/-- Sign of the scalar multiplying the exhaustive difference-root product,
anchored by the source value `D(x_{g+1}) = 2`. -/
private lemma gapDifferenceScale_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (-1 : ℝ) ^ (n - 2 - g.val) * data.scale := by
  classical
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  let y : ℝ := nodes.point (gapRightIndex g)
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hMySign : 0 < (-1 : ℝ) ^ (n - 2 - g.val) * M.eval y := by
    have hsign := negOnePowFilter_mul_prod_pos
      (Finset.univ : Finset (Fin (n - 1))) (fun q => g < q)
      (fun q => y - root q)
      (fun q _hq hgq => by
        have hleft : y ≤ nodes.point (gapLeftIndex q) := by
          apply nodes.strictMono.monotone
          apply Fin.le_iff_val_le_val.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega
        have hroot : nodes.point (gapLeftIndex q) < root q := by
          simpa only [root] using left_lt_gapDifferenceRootPoint_of_lt
            nodes g h hgh q hgq
        exact sub_neg.mpr (hleft.trans_lt hroot))
      (fun q _hq hngq => by
        have hqg : q.val ≤ g.val := by omega
        have hroot : root q = nodes.point (gapLeftIndex q) := by
          simpa only [root] using gapDifferenceRootPoint_eq_left_of_le
            nodes g h hgh q hqg
        change 0 < y - root q
        rw [hroot]
        exact sub_pos.mpr (nodes.strictMono (by
          apply Fin.lt_def.mpr
          simp only [gapRightIndex_val, gapLeftIndex_val]
          omega)))
    rw [card_filter_gt_fin g] at hsign
    rw [show n - 1 - 1 = n - 2 by omega] at hsign
    simpa only [M, finiteRootProduct, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, root, y]
      using hsign
  have hDy : (gapDifferenceCombination nodes g h).eval y = 2 := by
    rw [gapDifferenceCombination_eval_node nodes g h hgh]
    have hinside : ¬((gapRightIndex g).val ≤ g.val ∨
        h.val < (gapRightIndex g).val) := by
      simp only [gapRightIndex_val]
      omega
    rw [if_neg hinside]
    simp
  have hMscale : M.eval y * data.scale = 2 := by
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_C] at hDy
    exact hDy
  have hsquare := sq_negOnePow (n - 2 - g.val)
  by_contra hnot
  have hle : (-1 : ℝ) ^ (n - 2 - g.val) * data.scale ≤ 0 :=
    le_of_not_gt hnot
  have hproduct := mul_nonpos_of_nonneg_of_nonpos hMySign.le hle
  have heq :
      ((-1 : ℝ) ^ (n - 2 - g.val) * M.eval y) *
          ((-1 : ℝ) ^ (n - 2 - g.val) * data.scale) =
        M.eval y * data.scale := by nlinarith
  rw [heq, hMscale] at hproduct
  norm_num at hproduct

private lemma gapDifference_derivative_eval_root_checkerboard {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (-1 : ℝ) ^ (g.val + q.val) *
      (gapDifferenceCombination nodes g h).derivative.eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  let e : ℝ := (finiteRootComplement root q).eval (root q)
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hderivative :
      (gapDifferenceCombination nodes g h).derivative.eval (root q) =
        e * data.scale := by
    rw [hfactor]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
      mul_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
    rw [finiteRootProduct_derivative_eval_root]
  have hscale := gapDifferenceScale_checkerboard nodes g h hgh data
  have hcomplement :
      0 < (-1 : ℝ) ^ (n - 2 - q.val) * e := by
    have h := finiteRootComplement_checkerboard_sign
      (gapDifferenceRootPoint_strictMono nodes g h hgh) q
    rw [show n - 1 - 1 = n - 2 by omega] at h
    simpa only [e, root] using h
  have hparity := negOnePow_two_complements_eq_add
    (m := n - 1) g q
  rw [show n - 1 - 1 = n - 2 by omega] at hparity
  rw [hderivative, ← hparity]
  nlinarith [mul_pos hscale hcomplement]

private lemma gapDifference_sum_residue_pos {n : ℕ}
    (nodes : OrderedNodes n) (g h q : Fin (n - 1)) (hgh : g < h)
    (data : GapDifferenceFactorData nodes g h hgh) :
    0 < (gapSumCombination nodes g h).eval
        (gapDifferenceRootPoint nodes g h hgh q) *
      (gapDifferenceCombination nodes g h).derivative.eval
        (gapDifferenceRootPoint nodes g h hgh q) := by
  have hsum := gapSumCombination_eval_differenceRoot_checkerboard
    nodes g h q hgh
  have hderiv := gapDifference_derivative_eval_root_checkerboard
    nodes g h q hgh data
  have hsquare := sq_negOnePow (g.val + q.val)
  nlinarith [mul_pos hsum hderiv]

/-- The strict Wronskian form of the finite Markov theorem for the two
source combinations.  In particular it covers both possible degree cases
for `S`: the interpolation remainder removes a possible same-degree
exterior root automatically. -/
theorem gapCombination_wronskian_neg {n : ℕ} (nodes : OrderedNodes n)
    (g h : Fin (n - 1)) (hgh : g < h) (x : ℝ) :
    (gapDifferenceCombination nodes g h).eval x *
        (gapSumCombination nodes g h).derivative.eval x -
      (gapDifferenceCombination nodes g h).derivative.eval x *
        (gapSumCombination nodes g h).eval x < 0 := by
  let data := Classical.choice
    (exists_markovGapDifferenceFactorData nodes g h hgh)
  let root : Fin (n - 1) → ℝ := gapDifferenceRootPoint nodes g h hgh
  let M : ℝ[X] := finiteRootProduct root
  have hm : 0 < n - 1 := by
    have := g.isLt
    omega
  have hfactor : gapDifferenceCombination nodes g h = M * C data.scale := by
    simpa only [M, root, finiteRootProduct, gapDifferenceRootProduct] using
      data.factor
  have hmarkov := finite_markov_wronskian_neg hm root
    (gapDifferenceRootPoint_strictMono nodes g h hgh).injective
    data.scale data.scale_ne_zero (gapSumCombination nodes g h)
    (natDegree_gapSumCombination_le_sub_one nodes g h hgh)
    (fun q => by
      have hr := gapDifference_sum_residue_pos nodes g h q hgh data
      rw [hfactor] at hr
      simpa only [root] using hr) x
  rw [← hfactor] at hmarkov
  exact hmarkov

private lemma gapCombination_wronskian_eq_gapPolynomials {n : ℕ}
    (nodes : OrderedNodes n) (g h : Fin (n - 1)) (x : ℝ) :
    (gapDifferenceCombination nodes g h).eval x *
        (gapSumCombination nodes g h).derivative.eval x -
      (gapDifferenceCombination nodes g h).derivative.eval x *
        (gapSumCombination nodes g h).eval x =
      2 * gapPairParity g h *
        ((gapPolynomial nodes g).eval x *
            (gapPolynomial nodes h).derivative.eval x -
          (gapPolynomial nodes g).derivative.eval x *
            (gapPolynomial nodes h).eval x) := by
  simp only [gapDifferenceCombination, gapSumCombination,
    Polynomial.derivative_sub, Polynomial.derivative_add,
    Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C]
  ring

/-- Source Lemma 2 in the exact oriented form required by the quotient sign
table.  The proof specializes the checked negative Wronskian at the two
ordered own-gap critical points. -/
theorem crossDerivativeCriticalSignTable {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    CrossDerivativeCriticalSignTable nodes := by
  constructor
  · intro i j hij
    let x : ℝ := gapArgmax nodes j
    have hw := gapCombination_wronskian_neg nodes i j hij x
    rw [gapCombination_wronskian_eq_gapPolynomials] at hw
    have hjderiv := gapPolynomial_derivative_eval_gapArgmax nodes hn j
    have hjpos : 0 < (gapPolynomial nodes j).eval x := by
      exact zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap
        nodes hn j (gapArgmax_mem_openGap nodes hn j))
    have hprod : 0 < (gapPairParity i j *
        (gapPolynomial nodes i).derivative.eval x) *
          (gapPolynomial nodes j).eval x := by
      rw [show (gapPolynomial nodes j).derivative.eval x = 0 from hjderiv]
        at hw
      nlinarith
    have htarget : 0 < gapPairParity i j *
        (gapPolynomial nodes i).derivative.eval x := by
      rcases mul_pos_iff.mp hprod with hgood | hbad
      · exact hgood.1
      · exact (not_lt_of_ge hjpos.le hbad.2).elim
    have hparity : (-1 : ℝ) ^ (i.val + j.val) = gapPairParity i j := by
      rw [gapPairParity]
      exact negOnePow_add_eq_sub hij.le
    rwa [hparity]
  · intro i j hji
    let x : ℝ := gapArgmax nodes j
    have hw := gapCombination_wronskian_neg nodes j i hji x
    rw [gapCombination_wronskian_eq_gapPolynomials] at hw
    have hjderiv := gapPolynomial_derivative_eval_gapArgmax nodes hn j
    have hjpos : 0 < (gapPolynomial nodes j).eval x := by
      exact zero_lt_one.trans (one_lt_eval_gapPolynomial_of_mem_openGap
        nodes hn j (gapArgmax_mem_openGap nodes hn j))
    have hprod : (gapPairParity j i *
        (gapPolynomial nodes i).derivative.eval x) *
          (gapPolynomial nodes j).eval x < 0 := by
      rw [show (gapPolynomial nodes j).derivative.eval x = 0 from hjderiv]
        at hw
      nlinarith
    have htarget : gapPairParity j i *
        (gapPolynomial nodes i).derivative.eval x < 0 := by
      rcases mul_neg_iff.mp hprod with hgood | hbad
      · exact (not_lt_of_ge hjpos.le hgood.2).elim
      · exact hbad.1
    have hparity : (-1 : ℝ) ^ (i.val + j.val) = gapPairParity j i := by
      rw [gapPairParity, Nat.add_comm]
      exact negOnePow_add_eq_sub hji.le
    rwa [hparity]

/-- Complete general quotient sign table, including the diagonal supplied
by strict own-gap concavity. -/
theorem derivativeQuotientSignTable {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) :
    DerivativeQuotientSignTable nodes :=
  derivativeQuotientSignTable_of_crossDerivativeCriticalSignTable nodes hn
    (crossDerivativeCriticalSignTable nodes (by omega))

/-- The diagonal half of the quotient sign table for the genuine
multi-gap range. -/
lemma gapDerivativeQuotient_signTable_diagonal {n : ℕ}
    (nodes : OrderedNodes n) (hn : 4 ≤ n) (i : Fin (n - 1)) :
    (gapDerivativeQuotient nodes i).eval (gapArgmax nodes i) < 0 :=
  gapDerivativeQuotient_eval_gapArgmax_neg nodes hn i

/-- In the three-node case the removed-critical-factor quotient is constant. -/
lemma natDegree_gapDerivativeQuotient_eq_zero_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) :
    (gapDerivativeQuotient nodes i).natDegree = 0 := by
  rw [gapDerivativeQuotient,
    Polynomial.natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
  have hdegree := natDegree_gapPolynomial_derivative_le_one_of_three_nodes nodes i
  omega

/-- The three-node quotient has the same value at every point. -/
lemma gapDerivativeQuotient_eval_eq_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x y : ℝ) :
    (gapDerivativeQuotient nodes i).eval x =
      (gapDerivativeQuotient nodes i).eval y := by
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp
    (natDegree_gapDerivativeQuotient_eq_zero_of_three_nodes nodes i)
  rw [← hc]
  simp

/-- For three nodes the constant critical quotient is strictly negative.
This is the complete low-dimensional (`d=1`) sign table. -/
lemma gapDerivativeQuotient_eval_neg_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x : ℝ) :
    (gapDerivativeQuotient nodes i).eval x < 0 := by
  let p : ℝ[X] := gapPolynomial nodes i
  let a : ℝ := nodes.point (gapLeftIndex i)
  let τ : ℝ := gapArgmax nodes i
  have haτ : a < τ := (gapArgmax_mem_openGap nodes (by norm_num) i).1
  have hpa : p.eval a = 1 := by
    simpa only [p, a] using gapPolynomial_eval_left nodes i
  have hpτ : 1 < p.eval τ := by
    exact one_lt_eval_gapPolynomial_of_mem_openGap nodes (by norm_num) i
      (gapArgmax_mem_openGap nodes (by norm_num) i)
  obtain ⟨z, hz, hderiv⟩ := exists_deriv_eq_slope p.eval haτ
    p.continuous.continuousOn p.differentiable.differentiableOn
  have hslope : 0 < (p.eval τ - p.eval a) / (τ - a) :=
    div_pos (by rw [hpa]; linarith) (sub_pos.mpr haτ)
  have hdpz : 0 < p.derivative.eval z := by
    have hpderiv : deriv p.eval z = p.derivative.eval z := by
      simp only [Polynomial.deriv]
    rw [← hpderiv, hderiv]
    exact hslope
  have hfactor := congrArg (Polynomial.eval z)
    (X_sub_C_gapArgmax_mul_gapDerivativeQuotient nodes (by norm_num) i)
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hfactor
  have hzτ : z - τ < 0 := sub_neg.mpr hz.2
  have hqz : (gapDerivativeQuotient nodes i).eval z < 0 := by
    have hmul : 0 < (z - τ) * (gapDerivativeQuotient nodes i).eval z := by
      rwa [hfactor]
    rcases mul_pos_iff.mp hmul with hbad | hgood
    · exact (not_lt_of_ge hbad.1.le hzτ).elim
    · exact hgood.2
  rw [gapDerivativeQuotient_eval_eq_of_three_nodes nodes i x z]
  exact hqz

/-- Complete quotient sign table in the three-node (`d=1`) case. -/
theorem derivativeQuotientSignTable_three_nodes (nodes : OrderedNodes 3) :
    DerivativeQuotientSignTable nodes := by
  constructor
  · intro i
    exact gapDerivativeQuotient_eval_neg_of_three_nodes nodes i _
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    all_goals
      exact gapDerivativeQuotient_eval_neg_of_three_nodes nodes _ _

/-- Uniform nondegenerate sign-table API.  The proof keeps the constant
`n = 3` quotient separate from the strict-concavity `n ≥ 4` branch. -/
theorem derivativeQuotientSignTable_of_three_le {n : ℕ}
    (nodes : OrderedNodes n) (hn : 3 ≤ n) :
    DerivativeQuotientSignTable nodes := by
  by_cases heq : n = 3
  · subst n
    exact derivativeQuotientSignTable_three_nodes nodes
  · exact derivativeQuotientSignTable nodes (by omega)

/-- Explicit root-placement target supplied by source Lemma 2.  For the
quotient belonging to gap `i`, there is exactly one zero between consecutive
critical points `τ_j,τ_{j+1}` unless that interval touches `τ_i`.

The source's possible single exterior quotient zero is deliberately not
hidden in this interface.  The Wronskian proof above establishes the full
evaluation sign table without choosing that exterior zero; a later consumer
needing the complete global derivative-root list must still track it. -/
def InternalDerivativeInterlacing {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  ∀ (i : Fin (n - 1)) (j : Fin (n - 2)),
    j.val + 1 < i.val ∨ i.val < j.val →
      ∃! r : ℝ,
        r ∈ Set.Ioo (gapArgmax nodes ⟨j.val, by omega⟩)
          (gapArgmax nodes ⟨j.val + 1, by omega⟩) ∧
        (gapDerivativeQuotient nodes i).IsRoot r

/-- No quotient zero may occur in either critical interval adjacent to its
removed root.  This is the complementary, explicitly indexed half of source
Lemma 2. -/
def NoAdjacentDerivativeQuotientRoot {n : ℕ} (nodes : OrderedNodes n) : Prop :=
  ∀ (i : Fin (n - 1)) (j : Fin (n - 2)),
    (j.val = i.val ∨ j.val + 1 = i.val) →
      ∀ r ∈ Set.Ioo (gapArgmax nodes ⟨j.val, by omega⟩)
        (gapArgmax nodes ⟨j.val + 1, by omega⟩),
        ¬(gapDerivativeQuotient nodes i).IsRoot r

/-- Multiplicity-sensitive form of the internal part of source Lemma 2.
Strict derivative interlacing requires these zeros to be simple, not merely
distinct as points. -/
def SimpleInternalDerivativeInterlacing {n : ℕ}
    (nodes : OrderedNodes n) : Prop :=
  ∀ (i : Fin (n - 1)) (j : Fin (n - 2)),
    j.val + 1 < i.val ∨ i.val < j.val →
      ∃! r : ℝ,
        r ∈ Set.Ioo (gapArgmax nodes ⟨j.val, by omega⟩)
          (gapArgmax nodes ⟨j.val + 1, by omega⟩) ∧
        (gapDerivativeQuotient nodes i).IsRoot r ∧
        (gapDerivativeQuotient nodes i).rootMultiplicity r = 1

/-- The fully explicit internal conclusion of source Lemma 2.  The source
allows one possible exterior zero; it is intentionally not smuggled into
this internal statement. -/
def SourceLemmaTwoInternalPattern {n : ℕ}
    (nodes : OrderedNodes n) : Prop :=
  SimpleInternalDerivativeInterlacing nodes ∧
    NoAdjacentDerivativeQuotientRoot nodes

/-- The quotient is nowhere zero in the three-node case. -/
lemma not_isRoot_gapDerivativeQuotient_of_three_nodes
    (nodes : OrderedNodes 3) (i : Fin 2) (x : ℝ) :
    ¬(gapDerivativeQuotient nodes i).IsRoot x := by
  rw [Polynomial.IsRoot]
  exact ne_of_lt (gapDerivativeQuotient_eval_neg_of_three_nodes nodes i x)

/-- Source Lemma 2 has no internal quotient zero when there are only two
gaps: every critical interval touches the removed critical point. -/
theorem internalDerivativeInterlacing_three_nodes
    (nodes : OrderedNodes 3) :
    InternalDerivativeInterlacing nodes := by
  intro i j hfar
  fin_cases i <;> fin_cases j <;> omega

theorem simpleInternalDerivativeInterlacing_three_nodes
    (nodes : OrderedNodes 3) :
    SimpleInternalDerivativeInterlacing nodes := by
  intro i j hfar
  fin_cases i <;> fin_cases j <;> omega

theorem noAdjacentDerivativeQuotientRoot_three_nodes
    (nodes : OrderedNodes 3) :
    NoAdjacentDerivativeQuotientRoot nodes := by
  intro i j _hadj r _hr
  exact not_isRoot_gapDerivativeQuotient_of_three_nodes nodes i r

theorem sourceLemmaTwoInternalPattern_three_nodes
    (nodes : OrderedNodes 3) :
    SourceLemmaTwoInternalPattern nodes :=
  ⟨simpleInternalDerivativeInterlacing_three_nodes nodes,
    noAdjacentDerivativeQuotientRoot_three_nodes nodes⟩

/-- In the three-node case each derivative has exactly its own critical
point as a real zero, and the two zeros occur in strict gap order. -/
theorem derivativeZeros_three_nodes (nodes : OrderedNodes 3) :
    gapArgmax nodes (0 : Fin 2) < gapArgmax nodes (1 : Fin 2) ∧
    (∀ r : ℝ, (gapPolynomial nodes (0 : Fin 2)).derivative.eval r = 0 ↔
      r = gapArgmax nodes (0 : Fin 2)) ∧
    (∀ r : ℝ, (gapPolynomial nodes (1 : Fin 2)).derivative.eval r = 0 ↔
      r = gapArgmax nodes (1 : Fin 2)) := by
  refine ⟨gapArgmax_lt_of_gap_lt nodes (by norm_num) (by decide), ?_, ?_⟩
  · intro r
    constructor
    · exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes nodes 0
    · rintro rfl
      exact gapPolynomial_derivative_eval_gapArgmax nodes (by norm_num) 0
  · intro r
    constructor
    · exact eq_gapArgmax_of_derivative_eval_eq_zero_of_three_nodes nodes 1
    · rintro rfl
      exact gapPolynomial_derivative_eval_gapArgmax nodes (by norm_num) 1

theorem crossDerivativeCriticalSignTable_three_nodes
    (nodes : OrderedNodes 3) :
    CrossDerivativeCriticalSignTable nodes :=
  crossDerivativeCriticalSignTable_of_derivativeQuotientSignTable nodes
    (by norm_num) (derivativeQuotientSignTable_three_nodes nodes)

/-! ### The genuine two-node exception -/

@[simp]
lemma gapDerivativeQuotient_eq_zero_of_two_nodes
    (nodes : OrderedNodes 2) (g : Fin 1) :
    gapDerivativeQuotient nodes g = 0 := by
  rw [gapDerivativeQuotient, gapPolynomial_derivative_eq_zero_of_two_nodes]
  simp

/-- With two nodes the derivative vanishes at every real point, so there is
no distinguished derivative zero and no strict sign table. -/
lemma gapPolynomial_derivative_eval_eq_zero_of_two_nodes
    (nodes : OrderedNodes 2) (g : Fin 1) (x : ℝ) :
    (gapPolynomial nodes g).derivative.eval x = 0 := by
  rw [gapPolynomial_derivative_eq_zero_of_two_nodes]
  simp

theorem not_derivativeQuotientSignTable_two_nodes
    (nodes : OrderedNodes 2) :
    ¬DerivativeQuotientSignTable nodes := by
  intro htable
  have hneg := htable.1 (0 : Fin 1)
  rw [gapDerivativeQuotient_eq_zero_of_two_nodes] at hneg
  simp at hneg

end

end Randy1153.DeBoorPinkus
