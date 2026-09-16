import Randy1153.ClassicalBound.Sharp
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Pair transport and defect bookkeeping for a classical clock argument

The sharp classical proof needs more than the weighted Bernstein estimate:
it must retain the slack in the actual nodal derivatives when the nodes are
badly distributed.  This file proves the pairwise identities that permit
that bookkeeping without introducing an unproved phase coordinate.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- Exact transport identity between two cardinal values at the same point.

All derivative and separation factors are retained.  Thus multiplying such
identities over paired indices can cancel reciprocal derivative ratios before
any estimates are made.
-/
lemma abs_lagrangeFundamental_mul_distance_eq_pair_transport {n : ℕ}
    (nodes : NodeFamily n) {j k : Fin n} (hjk : j ≠ k) {t : ℝ}
    (ht : ∀ i : Fin n, t ≠ nodes.point i) :
    |lagrangeFundamental nodes k t| * |t - nodes.point k| =
      |lagrangeFundamental nodes j t| *
        |(lagrangeBasis nodes k).derivative.eval (nodes.point j)| *
          |nodes.point j - nodes.point k| * |t - nodes.point j| := by
  rw [abs_lagrangeFundamental_eq_nodalPolynomial nodes k (ht k),
    abs_lagrangeFundamental_eq_nodalPolynomial nodes j (ht j),
    derivative_lagrangeBasis_eval_of_ne nodes hjk]
  simp only [abs_mul, abs_inv]
  have hjderiv :
      |(nodalPolynomial nodes).derivative.eval (nodes.point j)| ≠ 0 :=
    abs_ne_zero.mpr (derivative_nodalPolynomial_eval_node_ne_zero nodes j)
  have hkderiv :
      |(nodalPolynomial nodes).derivative.eval (nodes.point k)| ≠ 0 :=
    abs_ne_zero.mpr (derivative_nodalPolynomial_eval_node_ne_zero nodes k)
  have htj : |t - nodes.point j| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (ht j))
  have htk : |t - nodes.point k| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (ht k))
  have hjkabs : |nodes.point j - nodes.point k| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (nodes.point_ne hjk))
  field_simp

/-- Left endpoint index of an adjacent pair, local to the clock module. -/
def clockLeftIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val, by omega⟩

/-- Right endpoint index of an adjacent pair, local to the clock module. -/
def clockRightIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨g.val + 1, by omega⟩

@[simp]
lemma clockLeftIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (clockLeftIndex g).val = g.val :=
  rfl

@[simp]
lemma clockRightIndex_val {n : ℕ} (g : Fin (n - 1)) :
    (clockRightIndex g).val = g.val + 1 :=
  rfl

lemma clockLeftIndex_lt_rightIndex {n : ℕ} (g : Fin (n - 1)) :
    clockLeftIndex g < clockRightIndex g := by
  simp [Fin.lt_def]

/-- Length of an adjacent gap in an ordered node family. -/
def clockGap {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  nodes.point (clockRightIndex g) - nodes.point (clockLeftIndex g)

lemma clockGap_pos {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    0 < clockGap nodes g := by
  exact sub_pos.mpr (nodes.point_lt (clockLeftIndex_lt_rightIndex g))

/-- Adjacent clock gaps telescope exactly between the extreme nodes. -/
lemma sum_clockGap_eq_extreme_difference {n : ℕ} (nodes : OrderedNodes n)
    (hn : 2 ≤ n) :
    (∑ g : Fin (n - 1), clockGap nodes g) =
      nodes.point ⟨n - 1, by omega⟩ - nodes.point ⟨0, by omega⟩ := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (n - 1), by omega⟩
  rw [Finset.sum_fin_eq_sum_range]
  have htel := Finset.sum_range_sub f (n - 1)
  rw [show f (n - 1) = nodes.point ⟨n - 1, by omega⟩ by simp [f],
    show f 0 = nodes.point ⟨0, by omega⟩ by simp [f]] at htel
  rw [← htel]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < n - 1 := Finset.mem_range.mp hi
  rw [dif_pos hi']
  simp only [clockGap, clockRightIndex, clockLeftIndex, f]
  congr 2
  · apply Fin.ext
    exact (Nat.min_eq_left (by omega)).symm
  · apply Fin.ext
    exact (Nat.min_eq_left hi'.le).symm

/-- Since all nodes lie in `[-1,1]`, the total adjacent clock length is at
most two. -/
lemma sum_clockGap_le_two {n : ℕ} (nodes : OrderedNodes n) :
    (∑ g : Fin (n - 1), clockGap nodes g) ≤ 2 := by
  by_cases hn : 2 ≤ n
  · rw [sum_clockGap_eq_extreme_difference nodes hn]
    calc
      nodes.point ⟨n - 1, by omega⟩ - nodes.point ⟨0, by omega⟩ ≤
          1 - (-1 : ℝ) :=
        sub_le_sub (nodes.le_one _) (nodes.neg_one_le _)
      _ = 2 := by norm_num
  · interval_cases n <;> simp

/-- For one adjacent pair, reciprocal cross derivatives force a large
two-sided derivative defect. -/
lemma two_mul_clockGap_inv_le_cross_derivatives {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    2 * (clockGap nodes g)⁻¹ ≤
      |(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
          (nodes.point (clockRightIndex g))| +
        |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
          (nodes.point (clockLeftIndex g))| := by
  let A :=
    |(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
      (nodes.point (clockRightIndex g))|
  let B :=
    |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
      (nodes.point (clockLeftIndex g))|
  have habs :
      |nodes.point (clockRightIndex g) - nodes.point (clockLeftIndex g)| =
        clockGap nodes g := by
    change |clockGap nodes g| = clockGap nodes g
    exact abs_of_pos (clockGap_pos nodes g)
  have hrecip : A * B = ((clockGap nodes g) ^ 2)⁻¹ := by
    simpa only [A, B, habs] using
      (abs_derivative_lagrangeBasis_mul_swap nodes.toNodeFamily
        (clockLeftIndex_lt_rightIndex g).ne')
  apply two_mul_le_add_of_sq_eq_mul (abs_nonneg _) (abs_nonneg _)
  rw [inv_pow]
  exact hrecip.symm

/-- Summed adjacent-pair defect inequality. -/
lemma sum_two_mul_clockGap_inv_le_cross_derivatives {n : ℕ}
    (nodes : OrderedNodes n) :
    ∑ g : Fin (n - 1), 2 * (clockGap nodes g)⁻¹ ≤
      ∑ g : Fin (n - 1),
        (|(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
            (nodes.point (clockRightIndex g))| +
          |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
            (nodes.point (clockLeftIndex g))|) := by
  exact Finset.sum_le_sum fun g _ ↦
    two_mul_clockGap_inv_le_cross_derivatives nodes g

/-- Globally, at least one orientation of the adjacent cross derivatives
carries the entire reciprocal-gap mass.  This is the finite orientation
dichotomy before any analytic estimate is applied to the cardinal
polynomials. -/
lemma clock_directional_derivative_dichotomy {n : ℕ}
    (nodes : OrderedNodes n) :
    (∑ g : Fin (n - 1), (clockGap nodes g)⁻¹) ≤
        ∑ g : Fin (n - 1),
          |(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
            (nodes.point (clockRightIndex g))| ∨
      (∑ g : Fin (n - 1), (clockGap nodes g)⁻¹) ≤
        ∑ g : Fin (n - 1),
          |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
            (nodes.point (clockLeftIndex g))| := by
  have hpair := sum_two_mul_clockGap_inv_le_cross_derivatives nodes
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hpair
  by_contra h
  push_neg at h
  linarith

/-- Pure finite arithmetic behind the cluster side of the clock dichotomy:
positive gaps of total length at most two have reciprocal mass at least
`m² / 2`. -/
lemma sq_card_div_two_le_sum_inv_of_sum_le_two {m : ℕ}
    (gap : Fin m → ℝ) (hgap : ∀ i, 0 < gap i)
    (hsum : (∑ i : Fin m, gap i) ≤ 2) :
    (m : ℝ) ^ 2 / 2 ≤ ∑ i : Fin m, (gap i)⁻¹ := by
  by_cases hm : m = 0
  · subst m
    simp
  have hsumpos : 0 < ∑ i : Fin m, gap i := by
    exact Finset.sum_pos' (fun i _ ↦ (hgap i).le)
      ⟨⟨0, Nat.pos_of_ne_zero hm⟩, Finset.mem_univ _, hgap _⟩
  have htitu := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin m))
    (fun _ ↦ (1 : ℝ)) (g := gap) (fun i _ ↦ hgap i)
  have hcard : (∑ _i : Fin m, (1 : ℝ)) = (m : ℝ) := by simp
  have hone : (∑ i : Fin m, (1 : ℝ) ^ 2 / gap i) =
      ∑ i : Fin m, (gap i)⁻¹ := by
    apply Finset.sum_congr rfl
    intro i _
    simp [div_eq_mul_inv]
  rw [hcard, hone] at htitu
  calc
    (m : ℝ) ^ 2 / 2 ≤
        (m : ℝ) ^ 2 / ∑ i : Fin m, gap i := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsumpos).2
      exact mul_le_mul_of_nonneg_left hsum (sq_nonneg (m : ℝ))
    _ ≤ ∑ i : Fin m, (gap i)⁻¹ := htitu

/-- In one global orientation, the sum of adjacent cross derivatives is at
least half the square of the number of gaps.  This is the concrete defect
alternative supplied by reciprocal pairing and ordered-node geometry. -/
lemma sq_card_div_two_le_directional_derivatives {n : ℕ}
    (nodes : OrderedNodes n) :
    (((n - 1 : ℕ) : ℝ) ^ 2 / 2 ≤
        ∑ g : Fin (n - 1),
          |(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
            (nodes.point (clockRightIndex g))|) ∨
      (((n - 1 : ℕ) : ℝ) ^ 2 / 2 ≤
        ∑ g : Fin (n - 1),
          |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
            (nodes.point (clockLeftIndex g))|) := by
  have hmass := sq_card_div_two_le_sum_inv_of_sum_le_two
    (fun g : Fin (n - 1) ↦ clockGap nodes g) (clockGap_pos nodes)
      (sum_clockGap_le_two nodes)
  rcases clock_directional_derivative_dichotomy nodes with hleft | hright
  · exact Or.inl (hmass.trans hleft)
  · exact Or.inr (hmass.trans hright)

/-- Combining reciprocal pairing with a length budget gives a quadratic
lower bound for the total adjacent cross-derivative defect. -/
lemma sq_card_le_sum_cross_derivatives_of_gap_sum_le_two {n : ℕ}
    (nodes : OrderedNodes n)
    (hsum : (∑ g : Fin (n - 1), clockGap nodes g) ≤ 2) :
    ((n - 1 : ℕ) : ℝ) ^ 2 ≤
      ∑ g : Fin (n - 1),
        (|(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
            (nodes.point (clockRightIndex g))| +
          |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
            (nodes.point (clockLeftIndex g))|) := by
  have hrecip := sq_card_div_two_le_sum_inv_of_sum_le_two
    (fun g : Fin (n - 1) ↦ clockGap nodes g) (clockGap_pos nodes) hsum
  have hpair := sum_two_mul_clockGap_inv_le_cross_derivatives nodes
  calc
    ((n - 1 : ℕ) : ℝ) ^ 2 =
        2 * (((n - 1 : ℕ) : ℝ) ^ 2 / 2) := by ring
    _ ≤ 2 * ∑ g : Fin (n - 1), (clockGap nodes g)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hrecip (by norm_num)
    _ = ∑ g : Fin (n - 1), 2 * (clockGap nodes g)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ _ := hpair

/-- The adjacent cross-derivative defect is unconditionally quadratic in
the number of gaps.  The only geometric input is that the ordered nodes lie
in an interval of length two. -/
lemma sq_card_le_sum_cross_derivatives {n : ℕ}
    (nodes : OrderedNodes n) :
    ((n - 1 : ℕ) : ℝ) ^ 2 ≤
      ∑ g : Fin (n - 1),
        (|(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
            (nodes.point (clockRightIndex g))| +
          |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
            (nodes.point (clockLeftIndex g))|) :=
  sq_card_le_sum_cross_derivatives_of_gap_sum_le_two nodes
    (sum_clockGap_le_two nodes)

end

end ClassicalBound
end Randy1153
