import Randy1153.Density.Damping

/-!
# Sparse-node alternative and the density/block interface

The sparse branch is completely proved here from the explicit damped
polynomial.  The final dense branch depends on the later block theorem, so the
last theorem accepts that branch as a plainly visible hypothesis rather than
postulating it globally.
-/

namespace Randy1153.Density

open Polynomial Finset Set

noncomputable section

/-- The exact upper bound for all nodal values of the sparse damped
polynomial. -/
def sparseDecay {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) : ℝ :=
  dampingRho a b ^ dampingExponent n (sparseIndices nodes a b).card *
    fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ^
      (sparseIndices nodes a b).card

lemma sparseDecay_pos {n : ℕ} (nodes : NodeFamily n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < sparseDecay nodes a b := by
  have hbase : 0 < fixedIntervalGrowthBase (j0Left a b) (j0Right a b) :=
    div_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (sub_pos.mpr (nested_interval_endpoints hab).2.2.1)
  exact mul_pos (pow_pos (dampingRho_pos ha hab hb) _)
    (pow_pos hbase _)

/-- Natural-degree control implies the degree inequality consumed by
Lagrange interpolation. -/
lemma degree_sparseDampedPolynomial_lt {n : ℕ} (nodes : NodeFamily n)
    {a b xstar : ℝ} (hn : 0 < n)
    (hm : (sparseIndices nodes a b).card ≤ n - 1) :
    (sparseDampedPolynomial nodes a b xstar).degree < n := by
  calc
    (sparseDampedPolynomial nodes a b xstar).degree ≤
        ((sparseDampedPolynomial nodes a b xstar).natDegree : WithBot ℕ) :=
      Polynomial.degree_le_natDegree
    _ ≤ ((n - 1 : ℕ) : WithBot ℕ) := by
      exact_mod_cast natDegree_sparseDampedPolynomial_le nodes hm
    _ < (n : WithBot ℕ) := by
      exact_mod_cast Nat.pred_lt hn.ne'

/-- Package the positive maximizer, normalization, degree budget, and nodal
decay of the sparse polynomial in one checked interface. -/
lemma exists_sparseDampedPolynomial_data {n : ℕ} (nodes : NodeFamily n)
    {a b : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hm : (sparseIndices nodes a b).card ≤ n - 1) :
    ∃ xstar ∈ Set.Icc (j0Left a b) (j0Right a b),
      (sparseDampedPolynomial nodes a b xstar).eval xstar = 1 ∧
      (sparseDampedPolynomial nodes a b xstar).natDegree ≤ n - 1 ∧
      ∀ i : Fin n,
        |(sparseDampedPolynomial nodes a b xstar).eval (nodes.point i)| ≤
          sparseDecay nodes a b := by
  obtain ⟨xstar, hx, hxmax, hxne, _⟩ :=
    exists_sparsePolynomial_maximizer nodes hab
  refine ⟨xstar, hx, sparseDampedPolynomial_eval_self nodes hxne,
    natDegree_sparseDampedPolynomial_le nodes hm, ?_⟩
  intro i
  exact abs_sparseDampedPolynomial_eval_node_le nodes ha hab hb hx hxmax hxne i

/-- Fully checked sparse branch: if not all degree slots are consumed by
`J₁` nodes, the reciprocal of the explicit decay factor is attained as a
lower bound for the Lebesgue function at a point of `[a,b]`. -/
theorem exists_sparseDecay_inv_le_lebesgueFunction {n : ℕ}
    (nodes : NodeFamily n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hn : 0 < n)
    (hm : (sparseIndices nodes a b).card ≤ n - 1) :
    ∃ t ∈ Set.Icc a b,
      (sparseDecay nodes a b)⁻¹ ≤ lebesgueFunction nodes t := by
  obtain ⟨xstar, hx, hself, _, hnodes⟩ :=
    exists_sparseDampedPolynomial_data nodes ha hab hb hm
  have hdegree := degree_sparseDampedPolynomial_lt nodes (xstar := xstar) hn hm
  have hinterp := abs_eval_le_mul_lebesgueFunction nodes
    (sparseDampedPolynomial nodes a b xstar) hdegree
    (sparseDecay nodes a b) xstar hnodes
  rw [hself, abs_one] at hinterp
  refine ⟨xstar, j0_subset_Icc hab hx, ?_⟩
  exact (inv_le_iff_one_le_mul₀' (sparseDecay_pos nodes ha hab hb)).2 hinterp

/-- If separate scalar bookkeeping bounds the explicit decay by `q^n`, the
sparse branch gives the conventional exponential lower bound `(q⁻¹)^n`. -/
theorem exists_inv_pow_le_lebesgueFunction_of_sparseDecay_le {n : ℕ}
    (nodes : NodeFamily n) {a b q : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hn : 0 < n)
    (hm : (sparseIndices nodes a b).card ≤ n - 1) (hq : 0 < q)
    (hdecay : sparseDecay nodes a b ≤ q ^ n) :
    ∃ t ∈ Set.Icc a b, (q⁻¹) ^ n ≤ lebesgueFunction nodes t := by
  obtain ⟨t, ht, hlocal⟩ :=
    exists_sparseDecay_inv_le_lebesgueFunction nodes ha hab hb hn hm
  have hinv : (q ^ n)⁻¹ ≤ (sparseDecay nodes a b)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div (pow_pos hq n) (sparseDecay_pos nodes ha hab hb)).2 hdecay
  exact ⟨t, ht, by simpa only [inv_pow] using hinv.trans hlocal⟩

/-- The fixed-interval growth constant can be absorbed by a sufficiently
large negative power of `ρ`.  This is the only Archimedean choice needed for
the sparse asymptotics. -/
lemma exists_growthBase_le_dampingRho_inv_pow {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ K : ℕ,
      fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
        (dampingRho a b)⁻¹ ^ K := by
  have hrho := dampingRho_pos ha hab hb
  have hinv : 1 < (dampingRho a b)⁻¹ :=
    (one_lt_inv₀ hrho).2 (dampingRho_lt_one hab)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt
    (fixedIntervalGrowthBase (j0Left a b) (j0Right a b)) hinv
  exact ⟨K, hK.le⟩

/-- Exact scalar decay ledger.  If `K m + e` damping slots fit into `d`, and
`K` powers of `ρ⁻¹` dominate the fixed-interval growth base, then the entire
nodal bound is at most `ρ^e`. -/
lemma sparseDecay_le_dampingRho_pow {n K e : ℕ}
    (nodes : NodeFamily n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hC : fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
      (dampingRho a b)⁻¹ ^ K)
    (hbudget : K * (sparseIndices nodes a b).card + e ≤
      dampingExponent n (sparseIndices nodes a b).card) :
    sparseDecay nodes a b ≤ dampingRho a b ^ e := by
  let m := (sparseIndices nodes a b).card
  let d := dampingExponent n m
  let ρ := dampingRho a b
  let C := fixedIntervalGrowthBase (j0Left a b) (j0Right a b)
  have hrho : 0 < ρ := dampingRho_pos ha hab hb
  have hrho_one : ρ ≤ 1 := (dampingRho_lt_one hab).le
  have hbase : 0 ≤ C := by
    exact (div_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (sub_pos.mpr (nested_interval_endpoints hab).2.2.1)).le
  have hC' : C ≤ ρ⁻¹ ^ K := by simpa only [C, ρ] using hC
  have hCpow : C ^ m ≤ (ρ⁻¹ ^ K) ^ m :=
    pow_le_pow_left₀ hbase hC' m
  have hbudget' : K * m + e ≤ d := by
    simpa only [m, d] using hbudget
  have hKm : K * m ≤ d := by omega
  have he : e ≤ d - K * m := by omega
  change ρ ^ d * C ^ m ≤ ρ ^ e
  calc
    ρ ^ d * C ^ m ≤ ρ ^ d * (ρ⁻¹ ^ K) ^ m :=
      mul_le_mul_of_nonneg_left hCpow (pow_nonneg hrho.le _)
    _ = ρ ^ (d - K * m) := by
      rw [← pow_mul, inv_pow, ← pow_sub₀ ρ hrho.ne' hKm]
    _ ≤ ρ ^ e := pow_le_pow_of_le_one hrho.le hrho_one he

/-- Sparse exponential alternative with an explicit natural exponent `e`.
The exponent is whatever remains after paying `K` damping slots per inside
node. -/
theorem exists_dampingRho_inv_pow_le_lebesgueFunction {n K e : ℕ}
    (nodes : NodeFamily n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hn : 0 < n)
    (hm : (sparseIndices nodes a b).card ≤ n - 1)
    (hC : fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
      (dampingRho a b)⁻¹ ^ K)
    (hbudget : K * (sparseIndices nodes a b).card + e ≤
      dampingExponent n (sparseIndices nodes a b).card) :
    ∃ t ∈ Set.Icc a b,
      (dampingRho a b)⁻¹ ^ e ≤ lebesgueFunction nodes t := by
  obtain ⟨t, ht, hlocal⟩ :=
    exists_sparseDecay_inv_le_lebesgueFunction nodes ha hab hb hn hm
  have hdecay := sparseDecay_le_dampingRho_pow nodes ha hab hb hC hbudget
  have hinv : (dampingRho a b ^ e)⁻¹ ≤ (sparseDecay nodes a b)⁻¹ := by
    simpa only [one_div] using
      (one_div_le_one_div (pow_pos (dampingRho_pos ha hab hb) e)
        (sparseDecay_pos nodes ha hab hb)).2 hdecay
  exact ⟨t, ht, by simpa only [inv_pow] using hinv.trans hlocal⟩

/-- Concrete exponential rate used by later asymptotic assembly: if the
inside-node count leaves `n/8` damping slots after paying for fixed-interval
growth, then the Lebesgue function is at least `ρ⁻(n/8)` somewhere in
`[a,b]`. -/
theorem exists_dampingRho_inv_pow_n_div_eight_le {n K : ℕ}
    (nodes : NodeFamily n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hn : 0 < n)
    (hm : (sparseIndices nodes a b).card ≤ n - 1)
    (hC : fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
      (dampingRho a b)⁻¹ ^ K)
    (hbudget : K * (sparseIndices nodes a b).card + n / 8 ≤
      dampingExponent n (sparseIndices nodes a b).card) :
    ∃ t ∈ Set.Icc a b,
      (dampingRho a b)⁻¹ ^ (n / 8) ≤ lebesgueFunction nodes t :=
  exists_dampingRho_inv_pow_le_lebesgueFunction nodes
    ha hab hb hn hm hC hbudget

/-- Source-facing cardinal form of the previous theorem.  The inequality
`(2K+1)m + 2⌊n/8⌋ ≤ n-1` is a concrete linear sparse-node cutoff and implies
the internal damping-slot budget. -/
theorem exists_dampingRho_inv_pow_n_div_eight_le_of_card_bound {n K : ℕ}
    (nodes : NodeFamily n) {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hn : 0 < n)
    (hm : (sparseIndices nodes a b).card ≤ n - 1)
    (hC : fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
      (dampingRho a b)⁻¹ ^ K)
    (hcard : (2 * K + 1) * (sparseIndices nodes a b).card +
      2 * (n / 8) ≤ n - 1) :
    ∃ t ∈ Set.Icc a b,
      (dampingRho a b)⁻¹ ^ (n / 8) ≤ lebesgueFunction nodes t := by
  apply exists_dampingRho_inv_pow_n_div_eight_le nodes ha hab hb hn hm hC
  exact dampingBudget_of_slot_bound hcard

/-- Uniform sparse alternative for a fixed interval.  One natural number
`K = K(a,b)` works for every cardinality and every node configuration. -/
theorem exists_uniform_sparse_exponential_cutoff {a b : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ K : ℕ, ∀ {n : ℕ} (nodes : NodeFamily n), 0 < n →
      (sparseIndices nodes a b).card ≤ n - 1 →
      (2 * K + 1) * (sparseIndices nodes a b).card + 2 * (n / 8) ≤ n - 1 →
      ∃ t ∈ Set.Icc a b,
        (dampingRho a b)⁻¹ ^ (n / 8) ≤ lebesgueFunction nodes t := by
  obtain ⟨K, hK⟩ := exists_growthBase_le_dampingRho_inv_pow ha hab hb
  refine ⟨K, ?_⟩
  intro n nodes hn hm hcard
  exact exists_dampingRho_inv_pow_n_div_eight_le_of_card_bound
    nodes ha hab hb hn hm hK hcard

/-- Precise assembly contract for the density dichotomy.

`K` is the chosen sparse/dense cutoff.  Scalar estimates provide `hdecay`
and `hsparseLarge`; the later block theorem supplies exactly `hblock` in the
dense case.  No block conclusion is assumed anywhere else in this module. -/
theorem exists_local_lower_bound_of_sparse_or_block {n K : ℕ}
    (nodes : NodeFamily n) {a b q L : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) (hn : 0 < n)
    (hK : K ≤ n - 1) (hq : 0 < q)
    (hdecay : (sparseIndices nodes a b).card ≤ K →
      sparseDecay nodes a b ≤ q ^ n)
    (hsparseLarge : L ≤ (q⁻¹) ^ n)
    (hblock : K < (sparseIndices nodes a b).card →
      ∃ t ∈ Set.Icc a b, L ≤ lebesgueFunction nodes t) :
    ∃ t ∈ Set.Icc a b, L ≤ lebesgueFunction nodes t := by
  by_cases hsparse : (sparseIndices nodes a b).card ≤ K
  · obtain ⟨t, ht, htbound⟩ :=
      exists_inv_pow_le_lebesgueFunction_of_sparseDecay_le nodes
        ha hab hb hn (hsparse.trans hK) hq (hdecay hsparse)
    exact ⟨t, ht, hsparseLarge.trans htbound⟩
  · exact hblock (Nat.lt_of_not_ge hsparse)

end

end Randy1153.Density
