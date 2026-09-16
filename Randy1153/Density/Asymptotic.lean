import Randy1153.Density.Dichotomy
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Asymptotic closure of the sparse density alternative

For a fixed interval, this file makes one Archimedean choice `K` absorbing
the fixed-interval growth constant.  The integer `densityDenominator K`
then gives an exact partition of every inside-node count into:

* a sparse case which fits the checked damping degree budget, and
* a positive-density case, stated without rounding as
  `n < densityDenominator K * m`.

The sparse exponential lower bound is proved to exceed the exact logarithmic
threshold from `Randy1153.Target` eventually.  The final assembly theorem
takes the genuinely dense conclusion as an explicit hypothesis.
-/

namespace Randy1153.Density

open Filter Set

noncomputable section

/-- The reciprocal density paid for one inside node after the fixed-interval
growth constant has been absorbed by `K` powers of the damping factor. -/
def densityDenominator (K : ℕ) : ℕ := 2 * (2 * K + 1)

@[simp]
lemma densityDenominator_pos (K : ℕ) : 0 < densityDenominator K := by
  simp [densityDenominator]

lemma two_le_densityDenominator (K : ℕ) : 2 ≤ densityDenominator K := by
  simp [densityDenominator]

/-- The exact natural-number sparse side of the density partition. -/
def SparseAt {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) (K : ℕ) : Prop :=
  densityDenominator K * (sparseIndices nodes a b).card ≤ n

/-- The complementary positive-density side.  Equivalently, the number of
inside nodes is strictly larger than `n / densityDenominator K`. -/
def DenseAt {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) (K : ℕ) : Prop :=
  n < densityDenominator K * (sparseIndices nodes a b).card

lemma sparseAt_or_denseAt {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) (K : ℕ) :
    SparseAt nodes a b K ∨ DenseAt nodes a b K := by
  exact le_or_gt _ _

lemma denseAt_iff_not_sparseAt {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) (K : ℕ) :
    DenseAt nodes a b K ↔ ¬ SparseAt nodes a b K := by
  simp only [DenseAt, SparseAt, not_le]

lemma denseAt_iff_div_lt_card {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) (K : ℕ) :
    DenseAt nodes a b K ↔
      n / densityDenominator K < (sparseIndices nodes a b).card := by
  rw [DenseAt, Nat.div_lt_iff_lt_mul (densityDenominator_pos K), mul_comm]

/-- Sparse density forces the basic `m ≤ n-1` degree condition once there
are at least two nodes. -/
lemma sparseAt_card_le_pred {n K : ℕ} (nodes : NodeFamily n) (a b : ℝ)
    (hn : 2 ≤ n) (hsparse : SparseAt nodes a b K) :
    (sparseIndices nodes a b).card ≤ n - 1 := by
  let m := (sparseIndices nodes a b).card
  have htwo : 2 * m ≤ densityDenominator K * m :=
    Nat.mul_le_mul_right m (two_le_densityDenominator K)
  have h2m : 2 * m ≤ n := htwo.trans hsparse
  omega

/-- The chosen sparse cutoff leaves both the fixed-growth payment and
`⌊n/8⌋` damping slots inside degree `n-1`. -/
lemma sparseAt_slot_bound {n K : ℕ} (nodes : NodeFamily n) (a b : ℝ)
    (hn : 4 ≤ n) (hsparse : SparseAt nodes a b K) :
    (2 * K + 1) * (sparseIndices nodes a b).card + 2 * (n / 8) ≤ n - 1 := by
  let m := (sparseIndices nodes a b).card
  have hsparse' : 2 * ((2 * K + 1) * m) ≤ n := by
    simpa only [SparseAt, densityDenominator, m, mul_assoc] using hsparse
  have hdiv : 8 * (n / 8) ≤ n := Nat.mul_div_le n 8
  change (2 * K + 1) * m + 2 * (n / 8) ≤ n - 1
  omega

/-- A geometric sequence with base greater than one eventually dominates
every fixed affine multiple `C * (8m+8)`. -/
lemma eventually_affine_lt_pow (r C : ℝ) (hr : 1 < r) (hC : 0 < C) :
    ∀ᶠ m : ℕ in Filter.atTop, C * (8 * (m : ℝ) + 8) < r ^ m := by
  have hsmall :=
    (@isLittleO_coe_const_pow_of_one_lt ℝ _ r hr).bound
      (c := (16 * C)⁻¹) (inv_pos.mpr (mul_pos (by norm_num) hC))
  have hlarge :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop (16 * C)
  filter_upwards [hsmall, hlarge] with m hm hpow
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [Real.norm_eq_abs, abs_of_nonneg hmnonneg, Real.norm_eq_abs,
    abs_of_pos (pow_pos hrpos m)] at hm
  have hlinear : 8 * C * (m : ℝ) ≤ (r ^ m) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ 8 * C by positivity)
    calc
      8 * C * (m : ℝ) ≤ 8 * C * ((16 * C)⁻¹ * r ^ m) := hmul
      _ = (r ^ m) / 2 := by field_simp; ring
  have hconst : 8 * C < (r ^ m) / 2 := by nlinarith
  nlinarith

/-- Any fixed multiple of `log n` is eventually strictly smaller than the
geometric lower bound with exponent `⌊n/8⌋`. -/
lemma eventually_mul_log_lt_pow_div_eight (r C : ℝ) (hr : 1 < r) :
    ∀ᶠ n : ℕ in Filter.atTop,
      C * Real.log (n : ℝ) < r ^ (n / 8) := by
  by_cases hC : 0 < C
  · have haffine := eventually_affine_lt_pow r C hr hC
    have hpull :=
      (Nat.tendsto_div_const_atTop (by norm_num : (8 : ℕ) ≠ 0)).eventually haffine
    filter_upwards [hpull, eventually_ge_atTop 2] with n hpow hn
    have hnpos : (0 : ℝ) < n := by positivity
    have hn_ne_one : (n : ℝ) ≠ 1 := by exact_mod_cast (show n ≠ 1 by omega)
    have hlog : Real.log (n : ℝ) < (n : ℝ) :=
      (Real.log_lt_sub_one_of_pos hnpos hn_ne_one).trans (by linarith)
    have hnmod : n % 8 < 8 := Nat.mod_lt n (by norm_num)
    have hnlt : (n : ℝ) < 8 * (n / 8 : ℕ) + 8 := by
      exact_mod_cast (show n < 8 * (n / 8) + 8 by omega)
    exact (mul_lt_mul_of_pos_left hlog hC).trans
      ((mul_lt_mul_of_pos_left hnlt hC).trans hpow)
  · have hCnonpos : C ≤ 0 := le_of_not_gt hC
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
    have hrpos : 0 < r := zero_lt_one.trans hr
    exact (mul_nonpos_of_nonpos_of_nonneg hCnonpos hlog).trans_lt
      (pow_pos hrpos _)

/-- For the actual damping base, the exact Randy threshold is eventually
strictly below the checked sparse exponential lower bound. -/
lemma eventually_targetThreshold_lt_damping_pow {a b ε : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (2 / Real.pi - ε) * Real.log (n : ℝ) <
        (dampingRho a b)⁻¹ ^ (n / 8) := by
  exact eventually_mul_log_lt_pow_div_eight
    (dampingRho a b)⁻¹ (2 / Real.pi - ε)
    ((one_lt_inv₀ (dampingRho_pos ha hab hb)).2 (dampingRho_lt_one hab))

/-- One interval-dependent `K` and one eventual threshold partition every
node family into an already-solved exact Target witness or an exact
positive-density alternative. -/
theorem exists_sparse_target_or_dense {a b ε : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    ∃ K N : ℕ, 4 ≤ N ∧
      fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
        (dampingRho a b)⁻¹ ^ K ∧
      ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
        (∃ t ∈ Set.Icc a b,
          (2 / Real.pi - ε) * Real.log (n : ℝ) <
            lebesgueFunction nodes t) ∨
        DenseAt nodes a b K := by
  obtain ⟨K, hK⟩ := exists_growthBase_le_dampingRho_inv_pow ha hab hb
  have heventual := eventually_targetThreshold_lt_damping_pow (ε := ε) ha hab hb
  rw [Filter.eventually_atTop] at heventual
  obtain ⟨N₀, hN₀⟩ := heventual
  refine ⟨K, max 4 N₀, le_max_left _ _, hK, ?_⟩
  intro n hn nodes
  have hn4 : 4 ≤ n := (le_max_left 4 N₀).trans hn
  have hn₀ : N₀ ≤ n := (le_max_right 4 N₀).trans hn
  rcases sparseAt_or_denseAt nodes a b K with hsparse | hdense
  · left
    have hm := sparseAt_card_le_pred nodes a b (by omega) hsparse
    have hslots := sparseAt_slot_bound nodes a b hn4 hsparse
    obtain ⟨t, ht, hleb⟩ :=
      exists_dampingRho_inv_pow_n_div_eight_le_of_card_bound
        nodes ha hab hb (by omega) hm hK hslots
    exact ⟨t, ht, (hN₀ n hn₀).trans_le hleb⟩
  · exact Or.inr hdense

/-- Final scalar assembly contract.  The sparse branch is discharged here;
the sole remaining input is the later block theorem on the explicit dense
condition `n < densityDenominator K * m`.

The dense hypothesis is local to a `K` which actually absorbs the interval
growth constant, and may choose its own eventual threshold. -/
theorem exists_eventual_target_witness_of_dense
    {a b ε : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hdense : ∀ K : ℕ,
      fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ≤
          (dampingRho a b)⁻¹ ^ K →
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ nodes : NodeFamily n,
          DenseAt nodes a b K →
            ∃ t ∈ Set.Icc a b,
              (2 / Real.pi - ε) * Real.log (n : ℝ) <
                lebesgueFunction nodes t) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
        ∃ t ∈ Set.Icc a b,
          (2 / Real.pi - ε) * Real.log (n : ℝ) <
            lebesgueFunction nodes t := by
  obtain ⟨K, N₁, hN₁, hK, halt⟩ :=
    exists_sparse_target_or_dense (ε := ε) ha hab hb
  obtain ⟨N₀, hblock⟩ := hdense K hK
  refine ⟨max N₀ N₁, by omega, ?_⟩
  intro n hn nodes
  have hn₀ : N₀ ≤ n := (le_max_left N₀ N₁).trans hn
  have hn₁ : N₁ ≤ n := (le_max_right N₀ N₁).trans hn
  rcases halt n hn₁ nodes with hsparse | hdense'
  · exact hsparse
  · exact hblock n hn₀ nodes hdense'

end

end Randy1153.Density
