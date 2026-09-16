import Randy1153.Density.Asymptotic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Uniform arithmetic for the dense fixed-interval branch

The positive-density relation

`n < densityDenominator K * m`

forces `m` to grow uniformly with `n`.  This file records both the resulting
eventual cardinality bounds and the fixed multiplicative change of logarithm
needed when a block theorem is stated in terms of `m` rather than `n`.
-/

namespace Randy1153.Density

open Filter

noncomputable section

/-- Exact floor form of the abstract positive-density relation. -/
lemma dense_nat_iff_div_lt {K n m : ℕ} :
    n < densityDenominator K * m ↔ n / densityDenominator K < m := by
  rw [Nat.div_lt_iff_lt_mul (densityDenominator_pos K), mul_comm]

/-- Under a fixed positive-density relation, the dense cardinality eventually
exceeds every prescribed fixed natural threshold, uniformly in `m`. -/
theorem eventually_fixedThreshold_lt_of_dense (K T : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ,
      n < densityDenominator K * m → T < m := by
  filter_upwards [eventually_ge_atTop (densityDenominator K * T)] with n hn
  intro m hdense
  by_contra hm
  have hmle : m ≤ T := Nat.le_of_not_gt hm
  have hmul : densityDenominator K * m ≤ densityDenominator K * T :=
    Nat.mul_le_mul_left (densityDenominator K) hmle
  omega

/-- In particular, every dense cardinality is eventually at least three. -/
theorem eventually_two_lt_of_dense (K : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ,
      n < densityDenominator K * m → 2 < m :=
  eventually_fixedThreshold_lt_of_dense K 2

/-- A fixed real constant is eventually smaller than any positive multiple
of the natural logarithm of a natural number. -/
lemma eventually_const_lt_pos_mul_log_nat (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in Filter.atTop, C < δ * Real.log (n : ℝ) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (C / δ)] with n hn
  simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn

/-- Replacing `log n` by the logarithm of any cardinality satisfying the
fixed dense relation costs less than half of `ε` eventually.  The bound is
uniform in `m`; `m ≤ n` is included in the interface used by the block
application, although the lower dense relation alone proves this direction. -/
theorem eventually_dense_log_comparison (K : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hεlt : ε < 2 / Real.pi) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ,
      n < densityDenominator K * m → m ≤ n →
        (2 / Real.pi - ε) * Real.log (n : ℝ) <
          (2 / Real.pi - ε / 2) * Real.log (m : ℝ) := by
  let D : ℕ := densityDenominator K
  let c' : ℝ := 2 / Real.pi - ε / 2
  have hDposNat : 0 < D := by
    simpa only [D] using densityDenominator_pos K
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDposNat
  have hc'pos : 0 < c' := by
    dsimp only [c']
    nlinarith
  have hpay := eventually_const_lt_pos_mul_log_nat
    (c' * Real.log (D : ℝ)) (ε / 2) (by positivity)
  filter_upwards [hpay, eventually_ge_atTop 1] with n hpayn hn
  intro m hdense _hmn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdenseReal : (n : ℝ) < (D : ℝ) * (m : ℝ) := by
    exact_mod_cast hdense
  have hquotlt : (n : ℝ) / (D : ℝ) < (m : ℝ) := by
    rw [div_lt_iff₀ hDpos]
    simpa only [mul_comm] using hdenseReal
  have hquotpos : (0 : ℝ) < (n : ℝ) / (D : ℝ) :=
    div_pos hnpos hDpos
  have hloglt :
      Real.log (n : ℝ) - Real.log (D : ℝ) < Real.log (m : ℝ) := by
    have := Real.log_lt_log hquotpos hquotlt
    rwa [Real.log_div (ne_of_gt hnpos) (ne_of_gt hDpos)] at this
  have hscaled :
      c' * (Real.log (n : ℝ) - Real.log (D : ℝ)) <
        c' * Real.log (m : ℝ) :=
    mul_lt_mul_of_pos_left hloglt hc'pos
  dsimp only [c'] at hpayn hscaled ⊢
  nlinarith

/-- The two uniform dense-branch consequences packaged at one eventual
threshold.  The natural threshold `T` can in particular be instantiated by
`2` or by any fixed threshold required by an equioscillating-height lemma. -/
theorem eventually_dense_cardinality_and_log (K T : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hεlt : ε < 2 / Real.pi) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ m : ℕ,
      n < densityDenominator K * m → m ≤ n →
        T < m ∧
          (2 / Real.pi - ε) * Real.log (n : ℝ) <
            (2 / Real.pi - ε / 2) * Real.log (m : ℝ) := by
  filter_upwards [eventually_fixedThreshold_lt_of_dense K T,
    eventually_dense_log_comparison K hε hεlt] with n hthreshold hlog
  intro m hdense hmn
  exact ⟨hthreshold m hdense, hlog m hdense hmn⟩

end

end Randy1153.Density
