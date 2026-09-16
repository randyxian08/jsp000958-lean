import Randy1153.Density.DenseBlockWitness
import Randy1153.Density.DenseAsymptoticTools
import Randy1153.ClassicalBound.EquioscillatingHeight

/-!
# Uniform closure of the ordered dense branch

For fixed density parameter `K`, the dense relation forces the central block
cardinality `m` to grow uniformly with the ambient cardinality `n`.  The
finite block theorem compares an equioscillating `m`-node pattern with an
actual point of the original interval, while the full-interval theorem gives
the sharp eventual lower bound for that pattern's common height.

The logarithmic change from `m` back to `n` is paid with an internal error
strictly smaller than both the requested error and `2 / π`.  This keeps all
coefficients and strict inequalities honest even when the requested error is
arbitrarily large.
-/

namespace Randy1153.Density

open Filter Set
open Randy1153.DeBoorPinkus
open Randy1153.ClassicalBound

noncomputable section

/-- Uniform dense-branch theorem for ordered node arrays.

The threshold is chosen before `n`, the ordered array, and the proof of its
dense relation.  The full-interval input is used only through the normalized
equioscillating block pattern supplied by `DenseBlockWitness`. -/
theorem exists_eventual_dense_target_witness_ordered
    (hfull : FullIntervalEventual) (K : ℕ) {a b eps : ℝ}
    (hab : a < b) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ nodes : OrderedNodes n,
      DenseAt nodes.toNodeFamily a b K →
        ∃ t ∈ Set.Icc a b,
          (2 / Real.pi - eps) * Real.log (n : ℝ) <
            lebesgueFunction nodes.toNodeFamily t := by
  let c : ℝ := 2 / Real.pi
  let delta : ℝ := min eps c / 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hmepos : 0 < min eps c := lt_min heps hc
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hdeltalt_eps : delta < eps := by
    have hminle : min eps c ≤ eps := min_le_left eps c
    dsimp only [delta]
    nlinarith
  have hdeltalt_c : delta < 2 / Real.pi := by
    have hminle : min eps c ≤ c := min_le_right eps c
    dsimp only [delta, c] at hminle ⊢
    nlinarith
  obtain ⟨D, hheight⟩ :=
    equioscillatingUnitHeightEventual hfull (delta / 2) (by positivity)
  have heventual := eventually_dense_cardinality_and_log
    K (D + 1) hdelta hdeltalt_c
  have heventual' : ∀ᶠ n : ℕ in Filter.atTop,
      densityDenominator K ≤ n ∧
        ∀ m : ℕ, n < densityDenominator K * m → m ≤ n →
          D + 1 < m ∧
            (2 / Real.pi - delta) * Real.log (n : ℝ) <
              (2 / Real.pi - delta / 2) * Real.log (m : ℝ) := by
    filter_upwards [eventually_ge_atTop (densityDenominator K), heventual]
      with n hden htools
    exact ⟨hden, htools⟩
  rw [Filter.eventually_atTop] at heventual'
  obtain ⟨N, hN⟩ := heventual'
  refine ⟨N, ?_⟩
  intro n hn nodes hdense
  obtain ⟨hden, htools⟩ := hN n hn
  let m := (sparseIndices nodes.toNodeFamily a b).card
  have hdenseNat : n < densityDenominator K * m := by
    simpa only [DenseAt, m] using hdense
  have hmle : m ≤ n := by
    dsimp only [m, sparseIndices]
    exact card_insideIndices_le nodes.toNodeFamily (j1Left a b) (j1Right a b)
  obtain ⟨hDm, hlogCompare⟩ := htools m hdenseNat hmle
  have hm2 : 2 ≤ m := by omega
  have hD : D ≤ m - 2 := by omega
  have hwitness :=
    exists_equioscillatingPattern_denseBlockWitness nodes hab hden hdense
  change ∃ pattern : EndpointArray (m - 2) 0 1,
      Equioscillates pattern ∧
        ∃ t ∈ Set.Icc a b,
          pattern.height (⟨0, by omega⟩ : Fin ((m - 2) + 1)) ≤
            lebesgueFunction nodes.toNodeFamily t at hwitness
  obtain ⟨pattern, hequi, t, ht, hpattern⟩ := hwitness
  have hpatternHeight := hheight (m - 2) hD pattern hequi
  have hmcard : m - 2 + 2 = m := by omega
  rw [hmcard] at hpatternHeight
  have hn_one : 1 ≤ n := by
    exact (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hn_one
  have htarget_le :
      (2 / Real.pi - eps) * Real.log (n : ℝ) ≤
        (2 / Real.pi - delta) * Real.log (n : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (sub_le_sub_left hdeltalt_eps.le (2 / Real.pi)) hlognonneg
  refine ⟨t, ht, ?_⟩
  exact htarget_le.trans_lt
    (hlogCompare.trans (hpatternHeight.trans_le hpattern))

end

end Randy1153.Density
