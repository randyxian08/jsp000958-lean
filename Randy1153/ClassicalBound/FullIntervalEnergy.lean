import Randy1153.ClassicalBound.EnergyParameters
import Randy1153.ClassicalBound.EnergyToLebesgue

/-!
# The sharp full-interval bound from clipped pair energy

The four finite energy losses can be chosen with coefficient strictly above
the target coefficient.  The canonical energy lower bound is uniform in the
ordered nodes, and the unconditional polynomial-control upper bound converts
it to the Lebesgue constant.  Sorting then removes the internal ordering.
-/

namespace Randy1153
namespace ClassicalBound

open Filter

noncomputable section

/-- The sharp eventual full-interval estimate, uniformly over all ordered
node families of the given cardinality. -/
theorem fullIntervalEventual_ordered (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ nodes : OrderedNodes n,
      (2 / Real.pi - eps) * Real.log (n : ℝ) <
        lebesgueOn nodes.toNodeFamily (-1) 1 := by
  obtain ⟨q, R, L, eta, hq, hR, hL, heta, heta_one, hcoefficient⟩ :=
    exists_energy_parameters eps heps
  let C : ℝ :=
    ((1 - (1 : ℝ) / (R : ℝ)) ^ 2 / (q * Real.pi)) *
      (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * (1 - eta)
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hqpi : 0 < q * Real.pi :=
      mul_pos (by linarith) Real.pi_pos
    exact mul_nonneg
      (mul_nonneg (div_nonneg (sq_nonneg _) hqpi.le) (sq_nonneg _))
      (sub_nonneg.mpr heta_one.le)
  have hcoefficientC : 2 / Real.pi - eps < 2 * C := by
    dsimp only [C]
    simpa only [one_div, mul_assoc] using hcoefficient
  have henergy := eventually_clippedPairEnergy_lower_canonical
    hq hR hL heta
  rw [Filter.eventually_atTop] at henergy
  obtain ⟨N, hN⟩ := henergy
  refine ⟨max N 2, fun n hn nodes ↦ ?_⟩
  have hnN : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have henergy_n := hN n hnN nodes
  change C * (n : ℝ) ^ 2 * Real.log (n : ℝ) ≤
    clippedPairEnergy (n - 1) nodes at henergy_n
  have hlebesgue :=
    two_mul_coefficient_mul_log_le_lebesgueOn_of_energy
      nodes hn2 hC henergy_n
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  calc
    (2 / Real.pi - eps) * Real.log (n : ℝ) <
        (2 * C) * Real.log (n : ℝ) :=
      (mul_lt_mul_iff_left₀ hlog).2 hcoefficientC
    _ = 2 * C * Real.log (n : ℝ) := by ring
    _ ≤ lebesgueOn nodes.toNodeFamily (-1) 1 := hlebesgue

/-- The exact G6 full-interval theorem for arbitrary enumerations of the
node family.  Sorting is used only for the internal ordered proof, and the
Lebesgue constant is transported by permutation invariance. -/
theorem fullIntervalEventual : FullIntervalEventual := by
  intro eps heps
  obtain ⟨N, hN⟩ := fullIntervalEventual_ordered eps heps
  refine ⟨N, fun n hn nodes ↦ ?_⟩
  unfold FullIntervalAt
  rw [← nodes.lebesgueOn_sorted (-1) 1]
  exact hN n hn nodes.sorted

end

end ClassicalBound
end Randy1153
