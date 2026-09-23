import Randy1153.ClassicalBound.EnergyLowerAsymptotic
import Randy1153.ClassicalBound.PolynomialControl

/-!
# From clipped pair energy to the Lebesgue constant

The unconditional polynomial-control theorem gives

    2 E <= n (n-1) Lambda.

An energy lower bound of size `C n^2 log n` therefore first yields the
slightly stronger finite estimate

    2 C (n/(n-1)) log n <= Lambda.

Since `n/(n-1) >= 1`, a nonnegative coefficient gives the plan-facing
sharp estimate `2 C log n <= Lambda`.  This file keeps both forms visible.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Exact finite cancellation of an `n^2` clipped-energy lower bound
against the unconditional `n(n-1)` energy upper bound.  No sign assumption
on `C` is needed for this stronger quotient form. -/
theorem two_mul_coefficient_mul_n_div_pred_mul_log_le_lebesgueOn
    {n : ℕ} (nodes : OrderedNodes n) (hn : 2 ≤ n) (C : ℝ)
    (henergy : C * (n : ℝ) ^ 2 * Real.log (n : ℝ) ≤
      clippedPairEnergy (n - 1) nodes) :
    2 * C * (n : ℝ) / ((n - 1 : ℕ) : ℝ) * Real.log (n : ℝ) ≤
      lebesgueOn nodes.toNodeFamily (-1) 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hpredR : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hupper := two_mul_clippedPairEnergy_le_lebesgueOn nodes hn
  have hcombined :
      2 * (C * (n : ℝ) ^ 2 * Real.log (n : ℝ)) ≤
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) *
          lebesgueOn nodes.toNodeFamily (-1) 1 :=
    (mul_le_mul_of_nonneg_left henergy (by norm_num)).trans hupper
  have hcancel :
      2 * C * (n : ℝ) * Real.log (n : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) *
          lebesgueOn nodes.toNodeFamily (-1) 1 := by
    apply le_of_mul_le_mul_left _ hnR
    convert hcombined using 1 <;> first | rfl | ring
  rw [show 2 * C * (n : ℝ) / ((n - 1 : ℕ) : ℝ) * Real.log (n : ℝ) =
    (2 * C * (n : ℝ) * Real.log (n : ℝ)) /
      ((n - 1 : ℕ) : ℝ) by ring]
  exact (div_le_iff₀ hpredR).2 (by simpa [mul_comm] using hcancel)

/-- Plan-facing bridge: a nonnegative `C n^2 log n` lower bound for the
clipped pair energy forces the sharp `2 C log n` Lebesgue lower bound. -/
theorem two_mul_coefficient_mul_log_le_lebesgueOn_of_energy
    {n : ℕ} (nodes : OrderedNodes n) (hn : 2 ≤ n) {C : ℝ}
    (hC : 0 ≤ C)
    (henergy : C * (n : ℝ) ^ 2 * Real.log (n : ℝ) ≤
      clippedPairEnergy (n - 1) nodes) :
    2 * C * Real.log (n : ℝ) ≤
      lebesgueOn nodes.toNodeFamily (-1) 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by positivity
  have hpredR : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hpred_le_n : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hbase0 : 0 ≤ 2 * C * Real.log (n : ℝ) := by positivity
  have hratio : (1 : ℝ) ≤ (n : ℝ) / ((n - 1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hpredR).2
    rw [one_mul]
    exact hpred_le_n
  calc
    2 * C * Real.log (n : ℝ) ≤
        (2 * C * Real.log (n : ℝ)) *
          ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
      nlinarith
    _ = 2 * C * (n : ℝ) / ((n - 1 : ℕ) : ℝ) *
        Real.log (n : ℝ) := by ring
    _ ≤ lebesgueOn nodes.toNodeFamily (-1) 1 :=
      two_mul_coefficient_mul_n_div_pred_mul_log_le_lebesgueOn
        nodes hn C henergy

end

end ClassicalBound
end Randy1153
