import Randy1153.ClassicalBound.EnergyLowerFinite
import Randy1153.ClassicalBound.EnergyAsymptoticTools

/-!
# Fixed-parameter asymptotic lower bound for clipped pair energy

This file specializes the exact finite energy theorem to degree `d=n-1`,
the canonical logarithmic arcsine exponent, and the natural dense-bin
threshold.  All parameters are fixed before `n`, and the eventual statement
is uniform over every ordered node family of size `n`.

No parameter optimization and no polynomial upper bound occur here.
-/

namespace Randy1153
namespace ClassicalBound

open Filter

noncomputable section

/-- The natural canonical threshold always satisfies the finite theorem's
bin-mass condition when `R` is positive. -/
lemma totalBinCount_mul_denseThreshold_le
    {n R : ℕ} {q : ℝ} (hR : 1 ≤ R) :
    arcsineTotalBinCount n q * arcsineDenseThreshold n q R ≤ n := by
  let B := arcsineTotalBinCount n q
  let T := arcsineDenseThreshold n q R
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hBpos : 0 < B := arcsineTotalBinCount_pos n q
  have hBRpos : 0 < B * R := mul_pos hBpos hRpos
  have hmul : T * (B * R) ≤ n := by
    dsimp only [T, arcsineDenseThreshold]
    exact Nat.div_mul_le_self n (B * R)
  have hBTdiv : B * T ≤ n / R := by
    apply (Nat.le_div_iff_mul_le hRpos).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  exact hBTdiv.trans (Nat.div_le_self n R)

/-- Fixed-parameter eventual lower bound, uniform in the ordered nodes.

The coefficient displays separately the retained-bin mass loss `R`, the
local truncation loss `L`, the geometric ratio `q`, and the arbitrarily
small harmonic loss `eta`. -/
theorem eventually_clippedPairEnergy_lower_canonical
    {q : ℝ} (hq : 1 < q) {R L : ℕ}
    (hR : 1 ≤ R) (hL : 1 < L) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ nodes : OrderedNodes n,
      (((1 - (1 : ℝ) / (R : ℝ)) ^ 2 / (q * Real.pi)) *
          (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * (1 - η)) *
          (n : ℝ) ^ 2 * Real.log (n : ℝ) ≤
        clippedPairEnergy (n - 1) nodes := by
  have hthreshold := eventually_le_arcsineDenseThreshold
    hq hR hL.le
  have hharmonic :=
    eventually_one_sub_mul_log_le_realHarmonic_denseThreshold_div
      hq hR hL.le hη
  filter_upwards [eventually_ge_atTop 2, hthreshold, hharmonic] with
      n hn hLT hharmonic
  intro nodes
  let d := n - 1
  let K := arcsineGeometricExponent d q
  let T := arcsineDenseThreshold n q R
  have hd : 1 ≤ d := by
    dsimp only [d]
    omega
  have hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d := by
    exact arcsineGeometricExponent_terminal hd hq
  have hBTn : 2 * (K + 1) * T ≤ n := by
    change arcsineTotalBinCount n q *
      arcsineDenseThreshold n q R ≤ n
    exact totalBinCount_mul_denseThreshold_le hR
  have hfinite := clippedPairEnergy_lower_finite
    hd hq hterminal nodes hL hLT hBTn
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRpos
  have hRfrac : (1 : ℝ) / (R : ℝ) ≤ 1 :=
    (div_le_one hRreal).2 (by exact_mod_cast hR)
  have hmassLeft0 :
      0 ≤ (1 - (1 : ℝ) / (R : ℝ)) * (n : ℝ) :=
    mul_nonneg (sub_nonneg.mpr hRfrac) (Nat.cast_nonneg n)
  have hmass :=
    one_sub_inv_mul_le_sub_totalBinCount_mul_denseThreshold
      (n := n) (q := q) hRpos
  rw [inv_eq_one_div] at hmass
  have hmassRight0 :
      0 ≤ ((n - arcsineTotalBinCount n q *
        arcsineDenseThreshold n q R : ℕ) : ℝ) := Nat.cast_nonneg _
  have hmassSqNat :
      ((1 - (1 : ℝ) / (R : ℝ)) * (n : ℝ)) ^ 2 ≤
        ((n - arcsineTotalBinCount n q *
          arcsineDenseThreshold n q R : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hmassSq :
      (1 - (1 : ℝ) / (R : ℝ)) ^ 2 * (n : ℝ) ^ 2 ≤
        ((n : ℝ) -
          ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 := by
    have hcast : (((n - 2 * (K + 1) * T : ℕ) : ℝ)) =
        (n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ) := by
      rw [Nat.cast_sub hBTn]
    have hcanonical :
        arcsineTotalBinCount n q * arcsineDenseThreshold n q R =
          2 * (K + 1) * T := by rfl
    rw [hcanonical] at hmassSqNat
    rw [← hcast]
    simpa only [mul_pow] using hmassSqNat
  have hqpiPos : 0 < q * Real.pi :=
    mul_pos (by linarith) Real.pi_pos
  have hlocal0 :
      0 ≤ (1 - (1 : ℝ) / (L : ℝ)) ^ 2 := sq_nonneg _
  have hlog0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have htargetToFinite :
      (((1 - (1 : ℝ) / (R : ℝ)) ^ 2 / (q * Real.pi)) *
          (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * (1 - η)) *
          (n : ℝ) ^ 2 * Real.log (n : ℝ) ≤
        (((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
          (q * Real.pi)) *
          (1 - (1 : ℝ) / (L : ℝ)) ^ 2 *
            realHarmonic (T / L) := by
    by_cases hηone : η ≤ 1
    · have hharmonic0 :
          0 ≤ (1 - η) * Real.log (n : ℝ) :=
        mul_nonneg (sub_nonneg.mpr hηone) hlog0
      have hmassDiv :
          ((1 - (1 : ℝ) / (R : ℝ)) ^ 2 * (n : ℝ) ^ 2) /
              (q * Real.pi) ≤
            (((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2) /
              (q * Real.pi) :=
        div_le_div_of_nonneg_right hmassSq hqpiPos.le
      calc
        _ = (((1 - (1 : ℝ) / (R : ℝ)) ^ 2 * (n : ℝ) ^ 2) /
              (q * Real.pi) *
            (1 - (1 : ℝ) / (L : ℝ)) ^ 2) *
              ((1 - η) * Real.log (n : ℝ)) := by ring
        _ ≤ ((((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
              (q * Real.pi)) *
            (1 - (1 : ℝ) / (L : ℝ)) ^ 2) *
              ((1 - η) * Real.log (n : ℝ)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hmassDiv hlocal0) hharmonic0
        _ ≤ ((((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
              (q * Real.pi)) *
            (1 - (1 : ℝ) / (L : ℝ)) ^ 2) *
              realHarmonic (T / L) := by
          exact mul_le_mul_of_nonneg_left hharmonic
            (mul_nonneg
              (div_nonneg (sq_nonneg _) hqpiPos.le) hlocal0)
        _ = _ := by ring
    · have hnonpos : (1 - η) * Real.log (n : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hηone)) hlog0
      have hright0 :
          0 ≤ (((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
            (q * Real.pi)) *
            (1 - (1 : ℝ) / (L : ℝ)) ^ 2 *
              realHarmonic (T / L) := by
        exact mul_nonneg
          (mul_nonneg (div_nonneg (sq_nonneg _) hqpiPos.le) (sq_nonneg _))
          (realHarmonic_nonneg _)
      calc
        _ = (((1 - (1 : ℝ) / (R : ℝ)) ^ 2 /
              (q * Real.pi)) *
            (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * (n : ℝ) ^ 2) *
              ((1 - η) * Real.log (n : ℝ)) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
        _ ≤ _ := hright0
  exact htargetToFinite.trans hfinite

end

end ClassicalBound
end Randy1153
