import Randy1153.ClassicalBound.EnergyBins

/-!
# Finite combinatorics for a bin decomposition

This file contains the two finite estimates needed after a geometric
partition into K bins.

First, a collection of at most K sparse bins, each carrying at most
n / K^2 points in the real-valued sense, carries total mass at most
n / K.  The formulation uses casts to the reals and therefore makes no
false assertion about natural-number floors.

Second, Engel's form of Cauchy--Schwarz combines bin masses with positive
local scales:

    sum_s a_s m_s^2 / h_s
      >= (sum_s m_s)^2 / sum_s (h_s / a_s).

No geometric construction of the bins or asymptotic choice of K occurs
here.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Any selected family of bins has cardinality at most the total number
of bins. -/
lemma card_finset_fin_le (K : ℕ) (bins : Finset (Fin K)) :
    bins.card ≤ K := by
  simpa using Finset.card_le_card (Finset.subset_univ bins)

/-- Real-valued sparse-bin mass estimate.

The non-strict pointwise hypothesis is intentionally the weakest useful
one.  A strict sparse threshold immediately implies it.
-/
theorem sum_sparseCounts_le_div {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) ≤ (n : ℝ) / (K : ℝ) ^ 2) :
    (∑ s ∈ sparse, (count s : ℝ)) ≤ (n : ℝ) / (K : ℝ) := by
  have hthreshold : 0 ≤ (n : ℝ) / (K : ℝ) ^ 2 := by positivity
  calc
    (∑ s ∈ sparse, (count s : ℝ)) ≤
        ∑ _s ∈ sparse, (n : ℝ) / (K : ℝ) ^ 2 := by
      exact Finset.sum_le_sum hsparse
    _ = (sparse.card : ℝ) * ((n : ℝ) / (K : ℝ) ^ 2) := by
      simp
    _ ≤ (K : ℝ) * ((n : ℝ) / (K : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_finset_fin_le K sparse) hthreshold
    _ = (n : ℝ) / (K : ℝ) := by
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hK)
      field_simp

/-- Strict sparse thresholds imply the non-strict total-mass estimate. -/
theorem sum_strictSparseCounts_le_div {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) < (n : ℝ) / (K : ℝ) ^ 2) :
    (∑ s ∈ sparse, (count s : ℝ)) ≤ (n : ℝ) / (K : ℝ) :=
  sum_sparseCounts_le_div hK count sparse
    (fun s hs ↦ (hsparse s hs).le)

/-- The real sum of all natural bin counts is the cast of their prescribed
natural total. -/
lemma sum_count_cast_eq {K n : ℕ} (count : Fin K → ℕ)
    (hsum : ∑ s : Fin K, count s = n) :
    (∑ s : Fin K, (count s : ℝ)) = (n : ℝ) := by
  exact_mod_cast hsum

/-- Complementary dense bins retain at least n - n/K real mass. -/
theorem sub_div_le_sum_denseCounts {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (hsum : ∑ s : Fin K, count s = n)
    (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) ≤ (n : ℝ) / (K : ℝ) ^ 2) :
    (n : ℝ) - (n : ℝ) / (K : ℝ) ≤
      ∑ s ∈ (Finset.univ \ sparse), (count s : ℝ) := by
  have hsparseMass :=
    sum_sparseCounts_le_div hK count sparse hsparse
  have hpartition :
      (∑ s ∈ sparse, (count s : ℝ)) +
        ∑ s ∈ (Finset.univ \ sparse), (count s : ℝ) =
          ∑ s : Fin K, (count s : ℝ) := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ sparse)
  rw [sum_count_cast_eq count hsum] at hpartition
  linarith

/-- Strict sparse thresholds give the same complementary dense-mass
bound. -/
theorem sub_div_le_sum_denseCounts_of_strict {K n : ℕ} (hK : 0 < K)
    (count : Fin K → ℕ) (hsum : ∑ s : Fin K, count s = n)
    (sparse : Finset (Fin K))
    (hsparse : ∀ s ∈ sparse,
      (count s : ℝ) < (n : ℝ) / (K : ℝ) ^ 2) :
    (n : ℝ) - (n : ℝ) / (K : ℝ) ≤
      ∑ s ∈ (Finset.univ \ sparse), (count s : ℝ) :=
  sub_div_le_sum_denseCounts hK count hsum sparse
    (fun s hs ↦ (hsparse s hs).le)

/-- Weighted Engel/Cauchy inequality on an arbitrary finite index set.

Both weights are assumed strictly positive so every denominator appearing
in the conclusion and in the Engel reduction is honest.
-/
theorem sq_sum_div_sum_div_le_sum_mul_sq_div
    {ι : Type*} [DecidableEq ι] (bins : Finset ι)
    (mass a h : ι → ℝ)
    (ha : ∀ s ∈ bins, 0 < a s) (hh : ∀ s ∈ bins, 0 < h s) :
    ((∑ s ∈ bins, mass s) ^ 2) /
        (∑ s ∈ bins, h s / a s) ≤
      ∑ s ∈ bins, a s * (mass s) ^ 2 / h s := by
  have hengel := Finset.sq_sum_div_le_sum_sq_div bins mass
    (g := fun s ↦ h s / a s)
    (fun s hs ↦ div_pos (hh s hs) (ha s hs))
  calc
    ((∑ s ∈ bins, mass s) ^ 2) /
        (∑ s ∈ bins, h s / a s) ≤
        ∑ s ∈ bins, (mass s) ^ 2 / (h s / a s) := hengel
    _ = ∑ s ∈ bins, a s * (mass s) ^ 2 / h s := by
      apply Finset.sum_congr rfl
      intro s hs
      have ha0 : a s ≠ 0 := (ha s hs).ne'
      have hh0 : h s ≠ 0 := (hh s hs).ne'
      field_simp

/-- Natural-count specialization of the weighted Engel inequality. -/
theorem sq_sum_natCount_div_sum_div_le_sum_mul_sq_div
    {ι : Type*} [DecidableEq ι] (bins : Finset ι)
    (count : ι → ℕ) (a h : ι → ℝ)
    (ha : ∀ s ∈ bins, 0 < a s) (hh : ∀ s ∈ bins, 0 < h s) :
    ((∑ s ∈ bins, (count s : ℝ)) ^ 2) /
        (∑ s ∈ bins, h s / a s) ≤
      ∑ s ∈ bins, a s * (count s : ℝ) ^ 2 / h s :=
  sq_sum_div_sum_div_le_sum_mul_sq_div bins
    (fun s ↦ (count s : ℝ)) a h ha hh

/-- The form used when all K bins participate and their natural counts sum
to n. -/
theorem sq_total_div_sum_div_le_sum_mul_countSq_div
    {K n : ℕ} (count : Fin K → ℕ)
    (hsum : ∑ s : Fin K, count s = n) (a h : Fin K → ℝ)
    (ha : ∀ s, 0 < a s) (hh : ∀ s, 0 < h s) :
    (n : ℝ) ^ 2 / (∑ s : Fin K, h s / a s) ≤
      ∑ s : Fin K, a s * (count s : ℝ) ^ 2 / h s := by
  have hengel :=
    sq_sum_natCount_div_sum_div_le_sum_mul_sq_div
      (Finset.univ : Finset (Fin K)) count a h
      (fun s _ ↦ ha s) (fun s _ ↦ hh s)
  simpa only [sum_count_cast_eq count hsum] using hengel

end

end ClassicalBound
end Randy1153
