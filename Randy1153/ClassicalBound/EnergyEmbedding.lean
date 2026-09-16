import Randy1153.ClassicalBound.PairEnergy
import Randy1153.ClassicalBound.EnergyGeometry

/-!
# Embedding local pair energies into the global energy

The global clipped energy was deliberately defined as half of an ordered
off-diagonal sum, which is convenient for derivative-row estimates.  Local
spacing geometry instead enumerates every pair once by its positive index
separation.  This file proves that these are the same finite pair sum and
that any strictly increasing selection of nodes contributes at most the
global energy.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Every strictly ordered pair of indices, represented once. -/
def strictIndexPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ.offDiag).filter fun p ↦ p.1 < p.2

@[simp]
lemma mem_strictIndexPairs {n : ℕ} (p : Fin n × Fin n) :
    p ∈ strictIndexPairs n ↔ p.1 < p.2 := by
  rw [strictIndexPairs, Finset.mem_filter, Finset.mem_offDiag]
  simp only [Finset.mem_univ, true_and]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦ ⟨ne_of_lt h, h⟩

/-- The dependent finite set which flattens an outer index together with a
distinct inner index. -/
private def offDiagonalSigma (n : ℕ) : Finset (Σ _j : Fin n, Fin n) :=
  Finset.univ.sigma fun j ↦ (Finset.univ : Finset (Fin n)).erase j

/-- A nested erase sum is exactly a flat sum over all ordered distinct
pairs. -/
private lemma sum_erase_eq_sum_offDiag {n : ℕ} (f : Fin n → Fin n → ℝ) :
    (∑ j : Fin n,
        ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, f j k) =
      ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2 := by
  classical
  have hflatten :
      (∑ q ∈ offDiagonalSigma n, f q.1 q.2) =
        ∑ j : Fin n,
          ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j, f j k := by
    rw [offDiagonalSigma, Finset.sum_sigma]
  rw [← hflatten]
  apply Finset.sum_bij (fun q hq ↦ (q.1, q.2))
  · intro q hq
    rw [Finset.mem_offDiag]
    have hmem := Finset.mem_sigma.mp hq
    exact ⟨Finset.mem_univ _, Finset.mem_univ _,
      (Finset.mem_erase.mp hmem.2).1.symm⟩
  · intro q hq q' hq' heq
    cases q with
    | mk j k =>
      cases q' with
      | mk j' k' =>
        simp only at heq
        cases heq
        rfl
  · intro p hp
    refine ⟨⟨p.1, p.2⟩, ?_, rfl⟩
    rw [offDiagonalSigma, Finset.mem_sigma]
    have hmem := Finset.mem_offDiag.mp hp
    exact ⟨Finset.mem_univ _,
      Finset.mem_erase.mpr ⟨hmem.2.2.symm, Finset.mem_univ _⟩⟩
  · intro q hq
    rfl

/-- For a symmetric summand, the ordered off-diagonal sum consists of two
copies of the strictly ordered sum. -/
private lemma sum_offDiag_eq_two_mul_sum_strict {n : ℕ}
    (f : Fin n → Fin n → ℝ) (hsymm : ∀ j k, f j k = f k j) :
    (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2) =
      2 * ∑ p ∈ strictIndexPairs n, f p.1 p.2 := by
  classical
  let off := (Finset.univ : Finset (Fin n)).offDiag
  let upper := off.filter fun p ↦ p.1 < p.2
  let lower := off.filter fun p ↦ ¬ p.1 < p.2
  have hlower :
      (∑ p ∈ lower, f p.1 p.2) = ∑ p ∈ upper, f p.1 p.2 := by
    apply Finset.sum_bij (fun p hp ↦ (p.2, p.1))
    · intro p hp
      simp only [lower, upper, off, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1.symm, lt_of_le_of_ne (not_lt.mp hp.2) hp.1.symm⟩
    · intro p hp q hq heq
      exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
    · intro p hp
      refine ⟨(p.2, p.1), ?_, rfl⟩
      simp only [lower, upper, off, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1.symm, not_lt.mpr hp.2.le⟩
    · intro p hp
      simpa only using hsymm p.1 p.2
  calc
    (∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2) =
        (∑ p ∈ upper, f p.1 p.2) + ∑ p ∈ lower, f p.1 p.2 := by
      exact (Finset.sum_filter_add_sum_filter_not off
        (fun p : Fin n × Fin n ↦ p.1 < p.2) (fun p ↦ f p.1 p.2)).symm
    _ = (∑ p ∈ upper, f p.1 p.2) +
        ∑ p ∈ upper, f p.1 p.2 := by rw [hlower]
    _ = 2 * ∑ p ∈ strictIndexPairs n, f p.1 p.2 := by
      change _ = 2 * ∑ p ∈ upper, f p.1 p.2
      ring

lemma clippedPairWeight_comm {d n : ℕ} (nodes : OrderedNodes n)
    (j k : Fin n) :
    clippedPairWeight d nodes j k = clippedPairWeight d nodes k j := by
  rw [clippedPairWeight, clippedPairWeight]
  congr 1
  · rw [mul_comm]
  · rw [abs_sub_comm]

/-- The global clipped energy is one sum over strictly ordered index pairs;
the factor one-half in its row-oriented definition disappears exactly. -/
theorem clippedPairEnergy_eq_sum_strictIndexPairs {d n : ℕ}
    (nodes : OrderedNodes n) :
    clippedPairEnergy d nodes =
      ∑ p ∈ strictIndexPairs n,
        clippedPairWeight d nodes p.1 p.2 := by
  rw [clippedPairEnergy, sum_erase_eq_sum_offDiag]
  rw [sum_offDiag_eq_two_mul_sum_strict
    (fun j k ↦ clippedPairWeight d nodes j k)
    (clippedPairWeight_comm nodes)]
  ring

/-- The one-copy weight of a local strictly ordered pair. -/
def localPairWeight {m : ℕ} (x scale : Fin m → ℝ) (i j : Fin m) : ℝ :=
  Real.sqrt (scale i * scale j) * |x i - x j|⁻¹

/-- The dependent finite set used by `localPairEnergy`: a positive step and
the left endpoint of a pair having that step. -/
private def stepPairSigma (m : ℕ) : Finset (Σ r : ℕ, Fin (m - r)) :=
  (Finset.Ico 1 m).sigma fun _r ↦ Finset.univ

/-- Convert a positive-step occurrence into its strictly ordered pair. -/
private def stepSigmaToPair {m : ℕ} (q : Σ r : ℕ, Fin (m - r)) :
    Fin m × Fin m :=
  (stepLeftIndex q.2, stepRightIndex q.2)

/-- The separation enumeration used by `localPairEnergy` contains each
strictly ordered pair exactly once. -/
theorem localPairEnergy_eq_sum_strictIndexPairs {m : ℕ}
    (x scale : Fin m → ℝ) (hx : StrictMono x) :
    localPairEnergy x scale =
      ∑ p ∈ strictIndexPairs m, localPairWeight x scale p.1 p.2 := by
  classical
  have hflatten :
      (∑ q ∈ stepPairSigma m,
          stepGeometricWeight scale q.2 * (stepSpan x q.2)⁻¹) =
        localPairEnergy x scale := by
    rw [stepPairSigma, Finset.sum_sigma]
    rfl
  rw [← hflatten]
  apply Finset.sum_bij (fun q hq ↦ stepSigmaToPair q)
  · intro q hq
    rw [mem_strictIndexPairs]
    have hmem := Finset.mem_sigma.mp hq
    exact stepLeftIndex_lt_stepRightIndex (Finset.mem_Ico.mp hmem.1).1 q.2
  · intro q hq q' hq' heq
    cases q with
    | mk r i =>
      cases q' with
      | mk s k =>
        have hleft := congrArg (fun p : Fin m × Fin m ↦ p.1.val) heq
        have hright := congrArg (fun p : Fin m × Fin m ↦ p.2.val) heq
        simp only [stepSigmaToPair, stepLeftIndex_val,
          stepRightIndex_val] at hleft hright
        have hrs : r = s := by omega
        subst s
        rw [Sigma.mk.inj_iff]
        exact ⟨rfl, heq_of_eq (Fin.ext hleft)⟩
  · intro p hp
    have hp' : p.1 < p.2 := (mem_strictIndexPairs p).mp hp
    let r : ℕ := p.2.val - p.1.val
    have hr : 0 < r := by
      simp only [r]
      omega
    have hrm : r < m := by
      simp only [r]
      omega
    let i : Fin (m - r) := ⟨p.1.val, by
      simp only [r]
      omega⟩
    refine ⟨⟨r, i⟩, ?_, ?_⟩
    · rw [stepPairSigma, Finset.mem_sigma]
      exact ⟨Finset.mem_Ico.mpr ⟨hr, hrm⟩, Finset.mem_univ _⟩
    · apply Prod.ext <;> apply Fin.ext
      · rfl
      · simp only [stepSigmaToPair, stepRightIndex_val, i, r]
        omega
  · intro q hq
    have hmem := Finset.mem_sigma.mp hq
    have hr : 0 < q.1 := (Finset.mem_Ico.mp hmem.1).1
    have hlt : x (stepLeftIndex q.2) < x (stepRightIndex q.2) :=
      hx (stepLeftIndex_lt_stepRightIndex hr q.2)
    rw [localPairWeight, stepSigmaToPair, stepGeometricWeight, stepSpan]
    rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]

lemma clippedPairWeight_nonneg {d n : ℕ} (nodes : OrderedNodes n)
    (j k : Fin n) :
    0 ≤ clippedPairWeight d nodes j k := by
  exact mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (abs_nonneg _))

/-- A strictly increasing selection of global indices embeds its complete
local pair energy into the global clipped pair energy.  No interval,
cardinality, or asymptotic hypothesis is used. -/
theorem localPairEnergy_le_clippedPairEnergy_of_strictMonoEmbedding
    {d m n : ℕ} (nodes : OrderedNodes n) (ι : Fin m → Fin n)
    (hι : StrictMono ι) :
    localPairEnergy
        (fun i ↦ nodes.point (ι i))
        (fun i ↦ clippedArcsineScale d (nodes.point (ι i))) ≤
      clippedPairEnergy d nodes := by
  classical
  let x : Fin m → ℝ := fun i ↦ nodes.point (ι i)
  let scale : Fin m → ℝ :=
    fun i ↦ clippedArcsineScale d (nodes.point (ι i))
  let embed : Fin m × Fin m → Fin n × Fin n :=
    fun p ↦ (ι p.1, ι p.2)
  have hx : StrictMono x := nodes.strictMono.comp hι
  have hembed : Function.Injective embed :=
    hι.injective.prodMap hι.injective
  have hsubset : (strictIndexPairs m).image embed ⊆ strictIndexPairs n := by
    rw [Finset.image_subset_iff]
    intro p hp
    rw [mem_strictIndexPairs] at hp ⊢
    exact hι hp
  rw [show (fun i ↦ nodes.point (ι i)) = x by rfl,
    show (fun i ↦ clippedArcsineScale d (nodes.point (ι i))) = scale by rfl,
    localPairEnergy_eq_sum_strictIndexPairs x scale hx,
    clippedPairEnergy_eq_sum_strictIndexPairs]
  calc
    (∑ p ∈ strictIndexPairs m, localPairWeight x scale p.1 p.2) =
        ∑ p ∈ strictIndexPairs m,
          clippedPairWeight d nodes (ι p.1) (ι p.2) := by
      rfl
    _ = ∑ q ∈ (strictIndexPairs m).image embed,
        clippedPairWeight d nodes q.1 q.2 := by
      rw [Finset.sum_image hembed.injOn]
    _ ≤ ∑ q ∈ strictIndexPairs n,
        clippedPairWeight d nodes q.1 q.2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun q hq hqnot ↦ clippedPairWeight_nonneg nodes q.1 q.2)

end

end ClassicalBound
end Randy1153
