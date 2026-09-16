import Randy1153.ClassicalBound.EnergyPartition
import Randy1153.ClassicalBound.ArcsineBinCount
import Randy1153.ClassicalBound.BinCombinatorics

/-!
# An exact finite global energy lower bound

There are `2 * (K+1)` signed geometric bins.  Given a natural threshold
`T`, this file calls a bin dense when it contains at least `T` nodes.  The
sparse bins lose at most `2 * (K+1) * T` nodes.  On the dense bins the exact
local harmonic estimate, finite monotonicity, weighted Engel, and the
reflected arcsine budget combine into a single global lower bound.

All natural-division and threshold losses remain explicit.  No asymptotic
choice of `K`, `L`, or `T`, and no polynomial upper estimate, occurs here.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Canonical signed bins containing at least `T` nodes. -/
def denseArcsineLabels {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (T : ℕ) :
    Finset (Bool × Fin (K + 1)) :=
  Finset.univ.filter fun b ↦
    T ≤ arcsineNodeBinCount q hterminal nodes b

@[simp]
lemma mem_denseArcsineLabels {d K n T : ℕ} {q : ℝ}
    {hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d}
    {nodes : OrderedNodes n} {b : Bool × Fin (K + 1)} :
    b ∈ denseArcsineLabels q hterminal nodes T ↔
      T ≤ arcsineNodeBinCount q hterminal nodes b := by
  simp [denseArcsineLabels]

lemma card_signedArcsineLabels (K : ℕ) :
    Fintype.card (Bool × Fin (K + 1)) = 2 * (K + 1) := by
  simp [Fintype.card_prod]

/-- Exact real mass retained by the threshold-dense labels.  The estimate
uses `B*T`, rather than `B*(T-1)`, so it remains valid without a separate
case at `T=0`. -/
theorem sub_binThreshold_le_sum_denseArcsineCounts
    {d K n T : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) :
    (n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ) ≤
      ∑ b ∈ denseArcsineLabels q hterminal nodes T,
        (arcsineNodeBinCount q hterminal nodes b : ℝ) := by
  let dense := denseArcsineLabels q hterminal nodes T
  let count : Bool × Fin (K + 1) → ℕ :=
    fun b ↦ arcsineNodeBinCount q hterminal nodes b
  have hsparse :
      (∑ b ∈ (Finset.univ \ dense), (count b : ℝ)) ≤
        ((2 * (K + 1) * T : ℕ) : ℝ) := by
    calc
      (∑ b ∈ (Finset.univ \ dense), (count b : ℝ)) ≤
          ∑ _b ∈ (Finset.univ \ dense), (T : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        have hbnot : b ∉ dense := (Finset.mem_sdiff.mp hb).2
        have hlt : count b < T := by
          dsimp only [dense] at hbnot
          rw [denseArcsineLabels, Finset.mem_filter] at hbnot
          simpa only [Finset.mem_univ, true_and, not_le] using hbnot
        exact_mod_cast hlt.le
      _ = (((Finset.univ \ dense).card * T : ℕ) : ℝ) := by
        simp [Nat.cast_mul]
      _ ≤ ((2 * (K + 1) * T : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_le_mul_right T
          (calc
            (Finset.univ \ dense).card ≤
                (Finset.univ : Finset (Bool × Fin (K + 1))).card :=
              Finset.card_le_card (Finset.sdiff_subset)
            _ = 2 * (K + 1) := by simp [Fintype.card_prod])
  have hpartition :
      (∑ b ∈ dense, (count b : ℝ)) +
          ∑ b ∈ (Finset.univ \ dense), (count b : ℝ) =
        ∑ b : Bool × Fin (K + 1), (count b : ℝ) := by
    rw [add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ dense)
  have htotal :
      (∑ b : Bool × Fin (K + 1), (count b : ℝ)) = (n : ℝ) := by
    exact_mod_cast sum_arcsineNodeBinCount q hterminal nodes
  rw [htotal] at hpartition
  change (n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ) ≤
    ∑ b ∈ dense, (count b : ℝ)
  linarith

/-- The real harmonic numbers are monotone. -/
lemma realHarmonic_mono {R S : ℕ} (hRS : R ≤ S) :
    realHarmonic R ≤ realHarmonic S := by
  rw [realHarmonic_eq_sum_Icc, realHarmonic_eq_sum_Icc]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
      (Finset.mem_Icc.mp hr).2.trans hRS⟩
  · intro r hrS hrR
    exact inv_nonneg.mpr (Nat.cast_nonneg r)

/-- Replacing the exact dense-bin truncation by the common threshold loses
at most the visible factor `(1-1/L)^2` and `H_(T/L)`. -/
lemma common_dense_harmonicFactor_le
    {m T L : ℕ} (hL : 1 < L) (hTm : T ≤ m) :
    (m : ℝ) ^ 2 * (1 - (1 : ℝ) / (L : ℝ)) ^ 2 *
        realHarmonic (T / L) ≤
      (((m - m / L : ℕ) : ℝ) ^ 2) * realHarmonic (m / L) := by
  have hL0 : (0 : ℝ) < (L : ℝ) := by positivity
  have hdiv : ((m / L : ℕ) : ℝ) ≤ (m : ℝ) / (L : ℝ) :=
    Nat.cast_div_le
  have hbase0 : 0 ≤ (m : ℝ) * (1 - (1 : ℝ) / (L : ℝ)) := by
    have : (1 : ℝ) / (L : ℝ) ≤ 1 := by
      exact (div_le_one hL0).2 (by exact_mod_cast hL.le)
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr this)
  have hnatSub :
      (m : ℝ) * (1 - (1 : ℝ) / (L : ℝ)) ≤
        ((m - m / L : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.div_le_self m L)]
    have hidentity :
        (m : ℝ) * (1 - (1 : ℝ) / (L : ℝ)) =
          (m : ℝ) - (m : ℝ) / (L : ℝ) := by ring
    rw [hidentity]
    linarith
  have hsquare :
      (m : ℝ) ^ 2 * (1 - (1 : ℝ) / (L : ℝ)) ^ 2 ≤
        (((m - m / L : ℕ) : ℝ) ^ 2) := by
    have hsub0 : (0 : ℝ) ≤ ((m - m / L : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    rw [← mul_pow]
    nlinarith
  have hharm : realHarmonic (T / L) ≤ realHarmonic (m / L) :=
    realHarmonic_mono (Nat.div_le_div_right hTm)
  have hHT0 : 0 ≤ realHarmonic (T / L) := realHarmonic_nonneg _
  have hHm0 : 0 ≤ realHarmonic (m / L) := realHarmonic_nonneg _
  have hsq0 : 0 ≤ (((m - m / L : ℕ) : ℝ) ^ 2) := sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hsquare hHT0).trans
    (mul_le_mul_of_nonneg_left hharm hsq0)

private lemma cosineBinLength_nonneg
    {d K : ℕ} {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (i : Fin (K + 1)) :
    0 ≤ cosineBinLength
      (geometricHalfArcsinePartition d K q hq hterminal).angle i := by
  let P := geometricHalfArcsinePartition d K q hq hterminal
  exact sub_nonneg.mpr (Real.cos_le_cos_of_nonneg_of_le_pi
    (P.angle_nonneg (angleBinLeft i))
    ((P.angle_le_pi_div_two (angleBinRight i)).trans
      (by linarith [Real.pi_pos]))
    (P.angle_left_le_right i))

private lemma cosineBinLength_pos_of_two_le_count
    {d K n : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1))
    (hm : 2 ≤ arcsineNodeBinCount q hterminal nodes b) :
    0 < cosineBinLength
      (geometricHalfArcsinePartition d K q hq hterminal).angle b.2 := by
  let m := arcsineNodeBinCount q hterminal nodes b
  let x : Fin m → ℝ :=
    fun i ↦ nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i)
  let i₀ : Fin m := ⟨0, by dsimp only [m]; omega⟩
  let i₁ : Fin m := ⟨1, by dsimp only [m]; omega⟩
  have hx : StrictMono x := nodes.strictMono.comp
    (arcsineNodeBinEmbedding_strictMono q hterminal nodes b)
  have hlt : x i₀ < x i₁ := hx (by simp [i₀, i₁])
  have h₀ := arcsineNodeBinEmbedding_mem_interval
    hd hq hterminal nodes b i₀
  have h₁ := arcsineNodeBinEmbedding_mem_interval
    hd hq hterminal nodes b i₁
  have hlength := geometricSignedBin_intervalLength
    d K hq hterminal b
  change x i₀ ∈ Set.Icc
    (geometricSignedBinLowerEndpoint d q b)
    (geometricSignedBinUpperEndpoint d q b) at h₀
  change x i₁ ∈ Set.Icc
    (geometricSignedBinLowerEndpoint d q b)
    (geometricSignedBinUpperEndpoint d q b) at h₁
  rcases h₀ with ⟨hA₀, h₀B⟩
  rcases h₁ with ⟨hA₁, h₁B⟩
  linarith

/-- Any selected family of signed bins uses at most the complete reflected
length-over-scale budget. -/
theorem sum_selected_arcsineBinLength_div_lowerScale_le
    {d K : ℕ} {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (bins : Finset (Bool × Fin (K + 1))) :
    (∑ b ∈ bins,
      cosineBinLength
          (geometricHalfArcsinePartition d K q hq hterminal).angle b.2 /
        geometricBinLowerScale d q b.2) ≤ q * Real.pi := by
  have hsubset :
      (∑ b ∈ bins,
        cosineBinLength
            (geometricHalfArcsinePartition d K q hq hterminal).angle b.2 /
          geometricBinLowerScale d q b.2) ≤
        ∑ b : Bool × Fin (K + 1),
          cosineBinLength
              (geometricHalfArcsinePartition d K q hq hterminal).angle b.2 /
            geometricBinLowerScale d q b.2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bins)
      (fun b hb hbn ↦ div_nonneg
        (cosineBinLength_nonneg hq hterminal b.2)
        (geometricBinLowerScale_pos d b.2).le)
  have hall :
      (∑ b : Bool × Fin (K + 1),
        cosineBinLength
            (geometricHalfArcsinePartition d K q hq hterminal).angle b.2 /
          geometricBinLowerScale d q b.2) =
        2 * ∑ i : Fin (K + 1),
          cosineBinLength
              (geometricHalfArcsinePartition d K q hq hterminal).angle i /
            geometricBinLowerScale d q i := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  calc
    _ ≤ ∑ b : Bool × Fin (K + 1),
          cosineBinLength
              (geometricHalfArcsinePartition d K q hq hterminal).angle b.2 /
            geometricBinLowerScale d q b.2 := hsubset
    _ = 2 * ∑ i : Fin (K + 1),
          cosineBinLength
              (geometricHalfArcsinePartition d K q hq hterminal).angle i /
            geometricBinLowerScale d q i := hall
    _ ≤ q * Real.pi := by
      simpa only [geometricBinLowerScale_eq_cosineBinLowerScale
        d K hq hterminal] using
          geometricPartition_full_budget_le hq hterminal

private theorem denseArcsineLabels_nonempty
    {d K n T L : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (hL : 1 < L) (hLT : L ≤ T)
    (hBTn : 2 * (K + 1) * T ≤ n) :
    (denseArcsineLabels q hterminal nodes T).Nonempty := by
  by_contra hempty
  have hempty' : denseArcsineLabels q hterminal nodes T = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hcount : ∀ b : Bool × Fin (K + 1),
      arcsineNodeBinCount q hterminal nodes b ≤ T - 1 := by
    intro b
    have hbnot : b ∉ denseArcsineLabels q hterminal nodes T := by
      rw [hempty']
      simp
    rw [mem_denseArcsineLabels, not_le] at hbnot
    omega
  have hsum :
      n ≤ 2 * (K + 1) * (T - 1) := by
    rw [← sum_arcsineNodeBinCount q hterminal nodes]
    calc
      (∑ b : Bool × Fin (K + 1),
          arcsineNodeBinCount q hterminal nodes b) ≤
          ∑ _b : Bool × Fin (K + 1), (T - 1) :=
        Finset.sum_le_sum fun b hb ↦ hcount b
      _ = 2 * (K + 1) * (T - 1) := by
        simp [Fintype.card_prod]
  have hTpos : 0 < T := lt_of_lt_of_le (Nat.zero_lt_of_lt hL) hLT
  have hBpos : 0 < 2 * (K + 1) := by omega
  have hstrict : 2 * (K + 1) * (T - 1) < 2 * (K + 1) * T := by
    exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hTpos (by omega)) hBpos
  omega

/-- Exact finite global lower bound obtained from threshold-dense bins.

The hypothesis `2*(K+1)*T ≤ n` is precisely what makes the retained-mass
quantity nonnegative before it is squared.  This theorem makes no
asymptotic choice of the parameters and does not invoke a polynomial upper
bound for the energy. -/
theorem clippedPairEnergy_lower_finite
    {d K n T L : ℕ} {q : ℝ}
    (hd : 1 ≤ d) (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (hL : 1 < L) (hLT : L ≤ T)
    (hBTn : 2 * (K + 1) * T ≤ n) :
    (((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
        (q * Real.pi)) *
        (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * realHarmonic (T / L) ≤
      clippedPairEnergy d nodes := by
  let dense := denseArcsineLabels q hterminal nodes T
  let mass : Bool × Fin (K + 1) → ℝ := fun b ↦
    (arcsineNodeBinCount q hterminal nodes b : ℝ)
  let a : Bool × Fin (K + 1) → ℝ := fun b ↦
    geometricBinLowerScale d q b.2
  let h : Bool × Fin (K + 1) → ℝ := fun b ↦
    cosineBinLength
      (geometricHalfArcsinePartition d K q hq hterminal).angle b.2
  let C : ℝ :=
    (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * realHarmonic (T / L)
  let denseMass : ℝ := ∑ b ∈ dense, mass b
  let denominator : ℝ := ∑ b ∈ dense, h b / a b
  have hT2 : 2 ≤ T := by omega
  have hdense : ∀ b ∈ dense,
      L ≤ arcsineNodeBinCount q hterminal nodes b := by
    intro b hb
    exact hLT.trans (mem_denseArcsineLabels.mp hb)
  have ha : ∀ b ∈ dense, 0 < a b := by
    intro b hb
    exact geometricBinLowerScale_pos d b.2
  have hh : ∀ b ∈ dense, 0 < h b := by
    intro b hb
    exact cosineBinLength_pos_of_two_le_count hd hq hterminal nodes b
      (hT2.trans (mem_denseArcsineLabels.mp hb))
  have hC0 : 0 ≤ C := by
    exact mul_nonneg (sq_nonneg _) (realHarmonic_nonneg _)
  have hdenominatorPos : 0 < denominator := by
    apply Finset.sum_pos (fun b hb ↦ div_pos (hh b hb) (ha b hb))
    exact denseArcsineLabels_nonempty hterminal nodes hL hLT hBTn
  have hdenominatorBudget : denominator ≤ q * Real.pi := by
    exact sum_selected_arcsineBinLength_div_lowerScale_le
      hq hterminal dense
  have hqpiPos : 0 < q * Real.pi :=
    mul_pos (by linarith) Real.pi_pos
  have hmassLower :
      (n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ) ≤ denseMass := by
    exact sub_binThreshold_le_sum_denseArcsineCounts
      q hterminal nodes
  have hlostMass0 :
      0 ≤ (n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ) := by
    have hcast : ((2 * (K + 1) * T : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hBTn
    linarith
  have hdenseMass0 : 0 ≤ denseMass := by
    exact Finset.sum_nonneg fun b hb ↦ Nat.cast_nonneg _
  have hmassSq :
      ((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 ≤
        denseMass ^ 2 := by
    nlinarith
  have hengel :
      denseMass ^ 2 / denominator ≤
        ∑ b ∈ dense, a b * (mass b) ^ 2 / h b := by
    exact sq_sum_natCount_div_sum_div_le_sum_mul_sq_div dense
      (fun b ↦ arcsineNodeBinCount q hterminal nodes b) a h ha hh
  have hcommonEnergy :
      C * (∑ b ∈ dense, a b * (mass b) ^ 2 / h b) ≤
        clippedPairEnergy d nodes := by
    calc
      C * (∑ b ∈ dense, a b * (mass b) ^ 2 / h b) =
          ∑ b ∈ dense, C * (a b * (mass b) ^ 2 / h b) := by
        rw [Finset.mul_sum]
      _ ≤ ∑ b ∈ dense,
          geometricBinLowerScale d q b.2 *
            (((((arcsineNodeBinCount q hterminal nodes b -
                  arcsineNodeBinCount q hterminal nodes b / L : ℕ) : ℝ) ^ 2) *
                realHarmonic
                  (arcsineNodeBinCount q hterminal nodes b / L)) /
              cosineBinLength
                (geometricHalfArcsinePartition d K q hq hterminal).angle b.2) := by
        apply Finset.sum_le_sum
        intro b hb
        have hfactor := common_dense_harmonicFactor_le hL
          (mem_denseArcsineLabels.mp hb)
        have hah : 0 ≤ a b / h b :=
          div_nonneg (ha b hb).le (hh b hb).le
        calc
          C * (a b * (mass b) ^ 2 / h b) =
              (a b / h b) *
                ((mass b) ^ 2 *
                  (1 - (1 : ℝ) / (L : ℝ)) ^ 2 *
                    realHarmonic (T / L)) := by
            dsimp only [C, mass]
            ring
          _ ≤ (a b / h b) *
              (((arcsineNodeBinCount q hterminal nodes b -
                  arcsineNodeBinCount q hterminal nodes b / L : ℕ) : ℝ) ^ 2 *
                realHarmonic
                  (arcsineNodeBinCount q hterminal nodes b / L)) :=
            mul_le_mul_of_nonneg_left hfactor hah
          _ = geometricBinLowerScale d q b.2 *
              (((((arcsineNodeBinCount q hterminal nodes b -
                    arcsineNodeBinCount q hterminal nodes b / L : ℕ) : ℝ) ^ 2) *
                  realHarmonic
                    (arcsineNodeBinCount q hterminal nodes b / L)) /
                cosineBinLength
                  (geometricHalfArcsinePartition d K q hq hterminal).angle b.2) := by
            dsimp only [a, h]
            ring
      _ ≤ clippedPairEnergy d nodes := by
        exact sum_selectedDense_arcsineBin_lower_le_clippedPairEnergy
          hd hq hterminal nodes dense hL hdense
  calc
    (((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
        (q * Real.pi)) *
        (1 - (1 : ℝ) / (L : ℝ)) ^ 2 * realHarmonic (T / L) =
      (((n : ℝ) - ((2 * (K + 1) * T : ℕ) : ℝ)) ^ 2 /
        (q * Real.pi)) * C := by
      dsimp only [C]
      ring
    _ ≤ (denseMass ^ 2 / (q * Real.pi)) * C := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hmassSq hqpiPos.le) hC0
    _ ≤ (denseMass ^ 2 / denominator) * C := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (sq_nonneg _) hdenominatorPos
          hdenominatorBudget) hC0
    _ = C * (denseMass ^ 2 / denominator) := by ring
    _ ≤ C * (∑ b ∈ dense, a b * (mass b) ^ 2 / h b) :=
      mul_le_mul_of_nonneg_left hengel hC0
    _ ≤ clippedPairEnergy d nodes := hcommonEnergy

end

end ClassicalBound
end Randy1153
