import Randy1153.ClassicalBound.ArcsinePartition
import Randy1153.ClassicalBound.EnergyBins
import Randy1153.ClassicalBound.BinCombinatorics
import Randy1153.ClassicalBound.EnergyEmbedding

/-!
# Aggregating energy over the canonical arcsine partition

This file supplies the finite bridge between the canonical scale-shell
assignment and the global clipped pair energy.  The images of the strict
local pairs in distinct assignment fibers are disjoint, so their local
energies may be summed without paying an overlap factor.

The geometric statements below keep the positive and reflected negative
intervals explicit.  The last theorems insert the exact finite
`denseBin_divisor_lower` estimate in every selected bin; no asymptotic
choice of parameters is made here.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- Local clipped pair energy carried by one fiber of a finite assignment. -/
def assignmentFiberLocalEnergy {d n : ℕ} {β : Type*} [DecidableEq β]
    (nodes : OrderedNodes n) (assign : Fin n → β) (b : β) : ℝ :=
  localPairEnergy
    (fun i ↦ nodes.point (assignmentEmbedding assign b i))
    (fun i ↦ clippedArcsineScale d
      (nodes.point (assignmentEmbedding assign b i)))

/-- Flatten all strict pairs in all assignment fibers. -/
private def assignmentStrictPairSigma {n : ℕ} {β : Type*}
    [Fintype β] [DecidableEq β] (assign : Fin n → β) :
    Finset (Σ b : β,
      Fin (assignmentCount assign b) × Fin (assignmentCount assign b)) :=
  Finset.univ.sigma fun b ↦ strictIndexPairs (assignmentCount assign b)

/-- Send a local pair in an assignment fiber to its pair of global indices. -/
private def assignmentPairToGlobal {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β)
    (q : Σ b : β,
      Fin (assignmentCount assign b) × Fin (assignmentCount assign b)) :
    Fin n × Fin n :=
  (assignmentEmbedding assign q.1 q.2.1,
    assignmentEmbedding assign q.1 q.2.2)

private lemma assignmentPairToGlobal_injective {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) :
    Function.Injective (assignmentPairToGlobal assign) := by
  intro q r hqr
  rcases q with ⟨b, p⟩
  rcases r with ⟨c, s⟩
  have hfirst :
      assignmentEmbedding assign b p.1 =
        assignmentEmbedding assign c s.1 :=
    congrArg Prod.fst hqr
  have hbc : b = c := by
    rw [← assignmentEmbedding_mem_fiber assign b p.1,
      ← assignmentEmbedding_mem_fiber assign c s.1]
    exact congrArg assign hfirst
  subst c
  have hp1 : p.1 = s.1 :=
    (assignmentEmbedding assign b).injective hfirst
  have hsecond :
      assignmentEmbedding assign b p.2 =
        assignmentEmbedding assign b s.2 :=
    congrArg Prod.snd hqr
  have hp2 : p.2 = s.2 :=
    (assignmentEmbedding assign b).injective hsecond
  cases p
  cases s
  simp_all

/-- Exact finite bookkeeping: local energies of all fibers of an arbitrary
finite assignment fit disjointly inside the global clipped pair energy. -/
theorem sum_assignmentFiberLocalEnergy_le_clippedPairEnergy
    {d n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (nodes : OrderedNodes n) (assign : Fin n → β) :
    (∑ b : β, assignmentFiberLocalEnergy (d := d) nodes assign b) ≤
      clippedPairEnergy d nodes := by
  classical
  let source := assignmentStrictPairSigma assign
  let embed := assignmentPairToGlobal assign
  have hembed : Function.Injective embed :=
    assignmentPairToGlobal_injective assign
  have hsubset : source.image embed ⊆ strictIndexPairs n := by
    rw [Finset.image_subset_iff]
    intro q hq
    have hmem := Finset.mem_sigma.mp hq
    rw [mem_strictIndexPairs] at hmem ⊢
    exact assignmentEmbedding_strictMono assign q.1 hmem.2
  rw [clippedPairEnergy_eq_sum_strictIndexPairs]
  calc
    (∑ b : β, assignmentFiberLocalEnergy (d := d) nodes assign b) =
        ∑ q ∈ source,
          clippedPairWeight d nodes (embed q).1 (embed q).2 := by
      dsimp only [source]
      rw [assignmentStrictPairSigma, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro b hb
      rw [assignmentFiberLocalEnergy,
        localPairEnergy_eq_sum_strictIndexPairs
          (fun i ↦ nodes.point (assignmentEmbedding assign b i))
          (fun i ↦ clippedArcsineScale d
            (nodes.point (assignmentEmbedding assign b i)))
          (nodes.strictMono.comp (assignmentEmbedding_strictMono assign b))]
      rfl
    _ = ∑ p ∈ source.image embed,
        clippedPairWeight d nodes p.1 p.2 := by
      rw [Finset.sum_image hembed.injOn]
    _ ≤ ∑ p ∈ strictIndexPairs n,
        clippedPairWeight d nodes p.1 p.2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hpn ↦ clippedPairWeight_nonneg nodes p.1 p.2)

/-- Canonical local energy in a signed geometric arcsine bin. -/
def arcsineBinLocalEnergy {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) : ℝ :=
  assignmentFiberLocalEnergy (d := d) nodes
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal) b

/-- The sum of the canonical bin energies is bounded by the global energy. -/
theorem sum_arcsineBinLocalEnergy_le_clippedPairEnergy
    {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) :
    (∑ b : Bool × Fin (K + 1),
      arcsineBinLocalEnergy q hterminal nodes b) ≤
        clippedPairEnergy d nodes := by
  exact sum_assignmentFiberLocalEnergy_le_clippedPairEnergy nodes
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal)

private lemma cubicChebyshevFloor_le_one_of_one_le {d : ℕ}
    (hd : 1 ≤ d) :
    cubicChebyshevFloor d ≤ 1 := by
  unfold cubicChebyshevFloor
  have hden :
      0 < (((d + 1 : ℕ) : ℝ) * ((2 * d + 1 : ℕ) : ℝ)) := by
    positivity
  apply (div_le_iff₀ hden).2
  norm_num only [one_mul, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat]
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  nlinarith [sq_nonneg (d : ℝ)]

private lemma cubicChebyshevFloor_le_geometricScaleLevel
    {d i : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 ≤ q) :
    cubicChebyshevFloor d ≤ geometricScaleLevel d q i := by
  rw [geometricScaleLevel]
  apply le_min
  · have hpow : 1 ≤ q ^ i := one_le_pow₀ hq
    nlinarith [cubicChebyshevFloor_nonneg d]
  · exact cubicChebyshevFloor_le_one_of_one_le hd

/-- The positive-half interval belonging to an unsigned geometric shell. -/
def geometricPositiveBinInterval (d : ℕ) (q : ℝ) {K : ℕ}
    (i : Fin (K + 1)) : Set ℝ :=
  Set.Icc
    (Real.cos (geometricHalfAngle d q (i.val + 1)))
    (Real.cos (geometricHalfAngle d q i.val))

/-- Full signed interval belonging to a canonical bin label. -/
def geometricSignedBinLowerEndpoint (d : ℕ) (q : ℝ) {K : ℕ}
    (b : Bool × Fin (K + 1)) : ℝ :=
  if b.1 then Real.cos (geometricHalfAngle d q (b.2.val + 1))
  else -Real.cos (geometricHalfAngle d q b.2.val)

/-- Upper endpoint of a canonical signed geometric bin. -/
def geometricSignedBinUpperEndpoint (d : ℕ) (q : ℝ) {K : ℕ}
    (b : Bool × Fin (K + 1)) : ℝ :=
  if b.1 then Real.cos (geometricHalfAngle d q b.2.val)
  else -Real.cos (geometricHalfAngle d q (b.2.val + 1))

/-- Full signed interval belonging to a canonical bin label. -/
def geometricSignedBinInterval (d : ℕ) (q : ℝ) {K : ℕ}
    (b : Bool × Fin (K + 1)) : Set ℝ :=
  Set.Icc (geometricSignedBinLowerEndpoint d q b)
    (geometricSignedBinUpperEndpoint d q b)

/-- Reflection preserves the exact cosine-bin length. -/
lemma geometricSignedBin_intervalLength
    (d K : ℕ) {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1)) :
    geometricSignedBinUpperEndpoint d q b -
        geometricSignedBinLowerEndpoint d q b =
      cosineBinLength
        (geometricHalfArcsinePartition d K q
          hq hterminal).angle b.2 := by
  rcases b with ⟨side, i⟩
  cases side
  · simp [geometricSignedBinUpperEndpoint,
      geometricSignedBinLowerEndpoint, cosineBinLength,
      geometricHalfArcsinePartition, angleBinLeft, angleBinRight]
    ring
  · simp [geometricSignedBinUpperEndpoint,
      geometricSignedBinLowerEndpoint, cosineBinLength,
      geometricHalfArcsinePartition, angleBinLeft, angleBinRight]

private lemma cos_le_of_clippedScale_le {d : ℕ} {x θ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ0 : 0 ≤ θ)
    (hθhalf : θ ≤ Real.pi / 2)
    (hfloor : cubicChebyshevFloor d ≤ Real.sin θ)
    (hscale : clippedArcsineScale d x ≤
      clippedArcsineScale d (Real.cos θ)) :
    Real.cos θ ≤ x := by
  have hθpi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθhalf⟩
  have hxrad : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [clippedArcsineScale, clippedArcsineScale,
    ← Real.sin_eq_sqrt_one_sub_cos_sq hθ0 hθpi,
    max_eq_left hfloor] at hscale
  have hsqrt : Real.sqrt (1 - x ^ 2) ≤ Real.sin θ :=
    (le_max_left _ _).trans hscale
  have hsqr := Real.sq_sqrt hxrad
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sqrt_nonneg (1 - x ^ 2)]

private lemma le_cos_of_clippedScale_lt {d : ℕ} {x θ : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ0 : 0 ≤ θ)
    (hθhalf : θ ≤ Real.pi / 2)
    (hfloor : cubicChebyshevFloor d ≤ Real.sin θ)
    (hscale : clippedArcsineScale d (Real.cos θ) <
      clippedArcsineScale d x) :
    x ≤ Real.cos θ := by
  have hθpi : θ ≤ Real.pi := by linarith [Real.pi_pos]
  have hsin0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθpi
  have hcos0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθhalf⟩
  have hxrad : 0 ≤ 1 - x ^ 2 := by nlinarith
  rw [clippedArcsineScale, clippedArcsineScale,
    ← Real.sin_eq_sqrt_one_sub_cos_sq hθ0 hθpi,
    max_eq_left hfloor, lt_max_iff] at hscale
  have hsqrt : Real.sin θ < Real.sqrt (1 - x ^ 2) :=
    hscale.resolve_right (not_lt_of_ge hfloor)
  have hsqr := Real.sq_sqrt hxrad
  nlinarith [Real.sin_sq_add_cos_sq θ, Real.sqrt_nonneg (1 - x ^ 2)]

/-- Exact geometric localization of a point in a canonical signed shell.
Positive degree is necessary: at degree zero the cubic floor is three and
the scale assignment cannot recover spatial shells inside `[-1,1]`. -/
theorem mem_geometricSignedBinInterval_of_assignment
    {d K : ℕ} {q x : ℝ} (hd : 1 ≤ d) (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (hxIcc : x ∈ Set.Icc (-1 : ℝ) 1)
    (b : Bool × Fin (K + 1))
    (hx : x ∈ arcsineAssignedBin d K q hterminal b) :
    x ∈ geometricSignedBinInterval d q b := by
  rcases b with ⟨side, i⟩
  have hindex : geometricScaleBinIndex d K q x hterminal = i :=
    congrArg Prod.snd hx
  have hupp : clippedArcsineScale d x ≤
      clippedArcsineScale d
        (Real.cos (geometricHalfAngle d q (i.val + 1))) := by
    have h := clippedArcsineScale_le_assignedThreshold
      d K q x hterminal
    rw [hindex, geometricScaleThreshold,
      ← clippedArcsineScale_cos_geometricHalfAngle_succ d i.val
        (zero_le_one.trans hq.le)] at h
    exact h
  have hright0 : 0 ≤ geometricHalfAngle d q (i.val + 1) :=
    geometricHalfAngle_nonneg (zero_le_one.trans hq.le)
  have hrightHalf :
      geometricHalfAngle d q (i.val + 1) ≤ Real.pi / 2 :=
    geometricHalfAngle_le_pi_div_two d q _
  have hrightFloor : cubicChebyshevFloor d ≤
      Real.sin (geometricHalfAngle d q (i.val + 1)) := by
    have hlevel0 : 0 ≤ geometricScaleLevel d q i.val :=
      geometricScaleLevel_nonneg (zero_le_one.trans hq.le)
    rw [geometricHalfAngle_succ,
      Real.sin_arcsin (by linarith)
        (geometricScaleLevel_le_one d q i.val)]
    exact cubicChebyshevFloor_le_geometricScaleLevel hd hq.le
  cases side with
  | false =>
      have hxneg : x < 0 := by
        have hside := congrArg Prod.fst hx
        simp only [arcsineBinAssignment, decide_eq_false_iff_not] at hside
        exact lt_of_not_ge hside
      have hyIcc : -x ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hxIcc.1, hxIcc.2]
      have huppNeg : clippedArcsineScale d (-x) ≤
          clippedArcsineScale d
            (Real.cos (geometricHalfAngle d q (i.val + 1))) := by
        simpa only [clippedArcsineScale_neg] using hupp
      have hright := cos_le_of_clippedScale_le
        hyIcc.1 hyIcc.2 hright0 hrightHalf hrightFloor huppNeg
      have hleft : -x ≤ Real.cos (geometricHalfAngle d q i.val) := by
        by_cases hi : i.val = 0
        · simpa [hi, geometricHalfAngle] using hyIcc.2
        · have hlower :=
            previousThreshold_lt_clippedArcsineScale_of_assigned_ne_zero
              d K q x hterminal (by simpa [hindex] using hi)
          rw [hindex] at hlower
          obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
          have hleftScale : clippedArcsineScale d
              (Real.cos (geometricHalfAngle d q i.val)) <
                clippedArcsineScale d (-x) := by
            rw [hj, clippedArcsineScale_cos_geometricHalfAngle_succ
              d j (zero_le_one.trans hq.le), clippedArcsineScale_neg]
            simpa [geometricScaleThreshold, hj] using hlower
          have hleft0 : 0 ≤ geometricHalfAngle d q i.val :=
            geometricHalfAngle_nonneg (zero_le_one.trans hq.le)
          have hleftHalf : geometricHalfAngle d q i.val ≤ Real.pi / 2 :=
            geometricHalfAngle_le_pi_div_two d q _
          have hleftFloor : cubicChebyshevFloor d ≤
              Real.sin (geometricHalfAngle d q i.val) := by
            have hlevel0 : 0 ≤ geometricScaleLevel d q j :=
              geometricScaleLevel_nonneg (zero_le_one.trans hq.le)
            rw [hj, geometricHalfAngle_succ,
              Real.sin_arcsin (by linarith)
                (geometricScaleLevel_le_one d q j)]
            exact cubicChebyshevFloor_le_geometricScaleLevel hd hq.le
          exact le_cos_of_clippedScale_lt hyIcc.1 hyIcc.2
            hleft0 hleftHalf hleftFloor hleftScale
      change -Real.cos (geometricHalfAngle d q i.val) ≤ x ∧
        x ≤ -Real.cos (geometricHalfAngle d q (i.val + 1))
      exact ⟨by linarith, by linarith⟩
  | true =>
      have hx0 : 0 ≤ x := by
        have hside := congrArg Prod.fst hx
        simpa only [arcsineBinAssignment, decide_eq_true_eq] using hside
      have hright := cos_le_of_clippedScale_le
        hx0 hxIcc.2 hright0 hrightHalf hrightFloor hupp
      have hleft : x ≤ Real.cos (geometricHalfAngle d q i.val) := by
        by_cases hi : i.val = 0
        · simpa [hi, geometricHalfAngle] using hxIcc.2
        · have hlower :=
            previousThreshold_lt_clippedArcsineScale_of_assigned_ne_zero
              d K q x hterminal (by simpa [hindex] using hi)
          rw [hindex] at hlower
          obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
          have hleftScale : clippedArcsineScale d
              (Real.cos (geometricHalfAngle d q i.val)) <
                clippedArcsineScale d x := by
            rw [hj, clippedArcsineScale_cos_geometricHalfAngle_succ
              d j (zero_le_one.trans hq.le)]
            simpa [geometricScaleThreshold, hj] using hlower
          have hleft0 : 0 ≤ geometricHalfAngle d q i.val :=
            geometricHalfAngle_nonneg (zero_le_one.trans hq.le)
          have hleftHalf : geometricHalfAngle d q i.val ≤ Real.pi / 2 :=
            geometricHalfAngle_le_pi_div_two d q _
          have hleftFloor : cubicChebyshevFloor d ≤
              Real.sin (geometricHalfAngle d q i.val) := by
            have hlevel0 : 0 ≤ geometricScaleLevel d q j :=
              geometricScaleLevel_nonneg (zero_le_one.trans hq.le)
            rw [hj, geometricHalfAngle_succ,
              Real.sin_arcsin (by linarith)
                (geometricScaleLevel_le_one d q j)]
            exact cubicChebyshevFloor_le_geometricScaleLevel hd hq.le
          exact le_cos_of_clippedScale_lt hx0 hxIcc.2
            hleft0 hleftHalf hleftFloor hleftScale
      exact ⟨hright, hleft⟩

/-- Every node in the canonical fiber lies in its explicit signed cosine
interval. -/
theorem arcsineNodeBinEmbedding_mem_interval
    {d K n : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1))
    (i : Fin (arcsineNodeBinCount q hterminal nodes b)) :
    nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i) ∈
      geometricSignedBinInterval d q b := by
  have hfiber := assignmentEmbedding_mem_fiber
    (fun j ↦ arcsineBinAssignment d K q (nodes.point j) hterminal) b i
  apply mem_geometricSignedBinInterval_of_assignment hd hq hterminal
    (nodes.mem_Icc _)
  change arcsineBinAssignment d K q
    (nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i)) hterminal = b
  convert hfiber using 1
  simp only [arcsineNodeBinEmbedding]
  congr 1

/-- Every node in a canonical fiber has scale at least the bin's geometric
lower scale. -/
theorem geometricBinLowerScale_le_arcsineNodeBinScale
    {d K n : ℕ} {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1))
    (i : Fin (arcsineNodeBinCount q hterminal nodes b)) :
    geometricBinLowerScale d q b.2 ≤
      clippedArcsineScale d
        (nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i)) := by
  have hfiber := assignmentEmbedding_mem_fiber
    (fun j ↦ arcsineBinAssignment d K q (nodes.point j) hterminal) b i
  have hx : nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i) ∈
      arcsineAssignedBin d K q hterminal b := by
    change arcsineBinAssignment d K q
      (nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i)) hterminal = b
    convert hfiber using 1
    simp only [arcsineNodeBinEmbedding]
    congr 1
  exact (mem_arcsineAssignedBin_scale_bounds
    d K hq.le hterminal b hx).1

private lemma intervalLength_pos_of_strictMono
    {m : ℕ} (x : Fin m → ℝ) (hx : StrictMono x) (hm : 2 ≤ m)
    {A B : ℝ} (hxIcc : ∀ i, x i ∈ Set.Icc A B) :
    0 < B - A := by
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  have hlt : x i₀ < x i₁ := hx (by simp [i₀, i₁])
  rcases hxIcc i₀ with ⟨hA₀, h₀B⟩
  rcases hxIcc i₁ with ⟨hA₁, h₁B⟩
  linarith

/-- Exact dense-bin lower bound for one canonical fiber.  All floor losses
remain visible, and the interval denominator is the actual cosine-bin
length. -/
theorem dense_arcsineBin_divisor_lower
    {d K n L : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1))
    (hL : 1 < L) (hLm : L ≤ arcsineNodeBinCount q hterminal nodes b) :
    geometricBinLowerScale d q b.2 *
        (((((arcsineNodeBinCount q hterminal nodes b -
              arcsineNodeBinCount q hterminal nodes b / L : ℕ) : ℝ) ^ 2) *
            realHarmonic
              (arcsineNodeBinCount q hterminal nodes b / L)) /
          cosineBinLength
            (geometricHalfArcsinePartition d K q hq hterminal).angle b.2) ≤
      arcsineBinLocalEnergy q hterminal nodes b := by
  let m := arcsineNodeBinCount q hterminal nodes b
  let x : Fin m → ℝ :=
    fun i ↦ nodes.point (arcsineNodeBinEmbedding q hterminal nodes b i)
  let scale : Fin m → ℝ := fun i ↦ clippedArcsineScale d (x i)
  let A := geometricSignedBinLowerEndpoint d q b
  let B := geometricSignedBinUpperEndpoint d q b
  let h := cosineBinLength
    (geometricHalfArcsinePartition d K q hq hterminal).angle b.2
  have hx : StrictMono x :=
    nodes.strictMono.comp (arcsineNodeBinEmbedding_strictMono
      q hterminal nodes b)
  have hxIcc : ∀ i, x i ∈ Set.Icc A B := by
    intro i
    exact arcsineNodeBinEmbedding_mem_interval hd hq hterminal nodes b i
  have hm2 : 2 ≤ m := by
    dsimp only [m]
    omega
  have hh : 0 < h := by
    have hpos := intervalLength_pos_of_strictMono x hx hm2 hxIcc
    rw [geometricSignedBin_intervalLength d K hq hterminal b] at hpos
    exact hpos
  have hinterval : B - A ≤ h := by
    rw [geometricSignedBin_intervalLength d K hq hterminal b]
  have hscale : ∀ i, geometricBinLowerScale d q b.2 ≤ scale i := by
    intro i
    exact geometricBinLowerScale_le_arcsineNodeBinScale
      hq hterminal nodes b i
  have hbound := denseBin_divisor_lower x scale hx hL hLm
    hxIcc hh hinterval (geometricBinLowerScale_pos d b.2).le hscale
  convert hbound using 1
  simp only [arcsineBinLocalEnergy, assignmentFiberLocalEnergy, m, x, scale, h,
    arcsineNodeBinEmbedding]
  congr 1

lemma arcsineBinLocalEnergy_nonneg
    {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) :
    0 ≤ arcsineBinLocalEnergy q hterminal nodes b := by
  rw [arcsineBinLocalEnergy, assignmentFiberLocalEnergy, localPairEnergy]
  apply Finset.sum_nonneg
  intro r hr
  exact stepPairEnergy_nonneg _ _
    (nodes.strictMono.comp (assignmentEmbedding_strictMono
      (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal) b))
    (Finset.mem_Ico.mp hr).1

/-- Strongest exact finite aggregate before choosing any asymptotic
parameters: every selected bin containing at least `L` nodes contributes
its full floor-sensitive harmonic lower bound, and their sum is bounded by
the single global clipped pair energy. -/
theorem sum_selectedDense_arcsineBin_lower_le_clippedPairEnergy
    {d K n L : ℕ} {q : ℝ} (hd : 1 ≤ d) (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n)
    (bins : Finset (Bool × Fin (K + 1))) (hL : 1 < L)
    (hdense : ∀ b ∈ bins, L ≤ arcsineNodeBinCount q hterminal nodes b) :
    (∑ b ∈ bins,
      geometricBinLowerScale d q b.2 *
        (((((arcsineNodeBinCount q hterminal nodes b -
              arcsineNodeBinCount q hterminal nodes b / L : ℕ) : ℝ) ^ 2) *
            realHarmonic
              (arcsineNodeBinCount q hterminal nodes b / L)) /
          cosineBinLength
            (geometricHalfArcsinePartition d K q hq hterminal).angle b.2)) ≤
      clippedPairEnergy d nodes := by
  calc
    _ ≤ ∑ b ∈ bins, arcsineBinLocalEnergy q hterminal nodes b := by
      exact Finset.sum_le_sum fun b hb ↦
        dense_arcsineBin_divisor_lower hd hq hterminal nodes b hL
          (hdense b hb)
    _ ≤ ∑ b : Bool × Fin (K + 1),
        arcsineBinLocalEnergy q hterminal nodes b := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bins)
        (fun b hb hbn ↦ arcsineBinLocalEnergy_nonneg
          q hterminal nodes b)
    _ ≤ clippedPairEnergy d nodes :=
      sum_arcsineBinLocalEnergy_le_clippedPairEnergy q hterminal nodes

end

end ClassicalBound
end Randy1153
