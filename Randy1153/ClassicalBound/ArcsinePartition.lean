import Randy1153.ClassicalBound.ArcsineBins

/-!
# Explicit geometric arcsine partitions

For q > 1, let c be the positive cubic Chebyshev floor and set

    level i = min (q^i c) 1.

The half-angle endpoints are zero followed by the arcsines of levels
zero through K.  Thus the construction has K+1 bins.  If q^K c ≥ 1,
the final endpoint is pi/2.  This file proves the construction satisfies
the exact HalfArcsinePartition interface.

The endpoint zero is kept separate because c is positive: starting the
geometric levels themselves at index zero would incorrectly begin at
arcsin c rather than at the endpoint x = 1.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- The clipped geometric scale level before applying arcsine. -/
def geometricScaleLevel (d : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  min (q ^ i * cubicChebyshevFloor d) 1

lemma geometricScaleLevel_nonneg {d i : ℕ} {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ geometricScaleLevel d q i := by
  rw [geometricScaleLevel]
  exact le_min
    (mul_nonneg (pow_nonneg hq _) (cubicChebyshevFloor_nonneg d))
    zero_le_one

lemma geometricScaleLevel_le_one (d : ℕ) (q : ℝ) (i : ℕ) :
    geometricScaleLevel d q i ≤ 1 :=
  min_le_right _ _

lemma geometricScaleLevel_mono {d : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    Monotone (geometricScaleLevel d q) := by
  intro i j hij
  rw [geometricScaleLevel, geometricScaleLevel]
  apply min_le_min
  · exact mul_le_mul_of_nonneg_right
      (pow_right_mono₀ hq hij) (cubicChebyshevFloor_nonneg d)
  · exact le_rfl

lemma geometricScaleLevel_succ_le_mul {d i : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    geometricScaleLevel d q (i + 1) ≤ q * geometricScaleLevel d q i := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  by_cases hi : q ^ i * cubicChebyshevFloor d ≤ 1
  · rw [geometricScaleLevel, geometricScaleLevel, min_eq_left hi]
    calc
      min (q ^ (i + 1) * cubicChebyshevFloor d) 1 ≤
          q ^ (i + 1) * cubicChebyshevFloor d := min_le_left _ _
      _ = q * (q ^ i * cubicChebyshevFloor d) := by
        rw [pow_succ]
        ring
  · have hi' : 1 ≤ q ^ i * cubicChebyshevFloor d := le_of_not_ge hi
    simp only [geometricScaleLevel]
    rw [min_eq_right hi']
    exact (geometricScaleLevel_le_one d q (i + 1)).trans (by simpa using hq)

lemma geometricScaleLevel_terminal {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricScaleLevel d q K = 1 := by
  exact min_eq_right hterminal

/-- The natural-index endpoint sequence: zero first, then arcsines of the
geometric scale levels. -/
def geometricHalfAngle (d : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0
  else Real.arcsin (geometricScaleLevel d q (j - 1))

@[simp]
lemma geometricHalfAngle_zero (d : ℕ) (q : ℝ) :
    geometricHalfAngle d q 0 = 0 := by
  simp [geometricHalfAngle]

lemma geometricHalfAngle_succ (d : ℕ) (q : ℝ) (i : ℕ) :
    geometricHalfAngle d q (i + 1) =
      Real.arcsin (geometricScaleLevel d q i) := by
  simp [geometricHalfAngle]

lemma geometricHalfAngle_nonneg {d j : ℕ} {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ geometricHalfAngle d q j := by
  by_cases hj : j = 0
  · simp [hj]
  · rw [geometricHalfAngle, if_neg hj]
    exact Real.arcsin_nonneg.mpr (geometricScaleLevel_nonneg hq)

lemma geometricHalfAngle_mono {d : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    Monotone (geometricHalfAngle d q) := by
  intro i j hij
  by_cases hi : i = 0
  · subst i
    exact geometricHalfAngle_nonneg (zero_le_one.trans hq)
  · have hj : j ≠ 0 := by omega
    rw [geometricHalfAngle, if_neg hi, geometricHalfAngle, if_neg hj]
    exact Real.arcsin_le_arcsin
      (geometricScaleLevel_mono hq (Nat.sub_le_sub_right hij 1))

lemma geometricHalfAngle_terminal {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricHalfAngle d q (K + 1) = Real.pi / 2 := by
  rw [geometricHalfAngle_succ, geometricScaleLevel_terminal hterminal,
    Real.arcsin_one]

lemma geometricHalfAngle_le_pi_div_two (d : ℕ) (q : ℝ) (j : ℕ) :
    geometricHalfAngle d q j ≤ Real.pi / 2 := by
  by_cases hj : j = 0
  · simp [hj]
    positivity
  · rw [geometricHalfAngle, if_neg hj]
    exact Real.arcsin_le_pi_div_two _

/-- At a geometric angle endpoint, the clipped scale is the maximum of
that level and the floor. -/
lemma clippedArcsineScale_cos_geometricHalfAngle_succ
    (d i : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    clippedArcsineScale d
        (Real.cos (geometricHalfAngle d q (i + 1))) =
      max (geometricScaleLevel d q i) (cubicChebyshevFloor d) := by
  rw [geometricHalfAngle_succ,
    clippedArcsineScale_cos
      (Real.arcsin_nonneg.mpr (geometricScaleLevel_nonneg hq))
      (Real.arcsin_le_pi_div_two _ |>.trans
        (by linarith [Real.pi_pos]))]
  rw [Real.sin_arcsin
    (by linarith [geometricScaleLevel_nonneg (d := d) (i := i) hq])
    (geometricScaleLevel_le_one d q i)]

lemma clippedArcsineScale_cos_geometricHalfAngle_zero (d : ℕ) (q : ℝ) :
    clippedArcsineScale d
        (Real.cos (geometricHalfAngle d q 0)) =
      cubicChebyshevFloor d := by
  simp [geometricHalfAngle, clippedArcsineScale,
    cubicChebyshevFloor_nonneg]

lemma max_geometricScaleLevel_floor_succ_le_mul
    {d i : ℕ} {q : ℝ} (hq : 1 ≤ q) :
    max (geometricScaleLevel d q (i + 1)) (cubicChebyshevFloor d) ≤
      q * max (geometricScaleLevel d q i) (cubicChebyshevFloor d) := by
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  apply max_le
  · exact (geometricScaleLevel_succ_le_mul hq).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hq0)
  · calc
      cubicChebyshevFloor d ≤ q * cubicChebyshevFloor d := by
        nlinarith [cubicChebyshevFloor_nonneg d]
      _ ≤ q * max (geometricScaleLevel d q i)
          (cubicChebyshevFloor d) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hq0

/-- The explicit K+1-bin half partition generated by geometric scale
levels through exponent K. -/
def geometricHalfArcsinePartition (d K : ℕ) (q : ℝ)
    (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    HalfArcsinePartition d (K + 1) q where
  positive_bins := Nat.succ_pos K
  angle j := geometricHalfAngle d q j.val
  monotone_angle := by
    intro i j hij
    exact geometricHalfAngle_mono (d := d) hq.le hij
  angle_zero := geometricHalfAngle_zero d q
  angle_last := geometricHalfAngle_terminal hterminal
  scale_ratio := by
    intro i
    by_cases hi : i.val = 0
    · have hiright : (angleBinRight i).val = 1 := by
        simp [angleBinRight, hi]
      have hileft : (angleBinLeft i).val = 0 := by
        simp [angleBinLeft, hi]
      rw [show geometricHalfAngle d q (angleBinRight i).val =
          geometricHalfAngle d q 1 by rw [hiright],
        show geometricHalfAngle d q (angleBinLeft i).val =
          geometricHalfAngle d q 0 by rw [hileft],
        clippedArcsineScale_cos_geometricHalfAngle_succ d 0
          (zero_le_one.trans hq.le),
        clippedArcsineScale_cos_geometricHalfAngle_zero]
      have hlevel0 :
          geometricScaleLevel d q 0 ≤ cubicChebyshevFloor d := by
        rw [geometricScaleLevel, pow_zero, one_mul]
        exact min_le_left _ _
      rw [max_eq_right hlevel0]
      exact (le_mul_of_one_le_left
        (cubicChebyshevFloor_nonneg d) hq.le)
    · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := by
        exact ⟨i.val - 1, by omega⟩
      have hiright : (angleBinRight i).val = j + 2 := by
        simp [angleBinRight, hj]
      have hileft : (angleBinLeft i).val = j + 1 := by
        simp [angleBinLeft, hj]
      rw [show geometricHalfAngle d q (angleBinRight i).val =
          geometricHalfAngle d q (j + 2) by rw [hiright],
        show geometricHalfAngle d q (angleBinLeft i).val =
          geometricHalfAngle d q (j + 1) by rw [hileft],
        show j + 2 = (j + 1) + 1 by omega,
        clippedArcsineScale_cos_geometricHalfAngle_succ d (j + 1)
          (zero_le_one.trans hq.le),
        clippedArcsineScale_cos_geometricHalfAngle_succ d j
          (zero_le_one.trans hq.le)]
      exact max_geometricScaleLevel_floor_succ_le_mul hq.le

/-- The explicit construction inherits the exact full reflected
length-over-scale budget. -/
theorem geometricPartition_full_budget_le
    {d K : ℕ} {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    2 * (∑ i : Fin (K + 1),
      cosineBinLength (geometricHalfArcsinePartition d K q hq hterminal).angle i /
        cosineBinLowerScale d
          (geometricHalfArcsinePartition d K q hq hterminal).angle i) ≤
      q * Real.pi :=
  (geometricHalfArcsinePartition d K q hq hterminal).two_mul_sum_cosineBinLength_div_lowerScale_le

/-- The actual clipped-scale threshold attached to geometric level i. -/
def geometricScaleThreshold (d : ℕ) (q : ℝ) (i : ℕ) : ℝ :=
  max (geometricScaleLevel d q i) (cubicChebyshevFloor d)

lemma geometricScaleThreshold_terminal {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricScaleThreshold d q K =
      max 1 (cubicChebyshevFloor d) := by
  rw [geometricScaleThreshold,
    geometricScaleLevel_terminal hterminal]

/-- Every clipped scale is below the terminal threshold once the geometric
levels have reached one. -/
lemma clippedArcsineScale_le_terminalThreshold {d K : ℕ} {q x : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    clippedArcsineScale d x ≤ geometricScaleThreshold d q K := by
  rw [geometricScaleThreshold_terminal hterminal, clippedArcsineScale]
  apply max_le_max
  · rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg x]
  · exact le_rfl

/-- Some geometric threshold with index at most K contains every real
point. -/
lemma exists_scaleThreshold_index {d K : ℕ} {q x : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    ∃ i : ℕ, i ≤ K ∧
      clippedArcsineScale d x ≤ geometricScaleThreshold d q i :=
  ⟨K, le_rfl, clippedArcsineScale_le_terminalThreshold hterminal⟩

/-- Least geometric scale shell containing x.  The terminal hypothesis
makes this a total function into the K+1 half-shell indices. -/
noncomputable def geometricScaleBinIndex (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) : Fin (K + 1) :=
  ⟨Nat.find (exists_scaleThreshold_index (d := d) (K := K)
      (q := q) (x := x) hterminal),
    by
      have hspec := Nat.find_spec
        (exists_scaleThreshold_index (d := d) (K := K)
          (q := q) (x := x) hterminal)
      omega⟩

lemma clippedArcsineScale_le_assignedThreshold
    (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    clippedArcsineScale d x ≤
      geometricScaleThreshold d q
        (geometricScaleBinIndex d K q x hterminal).val := by
  exact (Nat.find_spec
    (exists_scaleThreshold_index (d := d) (K := K)
      (q := q) (x := x) hterminal)).2

lemma geometricScaleThreshold_succ_le_mul {d i : ℕ} {q : ℝ}
    (hq : 1 ≤ q) :
    geometricScaleThreshold d q (i + 1) ≤
      q * geometricScaleThreshold d q i := by
  simpa only [geometricScaleThreshold] using
    (max_geometricScaleLevel_floor_succ_le_mul (d := d) (i := i) hq)

/-- Lower scale attached to a shell.  The first shell starts at the cubic
floor; later shells start at the preceding threshold. -/
def geometricBinLowerScale (d : ℕ) (q : ℝ) {K : ℕ}
    (i : Fin (K + 1)) : ℝ :=
  if i.val = 0 then cubicChebyshevFloor d
  else geometricScaleThreshold d q (i.val - 1)

lemma geometricBinLowerScale_pos (d : ℕ) {q : ℝ} {K : ℕ}
    (i : Fin (K + 1)) :
    0 < geometricBinLowerScale d q i := by
  rw [geometricBinLowerScale]
  split_ifs
  · exact cubicChebyshevFloor_pos d
  · exact (cubicChebyshevFloor_pos d).trans_le (le_max_right _ _)

/-- The shell lower scales used by the canonical assignment are exactly
the lower scales of the explicit cosine bins. -/
lemma geometricBinLowerScale_eq_cosineBinLowerScale
    (d K : ℕ) {q : ℝ} (hq : 1 < q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (i : Fin (K + 1)) :
    geometricBinLowerScale d q i =
      cosineBinLowerScale d
        (geometricHalfArcsinePartition d K q hq hterminal).angle i := by
  change geometricBinLowerScale d q i =
    clippedArcsineScale d
      (Real.cos (geometricHalfAngle d q (angleBinLeft i).val))
  by_cases hi : i.val = 0
  · have hleft : (angleBinLeft i).val = 0 := by
      simp [angleBinLeft, hi]
    rw [geometricBinLowerScale, if_pos hi,
      show geometricHalfAngle d q (angleBinLeft i).val =
        geometricHalfAngle d q 0 by rw [hleft],
      clippedArcsineScale_cos_geometricHalfAngle_zero]
  · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
    have hleft : (angleBinLeft i).val = j + 1 := by
      simp [angleBinLeft, hj]
    rw [geometricBinLowerScale, if_neg hi,
      show geometricHalfAngle d q (angleBinLeft i).val =
        geometricHalfAngle d q (j + 1) by rw [hleft],
      clippedArcsineScale_cos_geometricHalfAngle_succ d j
        (zero_le_one.trans hq.le),
      geometricScaleThreshold, hj, Nat.add_sub_cancel]

/-- Minimality of the assigned threshold gives a strict lower bound by the
preceding threshold away from the first shell. -/
lemma previousThreshold_lt_clippedArcsineScale_of_assigned_ne_zero
    (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (hi : (geometricScaleBinIndex d K q x hterminal).val ≠ 0) :
    geometricScaleThreshold d q
        ((geometricScaleBinIndex d K q x hterminal).val - 1) <
      clippedArcsineScale d x := by
  let hex := exists_scaleThreshold_index (d := d) (K := K)
    (q := q) (x := x) hterminal
  let j := Nat.find hex
  have hjeq :
      (geometricScaleBinIndex d K q x hterminal).val = j := rfl
  have hjpos : 0 < j := by
    rw [hjeq] at hi
    omega
  by_contra h
  have hle :
      clippedArcsineScale d x ≤ geometricScaleThreshold d q (j - 1) :=
    not_lt.mp h
  have hspec := Nat.find_spec hex
  have hcand :
      (j - 1) ≤ K ∧
        clippedArcsineScale d x ≤ geometricScaleThreshold d q (j - 1) :=
    ⟨by omega, hle⟩
  have hmin : j ≤ j - 1 := Nat.find_min' hex hcand
  omega

/-- Every assigned point lies above its shell lower scale. -/
lemma geometricBinLowerScale_le_assignedScale
    (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    geometricBinLowerScale d q
        (geometricScaleBinIndex d K q x hterminal) ≤
      clippedArcsineScale d x := by
  rw [geometricBinLowerScale]
  split_ifs with hi
  · exact le_max_right _ _
  · exact (previousThreshold_lt_clippedArcsineScale_of_assigned_ne_zero
      d K q x hterminal hi).le

/-- The upper threshold of a shell is at most q times its lower scale. -/
lemma assignedThreshold_le_mul_geometricBinLowerScale
    (d K : ℕ) {q : ℝ} (hq : 1 ≤ q) (i : Fin (K + 1)) :
    geometricScaleThreshold d q i.val ≤ q * geometricBinLowerScale d q i := by
  rw [geometricBinLowerScale]
  split_ifs with hi
  · have hlevel0 :
        geometricScaleLevel d q 0 ≤ cubicChebyshevFloor d := by
      rw [geometricScaleLevel, pow_zero, one_mul]
      exact min_le_left _ _
    rw [show i.val = 0 from hi, geometricScaleThreshold,
      max_eq_right hlevel0]
    exact le_mul_of_one_le_left (cubicChebyshevFloor_nonneg d) hq
  · obtain ⟨j, hj⟩ : ∃ j, i.val = j + 1 := ⟨i.val - 1, by omega⟩
    rw [hj, Nat.add_sub_cancel]
    exact geometricScaleThreshold_succ_le_mul hq

/-- Assigned scales oscillate by at most q inside every canonical shell. -/
theorem assignedScale_le_mul_geometricBinLowerScale
    (d K : ℕ) {q x : ℝ} (hq : 1 ≤ q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    clippedArcsineScale d x ≤ q * geometricBinLowerScale d q
      (geometricScaleBinIndex d K q x hterminal) := by
  exact (clippedArcsineScale_le_assignedThreshold
    d K q x hterminal).trans
      (assignedThreshold_le_mul_geometricBinLowerScale d K hq _)

/-- Side and least scale shell form a canonical full-interval bin label.
False is the negative half and true is the nonnegative half; hence zero is
assigned only once. -/
noncomputable def arcsineBinAssignment (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    Bool × Fin (K + 1) :=
  (decide (0 ≤ x), geometricScaleBinIndex d K q x hterminal)

/-- The set-theoretic bin determined by a canonical label.  These are the
half-open geometric scale shells, split by sign. -/
def arcsineAssignedBin (d K : ℕ) (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1)) : Set ℝ :=
  {x | arcsineBinAssignment d K q x hterminal = b}

lemma mem_arcsineAssignedBin_iff (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1)) :
    x ∈ arcsineAssignedBin d K q hterminal b ↔
      arcsineBinAssignment d K q x hterminal = b :=
  Iff.rfl

/-- Membership in a canonical bin gives the exact lower-scale and
factor-q upper-scale bounds used by the local energy estimate. -/
theorem mem_arcsineAssignedBin_scale_bounds
    (d K : ℕ) {q x : ℝ} (hq : 1 ≤ q)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1))
    (hx : x ∈ arcsineAssignedBin d K q hterminal b) :
    geometricBinLowerScale d q b.2 ≤ clippedArcsineScale d x ∧
      clippedArcsineScale d x ≤ q * geometricBinLowerScale d q b.2 := by
  have hindex :
      geometricScaleBinIndex d K q x hterminal = b.2 :=
    congrArg Prod.snd hx
  constructor
  · rw [← hindex]
    exact geometricBinLowerScale_le_assignedScale d K q x hterminal
  · rw [← hindex]
    exact assignedScale_le_mul_geometricBinLowerScale d K hq hterminal

lemma mem_arcsineAssignedBin_side
    (d K : ℕ) {q x : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (b : Bool × Fin (K + 1))
    (hx : x ∈ arcsineAssignedBin d K q hterminal b) :
    decide (0 ≤ x) = b.1 :=
  congrArg Prod.fst hx

/-- Every point has exactly one canonical full-interval bin label. -/
theorem existsUnique_mem_arcsineAssignedBin (d K : ℕ) (q x : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    ∃! b : Bool × Fin (K + 1),
      x ∈ arcsineAssignedBin d K q hterminal b := by
  refine ⟨arcsineBinAssignment d K q x hterminal, rfl, ?_⟩
  intro b hb
  exact hb.symm

/-- Distinct canonical bins are disjoint. -/
lemma arcsineAssignedBin_disjoint {d K : ℕ} {q : ℝ}
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    {b c : Bool × Fin (K + 1)} (hbc : b ≠ c) :
    Disjoint (arcsineAssignedBin d K q hterminal b)
      (arcsineAssignedBin d K q hterminal c) := by
  rw [Set.disjoint_left]
  intro x hxb hxc
  exact hbc (hxb.symm.trans hxc)

/-- The canonical bins cover the real line, hence in particular
the interpolation interval. -/
lemma iUnion_arcsineAssignedBin (d K : ℕ) (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d) :
    (⋃ b : Bool × Fin (K + 1),
      arcsineAssignedBin d K q hterminal b) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨arcsineBinAssignment d K q x hterminal, rfl⟩

/-- Fiber of a finite assignment. -/
def assignmentFiber {n : ℕ} {β : Type*} [DecidableEq β]
    (assign : Fin n → β) (b : β) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ assign i = b

/-- Cardinality of one assignment fiber. -/
def assignmentCount {n : ℕ} {β : Type*} [DecidableEq β]
    (assign : Fin n → β) (b : β) : ℕ :=
  (assignmentFiber assign b).card

/-- Assignment-fiber counts sum to the total number of indices. -/
theorem sum_assignmentCount {n : ℕ} {β : Type*}
    [Fintype β] [DecidableEq β] (assign : Fin n → β) :
    ∑ b : β, assignmentCount assign b = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset β)) (f := assign)
    (fun _ _ ↦ Finset.mem_univ _)
  simpa only [Finset.card_univ, Fintype.card_fin,
    assignmentCount, assignmentFiber] using h.symm

/-- Increasing enumeration of the indices in one assignment fiber. -/
noncomputable def assignmentEmbedding {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) (b : β) :
    Fin (assignmentCount assign b) ↪o Fin n :=
  (assignmentFiber assign b).orderEmbOfFin rfl

lemma assignmentEmbedding_mem_fiber {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) (b : β)
    (i : Fin (assignmentCount assign b)) :
    assign (assignmentEmbedding assign b i) = b := by
  have hmem := Finset.orderEmbOfFin_mem
    (assignmentFiber assign b) rfl i
  exact (Finset.mem_filter.mp hmem).2

lemma assignmentEmbedding_strictMono {n : ℕ} {β : Type*}
    [DecidableEq β] (assign : Fin n → β) (b : β) :
    StrictMono (assignmentEmbedding assign b) :=
  (assignmentEmbedding assign b).strictMono

/-- Canonical bin count for an ordered node family. -/
noncomputable def arcsineNodeBinCount {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) : ℕ :=
  assignmentCount
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal) b

theorem sum_arcsineNodeBinCount {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) :
    ∑ b : Bool × Fin (K + 1),
      arcsineNodeBinCount q hterminal nodes b = n :=
  sum_assignmentCount
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal)

/-- Strict increasing global-index embedding for one canonical node bin. -/
noncomputable def arcsineNodeBinEmbedding {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) :
    Fin (arcsineNodeBinCount q hterminal nodes b) ↪o Fin n :=
  assignmentEmbedding
    (fun i ↦ arcsineBinAssignment d K q (nodes.point i) hterminal) b

lemma arcsineNodeBinEmbedding_strictMono {d K n : ℕ} (q : ℝ)
    (hterminal : 1 ≤ q ^ K * cubicChebyshevFloor d)
    (nodes : OrderedNodes n) (b : Bool × Fin (K + 1)) :
    StrictMono (arcsineNodeBinEmbedding q hterminal nodes b) :=
  (arcsineNodeBinEmbedding q hterminal nodes b).strictMono

end

end ClassicalBound
end Randy1153
