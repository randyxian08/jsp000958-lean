import Randy1153.ClassicalBound.EnergyEmbedding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Angle-bin geometry for the clipped arcsine scale

The constant-sensitive part of a geometric bin construction is most
transparent in the angle coordinate x = cos theta.  On the half-angle,
the square-root scale is sin theta, and a bin whose endpoint scales differ
by at most a factor q satisfies

    (x_left - x_right) / scale_left ≤ q (theta_right - theta_left).

The angle widths telescope, giving q*pi/2 on one half and q*pi after
reflection.  This file proves that exact kernel and the scale-oscillation
property for any finite endpoint sequence satisfying the geometric ratio.

Constructing a particular geometric endpoint sequence and bounding its
cardinality by a logarithm are deliberately separate from these analytic
facts.
-/

namespace Randy1153
namespace ClassicalBound

noncomputable section

/-- The clipped scale is even. -/
lemma clippedArcsineScale_neg (d : ℕ) (x : ℝ) :
    clippedArcsineScale d (-x) = clippedArcsineScale d x := by
  simp [clippedArcsineScale]

/-- In the angle coordinate the unclipped square-root scale is exactly
the sine. -/
lemma clippedArcsineScale_cos {d : ℕ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθpi : θ ≤ Real.pi) :
    clippedArcsineScale d (Real.cos θ) =
      max (Real.sin θ) (cubicChebyshevFloor d) := by
  rw [clippedArcsineScale, ← Real.sin_eq_sqrt_one_sub_cos_sq hθ0 hθpi]

/-- The clipped scale along the cosine coordinate is monotone on the
right half-angle interval. -/
lemma clippedArcsineScale_cos_mono {d : ℕ} {u v : ℝ}
    (hu : 0 ≤ u) (hv : v ≤ Real.pi / 2) (huv : u ≤ v) :
    clippedArcsineScale d (Real.cos u) ≤
      clippedArcsineScale d (Real.cos v) := by
  rw [clippedArcsineScale_cos hu (huv.trans hv |>.trans (by linarith [Real.pi_pos])),
    clippedArcsineScale_cos (hu.trans huv) (hv.trans (by linarith [Real.pi_pos]))]
  exact max_le_max
    (Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hv huv)
    le_rfl

/-- Sharp elementary angle estimate for one cosine interval. -/
lemma cos_sub_cos_le_sin_mul_sub {u v : ℝ}
    (hu : 0 ≤ u) (hv : v ≤ Real.pi / 2) (huv : u ≤ v) :
    Real.cos u - Real.cos v ≤ Real.sin v * (v - u) := by
  have hmid_le : Real.sin ((u + v) / 2) ≤ Real.sin v := by
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hv (by linarith)
  have hdelta0 : 0 ≤ (v - u) / 2 := by linarith
  have hsindelta0 : 0 ≤ Real.sin ((v - u) / 2) := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi hdelta0
      (by linarith [Real.pi_pos])
  have hsinv0 : 0 ≤ Real.sin v := by
    exact Real.sin_nonneg_of_nonneg_of_le_pi
      (hu.trans huv) (hv.trans (by linarith [Real.pi_pos]))
  rw [Real.cos_sub_cos]
  have hrewrite :
      -2 * Real.sin ((u + v) / 2) * Real.sin ((u - v) / 2) =
        2 * Real.sin ((u + v) / 2) * Real.sin ((v - u) / 2) := by
    rw [show (u - v) / 2 = -((v - u) / 2) by ring, Real.sin_neg]
    ring
  rw [hrewrite]
  calc
    2 * Real.sin ((u + v) / 2) * Real.sin ((v - u) / 2) ≤
        2 * Real.sin v * Real.sin ((v - u) / 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmid_le (by norm_num)) hsindelta0
    _ ≤ 2 * Real.sin v * ((v - u) / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.sin_le hdelta0)
        (mul_nonneg (by norm_num) hsinv0)
    _ = Real.sin v * (v - u) := by ring

/-- One clipped-scale angle bin has length-over-lower-scale bounded by q
times its angle width. -/
theorem cosBin_length_div_scale_le {d : ℕ} {q u v : ℝ}
    (hu : 0 ≤ u) (hv : v ≤ Real.pi / 2) (huv : u ≤ v)
    (hratio : clippedArcsineScale d (Real.cos v) ≤
      q * clippedArcsineScale d (Real.cos u)) :
    (Real.cos u - Real.cos v) /
        clippedArcsineScale d (Real.cos u) ≤ q * (v - u) := by
  have hscale0 : 0 < clippedArcsineScale d (Real.cos u) :=
    clippedArcsineScale_pos d _
  have hsin_le_scale :
      Real.sin v ≤ clippedArcsineScale d (Real.cos v) := by
    rw [clippedArcsineScale_cos (hu.trans huv)
      (hv.trans (by linarith [Real.pi_pos]))]
    exact le_max_left _ _
  apply (div_le_iff₀ hscale0).2
  calc
    Real.cos u - Real.cos v ≤ Real.sin v * (v - u) :=
      cos_sub_cos_le_sin_mul_sub hu hv huv
    _ ≤ (q * clippedArcsineScale d (Real.cos u)) * (v - u) := by
      exact mul_le_mul_of_nonneg_right
        (hsin_le_scale.trans hratio) (sub_nonneg.mpr huv)
    _ = q * (v - u) * clippedArcsineScale d (Real.cos u) := by ring

/-- Left endpoint index of one bin in a sequence of K+1 angle endpoints. -/
def angleBinLeft {K : ℕ} (i : Fin K) : Fin (K + 1) :=
  ⟨i.val, by omega⟩

/-- Right endpoint index of one bin in a sequence of K+1 angle endpoints. -/
def angleBinRight {K : ℕ} (i : Fin K) : Fin (K + 1) :=
  ⟨i.val + 1, by omega⟩

@[simp]
lemma angleBinLeft_val {K : ℕ} (i : Fin K) :
    (angleBinLeft i).val = i.val :=
  rfl

@[simp]
lemma angleBinRight_val {K : ℕ} (i : Fin K) :
    (angleBinRight i).val = i.val + 1 :=
  rfl

lemma angleBinLeft_lt_right {K : ℕ} (i : Fin K) :
    angleBinLeft i < angleBinRight i := by
  simp [Fin.lt_def]

/-- Angle width of one bin. -/
def angleBinWidth {K : ℕ} (angle : Fin (K + 1) → ℝ)
    (i : Fin K) : ℝ :=
  angle (angleBinRight i) - angle (angleBinLeft i)

/-- Length of the corresponding interval in the nonnegative x-half. -/
def cosineBinLength {K : ℕ} (angle : Fin (K + 1) → ℝ)
    (i : Fin K) : ℝ :=
  Real.cos (angle (angleBinLeft i)) -
    Real.cos (angle (angleBinRight i))

/-- Lower clipped scale of the corresponding cosine bin. -/
def cosineBinLowerScale (d : ℕ) {K : ℕ}
    (angle : Fin (K + 1) → ℝ) (i : Fin K) : ℝ :=
  clippedArcsineScale d (Real.cos (angle (angleBinLeft i)))

/-- A finite angle partition of the nonnegative half interval, together
with the endpoint scale-ratio condition required by geometric bins. -/
structure HalfArcsinePartition (d K : ℕ) (q : ℝ) where
  positive_bins : 0 < K
  angle : Fin (K + 1) → ℝ
  monotone_angle : Monotone angle
  angle_zero : angle ⟨0, by omega⟩ = 0
  angle_last : angle ⟨K, by omega⟩ = Real.pi / 2
  scale_ratio : ∀ i : Fin K,
    clippedArcsineScale d (Real.cos (angle (angleBinRight i))) ≤
      q * clippedArcsineScale d (Real.cos (angle (angleBinLeft i)))

namespace HalfArcsinePartition

lemma angle_nonneg {d K : ℕ} {q : ℝ}
    (P : HalfArcsinePartition d K q) (i : Fin (K + 1)) :
    0 ≤ P.angle i := by
  rw [← P.angle_zero]
  exact P.monotone_angle (by simp [Fin.le_def])

lemma angle_le_pi_div_two {d K : ℕ} {q : ℝ}
    (P : HalfArcsinePartition d K q) (i : Fin (K + 1)) :
    P.angle i ≤ Real.pi / 2 := by
  rw [← P.angle_last]
  apply P.monotone_angle
  simp only [Fin.le_def]
  omega

lemma angle_left_le_right {d K : ℕ} {q : ℝ}
    (P : HalfArcsinePartition d K q) (i : Fin K) :
    P.angle (angleBinLeft i) ≤ P.angle (angleBinRight i) :=
  P.monotone_angle (angleBinLeft_lt_right i).le

/-- Every angle inside one bin has clipped scale between the left endpoint
scale and q times that endpoint scale. -/
theorem scale_oscillation {d K : ℕ} {q θ : ℝ}
    (P : HalfArcsinePartition d K q) (i : Fin K)
    (hθ : θ ∈ Set.Icc
      (P.angle (angleBinLeft i)) (P.angle (angleBinRight i))) :
    cosineBinLowerScale d P.angle i ≤ clippedArcsineScale d (Real.cos θ) ∧
      clippedArcsineScale d (Real.cos θ) ≤
        q * cosineBinLowerScale d P.angle i := by
  have hleft0 := P.angle_nonneg (angleBinLeft i)
  have hrightpi := P.angle_le_pi_div_two (angleBinRight i)
  constructor
  · exact clippedArcsineScale_cos_mono hleft0
      (hθ.2.trans hrightpi) hθ.1
  · exact (clippedArcsineScale_cos_mono
      (hleft0.trans hθ.1) hrightpi hθ.2).trans (P.scale_ratio i)

/-- The angle widths telescope exactly across the half partition. -/
lemma sum_angleBinWidth
    {d K : ℕ} {q : ℝ} (P : HalfArcsinePartition d K q) :
    (∑ i : Fin K, angleBinWidth P.angle i) = Real.pi / 2 := by
  let f : ℕ → ℝ := fun i ↦
    P.angle ⟨min i K, by omega⟩
  rw [Finset.sum_fin_eq_sum_range]
  have htel := Finset.sum_range_sub f K
  have hfK : f K = Real.pi / 2 := by
    simpa [f] using P.angle_last
  have hf0 : f 0 = 0 := by
    simpa [f] using P.angle_zero
  rw [hfK, hf0] at htel
  simp only [sub_zero] at htel
  rw [← htel]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < K := Finset.mem_range.mp hi
  rw [dif_pos hi']
  simp only [angleBinWidth, angleBinRight, angleBinLeft, f]
  congr 2
  · apply Fin.ext
    exact (Nat.min_eq_left (by omega)).symm
  · apply Fin.ext
    exact (Nat.min_eq_left (by omega)).symm

/-- Exact q*pi/2 length-over-scale budget on the nonnegative half. -/
theorem sum_cosineBinLength_div_lowerScale_le
    {d K : ℕ} {q : ℝ} (P : HalfArcsinePartition d K q) :
    (∑ i : Fin K,
      cosineBinLength P.angle i / cosineBinLowerScale d P.angle i) ≤
        q * (Real.pi / 2) := by
  calc
    (∑ i : Fin K,
        cosineBinLength P.angle i / cosineBinLowerScale d P.angle i) ≤
        ∑ i : Fin K, q * angleBinWidth P.angle i := by
      apply Finset.sum_le_sum
      intro i _
      exact cosBin_length_div_scale_le
        (P.angle_nonneg (angleBinLeft i))
        (P.angle_le_pi_div_two (angleBinRight i))
        (P.angle_left_le_right i)
        (P.scale_ratio i)
    _ = q * (Real.pi / 2) := by
      rw [← Finset.mul_sum, P.sum_angleBinWidth]

/-- After reflection, the two half-partitions have total budget at most
q*pi. -/
theorem two_mul_sum_cosineBinLength_div_lowerScale_le
    {d K : ℕ} {q : ℝ} (P : HalfArcsinePartition d K q) :
    2 * (∑ i : Fin K,
      cosineBinLength P.angle i / cosineBinLowerScale d P.angle i) ≤
        q * Real.pi := by
  calc
    2 * (∑ i : Fin K,
        cosineBinLength P.angle i / cosineBinLowerScale d P.angle i) ≤
        2 * (q * (Real.pi / 2)) := by
      exact mul_le_mul_of_nonneg_left
        P.sum_cosineBinLength_div_lowerScale_le (by norm_num)
    _ = q * Real.pi := by ring

end HalfArcsinePartition

end

end ClassicalBound
end Randy1153
