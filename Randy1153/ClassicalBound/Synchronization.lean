import Randy1153.ClassicalBound.Clock
import Randy1153.CompactMax
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Fixed-point synchronization for the classical clock argument

The adjacent derivative estimates in `Clock` live at different nodes.  They
cannot be summed as pointwise lower bounds for the Lebesgue function.  This
module instead fixes one point `t` and transports the weighted cardinal
values

`W k = |ℓ_k(t)| * |t - x_k|`

along the ordered chain.  Every identity below keeps the evaluation point
fixed.  The remaining sharp step must therefore be a genuine estimate on one
of these synchronized chains, rather than a sum of drifting maxima.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- Cardinal value with its barycentric distance denominator restored. -/
def synchronizedWeight {n : ℕ} (nodes : OrderedNodes n) (t : ℝ)
    (k : Fin n) : ℝ :=
  |lagrangeFundamental nodes.toNodeFamily k t| * |t - nodes.point k|

/-- Midpoint of an adjacent nodal gap. -/
def clockMidpoint {n : ℕ} (nodes : OrderedNodes n) (g : Fin (n - 1)) : ℝ :=
  (nodes.point (clockLeftIndex g) + nodes.point (clockRightIndex g)) / 2

/-- The existence of a gap supplies canonical first and last node indices. -/
def clockFirstIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨0, by have := g.isLt; omega⟩

def clockLastIndex {n : ℕ} (g : Fin (n - 1)) : Fin n :=
  ⟨n - 1, by have := g.isLt; omega⟩

lemma clockMidpoint_between {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    nodes.point (clockLeftIndex g) < clockMidpoint nodes g ∧
      clockMidpoint nodes g < nodes.point (clockRightIndex g) := by
  have hgap := clockGap_pos nodes g
  unfold clockMidpoint clockGap at *
  constructor <;> linarith

lemma clockMidpoint_mem_Icc {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    clockMidpoint nodes g ∈ Set.Icc (-1 : ℝ) 1 := by
  have hbetween := clockMidpoint_between nodes g
  exact ⟨(nodes.neg_one_le _).trans hbetween.1.le,
    hbetween.2.le.trans (nodes.le_one _)⟩

/-- A gap midpoint is different from every node, not only its two
endpoints. -/
lemma clockMidpoint_ne_node {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) (k : Fin n) :
    clockMidpoint nodes g ≠ nodes.point k := by
  have hbetween := clockMidpoint_between nodes g
  by_cases hk : k ≤ clockLeftIndex g
  · exact ne_of_gt ((nodes.strictMono.monotone hk).trans_lt hbetween.1)
  · have hk' : clockRightIndex g ≤ k := by
      have hkval : g.val < k.val := by
        simpa only [clockLeftIndex_val] using (Fin.not_le.mp hk)
      apply Fin.le_iff_val_le_val.mpr
      simp only [clockRightIndex_val]
      omega
    exact ne_of_lt (hbetween.2.trans_le (nodes.strictMono.monotone hk'))

lemma abs_clockMidpoint_sub_left {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    |clockMidpoint nodes g - nodes.point (clockLeftIndex g)| =
      clockGap nodes g / 2 := by
  rw [abs_of_pos (sub_pos.mpr (clockMidpoint_between nodes g).1)]
  unfold clockMidpoint clockGap
  ring

lemma abs_clockMidpoint_sub_right {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    |clockMidpoint nodes g - nodes.point (clockRightIndex g)| =
      clockGap nodes g / 2 := by
  rw [abs_of_neg (sub_neg.mpr (clockMidpoint_between nodes g).2)]
  unfold clockMidpoint clockGap
  ring

lemma synchronizedWeight_pos {n : ℕ} (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k) (k : Fin n) :
    0 < synchronizedWeight nodes t k := by
  apply mul_pos
  · rw [abs_pos]
    rw [lagrangeFundamental_eq_nodalPolynomial_mul nodes.toNodeFamily k (ht k)]
    exact mul_ne_zero
      (eval_nodalPolynomial_ne_zero_of_off_nodes nodes.toNodeFamily ht)
      (mul_ne_zero
        (inv_ne_zero
          (derivative_nodalPolynomial_eval_node_ne_zero nodes.toNodeFamily k))
        (inv_ne_zero (sub_ne_zero.mpr (ht k))))
  · exact abs_pos.mpr (sub_ne_zero.mpr (ht k))

/-- Multiplicative transport from the left endpoint of an adjacent gap to
its right endpoint. -/
def clockForwardFactor {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : ℝ :=
  |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
      (nodes.point (clockLeftIndex g))| * clockGap nodes g

/-- Multiplicative transport from the right endpoint of an adjacent gap to
its left endpoint. -/
def clockBackwardFactor {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) : ℝ :=
  |(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
      (nodes.point (clockRightIndex g))| * clockGap nodes g

lemma clockForwardFactor_mul_clockBackwardFactor {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    clockForwardFactor nodes g * clockBackwardFactor nodes g = 1 := by
  have habs :
      |nodes.point (clockRightIndex g) - nodes.point (clockLeftIndex g)| =
        clockGap nodes g := by
    change |clockGap nodes g| = clockGap nodes g
    exact abs_of_pos (clockGap_pos nodes g)
  have hrecip :=
    abs_derivative_lagrangeBasis_mul_swap nodes.toNodeFamily
      (clockLeftIndex_lt_rightIndex g).ne'
  rw [habs] at hrecip
  have hgap : clockGap nodes g ≠ 0 := (clockGap_pos nodes g).ne'
  unfold clockForwardFactor clockBackwardFactor
  rw [mul_mul_mul_comm,
    show
      |(lagrangeBasis nodes.toNodeFamily (clockRightIndex g)).derivative.eval
          (nodes.point (clockLeftIndex g))| *
        |(lagrangeBasis nodes.toNodeFamily (clockLeftIndex g)).derivative.eval
          (nodes.point (clockRightIndex g))| =
        (clockGap nodes g ^ 2)⁻¹ by simpa only [mul_comm] using hrecip]
  field_simp

lemma clockForwardFactor_pos {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    0 < clockForwardFactor nodes g := by
  have hprod := clockForwardFactor_mul_clockBackwardFactor nodes g
  have hfnonneg : 0 ≤ clockForwardFactor nodes g := by
    exact mul_nonneg (abs_nonneg _) (clockGap_pos nodes g).le
  have hbnonneg : 0 ≤ clockBackwardFactor nodes g := by
    exact mul_nonneg (abs_nonneg _) (clockGap_pos nodes g).le
  nlinarith

lemma clockBackwardFactor_pos {n : ℕ} (nodes : OrderedNodes n)
    (g : Fin (n - 1)) :
    0 < clockBackwardFactor nodes g := by
  have hprod := clockForwardFactor_mul_clockBackwardFactor nodes g
  have hfnonneg : 0 ≤ clockForwardFactor nodes g := by
    exact mul_nonneg (abs_nonneg _) (clockGap_pos nodes g).le
  have hbnonneg : 0 ≤ clockBackwardFactor nodes g := by
    exact mul_nonneg (abs_nonneg _) (clockGap_pos nodes g).le
  nlinarith

/-- The forward transport factor is exactly the ratio of adjacent absolute
nodal derivatives. -/
lemma clockForwardFactor_eq_nodalDerivative_ratio {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    clockForwardFactor nodes g =
      |(nodalPolynomial nodes.toNodeFamily).derivative.eval
          (nodes.point (clockLeftIndex g))| *
        |(nodalPolynomial nodes.toNodeFamily).derivative.eval
          (nodes.point (clockRightIndex g))|⁻¹ := by
  rw [clockForwardFactor,
    derivative_lagrangeBasis_eval_of_ne nodes.toNodeFamily
      (clockLeftIndex_lt_rightIndex g).ne]
  simp only [abs_mul, abs_inv]
  have hgap : clockGap nodes g ≠ 0 := (clockGap_pos nodes g).ne'
  have habs :
      |nodes.point (clockLeftIndex g) - nodes.point (clockRightIndex g)| =
        clockGap nodes g := by
    rw [abs_sub_comm]
    change |clockGap nodes g| = clockGap nodes g
    exact abs_of_pos (clockGap_pos nodes g)
  rw [habs]
  field_simp

/-- The backward factor is the reciprocal adjacent nodal-derivative ratio. -/
lemma clockBackwardFactor_eq_nodalDerivative_ratio {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    clockBackwardFactor nodes g =
      |(nodalPolynomial nodes.toNodeFamily).derivative.eval
          (nodes.point (clockRightIndex g))| *
        |(nodalPolynomial nodes.toNodeFamily).derivative.eval
          (nodes.point (clockLeftIndex g))|⁻¹ := by
  rw [clockBackwardFactor,
    derivative_lagrangeBasis_eval_of_ne nodes.toNodeFamily
      (clockLeftIndex_lt_rightIndex g).ne']
  simp only [abs_mul, abs_inv]
  have hgap : clockGap nodes g ≠ 0 := (clockGap_pos nodes g).ne'
  have habs :
      |nodes.point (clockRightIndex g) - nodes.point (clockLeftIndex g)| =
        clockGap nodes g := by
    change |clockGap nodes g| = clockGap nodes g
    exact abs_of_pos (clockGap_pos nodes g)
  rw [habs]
  field_simp

/-- At an off-node point, synchronized weight is the common nodal-polynomial
value divided by the absolute nodal derivative.  Thus all dependence on `t`
is a single common scalar. -/
lemma synchronizedWeight_eq_nodalPolynomial_mul_derivative_inv {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) (k : Fin n) :
    synchronizedWeight nodes t k =
      |(nodalPolynomial nodes.toNodeFamily).eval t| *
        |(nodalPolynomial nodes.toNodeFamily).derivative.eval
          (nodes.point k)|⁻¹ := by
  rw [synchronizedWeight,
    abs_lagrangeFundamental_eq_nodalPolynomial nodes.toNodeFamily k (ht k)]
  have hdist : |t - nodes.point k| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (ht k))
  rw [mul_inv]
  field_simp

/-- Exact one-step propagation to the right, at one fixed off-node point. -/
lemma synchronizedWeight_right_eq_left_mul_forward {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k) (g : Fin (n - 1)) :
    synchronizedWeight nodes t (clockRightIndex g) =
      synchronizedWeight nodes t (clockLeftIndex g) *
        clockForwardFactor nodes g := by
  have h := abs_lagrangeFundamental_mul_distance_eq_pair_transport
    nodes.toNodeFamily (clockLeftIndex_lt_rightIndex g).ne ht
  have habs :
      |nodes.point (clockLeftIndex g) - nodes.point (clockRightIndex g)| =
        clockGap nodes g := by
    rw [abs_sub_comm]
    change |clockGap nodes g| = clockGap nodes g
    exact abs_of_pos (clockGap_pos nodes g)
  unfold synchronizedWeight clockForwardFactor
  rw [h, habs]
  ring

/-- Exact one-step propagation to the left, at the same fixed point. -/
lemma synchronizedWeight_left_eq_right_mul_backward {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ k : Fin n, t ≠ nodes.point k) (g : Fin (n - 1)) :
    synchronizedWeight nodes t (clockLeftIndex g) =
      synchronizedWeight nodes t (clockRightIndex g) *
        clockBackwardFactor nodes g := by
  have h := abs_lagrangeFundamental_mul_distance_eq_pair_transport
    nodes.toNodeFamily (clockLeftIndex_lt_rightIndex g).ne' ht
  have habs :
      |nodes.point (clockRightIndex g) - nodes.point (clockLeftIndex g)| =
        clockGap nodes g := by
    change |clockGap nodes g| = clockGap nodes g
    exact abs_of_pos (clockGap_pos nodes g)
  unfold synchronizedWeight clockBackwardFactor
  rw [h, habs]
  ring

/-- A purely finite multiplicative-chain identity.  It is stated on natural
indices so later clock arguments can select arbitrary subchains without
dependent-index bookkeeping. -/
lemma chain_value_eq_base_mul_prod_Ico (v factor : ℕ → ℝ)
    {j k : ℕ} (hjk : j ≤ k)
    (hstep : ∀ i, j ≤ i → i < k → v (i + 1) = v i * factor i) :
    v k = v j * ∏ i ∈ Finset.Ico j k, factor i := by
  let w : ℕ → ℝ := fun r ↦ v (j + r)
  let a : ℕ → ℝ := fun r ↦ factor (j + r)
  have hzero : ∀ m : ℕ,
      (∀ i, i < m → w (i + 1) = w i * a i) →
        w m = w 0 * ∏ i ∈ Finset.range m, a i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        intro hs
        rw [hs m (by omega), ih (fun i hi ↦ hs i (by omega)),
          Finset.prod_range_succ]
        ring
  have hm := hzero (k - j) (fun i hi ↦ by
    simpa only [w, a, Nat.add_assoc] using
      hstep (j + i) (by omega) (by omega))
  rw [Finset.prod_Ico_eq_prod_range]
  simpa only [w, a, Nat.add_sub_of_le hjk, add_zero] using hm

/-- Reverse version of `chain_value_eq_base_mul_prod_Ico`. -/
lemma chain_value_eq_top_mul_prod_Ico (v factor : ℕ → ℝ)
    {j k : ℕ} (hjk : j ≤ k)
    (hstep : ∀ i, j ≤ i → i < k → v i = v (i + 1) * factor i) :
    v j = v k * ∏ i ∈ Finset.Ico j k, factor i := by
  induction k with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      simp
  | succ k ih =>
      by_cases hj : j ≤ k
      · rw [ih hj (fun i hji hik ↦ hstep i hji (by omega)),
          hstep k hj (by omega), Finset.prod_Ico_succ_top hj]
        ring
      · have hjEq : j = k + 1 := by omega
        subst j
        simp

/-- Natural-index extension of the adjacent forward factor.  Values outside
the actual gap range are set to one and never enter a valid chain theorem. -/
def clockForwardFactorNat {n : ℕ} (nodes : OrderedNodes n) (i : ℕ) : ℝ :=
  if hi : i < n - 1 then clockForwardFactor nodes ⟨i, hi⟩ else 1

/-- Natural-index extension of the adjacent backward factor. -/
def clockBackwardFactorNat {n : ℕ} (nodes : OrderedNodes n) (i : ℕ) : ℝ :=
  if hi : i < n - 1 then clockBackwardFactor nodes ⟨i, hi⟩ else 1

/-- Natural-index extension of the synchronized weight.  Values outside the
node range are set to zero and never enter a valid chain theorem. -/
def synchronizedWeightNat {n : ℕ} (nodes : OrderedNodes n) (t : ℝ)
    (i : ℕ) : ℝ :=
  if hi : i < n then synchronizedWeight nodes t ⟨i, hi⟩ else 0

@[simp]
lemma synchronizedWeightNat_of_lt {n : ℕ} (nodes : OrderedNodes n) (t : ℝ)
    {i : ℕ} (hi : i < n) :
    synchronizedWeightNat nodes t i = synchronizedWeight nodes t ⟨i, hi⟩ := by
  simp [synchronizedWeightNat, hi]

@[simp]
lemma clockForwardFactorNat_of_lt {n : ℕ} (nodes : OrderedNodes n)
    {i : ℕ} (hi : i < n - 1) :
    clockForwardFactorNat nodes i = clockForwardFactor nodes ⟨i, hi⟩ := by
  simp [clockForwardFactorNat, hi]

@[simp]
lemma clockBackwardFactorNat_of_lt {n : ℕ} (nodes : OrderedNodes n)
    {i : ℕ} (hi : i < n - 1) :
    clockBackwardFactorNat nodes i = clockBackwardFactor nodes ⟨i, hi⟩ := by
  simp [clockBackwardFactorNat, hi]

/-- Exact propagation across any ordered subchain, with every cardinal value
evaluated at the same point `t`. -/
lemma synchronizedWeight_eq_mul_prod_forward {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) {j k : Fin n} (hjk : j ≤ k) :
    synchronizedWeight nodes t k =
      synchronizedWeight nodes t j *
        ∏ i ∈ Finset.Ico j.val k.val, clockForwardFactorNat nodes i := by
  let v := synchronizedWeightNat nodes t
  let factor := clockForwardFactorNat nodes
  have hchain := chain_value_eq_base_mul_prod_Ico v factor
    (show j.val ≤ k.val from hjk) (fun i hji hik ↦ by
      have hiGap : i < n - 1 := by omega
      have hiNode : i < n := by omega
      have hiSuccNode : i + 1 < n := by omega
      rw [show v (i + 1) = synchronizedWeight nodes t ⟨i + 1, hiSuccNode⟩ by
        simp [v, hiSuccNode],
        show v i = synchronizedWeight nodes t ⟨i, hiNode⟩ by
          simp [v, hiNode],
        show factor i = clockForwardFactor nodes ⟨i, hiGap⟩ by
          simp [factor, hiGap]]
      simpa only [clockRightIndex, clockLeftIndex] using
        synchronizedWeight_right_eq_left_mul_forward nodes ht ⟨i, hiGap⟩)
  simpa only [v, synchronizedWeightNat_of_lt nodes t j.isLt,
    synchronizedWeightNat_of_lt nodes t k.isLt, factor] using hchain

/-- Exact reverse propagation across any ordered subchain, still at the one
fixed point `t`. -/
lemma synchronizedWeight_eq_mul_prod_backward {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) {j k : Fin n} (hjk : j ≤ k) :
    synchronizedWeight nodes t j =
      synchronizedWeight nodes t k *
        ∏ i ∈ Finset.Ico j.val k.val, clockBackwardFactorNat nodes i := by
  let v := synchronizedWeightNat nodes t
  let factor := clockBackwardFactorNat nodes
  have hchain := chain_value_eq_top_mul_prod_Ico v factor
    (show j.val ≤ k.val from hjk) (fun i hji hik ↦ by
      have hiGap : i < n - 1 := by omega
      have hiNode : i < n := by omega
      have hiSuccNode : i + 1 < n := by omega
      rw [show v (i + 1) = synchronizedWeight nodes t ⟨i + 1, hiSuccNode⟩ by
        simp [v, hiSuccNode],
        show v i = synchronizedWeight nodes t ⟨i, hiNode⟩ by
          simp [v, hiNode],
        show factor i = clockBackwardFactor nodes ⟨i, hiGap⟩ by
          simp [factor, hiGap]]
      simpa only [clockRightIndex, clockLeftIndex] using
        synchronizedWeight_left_eq_right_mul_backward nodes ht ⟨i, hiGap⟩)
  simpa only [v, synchronizedWeightNat_of_lt nodes t j.isLt,
    synchronizedWeightNat_of_lt nodes t k.isLt, factor] using hchain

/-- If no forward factor on a subchain is smaller than `q⁻¹`, then the
fixed-point weight loses at most that power along the whole subchain. -/
lemma synchronizedWeight_mul_inv_pow_le {n : ℕ}
    (nodes : OrderedNodes n) {t q : ℝ} (hq : 0 < q)
    (ht : ∀ r : Fin n, t ≠ nodes.point r) {j k : Fin n} (hjk : j ≤ k)
    (hfactor : ∀ i ∈ Finset.Ico j.val k.val,
      q⁻¹ ≤ clockForwardFactorNat nodes i) :
    synchronizedWeight nodes t j * q⁻¹ ^ (k.val - j.val) ≤
      synchronizedWeight nodes t k := by
  rw [synchronizedWeight_eq_mul_prod_forward nodes ht hjk]
  apply mul_le_mul_of_nonneg_left _
    (synchronizedWeight_pos nodes ht j).le
  calc
    q⁻¹ ^ (k.val - j.val) =
        ∏ _i ∈ Finset.Ico j.val k.val, q⁻¹ := by
      rw [Finset.prod_const, Nat.card_Ico]
    _ ≤ ∏ i ∈ Finset.Ico j.val k.val,
        clockForwardFactorNat nodes i := by
      exact Finset.prod_le_prod
        (fun _ _ ↦ inv_nonneg.mpr hq.le) hfactor

/-- Dual upper propagation when no forward factor exceeds `q`. -/
lemma synchronizedWeight_le_mul_pow {n : ℕ}
    (nodes : OrderedNodes n) {t q : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) {j k : Fin n} (hjk : j ≤ k)
    (hfactor : ∀ i ∈ Finset.Ico j.val k.val,
      clockForwardFactorNat nodes i ≤ q) :
    synchronizedWeight nodes t k ≤
      synchronizedWeight nodes t j * q ^ (k.val - j.val) := by
  rw [synchronizedWeight_eq_mul_prod_forward nodes ht hjk]
  apply mul_le_mul_of_nonneg_left _
    (synchronizedWeight_pos nodes ht j).le
  calc
    (∏ i ∈ Finset.Ico j.val k.val,
        clockForwardFactorNat nodes i) ≤
        ∏ _i ∈ Finset.Ico j.val k.val, q := by
      exact Finset.prod_le_prod
        (fun i hi ↦ by
          have hiGap : i < n - 1 := by
            simp only [Finset.mem_Ico] at hi
            omega
          rw [clockForwardFactorNat_of_lt nodes hiGap]
          exact (clockForwardFactor_pos nodes ⟨i, hiGap⟩).le)
        hfactor
    _ = q ^ (k.val - j.val) := by
      rw [Finset.prod_const, Nat.card_Ico]

/-- Quantitative fixed-point chain dichotomy.  Either a concrete adjacent
transport factor leaves the balanced range `[q⁻¹,q]`, or the endpoint
weights at the same point are trapped between the corresponding powers. -/
lemma synchronized_chain_defect_or_control {n : ℕ}
    (nodes : OrderedNodes n) {t q : ℝ} (hq : 0 < q)
    (ht : ∀ r : Fin n, t ≠ nodes.point r) {j k : Fin n} (hjk : j ≤ k) :
    (∃ i ∈ Finset.Ico j.val k.val,
        clockForwardFactorNat nodes i < q⁻¹ ∨
          q < clockForwardFactorNat nodes i) ∨
      (synchronizedWeight nodes t j * q⁻¹ ^ (k.val - j.val) ≤
          synchronizedWeight nodes t k ∧
        synchronizedWeight nodes t k ≤
          synchronizedWeight nodes t j * q ^ (k.val - j.val)) := by
  by_cases hdef : ∃ i ∈ Finset.Ico j.val k.val,
      clockForwardFactorNat nodes i < q⁻¹ ∨
        q < clockForwardFactorNat nodes i
  · exact Or.inl hdef
  · right
    have hlower : ∀ i ∈ Finset.Ico j.val k.val,
        q⁻¹ ≤ clockForwardFactorNat nodes i := by
      intro i hi
      exact not_lt.mp (fun hlt ↦ hdef ⟨i, hi, Or.inl hlt⟩)
    have hupper : ∀ i ∈ Finset.Ico j.val k.val,
        clockForwardFactorNat nodes i ≤ q := by
      intro i hi
      exact not_lt.mp (fun hlt ↦ hdef ⟨i, hi, Or.inr hlt⟩)
    exact ⟨synchronizedWeight_mul_inv_pow_le nodes hq ht hjk hlower,
      synchronizedWeight_le_mul_pow nodes ht hjk hupper⟩

/-- Restoring the distance denominator exactly recovers the cardinal value. -/
lemma synchronizedWeight_mul_distance_inv {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) (k : Fin n) :
    synchronizedWeight nodes t k * |t - nodes.point k|⁻¹ =
      |lagrangeFundamental nodes.toNodeFamily k t| := by
  unfold synchronizedWeight
  have hdist : |t - nodes.point k| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr (ht k))
  field_simp

/-- Every subset of synchronized rows is bounded by the Lebesgue function at
the same point.  No interval diameter loss occurs here. -/
lemma sum_synchronizedWeight_mul_distance_inv_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) (s : Finset (Fin n)) :
    (∑ k ∈ s, synchronizedWeight nodes t k * |t - nodes.point k|⁻¹) ≤
      lebesgueFunction nodes.toNodeFamily t := by
  calc
    (∑ k ∈ s, synchronizedWeight nodes t k * |t - nodes.point k|⁻¹) =
        ∑ k ∈ s, |lagrangeFundamental nodes.toNodeFamily k t| := by
      apply Finset.sum_congr rfl
      intro k _
      exact synchronizedWeight_mul_distance_inv nodes ht k
    _ ≤ ∑ k : Fin n, |lagrangeFundamental nodes.toNodeFamily k t| := by
      exact Finset.sum_le_univ_sum_of_nonneg (fun k ↦
        abs_nonneg (lagrangeFundamental nodes.toNodeFamily k t))
    _ = lebesgueFunction nodes.toNodeFamily t := rfl

/-- Exact one-sided synchronized row obtained by propagating from the left
anchor `j`.  This is a sharp-constant interface: the true distance weights
are retained term by term. -/
lemma forward_synchronized_row_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) (j k : Fin n) :
    synchronizedWeight nodes t j *
        ∑ r ∈ Finset.Icc j k,
          (∏ i ∈ Finset.Ico j.val r.val, clockForwardFactorNat nodes i) *
            |t - nodes.point r|⁻¹ ≤
      lebesgueFunction nodes.toNodeFamily t := by
  rw [Finset.mul_sum]
  calc
    (∑ r ∈ Finset.Icc j k,
        synchronizedWeight nodes t j *
          ((∏ i ∈ Finset.Ico j.val r.val, clockForwardFactorNat nodes i) *
            |t - nodes.point r|⁻¹)) =
        ∑ r ∈ Finset.Icc j k,
          synchronizedWeight nodes t r * |t - nodes.point r|⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hjr : j ≤ r := (Finset.mem_Icc.mp hr).1
      rw [synchronizedWeight_eq_mul_prod_forward nodes ht hjr]
      ring
    _ ≤ lebesgueFunction nodes.toNodeFamily t :=
      sum_synchronizedWeight_mul_distance_inv_le_lebesgueFunction
        nodes ht (Finset.Icc j k)

/-- Reverse one-sided synchronized row, propagated from the right anchor
`k`. -/
lemma backward_synchronized_row_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) (j k : Fin n) :
    synchronizedWeight nodes t k *
        ∑ r ∈ Finset.Icc j k,
          (∏ i ∈ Finset.Ico r.val k.val, clockBackwardFactorNat nodes i) *
            |t - nodes.point r|⁻¹ ≤
      lebesgueFunction nodes.toNodeFamily t := by
  rw [Finset.mul_sum]
  calc
    (∑ r ∈ Finset.Icc j k,
        synchronizedWeight nodes t k *
          ((∏ i ∈ Finset.Ico r.val k.val, clockBackwardFactorNat nodes i) *
            |t - nodes.point r|⁻¹)) =
        ∑ r ∈ Finset.Icc j k,
          synchronizedWeight nodes t r * |t - nodes.point r|⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrk : r ≤ k := (Finset.mem_Icc.mp hr).2
      rw [synchronizedWeight_eq_mul_prod_backward nodes ht hrk]
      ring
    _ ≤ lebesgueFunction nodes.toNodeFamily t :=
      sum_synchronizedWeight_mul_distance_inv_le_lebesgueFunction
        nodes ht (Finset.Icc j k)

/-- The full two-sided synchronized row around an anchor `m`.  The left and
right index sets are disjoint (`m` belongs only to the right set), so this is
a single lower bound for one Lebesgue value, not a sum of two independently
attained maxima. -/
lemma two_sided_synchronized_row_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ}
    (ht : ∀ r : Fin n, t ≠ nodes.point r) (j m k : Fin n) :
    synchronizedWeight nodes t m *
        ((∑ r ∈ Finset.Ico j m,
            (∏ i ∈ Finset.Ico r.val m.val, clockBackwardFactorNat nodes i) *
              |t - nodes.point r|⁻¹) +
          ∑ r ∈ Finset.Icc m k,
            (∏ i ∈ Finset.Ico m.val r.val, clockForwardFactorNat nodes i) *
              |t - nodes.point r|⁻¹) ≤
      lebesgueFunction nodes.toNodeFamily t := by
  have hleft :
      synchronizedWeight nodes t m *
          ∑ r ∈ Finset.Ico j m,
            (∏ i ∈ Finset.Ico r.val m.val, clockBackwardFactorNat nodes i) *
              |t - nodes.point r|⁻¹ =
        ∑ r ∈ Finset.Ico j m,
          synchronizedWeight nodes t r * |t - nodes.point r|⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hrm : r ≤ m := (Finset.mem_Ico.mp hr).2.le
    rw [synchronizedWeight_eq_mul_prod_backward nodes ht hrm]
    ring
  have hright :
      synchronizedWeight nodes t m *
          ∑ r ∈ Finset.Icc m k,
            (∏ i ∈ Finset.Ico m.val r.val, clockForwardFactorNat nodes i) *
              |t - nodes.point r|⁻¹ =
        ∑ r ∈ Finset.Icc m k,
          synchronizedWeight nodes t r * |t - nodes.point r|⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    have hmr : m ≤ r := (Finset.mem_Icc.mp hr).1
    rw [synchronizedWeight_eq_mul_prod_forward nodes ht hmr]
    ring
  rw [mul_add, hleft, hright]
  have hdisjoint : Disjoint (Finset.Ico j m) (Finset.Icc m k) := by
    rw [Finset.disjoint_left]
    intro r hrLeft hrRight
    have := (Finset.mem_Ico.mp hrLeft).2
    have := (Finset.mem_Icc.mp hrRight).1
    omega
  rw [← Finset.sum_union hdisjoint]
  exact sum_synchronizedWeight_mul_distance_inv_le_lebesgueFunction nodes ht
    (Finset.Ico j m ∪ Finset.Icc m k)

/-- Concrete full-chain specialization at the midpoint of a chosen nodal
gap.  This supplies an explicit admissible common point for a clock proof;
the two central distances are exactly `clockGap nodes g / 2` by the lemmas
above. -/
lemma clockMidpoint_full_synchronized_row_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    synchronizedWeight nodes (clockMidpoint nodes g) (clockLeftIndex g) *
        ((∑ r ∈ Finset.Ico (clockFirstIndex g) (clockLeftIndex g),
            (∏ i ∈ Finset.Ico r.val (clockLeftIndex g).val,
              clockBackwardFactorNat nodes i) *
                |clockMidpoint nodes g - nodes.point r|⁻¹) +
          ∑ r ∈ Finset.Icc (clockLeftIndex g) (clockLastIndex g),
            (∏ i ∈ Finset.Ico (clockLeftIndex g).val r.val,
              clockForwardFactorNat nodes i) *
                |clockMidpoint nodes g - nodes.point r|⁻¹) ≤
      lebesgueFunction nodes.toNodeFamily (clockMidpoint nodes g) := by
  exact two_sided_synchronized_row_le_lebesgueFunction nodes
    (clockMidpoint_ne_node nodes g) (clockFirstIndex g)
      (clockLeftIndex g) (clockLastIndex g)

/-- Full-interval form of the explicit gap-midpoint synchronized row. -/
lemma clockMidpoint_full_synchronized_row_le_lebesgueOn {n : ℕ}
    (nodes : OrderedNodes n) (g : Fin (n - 1)) :
    synchronizedWeight nodes (clockMidpoint nodes g) (clockLeftIndex g) *
        ((∑ r ∈ Finset.Ico (clockFirstIndex g) (clockLeftIndex g),
            (∏ i ∈ Finset.Ico r.val (clockLeftIndex g).val,
              clockBackwardFactorNat nodes i) *
                |clockMidpoint nodes g - nodes.point r|⁻¹) +
          ∑ r ∈ Finset.Icc (clockLeftIndex g) (clockLastIndex g),
            (∏ i ∈ Finset.Ico (clockLeftIndex g).val r.val,
              clockForwardFactorNat nodes i) *
                |clockMidpoint nodes g - nodes.point r|⁻¹) ≤
      lebesgueOn nodes.toNodeFamily (-1) 1 := by
  exact (clockMidpoint_full_synchronized_row_le_lebesgueFunction nodes g).trans
    (lebesgueFunction_le_lebesgueOn nodes.toNodeFamily (by norm_num)
      (clockMidpoint_mem_Icc nodes g))

/-- Restoring the distance denominator costs at most a factor two on the
source interval. -/
lemma synchronizedWeight_div_two_le_abs_lagrangeFundamental {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ} (htIcc : t ∈ Set.Icc (-1 : ℝ) 1)
    (k : Fin n) :
    synchronizedWeight nodes t k / 2 ≤
      |lagrangeFundamental nodes.toNodeFamily k t| := by
  have hdist : |t - nodes.point k| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [htIcc.1, htIcc.2,
      nodes.neg_one_le k, nodes.le_one k]
  unfold synchronizedWeight
  calc
    |lagrangeFundamental nodes.toNodeFamily k t| * |t - nodes.point k| / 2 ≤
        |lagrangeFundamental nodes.toNodeFamily k t| * 2 / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdist (abs_nonneg _)) (by norm_num)
    _ = |lagrangeFundamental nodes.toNodeFamily k t| := by ring

lemma abs_lagrangeFundamental_le_lebesgueFunction {n : ℕ}
    (nodes : NodeFamily n) (t : ℝ) (k : Fin n) :
    |lagrangeFundamental nodes k t| ≤ lebesgueFunction nodes t := by
  rw [lebesgueFunction]
  exact Finset.single_le_sum (fun i _ ↦ abs_nonneg
    (lagrangeFundamental nodes i t)) (Finset.mem_univ k)

/-- Each synchronized weight is a certified lower bound, up to factor two,
for the Lebesgue function at the very same point. -/
lemma synchronizedWeight_div_two_le_lebesgueFunction {n : ℕ}
    (nodes : OrderedNodes n) {t : ℝ} (htIcc : t ∈ Set.Icc (-1 : ℝ) 1)
    (k : Fin n) :
    synchronizedWeight nodes t k / 2 ≤
      lebesgueFunction nodes.toNodeFamily t :=
  (synchronizedWeight_div_two_le_abs_lagrangeFundamental nodes htIcc k).trans
    (abs_lagrangeFundamental_le_lebesgueFunction nodes.toNodeFamily t k)

/-- A concrete no-small-factor alternative already yields a lower bound at
one common point.  The other branch names the exact adjacent defect that a
sharp clock argument must exploit in the reverse direction. -/
lemma forward_defect_or_common_point_lower_bound {n : ℕ}
    (nodes : OrderedNodes n) {t q : ℝ} (hq : 0 < q)
    (htIcc : t ∈ Set.Icc (-1 : ℝ) 1)
    (ht : ∀ r : Fin n, t ≠ nodes.point r) {j k : Fin n} (hjk : j ≤ k) :
    (∃ i ∈ Finset.Ico j.val k.val,
        clockForwardFactorNat nodes i < q⁻¹) ∨
      synchronizedWeight nodes t j * q⁻¹ ^ (k.val - j.val) / 2 ≤
        lebesgueFunction nodes.toNodeFamily t := by
  by_cases hdef : ∃ i ∈ Finset.Ico j.val k.val,
      clockForwardFactorNat nodes i < q⁻¹
  · exact Or.inl hdef
  · right
    have hfactor : ∀ i ∈ Finset.Ico j.val k.val,
        q⁻¹ ≤ clockForwardFactorNat nodes i := by
      intro i hi
      exact not_lt.mp (fun hlt ↦ hdef ⟨i, hi, hlt⟩)
    have hprop := synchronizedWeight_mul_inv_pow_le nodes hq ht hjk hfactor
    have hpoint := synchronizedWeight_div_two_le_lebesgueFunction nodes htIcc k
    exact (div_le_div_of_nonneg_right hprop (by norm_num)).trans hpoint

end

end ClassicalBound
end Randy1153
