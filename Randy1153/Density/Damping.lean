import Randy1153.CompactMax
import Randy1153.Density.FixedInterval
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Order.Interval.Set.Infinite

/-!
# The sparse-node damping polynomial

This module implements the explicit polynomial used in the sparse branch of
the fixed-interval argument.  All interval locations and damping constants
are concrete, so later asymptotic bookkeeping does not conceal a compactness
or separation choice.
-/

namespace Randy1153.Density

open Polynomial Finset Set

noncomputable section

/-! ## Explicit nested intervals -/

/-- Left endpoint of the central interval `J₀`. -/
def j0Left (a b : ℝ) : ℝ := (3 * a + b) / 4

/-- Right endpoint of the central interval `J₀`. -/
def j0Right (a b : ℝ) : ℝ := (a + 3 * b) / 4

/-- Left endpoint of the wider interval `J₁`. -/
def j1Left (a b : ℝ) : ℝ := (7 * a + b) / 8

/-- Right endpoint of the wider interval `J₁`. -/
def j1Right (a b : ℝ) : ℝ := (a + 7 * b) / 8

/-- The five endpoints are strictly nested whenever `a < b`. -/
lemma nested_interval_endpoints {a b : ℝ} (hab : a < b) :
    a < j1Left a b ∧ j1Left a b < j0Left a b ∧
      j0Left a b < j0Right a b ∧ j0Right a b < j1Right a b ∧
        j1Right a b < b := by
  simp only [j0Left, j0Right, j1Left, j1Right]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma j0_nonempty {a b : ℝ} (hab : a < b) : j0Left a b ≤ j0Right a b :=
  (nested_interval_endpoints hab).2.2.1.le

lemma j0_subset_j1 {a b : ℝ} (hab : a < b) :
    Set.Icc (j0Left a b) (j0Right a b) ⊆
      Set.Icc (j1Left a b) (j1Right a b) := by
  intro x hx
  exact ⟨(nested_interval_endpoints hab).2.1.le.trans hx.1,
    hx.2.trans (nested_interval_endpoints hab).2.2.2.1.le⟩

lemma j1_subset_Icc {a b : ℝ} (hab : a < b) :
    Set.Icc (j1Left a b) (j1Right a b) ⊆ Set.Icc a b := by
  intro x hx
  exact ⟨(nested_interval_endpoints hab).1.le.trans hx.1,
    hx.2.trans (nested_interval_endpoints hab).2.2.2.2.le⟩

lemma j0_subset_Icc {a b : ℝ} (hab : a < b) :
    Set.Icc (j0Left a b) (j0Right a b) ⊆ Set.Icc a b :=
  (j0_subset_j1 hab).trans (j1_subset_Icc hab)

/-- The separation from either endpoint of `J₀` to the corresponding
endpoint of `J₁` is exactly `(b-a)/8`. -/
lemma j0_j1_separation_left (a b : ℝ) :
    j0Left a b - j1Left a b = (b - a) / 8 := by
  simp only [j0Left, j1Left]
  ring

lemma j0_j1_separation_right (a b : ℝ) :
    j1Right a b - j0Right a b = (b - a) / 8 := by
  simp only [j0Right, j1Right]
  ring

/-! ## The product over nodes in `J₁` -/

/-- Indices of nodes lying in a closed interval. -/
def insideIndices {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => nodes.point i ∈ Set.Icc u v

@[simp]
lemma mem_insideIndices {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) (i : Fin n) :
    i ∈ insideIndices nodes u v ↔ nodes.point i ∈ Set.Icc u v := by
  simp [insideIndices]

lemma card_insideIndices_le {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) :
    (insideIndices nodes u v).card ≤ n := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)

/-- Product of the linear factors belonging to the nodes in `[u,v]`. -/
def insidePolynomial {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) : ℝ[X] :=
  ∏ i ∈ insideIndices nodes u v, (Polynomial.X - Polynomial.C (nodes.point i))

lemma insidePolynomial_monic {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) :
    (insidePolynomial nodes u v).Monic := by
  exact Polynomial.monic_prod_X_sub_C nodes.point (insideIndices nodes u v)

lemma insidePolynomial_ne_zero {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) :
    insidePolynomial nodes u v ≠ 0 :=
  (insidePolynomial_monic nodes u v).ne_zero

@[simp]
lemma natDegree_insidePolynomial {n : ℕ} (nodes : NodeFamily n) (u v : ℝ) :
    (insidePolynomial nodes u v).natDegree = (insideIndices nodes u v).card := by
  simp only [insidePolynomial, Polynomial.natDegree_finset_prod_X_sub_C_eq_card]

/-- The product vanishes at every node used to construct it. -/
lemma insidePolynomial_eval_node_eq_zero {n : ℕ} (nodes : NodeFamily n)
    {u v : ℝ} {i : Fin n} (hi : i ∈ insideIndices nodes u v) :
    (insidePolynomial nodes u v).eval (nodes.point i) = 0 := by
  classical
  rw [insidePolynomial, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-- A nonzero real polynomial has a positive attained absolute maximum on a
nondegenerate compact interval. -/
lemma exists_positive_polyMaxIcc (p : ℝ[X]) (hp : p ≠ 0)
    {u v : ℝ} (huv : u < v) :
    ∃ x ∈ Set.Icc u v,
      polyMaxIcc p u v = |p.eval x| ∧ p.eval x ≠ 0 ∧
        ∀ y ∈ Set.Icc u v, |p.eval y| ≤ |p.eval x| := by
  obtain ⟨x, hx, hmax, hge⟩ := exists_polyMaxIcc_eq_and_ge p huv.le
  have hex : ∃ y ∈ Set.Icc u v, p.eval y ≠ 0 := by
    by_contra h
    push_neg at h
    have hinfinite : Set.Infinite {y : ℝ | p.IsRoot y} :=
      (Set.Icc_infinite huv).mono fun y hy => Polynomial.IsRoot.def.mpr (h y hy)
    exact hp (Polynomial.eq_zero_of_infinite_isRoot _ hinfinite)
  obtain ⟨y, hy, hyne⟩ := hex
  have hxne : p.eval x ≠ 0 := by
    intro hxzero
    have hypos : 0 < |p.eval y| := abs_pos.mpr hyne
    have hyle := hge y hy
    rw [hxzero, abs_zero] at hyle
    linarith
  exact ⟨x, hx, hmax, hxne, hge⟩

/-- A nonzero polynomial cannot vanish on a nondegenerate real interval. -/
lemma exists_insidePolynomial_eval_ne_zero {n : ℕ} (nodes : NodeFamily n)
    {u v : ℝ} (huv : u < v) :
    ∃ x ∈ Set.Icc u v, (insidePolynomial nodes u v).eval x ≠ 0 := by
  by_contra h
  push_neg at h
  have hinfinite : Set.Infinite
      {x : ℝ | (insidePolynomial nodes u v).IsRoot x} :=
    (Set.Icc_infinite huv).mono fun x hx => Polynomial.IsRoot.def.mpr (h x hx)
  exact insidePolynomial_ne_zero nodes u v
    (Polynomial.eq_zero_of_infinite_isRoot _ hinfinite)

/-- The compact maximum of the inside-node product on a nondegenerate
interval is attained at a point where the product is nonzero. -/
lemma exists_positive_insidePolynomial_maximizer {n : ℕ} (nodes : NodeFamily n)
    {u v : ℝ} (huv : u < v) :
    ∃ x ∈ Set.Icc u v,
      polyMaxIcc (insidePolynomial nodes u v) u v =
          |(insidePolynomial nodes u v).eval x| ∧
        (insidePolynomial nodes u v).eval x ≠ 0 ∧
        ∀ y ∈ Set.Icc u v,
          |(insidePolynomial nodes u v).eval y| ≤
            |(insidePolynomial nodes u v).eval x| := by
  exact exists_positive_polyMaxIcc (insidePolynomial nodes u v)
    (insidePolynomial_ne_zero nodes u v) huv

/-- The indices used in the sparse construction are precisely the nodes in
`J₁`. -/
def sparseIndices {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) : Finset (Fin n) :=
  insideIndices nodes (j1Left a b) (j1Right a b)

/-- The sparse-node product `Q`. -/
def sparsePolynomial {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) : ℝ[X] :=
  insidePolynomial nodes (j1Left a b) (j1Right a b)

@[simp]
lemma natDegree_sparsePolynomial {n : ℕ} (nodes : NodeFamily n) (a b : ℝ) :
    (sparsePolynomial nodes a b).natDegree = (sparseIndices nodes a b).card := by
  simp only [sparsePolynomial, sparseIndices, natDegree_insidePolynomial]

lemma sparsePolynomial_eval_node_eq_zero {n : ℕ} (nodes : NodeFamily n)
    {a b : ℝ} {i : Fin n} (hi : i ∈ sparseIndices nodes a b) :
    (sparsePolynomial nodes a b).eval (nodes.point i) = 0 := by
  exact insidePolynomial_eval_node_eq_zero nodes hi

/-- The specialized positive-maximizer theorem used by damping. -/
lemma exists_sparsePolynomial_maximizer {n : ℕ} (nodes : NodeFamily n)
    {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Icc (j0Left a b) (j0Right a b),
      polyMaxIcc (sparsePolynomial nodes a b) (j0Left a b) (j0Right a b) =
          |(sparsePolynomial nodes a b).eval x| ∧
        (sparsePolynomial nodes a b).eval x ≠ 0 ∧
        ∀ y ∈ Set.Icc (j0Left a b) (j0Right a b),
          |(sparsePolynomial nodes a b).eval y| ≤
            |(sparsePolynomial nodes a b).eval x| := by
  exact exists_positive_polyMaxIcc (sparsePolynomial nodes a b)
    (insidePolynomial_ne_zero nodes (j1Left a b) (j1Right a b))
    (nested_interval_endpoints hab).2.2.1

/-! ## Uniform quadratic damping -/

/-- A fixed coefficient small enough to keep the damping factor nonnegative
on all of `[-1,1]`. -/
def dampingAlpha : ℝ := 1 / 8

/-- Uniform contraction bound outside `J₁`. -/
def dampingRho (a b : ℝ) : ℝ := 1 - (b - a) ^ 2 / 512

/-- The quadratic factor `1 - α (X-x*)²`. -/
def dampingFactor (xstar : ℝ) : ℝ[X] :=
  1 - Polynomial.C dampingAlpha * (Polynomial.X - Polynomial.C xstar) ^ 2

@[simp]
lemma dampingFactor_eval (xstar t : ℝ) :
    (dampingFactor xstar).eval t = 1 - dampingAlpha * (t - xstar) ^ 2 := by
  simp [dampingFactor]

@[simp]
lemma dampingFactor_eval_self (xstar : ℝ) :
    (dampingFactor xstar).eval xstar = 1 := by
  simp

lemma natDegree_dampingFactor_le (xstar : ℝ) :
    (dampingFactor xstar).natDegree ≤ 2 := by
  unfold dampingFactor
  calc
    (1 - Polynomial.C dampingAlpha * (Polynomial.X - Polynomial.C xstar) ^ 2).natDegree ≤
        max (1 : ℝ[X]).natDegree
          (Polynomial.C dampingAlpha * (Polynomial.X - Polynomial.C xstar) ^ 2).natDegree :=
      Polynomial.natDegree_sub_le _ _
    _ ≤ 2 := by
      apply max_le
      · simp
      · calc
          (Polynomial.C dampingAlpha *
              (Polynomial.X - Polynomial.C xstar) ^ 2).natDegree ≤
              (Polynomial.C dampingAlpha).natDegree +
                ((Polynomial.X - Polynomial.C xstar) ^ 2).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 0 + 2 * 1 := by
            apply Nat.add_le_add
            · simp
            · exact Polynomial.natDegree_pow_le.trans
                (Nat.mul_le_mul_left 2 (by simp))
          _ = 2 := by norm_num

lemma dampingRho_pos {a b : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    0 < dampingRho a b := by
  have hdelta_pos : 0 < b - a := sub_pos.mpr hab
  have hdelta_le : b - a ≤ 2 := by linarith
  have hsq : (b - a) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdelta_le)
      (show 0 ≤ 2 + (b - a) by linarith)]
  simp only [dampingRho]
  nlinarith

lemma dampingRho_lt_one {a b : ℝ} (hab : a < b) : dampingRho a b < 1 := by
  have hdelta : 0 < (b - a) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
  simp only [dampingRho]
  nlinarith

/-- On `[-1,1]`, the damping factor lies in `[0,1]`, uniformly for
`x* ∈ J₀`. -/
lemma dampingFactor_eval_mem_Icc {a b xstar t : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hx : xstar ∈ Set.Icc (j0Left a b) (j0Right a b))
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    (dampingFactor xstar).eval t ∈ Set.Icc (0 : ℝ) 1 := by
  have hx_source : xstar ∈ Set.Icc (-1 : ℝ) 1 := by
    have hx_ab := j0_subset_Icc hab hx
    exact ⟨ha.trans hx_ab.1, hx_ab.2.trans hb⟩
  have hdiff_lo : -2 ≤ t - xstar := by linarith [ht.1, hx_source.2]
  have hdiff_hi : t - xstar ≤ 2 := by linarith [ht.2, hx_source.1]
  have hsq : (t - xstar) ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 - (t - xstar) by linarith)
      (show 0 ≤ 2 + (t - xstar) by linarith)]
  rw [dampingFactor_eval]
  constructor
  · simp only [dampingAlpha]
    nlinarith [sq_nonneg (t - xstar)]
  · have hsquare := sq_nonneg (t - xstar)
    simp only [dampingAlpha]
    nlinarith

/-- Outside `J₁`, the damping factor contracts by the fixed number
`dampingRho a b < 1`. -/
lemma abs_dampingFactor_eval_le_rho {a b xstar t : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hx : xstar ∈ Set.Icc (j0Left a b) (j0Right a b))
    (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hout : t ∉ Set.Icc (j1Left a b) (j1Right a b)) :
    |(dampingFactor xstar).eval t| ≤ dampingRho a b := by
  have hD := dampingFactor_eval_mem_Icc ha hab hb hx ht
  rw [abs_of_nonneg hD.1]
  have hsep : (b - a) / 8 ≤ |t - xstar| := by
    by_cases hleft : t < j1Left a b
    · have htx : t ≤ xstar :=
        le_trans hleft.le ((nested_interval_endpoints hab).2.1.le.trans hx.1)
      rw [abs_of_nonpos (sub_nonpos.mpr htx)]
      rw [← j0_j1_separation_left a b]
      linarith [hx.1, hleft]
    · have htleft : j1Left a b ≤ t := le_of_not_gt hleft
      have hright : j1Right a b < t := by
        by_contra h
        exact hout ⟨htleft, le_of_not_gt h⟩
      have hxt : xstar ≤ t :=
        le_trans (hx.2.trans (nested_interval_endpoints hab).2.2.2.1.le) hright.le
      rw [abs_of_nonneg (sub_nonneg.mpr hxt)]
      rw [← j0_j1_separation_right a b]
      linarith [hx.2, hright]
  have hsep0 : 0 ≤ (b - a) / 8 :=
    div_nonneg (sub_nonneg.mpr hab.le) (by norm_num)
  have hsq : ((b - a) / 8) ^ 2 ≤ (t - xstar) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ hsep0 (abs_nonneg _) |>.2 hsep)
  rw [dampingFactor_eval]
  simp only [dampingAlpha, dampingRho]
  nlinarith

/-! ## The normalized damped product -/

/-- The integer exponent reserved for quadratic damping after using `m`
linear factors. -/
def dampingExponent (n m : ℕ) : ℕ := (n - 1 - m) / 2

lemma two_mul_dampingExponent_add_le {n m : ℕ} (hm : m ≤ n - 1) :
    2 * dampingExponent n m + m ≤ n - 1 := by
  unfold dampingExponent
  omega

/-- A source-readable sufficient condition for leaving `e` damping slots
after paying `K` slots for each of the `m` inside nodes. -/
lemma dampingBudget_of_slot_bound {n m K e : ℕ}
    (hslots : (2 * K + 1) * m + 2 * e ≤ n - 1) :
    K * m + e ≤ dampingExponent n m := by
  have hexpand : (2 * K + 1) * m + 2 * e =
      2 * (K * m + e) + m := by ring
  rw [hexpand] at hslots
  have hm : m ≤ n - 1 := by omega
  unfold dampingExponent
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  have hsub : 2 * (K * m + e) ≤ n - 1 - m :=
    (le_tsub_iff_right hm).2 hslots
  simpa only [Nat.mul_comm] using hsub

/-- `D^d Q / Q(x*)`, written with a constant inverse to stay inside the
polynomial ring. -/
def dampedPolynomial (Q : ℝ[X]) (xstar : ℝ) (d : ℕ) : ℝ[X] :=
  (dampingFactor xstar) ^ d * Q * Polynomial.C (Q.eval xstar)⁻¹

@[simp]
lemma dampedPolynomial_eval (Q : ℝ[X]) (xstar t : ℝ) (d : ℕ) :
    (dampedPolynomial Q xstar d).eval t =
      (dampingFactor xstar).eval t ^ d * Q.eval t * (Q.eval xstar)⁻¹ := by
  simp [dampedPolynomial]

/-- The normalized damped polynomial equals one at its maximizing point. -/
lemma dampedPolynomial_eval_self (Q : ℝ[X]) {xstar : ℝ} (d : ℕ)
    (hx : Q.eval xstar ≠ 0) :
    (dampedPolynomial Q xstar d).eval xstar = 1 := by
  simp [dampedPolynomial_eval, hx]

/-- Every zero of `Q` remains a zero after damping. -/
lemma dampedPolynomial_eval_eq_zero_of_Q_eval_eq_zero (Q : ℝ[X])
    {xstar t : ℝ} (d : ℕ) (ht : Q.eval t = 0) :
    (dampedPolynomial Q xstar d).eval t = 0 := by
  simp [dampedPolynomial_eval, ht]

/-- Degree accounting before the concrete exponent is selected. -/
lemma natDegree_dampedPolynomial_le (Q : ℝ[X]) (xstar : ℝ) (d : ℕ) :
    (dampedPolynomial Q xstar d).natDegree ≤ 2 * d + Q.natDegree := by
  have hpow : ((dampingFactor xstar) ^ d).natDegree ≤ 2 * d := by
    calc
      ((dampingFactor xstar) ^ d).natDegree ≤
          d * (dampingFactor xstar).natDegree := Polynomial.natDegree_pow_le
      _ ≤ d * 2 := Nat.mul_le_mul_left d (natDegree_dampingFactor_le xstar)
      _ = 2 * d := Nat.mul_comm _ _
  unfold dampedPolynomial
  calc
    (((dampingFactor xstar) ^ d * Q) * Polynomial.C (Q.eval xstar)⁻¹).natDegree ≤
        ((dampingFactor xstar) ^ d * Q).natDegree +
          (Polynomial.C (Q.eval xstar)⁻¹).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (((dampingFactor xstar) ^ d).natDegree + Q.natDegree) + 0 := by
      exact Nat.add_le_add Polynomial.natDegree_mul_le (by simp)
    _ ≤ (2 * d + Q.natDegree) + 0 := by omega
    _ = 2 * d + Q.natDegree := by omega

/-- Fixed-interval growth after normalization by the attained nonzero
maximum on `[u,v]`. -/
lemma abs_eval_mul_inv_le_growthBase_pow (Q : ℝ[X])
    {u v xstar t : ℝ} (hu : -1 ≤ u) (huv : u < v) (hv : v ≤ 1)
    (hxmax : polyMaxIcc Q u v = |Q.eval xstar|) (hxne : Q.eval xstar ≠ 0)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |Q.eval t * (Q.eval xstar)⁻¹| ≤ fixedIntervalGrowthBase u v ^ Q.natDegree := by
  have hgrowth := abs_eval_le_growthBase_pow_mul_polyMaxIcc Q hu huv hv ht
  rw [hxmax] at hgrowth
  have hxabs : 0 < |Q.eval xstar| := abs_pos.mpr hxne
  calc
    |Q.eval t * (Q.eval xstar)⁻¹| = |Q.eval t| / |Q.eval xstar| := by
      simp only [abs_mul, abs_inv, div_eq_mul_inv]
    _ ≤ (fixedIntervalGrowthBase u v ^ Q.natDegree * |Q.eval xstar|) /
        |Q.eval xstar| :=
      div_le_div_of_nonneg_right hgrowth (abs_nonneg _)
    _ = fixedIntervalGrowthBase u v ^ Q.natDegree := by
      field_simp

/-- Outside `J₁`, the normalized damped product has the advertised product
decay: one factor `ρ^d` from damping and one fixed-interval growth factor for
each zero in `Q`. -/
lemma abs_dampedPolynomial_eval_le {Q : ℝ[X]} {a b xstar t : ℝ} {d : ℕ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hx : xstar ∈ Set.Icc (j0Left a b) (j0Right a b))
    (hxmax : polyMaxIcc Q (j0Left a b) (j0Right a b) = |Q.eval xstar|)
    (hxne : Q.eval xstar ≠ 0) (ht : t ∈ Set.Icc (-1 : ℝ) 1)
    (hout : t ∉ Set.Icc (j1Left a b) (j1Right a b)) :
    |(dampedPolynomial Q xstar d).eval t| ≤
      dampingRho a b ^ d *
        fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ^ Q.natDegree := by
  have hj0source :
      (-1 : ℝ) ≤ j0Left a b ∧ j0Right a b ≤ (1 : ℝ) := by
    exact ⟨ha.trans (j0_subset_Icc hab ⟨le_rfl,
      (nested_interval_endpoints hab).2.2.1.le⟩).1,
      (j0_subset_Icc hab ⟨(nested_interval_endpoints hab).2.2.1.le,
        le_rfl⟩).2.trans hb⟩
  have hnorm := abs_eval_mul_inv_le_growthBase_pow Q hj0source.1
    (nested_interval_endpoints hab).2.2.1 hj0source.2 hxmax hxne ht
  have hbase : 0 ≤ fixedIntervalGrowthBase (j0Left a b) (j0Right a b) := by
    exact (div_pos (mul_pos (by norm_num) (Real.exp_pos 1))
      (sub_pos.mpr (nested_interval_endpoints hab).2.2.1)).le
  have hD := abs_dampingFactor_eval_le_rho ha hab hb hx ht hout
  have hDpow : |(dampingFactor xstar).eval t| ^ d ≤ dampingRho a b ^ d :=
    pow_le_pow_left₀ (abs_nonneg _) hD d
  rw [dampedPolynomial_eval]
  calc
    |(dampingFactor xstar).eval t ^ d * Q.eval t * (Q.eval xstar)⁻¹| =
        |(dampingFactor xstar).eval t| ^ d *
          |Q.eval t * (Q.eval xstar)⁻¹| := by
      simp only [abs_mul, abs_pow]
      ring
    _ ≤ |(dampingFactor xstar).eval t| ^ d *
        fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ^ Q.natDegree :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ ≤ dampingRho a b ^ d *
        fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ^ Q.natDegree :=
      mul_le_mul_of_nonneg_right hDpow (pow_nonneg hbase _)

/-! ## The specialized sparse polynomial -/

/-- The fully specified polynomial used for a node family: `Q` is the
`J₁`-node product and `d = floor ((n-1-m)/2)`. -/
def sparseDampedPolynomial {n : ℕ} (nodes : NodeFamily n)
    (a b xstar : ℝ) : ℝ[X] :=
  dampedPolynomial (sparsePolynomial nodes a b) xstar
    (dampingExponent n (sparseIndices nodes a b).card)

@[simp]
lemma sparseDampedPolynomial_eval_self {n : ℕ} (nodes : NodeFamily n)
    {a b xstar : ℝ} (hxne : (sparsePolynomial nodes a b).eval xstar ≠ 0) :
    (sparseDampedPolynomial nodes a b xstar).eval xstar = 1 := by
  exact dampedPolynomial_eval_self _ _ hxne

/-- All nodes in `J₁` are exact zeros of the sparse damped polynomial. -/
lemma sparseDampedPolynomial_eval_inside_eq_zero {n : ℕ} (nodes : NodeFamily n)
    {a b xstar : ℝ} {i : Fin n} (hi : i ∈ sparseIndices nodes a b) :
    (sparseDampedPolynomial nodes a b xstar).eval (nodes.point i) = 0 := by
  exact dampedPolynomial_eval_eq_zero_of_Q_eval_eq_zero _ _
    (sparsePolynomial_eval_node_eq_zero nodes hi)

/-- Exact degree budget for the canonical sparse damping exponent. -/
lemma natDegree_sparseDampedPolynomial_le {n : ℕ} (nodes : NodeFamily n)
    {a b xstar : ℝ} (hm : (sparseIndices nodes a b).card ≤ n - 1) :
    (sparseDampedPolynomial nodes a b xstar).natDegree ≤ n - 1 := by
  calc
    (sparseDampedPolynomial nodes a b xstar).natDegree ≤
        2 * dampingExponent n (sparseIndices nodes a b).card +
          (sparsePolynomial nodes a b).natDegree :=
      natDegree_dampedPolynomial_le _ _ _
    _ = 2 * dampingExponent n (sparseIndices nodes a b).card +
        (sparseIndices nodes a b).card := by rw [natDegree_sparsePolynomial]
    _ ≤ n - 1 := two_mul_dampingExponent_add_le hm

/-- Every nodal value is bounded by the explicit sparse-decay expression.
Inside `J₁` it is zero; outside `J₁` the damping estimate applies. -/
lemma abs_sparseDampedPolynomial_eval_node_le {n : ℕ} (nodes : NodeFamily n)
    {a b xstar : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hx : xstar ∈ Set.Icc (j0Left a b) (j0Right a b))
    (hxmax : polyMaxIcc (sparsePolynomial nodes a b) (j0Left a b) (j0Right a b) =
      |(sparsePolynomial nodes a b).eval xstar|)
    (hxne : (sparsePolynomial nodes a b).eval xstar ≠ 0) (i : Fin n) :
    |(sparseDampedPolynomial nodes a b xstar).eval (nodes.point i)| ≤
      dampingRho a b ^ dampingExponent n (sparseIndices nodes a b).card *
        fixedIntervalGrowthBase (j0Left a b) (j0Right a b) ^
          (sparseIndices nodes a b).card := by
  by_cases hi : i ∈ sparseIndices nodes a b
  · rw [sparseDampedPolynomial_eval_inside_eq_zero nodes hi, abs_zero]
    exact mul_nonneg (pow_nonneg (dampingRho_pos ha hab hb).le _)
      (pow_nonneg
        ((div_pos (mul_pos (by norm_num) (Real.exp_pos 1))
          (sub_pos.mpr (nested_interval_endpoints hab).2.2.1)).le) _)
  · have hout : nodes.point i ∉ Set.Icc (j1Left a b) (j1Right a b) := by
      simpa only [sparseIndices, mem_insideIndices] using hi
    simpa only [sparseDampedPolynomial, natDegree_sparsePolynomial] using
      (abs_dampedPolynomial_eval_le (Q := sparsePolynomial nodes a b)
        ha hab hb hx hxmax hxne (nodes.mem_Icc i) hout)

end

end Randy1153.Density
