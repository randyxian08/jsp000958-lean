import Randy1153.ClassicalBound.FullIntervalEnergy
import Randy1153.DeBoorPinkus.Boundary

/-!
# Full-interval bounds for equioscillating endpoint arrays

An endpoint array normalized on `[0,1]` cannot be fed directly to the
full-interval theorem on `[-1,1]`.  We first transport it by the affine map
`x ↦ 2x-1`, prove invariance of its Lagrange and gap data, and only then
apply the sharp full-interval estimate.
-/

namespace Randy1153
namespace ClassicalBound

open DeBoorPinkus

noncomputable section

/-- Every point of an endpoint array with endpoints zero and one lies in
`[0,1]`, not merely in the ambient interval `[-1,1]`. -/
lemma unitEndpointArray_point_mem_Icc {d : ℕ}
    (nodes : EndpointArray d 0 1) (k : Fin (d + 2)) :
    nodes.point k ∈ Set.Icc (0 : ℝ) 1 := by
  have hmono := nodes.strictMono.monotone
  constructor
  · calc
      (0 : ℝ) = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
      _ ≤ nodes.point k := hmono (by
        apply Fin.le_iff_val_le_val.mpr
        simp)
  · calc
      nodes.point k ≤ nodes.point (endpointRightIndex d) := hmono (by
        apply Fin.le_iff_val_le_val.mpr
        simp only [endpointRightIndex_val]
        omega)
      _ = (1 : ℝ) := nodes.right_endpoint

/-- Affinely transport a unit-interval endpoint array onto the full source
interval `[-1,1]`. -/
def unitToFullEndpointArray {d : ℕ}
    (nodes : EndpointArray d 0 1) : EndpointArray d (-1) 1 where
  point k := 2 * nodes.point k - 1
  injective := by
    intro i j hij
    apply nodes.injective
    linarith
  mem_Icc k := by
    have hk := unitEndpointArray_point_mem_Icc nodes k
    rcases hk with ⟨hk₀, hk₁⟩
    constructor <;> linarith
  strictMono := by
    intro i j hij
    have h := nodes.strictMono hij
    linarith
  left_endpoint := by rw [nodes.left_endpoint]; norm_num
  right_endpoint := by rw [nodes.right_endpoint]; norm_num

@[simp]
lemma unitToFullEndpointArray_point {d : ℕ}
    (nodes : EndpointArray d 0 1) (k : Fin (d + 2)) :
    (unitToFullEndpointArray nodes).point k = 2 * nodes.point k - 1 :=
  rfl

/-- Affine invariance of each Lagrange fundamental function. -/
lemma lagrangeFundamental_unitToFullEndpointArray {d : ℕ}
    (nodes : EndpointArray d 0 1) (k : Fin (d + 2)) (t : ℝ) :
    lagrangeFundamental (unitToFullEndpointArray nodes).toNodeFamily k (2 * t - 1) =
      lagrangeFundamental nodes.toNodeFamily k t := by
  classical
  unfold lagrangeFundamental
  apply Finset.prod_congr rfl
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hden : nodes.point k - nodes.point j ≠ 0 := by
    exact sub_ne_zero.mpr (nodes.injective.ne hjk.symm)
  have hdenFull :
      (2 * nodes.point k - 1) - (2 * nodes.point j - 1) ≠ 0 := by
    intro h
    apply hden
    linarith
  simp only [unitToFullEndpointArray_point]
  field_simp [hden, hdenFull]
  ring

/-- Affine invariance of the complete Lebesgue function. -/
lemma lebesgueFunction_unitToFullEndpointArray {d : ℕ}
    (nodes : EndpointArray d 0 1) (t : ℝ) :
    lebesgueFunction (unitToFullEndpointArray nodes).toNodeFamily (2 * t - 1) =
      lebesgueFunction nodes.toNodeFamily t := by
  classical
  unfold lebesgueFunction
  apply Finset.sum_congr rfl
  intro k hk
  rw [lagrangeFundamental_unitToFullEndpointArray]

/-- Affine invariance of interval suprema.  Both directions explicitly map a
maximizer across the affine bijection. -/
lemma lebesgueOn_unitToFullEndpointArray {d : ℕ}
    (nodes : EndpointArray d 0 1) {a b : ℝ} (hab : a ≤ b) :
    lebesgueOn (unitToFullEndpointArray nodes).toNodeFamily
        (2 * a - 1) (2 * b - 1) =
      lebesgueOn nodes.toNodeFamily a b := by
  obtain ⟨u, hu, hu_eq, hu_max⟩ := exists_lebesgueOn_eq_and_ge
    (unitToFullEndpointArray nodes).toNodeFamily (by linarith : 2 * a - 1 ≤ 2 * b - 1)
  obtain ⟨t, ht, ht_eq, ht_max⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily hab
  apply le_antisymm
  · rw [hu_eq, ht_eq]
    let v : ℝ := (u + 1) / 2
    have hv : v ∈ Set.Icc a b := by
      dsimp only [v]
      constructor <;> linarith [hu.1, hu.2]
    have huv : 2 * v - 1 = u := by
      dsimp only [v]
      ring
    rw [← huv, lebesgueFunction_unitToFullEndpointArray]
    exact ht_max v hv
  · rw [hu_eq, ht_eq]
    have hmap : 2 * t - 1 ∈ Set.Icc (2 * a - 1) (2 * b - 1) := by
      constructor <;> linarith [ht.1, ht.2]
    have h := hu_max (2 * t - 1) hmap
    rw [lebesgueFunction_unitToFullEndpointArray] at h
    exact h

/-- Each compact gap height is invariant under the unit-to-full affine
transport. -/
lemma height_unitToFullEndpointArray {d : ℕ}
    (nodes : EndpointArray d 0 1) (g : Fin (d + 1)) :
    (unitToFullEndpointArray nodes).height g = nodes.height g := by
  unfold EndpointArray.height gapHeight
  simpa only [unitToFullEndpointArray_point] using
    (lebesgueOn_unitToFullEndpointArray nodes
      (gap_left_lt_right nodes.toOrderedNodes g).le)

/-- Equioscillation is invariant under the affine transport. -/
lemma equioscillates_unitToFullEndpointArray_iff {d : ℕ}
    (nodes : EndpointArray d 0 1) :
    Equioscillates (unitToFullEndpointArray nodes) ↔ Equioscillates nodes := by
  constructor
  · intro h i j
    rw [← height_unitToFullEndpointArray nodes i,
      ← height_unitToFullEndpointArray nodes j]
    exact h i j
  · intro h i j
    rw [height_unitToFullEndpointArray nodes i,
      height_unitToFullEndpointArray nodes j]
    exact h i j

/-- The finitely many closed nodal gaps of an endpoint array cover its full
endpoint interval.  The least-node argument also handles `d = 0`. -/
lemma exists_closedGap_of_mem_Icc {d : ℕ} {A B x : ℝ}
    (nodes : EndpointArray d A B) (hx : x ∈ Set.Icc A B) :
    ∃ g : Fin (d + 1), x ∈ closedGap nodes.toOrderedNodes g := by
  let P : ℕ → Prop := fun k ↦
    ∃ hk : k < d + 2, x ≤ nodes.point ⟨k, hk⟩
  have hP : ∃ k : ℕ, P k := by
    refine ⟨d + 1, ⟨by omega, ?_⟩⟩
    have hkEq : (⟨d + 1, by omega⟩ : Fin (d + 2)) = endpointRightIndex d := by
      apply Fin.ext
      simp
    rw [hkEq, nodes.right_endpoint]
    exact hx.2
  let k : ℕ := Nat.find hP
  obtain ⟨hklt, hxk⟩ := Nat.find_spec hP
  by_cases hk0 : k = 0
  · let g₀ : Fin (d + 1) := ⟨0, by omega⟩
    refine ⟨g₀, ?_⟩
    have hleftEq : nodes.point (gapLeftIndex g₀) = A := by
      rw [show gapLeftIndex g₀ = endpointLeftIndex d by
        apply Fin.ext
        simp [g₀, gapLeftIndex, endpointLeftIndex], nodes.left_endpoint]
    have hkEq : (⟨k, hklt⟩ : Fin (d + 2)) = gapLeftIndex g₀ := by
      apply Fin.ext
      simp [hk0, g₀, gapLeftIndex]
    have hxleft : nodes.point (gapLeftIndex g₀) ≤ x := by
      rw [hleftEq]
      exact hx.1
    have hxright : x ≤ nodes.point (gapRightIndex g₀) := by
      have hxatleft : x ≤ nodes.point (gapLeftIndex g₀) := by
        rw [← hkEq]
        exact hxk
      exact hxatleft.trans
        (gap_left_lt_right nodes.toOrderedNodes g₀).le
    exact ⟨hxleft, hxright⟩
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let g : Fin (d + 1) := ⟨k - 1, by omega⟩
    have hkpred : k - 1 < k := Nat.sub_lt hkpos (by omega)
    have hnotP : ¬P (k - 1) := by
      intro hpredP
      exact (not_le_of_gt hkpred) (Nat.find_min' hP hpredP)
    have hkpredBound : k - 1 < d + 2 := by omega
    have hxleft : nodes.point (⟨k - 1, hkpredBound⟩ : Fin (d + 2)) ≤ x := by
      by_contra h
      have hxle : x ≤ nodes.point (⟨k - 1, hkpredBound⟩ : Fin (d + 2)) :=
        le_of_not_ge h
      exact hnotP ⟨hkpredBound, hxle⟩
    refine ⟨g, ?_⟩
    constructor
    · simpa only [g, gapLeftIndex] using hxleft
    · have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
      simpa only [g, gapRightIndex, Nat.sub_add_cancel hkone] using hxk

/-- For an equioscillating endpoint array spanning `[-1,1]`, the global
Lebesgue maximum is exactly the common gap height. -/
theorem lebesgueOn_eq_height_zero_of_equioscillates {d : ℕ}
    (nodes : EndpointArray d (-1) 1) (heq : Equioscillates nodes) :
    lebesgueOn nodes.toNodeFamily (-1) 1 =
      nodes.height (0 : Fin (d + 1)) := by
  obtain ⟨t, ht, hsup, _hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (a := (-1 : ℝ)) (b := (1 : ℝ)) (by norm_num)
  have hupper : lebesgueOn nodes.toNodeFamily (-1) 1 ≤
      nodes.height (0 : Fin (d + 1)) := by
    obtain ⟨g, hg⟩ := exists_closedGap_of_mem_Icc nodes ht
    rw [hsup]
    exact (DeBoorPinkus.lebesgueFunction_le_height nodes g hg).trans_eq
      (heq g 0)
  have hlower : nodes.height (0 : Fin (d + 1)) ≤
      lebesgueOn nodes.toNodeFamily (-1) 1 := by
    unfold EndpointArray.height gapHeight
    exact lebesgueOn_mono_Icc nodes.toNodeFamily
      (gap_left_lt_right nodes.toOrderedNodes (0 : Fin (d + 1))).le
      (nodes.neg_one_le _) (nodes.le_one _)
  exact le_antisymm hupper hlower

/-- The full-interval theorem gives a uniform eventual lower bound for the
common height of every equioscillating unit-interval endpoint array.  The
unit pattern is first transported to `[-1,1]`; no supremum on `[0,1]` is
silently identified with the full-interval supremum. -/
theorem equioscillatingUnitHeightEventual
    (hfull : FullIntervalEventual) (eps : ℝ) (heps : 0 < eps) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀ nodes : EndpointArray d 0 1,
      Equioscillates nodes →
        (2 / Real.pi - eps) * Real.log ((d + 2 : ℕ) : ℝ) <
          nodes.height (0 : Fin (d + 1)) := by
  obtain ⟨N, hN⟩ := hfull eps heps
  refine ⟨N, fun d hd nodes heq ↦ ?_⟩
  let fullNodes : EndpointArray d (-1) 1 := unitToFullEndpointArray nodes
  have hfullEq : Equioscillates fullNodes :=
    (equioscillates_unitToFullEndpointArray_iff nodes).2 heq
  have hbound := hN (d + 2) (by omega) fullNodes.toNodeFamily
  unfold FullIntervalAt at hbound
  rw [lebesgueOn_eq_height_zero_of_equioscillates fullNodes hfullEq] at hbound
  change (2 / Real.pi - eps) * Real.log ((d + 2 : ℕ) : ℝ) <
    (unitToFullEndpointArray nodes).height (0 : Fin (d + 1)) at hbound
  rwa [height_unitToFullEndpointArray] at hbound

end


end ClassicalBound
end Randy1153
