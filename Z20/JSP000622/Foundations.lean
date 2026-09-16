/-
JSP-000622: the target is z(20) = 6.
This file reuses the pinned small-order formalization in plby/lean-proofs.
It does not claim new authorship of those imported results.
The last theorem in this file is explicitly conditional on the two-four-set theorem.
-/
import ErdosProblems.Erdos758.SmallValues

namespace JSP000622

open SimpleGraph Erdos758

/-- A homogeneous vertex set, without imposing finiteness on its ambient type. -/
def HomogeneousSet {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) ∨
  (∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬ G.Adj u v)

/-- A homogeneous cover suffices: choose one covering block for each vertex. -/
theorem colorable_of_homogeneous_cover {V : Type*} {k : ℕ}
    (G : SimpleGraph V) (blocks : Fin k → Set V)
    (cover : ∀ v, ∃ i, v ∈ blocks i)
    (hom : ∀ i, HomogeneousSet G (blocks i)) : CochromaticColorable G k := by
  classical
  let c : V → Fin k := fun v => Classical.choose (cover v)
  have hc : ∀ v, v ∈ blocks (c v) := fun v => Classical.choose_spec (cover v)
  refine ⟨c, ?_⟩
  intro i
  rcases hom i with hcl | hin
  · left
    intro u v hu hv huv
    apply hcl u (by simpa [hu] using hc u) v (by simpa [hv] using hc v) huv
  · right
    intro u v hu hv huv
    apply hin u (by simpa [hu] using hc u) v (by simpa [hv] using hc v) huv

/-- The packing statement needed for the twenty-vertex upper bound. -/
def TwoFours {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S T : Finset V, S.card = 4 ∧ T.card = 4 ∧ Disjoint S T ∧
    IsHomogeneousFinset G S ∧ IsHomogeneousFinset G T

/-- A convenient extraction from the already formalized small-order table. -/
theorem z_sixteen_eq_six : z 16 = 6 := by
  rcases small_values_exact with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h16, _, _, _⟩
  exact h16

/-- The twenty-vertex lower bound follows by induced-subgraph monotonicity. -/
theorem z_twenty_ge_six : 6 ≤ z 20 := by
  have h : z 16 ≤ z 20 := z_le
    (uniformBound_mono_vertices (by decide : 16 ≤ 20) (z_spec 20))
  simpa [z_sixteen_eq_six] using h

/-- The twelve-vertex input is an imported theorem, not a replacement target. -/
theorem upper_twelve : UniformBound 12 4 := by
  have h12 : z 12 = 4 := by
    rcases small_values_exact with
      ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, _, _, _, _, _, _⟩
    exact h12
  simpa [h12] using z_spec 12

/-- Two disjoint homogeneous four-sets and the twelve-vertex theorem give six colours. -/
theorem colorable_six_of_two_fours (G : SimpleGraph (Fin 20))
    (h : TwoFours G) : CochromaticColorable G 6 := by
  classical
  obtain ⟨S, T, hS4, hT4, hST, hS, hT⟩ := h
  let R : Finset (Fin 20) := (S ∪ T)ᶜ
  have hR : Fintype.card ↥R = 12 := by
    rw [Fintype.card_coe]
    dsimp [R]
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_union_of_disjoint hST, hS4, hT4]
  obtain ⟨c, hc⟩ := colorable_of_card_eq hR upper_twelve (G.induce (R : Set (Fin 20)))
  let P : Fin 2 ⊕ Fin 4 → Set (Fin 20) := fun j =>
    match j with
    | .inl i => if i = 0 then (S : Set (Fin 20)) else (T : Set (Fin 20))
    | .inr i => {v | ∃ hv : v ∈ R, c ⟨v, hv⟩ = i}
  have hP : ∀ j, HomogeneousSet G (P j) := by
    intro j
    cases j with
    | inl i =>
      fin_cases i
      · simpa [P, HomogeneousSet, IsHomogeneousFinset] using hS
      · simpa [P, HomogeneousSet, IsHomogeneousFinset] using hT
    | inr i =>
      rcases hc i with hcl | hin
      · left
        rintro u ⟨huR, hcu⟩ v ⟨hvR, hcv⟩ huv
        exact hcl ⟨u, huR⟩ ⟨v, hvR⟩ hcu hcv
          (fun he => huv (congrArg Subtype.val he))
      · right
        rintro u ⟨huR, hcu⟩ v ⟨hvR, hcv⟩ huv
        exact hin ⟨u, huR⟩ ⟨v, hvR⟩ hcu hcv
          (fun he => huv (congrArg Subtype.val he))
  let e : Fin 2 ⊕ Fin 4 ≃ Fin 6 := finSumFinEquiv
  apply colorable_of_homogeneous_cover G (fun i => P (e.symm i))
  · intro v
    by_cases hvS : v ∈ S
    · refine ⟨e (.inl 0), ?_⟩
      simpa [P] using hvS
    · by_cases hvT : v ∈ T
      · refine ⟨e (.inl 1), ?_⟩
        simpa [P] using hvT
      · have hvR : v ∈ R := by simp [R, hvS, hvT]
        refine ⟨e (.inr (c ⟨v, hvR⟩)), ?_⟩
        simp only [Equiv.symm_apply_apply]
        exact ⟨hvR, rfl⟩
  · intro i
    exact hP (e.symm i)

/-- This records exactly, rather than hides, the remaining graph-packing obligation. -/
theorem z_twenty_eq_six_of_two_fours
    (packing : ∀ G : SimpleGraph (Fin 20), TwoFours G) : z 20 = 6 :=
  Nat.le_antisymm (z_le (fun G => colorable_six_of_two_fours G (packing G)))
    z_twenty_ge_six

#print axioms z_twenty_ge_six
#print axioms colorable_six_of_two_fours
#print axioms z_twenty_eq_six_of_two_fours

end JSP000622
