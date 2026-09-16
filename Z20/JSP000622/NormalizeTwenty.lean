import JSP000622.NormalizeSixteen

namespace JSP000622.Certificate

open SimpleGraph

/-- Complete finite evidence consumed by the twenty-vertex graph theorem. -/
structure TwentyEvidence where
  classification : SixteenEvidence
  corePacking : ∀ code ∈ classification.cores, ∀ G : SimpleGraph (Fin 20), ∀ v : Sat.Valuation,
    Realizes G (template20 code) v → TwoFours G

/-- A clique of order four either has a disjoint homogeneous four-set, or its
complementary sixteen-vertex core falls under the checked classification. -/
theorem packing_of_clique_four (E : TwentyEvidence) (G : SimpleGraph (Fin 20))
    (S : Finset (Fin 20)) (hS : G.IsNClique 4 S) : TwoFours G := by
  classical
  by_contra hn
  let R : Finset (Fin 20) := Sᶜ
  have cardR : Fintype.card ↥R = 16 := by
    rw [Fintype.card_coe]
    dsimp [R]
    rw [Finset.card_compl, Fintype.card_fin, hS.card_eq]
  let eR : Fin 16 ≃ ↥R := (Fintype.equivFinOfCardEq cardR).symm
  let fR : Fin 16 ↪ Fin 20 :=
    ⟨fun a => (eR a).val, Subtype.val_injective.comp eR.injective⟩
  let RG : SimpleGraph (Fin 16) := G.comap fR
  have restNoHom : ∀ T : Finset (Fin 16), T.card = 4 → Homogeneous RG T → False := by
    intro T hT hhom
    have hd : Disjoint S (T.map fR) := by
      rw [Finset.disjoint_left]
      intro u huS huT
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp huT
      exact (Finset.mem_compl.mp (show fR a ∈ Sᶜ from (eR a).property)) huS
    apply hn
    refine ⟨S, T.map fR, hS.card_eq, by simpa using hT, hd, ?_, ?_⟩
    · left
      intro a ha b hb hab
      exact hS.isClique ha hb hab
    · exact Homogeneous.map_comap G fR hhom
  have freeR : RG.CliqueFree 4 ∧ RG.IndepSetFree 4 := by
    constructor
    · intro T hT
      apply restNoHom T hT.card_eq
      left
      intro a ha b hb hab
      exact hT.isClique ha hb hab
    · intro T hT
      apply restNoHom T hT.card_eq
      right
      intro a ha b hb hab
      have hi := hT.isIndepSet
      rw [SimpleGraph.isIndepSet_iff] at hi
      exact hi ha hb hab
  obtain ⟨code, hcode, ⟨isoR⟩⟩ := classify_sixteen E.classification RG freeR
  have cardS : Fintype.card ↥S = 4 := by simpa using hS.card_eq
  let eS : Fin 4 ≃ ↥S := (Fintype.equivFinOfCardEq cardS).symm
  let left : Fin 4 → Fin 20 := fun a => (eS a).val
  let right : Fin 16 → Fin 20 := fun a => fR (isoR.symm a)
  have leftInj : Function.Injective left := Subtype.val_injective.comp eS.injective
  have rightInj : Function.Injective right := fR.injective.comp isoR.symm.injective
  have separate : ∀ a b, left a ≠ right b := by
    intro a b he
    have hl : left a ∈ S := (eS a).property
    have hr : right b ∉ S :=
      Finset.mem_compl.mp (show right b ∈ Sᶜ from (eR (isoR.symm b)).property)
    exact hr (he ▸ hl)
  let point : Fin 4 ⊕ Fin 16 → Fin 20 := Sum.elim left right
  have pointInj : Function.Injective point := sumElim_injective left right leftInj rightInj separate
  let p : Equiv.Perm (Fin 20) := chartPerm index20 point pointInj
  have pLeft : ∀ a, p (left20 a) = left a :=
    fun a => chartPerm_apply_index index20 point pointInj (.inl a)
  have pRight : ∀ a, p (right20 a) = right a :=
    fun a => chartPerm_apply_index index20 point pointInj (.inr a)
  let H : SimpleGraph (Fin 20) := G.comap p
  have hleft : ∀ a b, H.Adj (left20 a) (left20 b) ↔ a ≠ b := by
    intro a b
    change G.Adj (p (left20 a)) (p (left20 b)) ↔ _
    rw [pLeft, pLeft]
    constructor
    · intro hadj he
      subst b
      simpa using hadj
    · intro hab
      exact hS.isClique (eS a).property (eS b).property (leftInj.ne hab)
  have hright : ∀ a b, H.Adj (right20 a) (right20 b) ↔ (codeGraph 16 code).Adj a b := by
    intro a b
    change G.Adj (p (right20 a)) (p (right20 b)) ↔ _
    rw [pRight, pRight]
    change RG.Adj (isoR.symm a) (isoR.symm b) ↔ _
    exact isoR.symm.map_adj_iff
  have hp := E.corePacking code hcode H (rowValuation H left20 right20)
    (realizes_template20 H code hleft hright)
  exact hn (TwoFours.map (comapIso G p) hp)

/-- Every twenty-vertex graph has two disjoint homogeneous four-sets, once all
finite certificates in `E` have been supplied. No symmetry-breaking assumption
is imposed on the input graph. -/
theorem packing_twenty_of_evidence (E : TwentyEvidence) (G : SimpleGraph (Fin 20)) : TwoFours G := by
  classical
  obtain ⟨S, hS, hhom⟩ := exists_homogeneous_four_twenty G
  rcases hhom with hc | hi
  · exact packing_of_clique_four E G S ⟨by
      intro a ha b hb hab
      exact hc a ha b hb hab, hS⟩
  · have hc : Gᶜ.IsNClique 4 S := by
      refine ⟨?_, hS⟩
      intro a ha b hb hab
      exact ⟨hab, hi a ha b hb hab⟩
    have hp := packing_of_clique_four E Gᶜ S hc
    simpa only [compl_compl] using TwoFours.compl hp

#print axioms packing_of_clique_four
#print axioms packing_twenty_of_evidence

end JSP000622.Certificate
