import JSP000622.Charts
import JSP000622.RamseyAux

namespace JSP000622.Certificate

open SimpleGraph

/-- The finite inputs used by the universal sixteen-vertex classification.
Every field is instantiated by a checked theorem in the final construction. -/
structure SixteenEvidence where
  small7 : List ℕ
  small8 : List ℕ
  cores : List ℕ
  complete7 : ∀ H : SimpleGraph (Fin 7), H.CliqueFree 3 ∧ H.IndepSetFree 4 → Classified H small7
  complete8 : ∀ H : SimpleGraph (Fin 8), H.CliqueFree 3 ∧ H.IndepSetFree 4 → Classified H small8
  normalized : ∀ a ∈ small7, ∀ b ∈ small8, ∀ H : SimpleGraph (Fin 16), ∀ v : Sat.Valuation,
    Realizes H (template16 a b) v →
    H.CliqueFree 4 ∧ H.IndepSetFree 4 → Classified H cores
  complementClosed : ∀ c ∈ cores, Classified (codeGraph 16 c)ᶜ cores

/-- Normalize the root, its seven neighbours and its eight non-neighbours. -/
theorem classify_degree_seven (E : SixteenEvidence) (G : SimpleGraph (Fin 16))
    [DecidableRel G.Adj] (free : G.CliqueFree 4 ∧ G.IndepSetFree 4)
    (hd : G.degree 0 = 7) : Classified G E.cores := by
  classical
  have cardN : Fintype.card (G.neighborSet 0) = 7 :=
    (G.card_neighborSet_eq_degree 0).trans hd
  have hdF : Gᶜ.degree 0 = 8 := by
    rw [G.degree_compl (v := 0), Fintype.card_fin, hd]
  have cardF : Fintype.card (Gᶜ.neighborSet 0) = 8 :=
    (Gᶜ.card_neighborSet_eq_degree 0).trans hdF
  let eN : Fin 7 ≃ G.neighborSet 0 := (Fintype.equivFinOfCardEq cardN).symm
  let eF : Fin 8 ≃ Gᶜ.neighborSet 0 := (Fintype.equivFinOfCardEq cardF).symm
  let fN : Fin 7 ↪ Fin 16 :=
    ⟨fun a => (eN a).val, Subtype.val_injective.comp eN.injective⟩
  let fF : Fin 8 ↪ Fin 16 :=
    ⟨fun a => (eF a).val, Subtype.val_injective.comp eF.injective⟩
  let NG : SimpleGraph (Fin 7) := G.comap fN
  let FG : SimpleGraph (Fin 8) := Gᶜ.comap fF
  have freeN : NG.CliqueFree 3 ∧ NG.IndepSetFree 4 :=
    ramseyFree_comap (G.induce (G.neighborSet 0)) eN.toEmbedding
      (neighborhood_r34 G 0 free)
  have freeF : FG.CliqueFree 3 ∧ FG.IndepSetFree 4 :=
    ramseyFree_comap (Gᶜ.induce (Gᶜ.neighborSet 0)) eF.toEmbedding
      (neighborhood_r34 Gᶜ 0 (ramseyFree_compl G free))
  obtain ⟨c7, hc7, ⟨isoN⟩⟩ := E.complete7 NG freeN
  obtain ⟨c8, hc8, ⟨isoF⟩⟩ := E.complete8 FG freeF
  let near : Fin 7 → Fin 16 := fun a => fN (isoN.symm a)
  let far : Fin 8 → Fin 16 := fun a => fF (isoF.symm a)
  have nearInj : Function.Injective near := fN.injective.comp isoN.symm.injective
  have farInj : Function.Injective far := fF.injective.comp isoF.symm.injective
  have rootN : ∀ a, G.Adj 0 (near a) := fun a => (eN (isoN.symm a)).property
  have rootF : ∀ a, Gᶜ.Adj 0 (far a) := fun a => (eF (isoF.symm a)).property
  have disjointNF : ∀ a b, near a ≠ far b := by
    intro a b he
    have hn : ¬G.Adj 0 (far b) := (show 0 ≠ far b ∧ ¬G.Adj 0 (far b) from rootF b).2
    exact hn (he ▸ rootN a)
  let inner : Fin 7 ⊕ Fin 8 → Fin 16 := Sum.elim near far
  let point : Split16 → Fin 16 := Sum.elim (fun _ => 0) inner
  have innerInj : Function.Injective inner := sumElim_injective near far nearInj farInj disjointNF
  have rootDisjoint : ∀ a : Fin 1, ∀ b : Fin 7 ⊕ Fin 8, (0 : Fin 16) ≠ inner b := by
    intro a b
    rcases b with b | b
    · intro he
      have hh := rootN b
      simpa only [inner, Sum.elim_inl, ←he, SimpleGraph.irrefl] using hh
    · exact (show 0 ≠ far b ∧ ¬G.Adj 0 (far b) from rootF b).1
  have pointInj : Function.Injective point :=
    sumElim_injective (fun _ : Fin 1 => (0 : Fin 16)) inner
      (fun _ _ _ => Subsingleton.elim _ _) innerInj rootDisjoint
  let p : Equiv.Perm (Fin 16) := chartPerm index16 point pointInj
  have pRoot : p root16 = 0 := chartPerm_apply_index index16 point pointInj (.inl 0)
  have pNear : ∀ a, p (near16 a) = near a :=
    fun a => chartPerm_apply_index index16 point pointInj (.inr (.inl a))
  have pFar : ∀ a, p (far16 a) = far a :=
    fun a => chartPerm_apply_index index16 point pointInj (.inr (.inr a))
  let H : SimpleGraph (Fin 16) := G.comap p
  have hrootN : ∀ a, H.Adj root16 (near16 a) := by
    intro a
    change G.Adj (p root16) (p (near16 a))
    rw [pRoot, pNear]
    exact rootN a
  have hrootF : ∀ a, ¬H.Adj root16 (far16 a) := by
    intro a
    change ¬G.Adj (p root16) (p (far16 a))
    rw [pRoot, pFar]
    exact (show 0 ≠ far a ∧ ¬G.Adj 0 (far a) from rootF a).2
  have hnear : ∀ a b, H.Adj (near16 a) (near16 b) ↔ (codeGraph 7 c7).Adj a b := by
    intro a b
    change G.Adj (p (near16 a)) (p (near16 b)) ↔ _
    rw [pNear, pNear]
    change NG.Adj (isoN.symm a) (isoN.symm b) ↔ _
    exact isoN.symm.map_adj_iff
  have hfar : ∀ a b, H.Adj (far16 a) (far16 b) ↔ (codeGraph 8 c8)ᶜ.Adj a b := by
    intro a b
    change G.Adj (p (far16 a)) (p (far16 b)) ↔ _
    rw [pFar, pFar]
    by_cases hab : a = b
    · subst b
      simp
    · have hbase : Gᶜ.Adj (far a) (far b) ↔ (codeGraph 8 c8).Adj a b := isoF.symm.map_adj_iff
      simpa only [SimpleGraph.compl_adj, farInj.ne hab, hab, true_and, not_not]
        using not_congr hbase
  have realizes := realizes_template16 H c7 c8 hrootN hrootF hnear hfar
  have freeH : H.CliqueFree 4 ∧ H.IndepSetFree 4 := ramseyFree_comap G p.toEmbedding free
  obtain ⟨code, hcode, ⟨eH⟩⟩ := E.normalized c7 hc7 c8 hc8 H
    (rowValuation H near16 far16) realizes freeH
  exact ⟨code, hcode, ⟨(comapIso G p).symm.trans eH⟩⟩

/-- Every sixteen-vertex (4,4)-graph is covered, including the degree-eight case. -/
theorem classify_sixteen (E : SixteenEvidence) (G : SimpleGraph (Fin 16))
    (free : G.CliqueFree 4 ∧ G.IndepSetFree 4) : Classified G E.cores := by
  classical
  rcases degree_seven_or_eight G free 0 with hd | hd
  · exact classify_degree_seven E G free hd
  · have hc : Gᶜ.degree 0 = 7 := by
      rw [G.degree_compl (v := 0), Fintype.card_fin, hd]
    obtain ⟨code, hcode, ⟨e⟩⟩ := classify_degree_seven E Gᶜ (ramseyFree_compl G free) hc
    obtain ⟨target, htarget, ⟨ec⟩⟩ := E.complementClosed code hcode
    have eg : G ≃g (codeGraph 16 code)ᶜ := by
      simpa only [compl_compl] using complIso e
    exact ⟨target, htarget, ⟨eg.trans ec⟩⟩

#print axioms classify_degree_seven
#print axioms classify_sixteen

end JSP000622.Certificate
