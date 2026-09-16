import JSP000622.Templates
import ErdosProblems.Erdos758.SmallUpper

namespace JSP000622.Certificate

open SimpleGraph

/-- The classical off-diagonal Ramsey bound rules out a nine-vertex (3,4)-graph. -/
theorem r34_card_le_eight {V : Type*} [Fintype V] (G : SimpleGraph V)
    (free : G.CliqueFree 3 ∧ G.IndepSetFree 4) : Fintype.card V ≤ 8 := by
  classical
  by_contra h
  have hn : 9 ≤ Fintype.card V := by omega
  exact (Ramsey.ramseyProperty_of_card rfl
    (Ramsey.ramseyProperty_mono hn Erdos758.ramseyProperty_three_four_nine) G) free

/-- The neighbourhood of a vertex in a (4,4)-graph is a (3,4)-graph. -/
theorem neighborhood_r34 {V : Type*} (G : SimpleGraph V) (v : V)
    (free : G.CliqueFree 4 ∧ G.IndepSetFree 4) :
    (G.induce (G.neighborSet v)).CliqueFree 3 ∧
    (G.induce (G.neighborSet v)).IndepSetFree 4 := by
  classical
  let f : G.neighborSet v ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  constructor
  · intro S hS
    have h3 : G.IsNClique 3 (S.map f) := by
      refine ⟨?_, by simpa using hS.card_eq⟩
      intro a ha b hb hab
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
      exact hS.isClique hi hj (fun he => hab (congrArg f he))
    have hconn : ∀ b ∈ S.map f, G.Adj v b := by
      intro b hb
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hb
      exact i.property
    exact free.1 _ (h3.insert hconn)
  · exact indepSetFree_comap G f free.2

/-- Every vertex in a finite (4,4)-graph has at most eight neighbours. -/
theorem degree_le_eight {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (free : G.CliqueFree 4 ∧ G.IndepSetFree 4) (v : V) : G.degree v ≤ 8 := by
  classical
  have h := r34_card_le_eight (G.induce (G.neighborSet v)) (neighborhood_r34 G v free)
  simpa only [G.card_neighborSet_eq_degree] using h

/-- The two degree possibilities are proved for every labelled sixteen-vertex graph. -/
theorem degree_seven_or_eight (G : SimpleGraph (Fin 16)) [DecidableRel G.Adj]
    (free : G.CliqueFree 4 ∧ G.IndepSetFree 4) (v : Fin 16) :
    G.degree v = 7 ∨ G.degree v = 8 := by
  classical
  have hg := degree_le_eight G free v
  have hc := degree_le_eight Gᶜ (ramseyFree_compl G free) v
  rw [G.degree_compl (v := v), Fintype.card_fin] at hc
  omega

/-- The initial homogeneous four-set follows from the checked Ramsey upper bound. -/
theorem exists_homogeneous_four_twenty (G : SimpleGraph (Fin 20)) :
    ∃ S : Finset (Fin 20), S.card = 4 ∧ Homogeneous G S := by
  obtain ⟨S, hS, hs⟩ := Erdos758.exists_homogeneous_finset_of_ramsey
    (Ramsey.ramseyProperty_mono (by decide : 18 ≤ 20)
      Erdos758.ramseyProperty_four_four_eighteen) G
  exact ⟨S, hS, hs⟩

#print axioms degree_seven_or_eight
#print axioms exists_homogeneous_four_twenty

end JSP000622.Certificate
