import JSP000622.Transport

namespace JSP000622.Certificate

open SimpleGraph

/-- A fixed old graph with all edges to one new vertex left as independent variables. -/
def extensionSymbols (n code : ℕ) : Symbols (n + 1) := fun a b =>
  Fin.lastCases
    (Fin.lastCases (.fixed false) (fun j => .variable j.val) b)
    (fun i => Fin.lastCases (.variable i.val)
      (fun j => .fixed (codeEdge n code i j)) b) a

/-- Every actual extension supplies a valuation of the new-vertex edges. -/
def extensionValuation {n : ℕ} (G : SimpleGraph (Fin (n + 1))) : Sat.Valuation :=
  fun i => if hi : i < n then G.Adj (Fin.castSucc ⟨i, hi⟩) (Fin.last n) else False

/-- No graph-to-SAT encoding assumption is needed: an arbitrary extension realizes the symbols. -/
theorem realizes_extension {n : ℕ} (G : SimpleGraph (Fin (n + 1))) (code : ℕ)
    (old : ∀ i j : Fin n, G.Adj i.castSucc j.castSucc ↔ (codeGraph n code).Adj i j) :
    Realizes G (extensionSymbols n code) (extensionValuation G) := by
  intro a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · intro b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · intro h
      exact (h rfl).elim
    · intro h
      simp [extensionSymbols, extensionValuation, Atom.eval, SimpleGraph.adj_comm]
  · intro b
    refine Fin.lastCases ?_ (fun j => ?_) b
    · intro h
      simp [extensionSymbols, extensionValuation, Atom.eval]
    · intro h
      have hij : i ≠ j := fun he => h (congrArg Fin.castSucc he)
      simpa [extensionSymbols, Atom.eval, codeGraph, hij] using old i j

/-- The empty graph starts the catalog induction without an enumeration assumption. -/
theorem classified_zero (G : SimpleGraph (Fin 0)) : Classified G [0] := by
  refine ⟨0, by simp, ⟨{ toEquiv := Equiv.refl _, map_rel_iff' := ?_ }⟩⟩
  intro a
  exact Fin.elim0 a

/-- Complete coverage at order n plus complete extension certificates gives coverage at n+1.

This statement is about every labelled graph. Isomorphism search is only used to
produce witnesses for the finite `step` input; no canonical-labelling algorithm
is assumed correct.
-/
theorem classified_step {n k l : ℕ} (oldCatalog newCatalog : List ℕ)
    (base : ∀ H : SimpleGraph (Fin n), H.CliqueFree k ∧ H.IndepSetFree l →
      Classified H oldCatalog)
    (step : ∀ code ∈ oldCatalog, ∀ H : SimpleGraph (Fin (n + 1)), ∀ v : Sat.Valuation,
      Realizes H (extensionSymbols n code) v →
      H.CliqueFree k ∧ H.IndepSetFree l → Classified H newCatalog)
    (G : SimpleGraph (Fin (n + 1))) (free : G.CliqueFree k ∧ G.IndepSetFree l) :
    Classified G newCatalog := by
  classical
  let inclusion : Fin n ↪ Fin (n + 1) :=
    ⟨Fin.castSucc, fun _ _ he => Fin.ext (congrArg Fin.val he)⟩
  let oldG : SimpleGraph (Fin n) := G.comap inclusion
  have oldFree : oldG.CliqueFree k ∧ oldG.IndepSetFree l :=
    ramseyFree_comap G inclusion free
  obtain ⟨code, hcode, ⟨e⟩⟩ := base oldG oldFree
  let p : Equiv.Perm (Fin (n + 1)) := extendPerm e.symm.toEquiv
  let H : SimpleGraph (Fin (n + 1)) := G.comap p
  have old : ∀ i j : Fin n, H.Adj i.castSucc j.castSucc ↔ (codeGraph n code).Adj i j := by
    intro i j
    change G.Adj (p i.castSucc) (p j.castSucc) ↔ _
    simp only [p, extendPerm_castSucc]
    change oldG.Adj (e.symm i) (e.symm j) ↔ _
    exact e.symm.map_adj_iff
  have freeH : H.CliqueFree k ∧ H.IndepSetFree l :=
    ramseyFree_comap G p.toEmbedding free
  obtain ⟨target, htarget, ⟨eH⟩⟩ := step code hcode H (extensionValuation H)
    (realizes_extension H code old) freeH
  exact ⟨target, htarget, ⟨(comapIso G p).symm.trans eH⟩⟩

#print axioms classified_step

end JSP000622.Certificate
