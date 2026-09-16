import JSP000622.ClassificationKernel

namespace JSP000622.Certificate

open SimpleGraph

/-- Relabelling a graph by an equivalence gives a graph isomorphism. -/
def comapIso {V W : Type*} (G : SimpleGraph W) (e : V ≃ W) : G.comap e ≃g G where
  toEquiv := e
  map_rel_iff' := by intro a b; rfl

/-- Clique obstructions pass to every injectively induced graph. -/
theorem cliqueFree_comap {V W : Type*} (G : SimpleGraph W) (f : V ↪ W)
    {k : ℕ} (h : G.CliqueFree k) : (G.comap f).CliqueFree k := by
  classical
  intro S hS
  apply h (S.map f)
  refine ⟨?_, by simpa using hS.card_eq⟩
  intro u hu v hv huv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
  exact hS.isClique ha hb (fun he => huv (congrArg f he))

/-- Independent-set obstructions pass to every injectively induced graph. -/
theorem indepSetFree_comap {V W : Type*} (G : SimpleGraph W) (f : V ↪ W)
    {k : ℕ} (h : G.IndepSetFree k) : (G.comap f).IndepSetFree k := by
  classical
  intro S hS
  apply h (S.map f)
  refine ⟨?_, by simpa using hS.card_eq⟩
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv huv
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
  have hi := hS.isIndepSet
  rw [SimpleGraph.isIndepSet_iff] at hi
  exact hi ha hb (fun he => huv (congrArg f he))

theorem ramseyFree_comap {V W : Type*} (G : SimpleGraph W) (f : V ↪ W)
    {k l : ℕ} (h : G.CliqueFree k ∧ G.IndepSetFree l) :
    (G.comap f).CliqueFree k ∧ (G.comap f).IndepSetFree l :=
  ⟨cliqueFree_comap G f h.1, indepSetFree_comap G f h.2⟩

/-- The complement exchanges the two Ramsey obstruction parameters. -/
theorem ramseyFree_compl {V : Type*} (G : SimpleGraph V) {k l : ℕ}
    (h : G.CliqueFree k ∧ G.IndepSetFree l) :
    Gᶜ.CliqueFree l ∧ Gᶜ.IndepSetFree k := by
  constructor
  · simpa only [SimpleGraph.cliqueFree_compl] using h.2
  · simpa only [SimpleGraph.indepSetFree_compl] using h.1

/-- A homogeneous set remains homogeneous in the complementary graph. -/
theorem Homogeneous.compl {V : Type*} {G : SimpleGraph V} {S : Finset V}
    (h : Homogeneous G S) : Homogeneous Gᶜ S := by
  rcases h with hc | hi
  · right
    intro u hu v hv huv hcompl
    simpa [SimpleGraph.compl_adj, hc u hu v hv huv, huv] using hcompl
  · left
    intro u hu v hv huv
    simpa [SimpleGraph.compl_adj, huv] using hi u hu v hv huv

theorem TwoFours.compl {V : Type*} {G : SimpleGraph V} (h : TwoFours G) :
    TwoFours Gᶜ := by
  obtain ⟨S, T, hS, hT, hd, hs, ht⟩ := h
  exact ⟨S, T, hS, hT, hd, hs.compl, ht.compl⟩

/-- Complementation also preserves graph isomorphisms. -/
def complIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Gᶜ ≃g Hᶜ where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro a b
    simp only [SimpleGraph.compl_adj, e.map_adj_iff, e.injective.ne_iff]

/-- An explicit isomorphism transports all six pieces of the packing assertion. -/
theorem TwoFours.map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (h : TwoFours G) : TwoFours H := by
  classical
  let f : V ↪ W := e.toEquiv.toEmbedding
  have hmap : ∀ S : Finset V, Homogeneous G S → Homogeneous H (S.map f) := by
    intro S hs
    rcases hs with hc | hi
    · left
      intro u hu v hv huv
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      apply e.map_adj_iff.mpr
      exact hc a ha b hb (fun he => huv (congrArg f he))
    · right
      intro u hu v hv huv hadj
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hu
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hv
      apply hi a ha b hb (fun he => huv (congrArg f he))
      exact e.map_adj_iff.mp hadj
  obtain ⟨S, T, hS, hT, hd, hs, ht⟩ := h
  refine ⟨S.map f, T.map f, by simpa using hS, by simpa using hT, ?_, hmap S hs, hmap T ht⟩
  rw [Finset.disjoint_left]
  intro w hwS hwT
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hwS
  obtain ⟨b, hb, he⟩ := Finset.mem_map.mp hwT
  have : b = a := f.injective he
  subst b
  exact Finset.disjoint_left.mp hd ha hb

/-- A permutation of the old vertices, extended by fixing the new last vertex. -/
def extendPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.lastCases (Fin.last n) (fun a => (e a).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun a => (e.symm a).castSucc)
  left_inv a := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp
    · simp
  right_inv a := by
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simp
    · simp

@[simp] theorem extendPerm_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    extendPerm e (Fin.last n) = Fin.last n := by simp [extendPerm]

@[simp] theorem extendPerm_castSucc {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    extendPerm e i.castSucc = (e i).castSucc := by simp [extendPerm]

#print axioms TwoFours.map
#print axioms TwoFours.compl
#print axioms ramseyFree_comap

end JSP000622.Certificate
