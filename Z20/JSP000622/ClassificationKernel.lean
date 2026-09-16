import JSP000622.CertificateKernel

namespace JSP000622.Certificate

open SimpleGraph

def codeEdge (n code : ℕ) (u w : Fin n) : Bool :=
  code.testBit (min u.val w.val * n + max u.val w.val)

/-- The dense upper-triangle bit code describes an actual simple graph. -/
def codeGraph (n code : ℕ) : SimpleGraph (Fin n) where
  Adj u w := u ≠ w ∧ codeEdge n code u w = true
  symm := ⟨by
    intro u w h
    exact ⟨Ne.symm h.1, by simpa [codeEdge, min_comm, max_comm] using h.2⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

instance (n code : ℕ) : DecidableRel (codeGraph n code).Adj := fun u w =>
  inferInstanceAs (Decidable (u ≠ w ∧ codeEdge n code u w = true))

inductive ClassWitness (n : ℕ) where
  | forbidden (m : ℕ) (vertices : Fin m → Fin n) (color : Bool)
  | isomorphic (code : ℕ) (mapping : Fin n → Fin n)

structure ClassRule (n : ℕ) where
  clause : List Sat.Literal
  witness : ClassWitness n

def ClassRule.Valid {n : ℕ} (s : Symbols n) (k l : ℕ)
    (targets : List ℕ) (r : ClassRule n) : Prop :=
  match r.witness with
  | .forbidden m q color =>
      m = (if color then k else l) ∧ Function.Injective q ∧
      (∀ a b, a ≠ b → Forces r.clause (s (q a) (q b)) color)
  | .isomorphic code p =>
      code ∈ targets ∧ Function.Injective p ∧
      (∀ a b, a ≠ b → Forces r.clause (s a b) (decide ((codeGraph n code).Adj (p a) (p b))))

instance {n : ℕ} (s : Symbols n) (k l : ℕ) (targets : List ℕ)
    (r : ClassRule n) : Decidable (r.Valid s k l targets) := by
  unfold ClassRule.Valid
  cases r.witness <;> unfold Function.Injective <;> infer_instance

def Classified {n : ℕ} (G : SimpleGraph (Fin n)) (targets : List ℕ) : Prop :=
  ∃ code ∈ targets, Nonempty (G ≃g codeGraph n code)

theorem ClassRule.sound {n : ℕ} (G : SimpleGraph (Fin n)) (s : Symbols n)
    (v : Sat.Valuation) (hr : Realizes G s v) (k l : ℕ)
    (free : G.CliqueFree k ∧ G.IndepSetFree l) (targets : List ℕ)
    (r : ClassRule n) (h : r.Valid s k l targets) (hf : AllFalse v r.clause) :
    Classified G targets := by
  classical
  obtain ⟨c, w⟩ := r
  cases w with
  | forbidden m q color =>
    rcases h with ⟨hm, hq, hforce⟩
    let S : Finset (Fin n) := Finset.univ.image q
    have hcard : S.card = m := by
      dsimp [S]
      rw [Finset.card_image_of_injective _ hq]
      simp
    have hedge : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → (G.Adj u w ↔ color = true) := by
      intro u hu w hw huw
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hw
      exact (hr (q a) (q b) huw).trans
        (forces_sound hf (hforce a b (fun he => huw (congrArg q he))))
    cases color with
    | true =>
      apply False.elim
      apply free.1 S
      refine ⟨?_, hcard.trans hm⟩
      intro u hu w hw huw
      exact (hedge u hu w hw huw).mpr rfl
    | false =>
      apply False.elim
      apply free.2 S
      refine ⟨?_, hcard.trans hm⟩
      rw [SimpleGraph.isIndepSet_iff]
      intro u hu w hw huw hadj
      have hh := (hedge u hu w hw huw).mp hadj
      cases hh
  | isomorphic code p =>
    rcases h with ⟨hcode, hp, hforce⟩
    have hedge : ∀ a b, G.Adj a b ↔ (codeGraph n code).Adj (p a) (p b) := by
      intro a b
      by_cases hab : a = b
      · subst b
        simp
      · have hh := (hr a b hab).trans (forces_sound hf (hforce a b hab))
        simpa only [decide_eq_true_eq] using hh
    let e : Fin n ≃ Fin n := Equiv.ofBijective p ⟨hp, Finite.surjective_of_injective hp⟩
    refine ⟨code, hcode, ⟨{ toEquiv := e, map_rel_iff' := ?_ }⟩⟩
    intro a b
    exact (hedge a b).symm

/-- The certificate proves coverage, not merely correctness of listed representatives. -/
theorem classified_of_refutation {n : ℕ} (s : Symbols n) (k l : ℕ)
    (targets : List ℕ) (rules : List (ClassRule n))
    (valid : ∀ r ∈ rules, r.Valid s k l targets)
    (unsat : Sat.Fmla.proof (rules.map ClassRule.clause) [])
    (G : SimpleGraph (Fin n)) (v : Sat.Valuation) (hr : Realizes G s v)
    (free : G.CliqueFree k ∧ G.IndepSetFree l) : Classified G targets := by
  classical
  by_contra hn
  apply unsat v
  constructor
  intro c hc
  obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hc
  apply satisfies_of_not_allFalse
  intro hf
  exact hn (r.sound G s v hr k l free targets (valid r hmem) hf)

#print axioms classified_of_refutation

end JSP000622.Certificate
