/-
Copyright (c) 2026. Released under Apache-2.0.
A semantic bridge from kernel-checked LRAT refutations to disjoint homogeneous sets.
The external SAT solver, encoder, parser and certificate generator are not axioms.
This module depends only on Mathlib, not on the twelve-vertex result.
-/
import Mathlib
import Mathlib.Tactic.Sat.FromLRAT

namespace JSP000622.Certificate

open SimpleGraph

deriving instance DecidableEq for Sat.Literal

inductive Atom where
  | fixed : Bool → Atom
  | variable : Nat → Atom
  deriving DecidableEq

def Atom.eval (v : Sat.Valuation) : Atom → Prop
  | .fixed b => b = true
  | .variable i => v i

abbrev Symbols (n : ℕ) := Fin n → Fin n → Atom

def Realizes {n : ℕ} (G : SimpleGraph (Fin n)) (s : Symbols n)
    (v : Sat.Valuation) : Prop :=
  ∀ a b, a ≠ b → (G.Adj a b ↔ Atom.eval v (s a b))

def AllFalse (v : Sat.Valuation) (c : List Sat.Literal) : Prop :=
  ∀ l ∈ c, v.neg l

/-- A falsified clause forces a symbolic edge to the indicated Boolean value. -/
def Forces (c : List Sat.Literal) (a : Atom) (b : Bool) : Prop :=
  match a with
  | .fixed d => d = b
  | .variable i => (if b then Sat.Literal.neg i else Sat.Literal.pos i) ∈ c

instance (c : List Sat.Literal) (a : Atom) (b : Bool) : Decidable (Forces c a b) := by
  cases a <;> unfold Forces <;> infer_instance

theorem forces_sound {v : Sat.Valuation} {c : List Sat.Literal} {a : Atom} {b : Bool}
    (hf : AllFalse v c) (h : Forces c a b) : (a.eval v ↔ b = true) := by
  cases a with
  | fixed d =>
    change d = b at h
    subst d
    rfl
  | «variable» i =>
    cases b with
    | false =>
      have hn : ¬v i := hf (.pos i) h
      simpa [Atom.eval] using hn
    | true =>
      have hp : v i := hf (.neg i) h
      simpa [Atom.eval] using hp

/-- This is the ordinary propositional meaning of a CNF clause. -/
theorem satisfies_of_not_allFalse (v : Sat.Valuation) (c : List Sat.Literal) :
    (AllFalse v c → False) → v.satisfies c := by
  induction c with
  | nil =>
    intro h
    exact h (fun _ hl => (List.not_mem_nil hl).elim)
  | cons l cs ih =>
    intro h hl
    apply ih
    intro hs
    apply h
    intro k hk
    rcases List.mem_cons.mp hk with hkl | hks
    · subst k
      exact hl
    · exact hs k hks

/-- A homogeneous finset, stated directly in the usual graph-theoretic language. -/
def Homogeneous {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  (∀ u ∈ S, ∀ w ∈ S, u ≠ w → G.Adj u w) ∨
  (∀ u ∈ S, ∀ w ∈ S, u ≠ w → ¬G.Adj u w)

def TwoFours {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ S T : Finset V, S.card = 4 ∧ T.card = 4 ∧ Disjoint S T ∧
    Homogeneous G S ∧ Homogeneous G T

abbrev Four (n : ℕ) := Fin 4 → Fin n

def Four.vertices {n : ℕ} (q : Four n) : Finset (Fin n) := Finset.univ.image q

theorem Four.card_vertices {n : ℕ} (q : Four n) (h : Function.Injective q) :
    q.vertices.card = 4 := by
  rw [Four.vertices, Finset.card_image_of_injective _ h]
  simp

structure PairRule (n : ℕ) where
  clause : List Sat.Literal
  first : Four n
  second : Four n
  firstColor : Bool
  secondColor : Bool

def PairRule.Valid {n : ℕ} (s : Symbols n) (r : PairRule n) : Prop :=
  Function.Injective r.first ∧ Function.Injective r.second ∧
  Disjoint r.first.vertices r.second.vertices ∧
  (∀ i j : Fin 4, i ≠ j → Forces r.clause (s (r.first i) (r.first j)) r.firstColor) ∧
  (∀ i j : Fin 4, i ≠ j → Forces r.clause (s (r.second i) (r.second j)) r.secondColor)

instance {n : ℕ} (s : Symbols n) (r : PairRule n) : Decidable (r.Valid s) := by
  unfold PairRule.Valid Function.Injective
  infer_instance

theorem homogeneous_of_forced_four {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Symbols n) (v : Sat.Valuation) (hr : Realizes G s v)
    (c : List Sat.Literal) (hf : AllFalse v c) (q : Four n) (b : Bool)
    (h : ∀ i j : Fin 4, i ≠ j → Forces c (s (q i) (q j)) b) :
    Homogeneous G q.vertices := by
  have he : ∀ u ∈ q.vertices, ∀ w ∈ q.vertices, u ≠ w → (G.Adj u w ↔ b = true) := by
    intro u hu w hw huw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    have hij : i ≠ j := fun hh => huw (congrArg q hh)
    exact (hr (q i) (q j) huw).trans (forces_sound hf (h i j hij))
  cases b with
  | false =>
    right
    intro u hu w hw huw hadj
    have := (he u hu w hw huw).mp hadj
    cases this
  | true =>
    left
    intro u hu w hw huw
    exact (he u hu w hw huw).mpr rfl

theorem PairRule.sound {n : ℕ} (G : SimpleGraph (Fin n)) (s : Symbols n)
    (v : Sat.Valuation) (hr : Realizes G s v) (r : PairRule n)
    (h : r.Valid s) (hf : AllFalse v r.clause) : TwoFours G := by
  rcases h with ⟨hi, hj, hd, ha, hb⟩
  exact ⟨r.first.vertices, r.second.vertices,
    r.first.card_vertices hi, r.second.card_vertices hj, hd,
    homogeneous_of_forced_four G s v hr r.clause hf r.first r.firstColor ha,
    homogeneous_of_forced_four G s v hr r.clause hf r.second r.secondColor hb⟩

/-- A genuine graph theorem follows from valid clause witnesses and an LRAT proof. -/
theorem twoFours_of_refutation {n : ℕ} (s : Symbols n) (rules : List (PairRule n))
    (valid : ∀ r ∈ rules, r.Valid s)
    (unsat : Sat.Fmla.proof (rules.map PairRule.clause) [])
    (G : SimpleGraph (Fin n)) (v : Sat.Valuation) (hr : Realizes G s v) : TwoFours G := by
  classical
  by_contra hn
  apply unsat v
  constructor
  intro c hc
  obtain ⟨r, hmem, rfl⟩ := List.mem_map.mp hc
  apply satisfies_of_not_allFalse
  intro hf
  exact hn (r.sound G s v hr (valid r hmem) hf)

#print axioms twoFours_of_refutation

end JSP000622.Certificate

open Lean Elab Term in
/-- Reconstruct the original CNF proof without expanding it into a huge disjunction.
The expected type still has to definitionally match the reconstructed formula. -/
elab "checked_from_lrat " cnf:term:max ppSpace lrat:term:max : term => do
  let c ← unsafe evalTerm String (mkConst ``String) cnf
  let p ← unsafe evalTerm String (mkConst ``String) lrat
  let name ← mkAuxName `z20_lrat
  let (_, _, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux c p name
  return proof
