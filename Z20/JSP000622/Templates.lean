import JSP000622.Transport
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.VecNotation

namespace JSP000622.Certificate

open SimpleGraph

abbrev Split16 := Fin 1 ⊕ (Fin 7 ⊕ Fin 8)

def index16 : Split16 ≃ Fin 16 :=
  (Equiv.sumCongr (Equiv.refl (Fin 1))
    (finSumFinEquiv : Fin 7 ⊕ Fin 8 ≃ Fin 15)).trans
    (finSumFinEquiv : Fin 1 ⊕ Fin 15 ≃ Fin 16)

def root16 : Fin 16 := index16 (.inl 0)
def near16 (a : Fin 7) : Fin 16 := index16 (.inr (.inl a))
def far16 (a : Fin 8) : Fin 16 := index16 (.inr (.inr a))

@[simp] theorem root16_eq_zero : root16 = 0 := rfl

/-- The root, its seven neighbours and its eight non-neighbours. -/
def template16 (code7 code8 : ℕ) : Symbols 16 := fun u v =>
  match index16.symm u, index16.symm v with
  | .inl _, .inl _ => .fixed false
  | .inl _, .inr (.inl _) => .fixed true
  | .inr (.inl _), .inl _ => .fixed true
  | .inl _, .inr (.inr _) => .fixed false
  | .inr (.inr _), .inl _ => .fixed false
  | .inr (.inl a), .inr (.inl b) => .fixed (decide ((codeGraph 7 code7).Adj a b))
  | .inr (.inr a), .inr (.inr b) => .fixed (decide ((codeGraph 8 code8)ᶜ.Adj a b))
  | .inr (.inl a), .inr (.inr b) => .variable (8 * a.val + b.val)
  | .inr (.inr b), .inr (.inl a) => .variable (8 * a.val + b.val)

def index20 : Fin 4 ⊕ Fin 16 ≃ Fin 20 := finSumFinEquiv
def left20 (a : Fin 4) : Fin 20 := index20 (.inl a)
def right20 (a : Fin 16) : Fin 20 := index20 (.inr a)

/-- An outer clique on four vertices joined arbitrarily to a fixed sixteen-vertex core. -/
def template20 (code : ℕ) : Symbols 20 := fun u v =>
  match index20.symm u, index20.symm v with
  | .inl a, .inl b => .fixed (decide (a ≠ b))
  | .inr a, .inr b => .fixed (decide ((codeGraph 16 code).Adj a b))
  | .inl a, .inr b => .variable (16 * a.val + b.val)
  | .inr b, .inl a => .variable (16 * a.val + b.val)

/-- A propositional valuation of the independently variable cross edges. -/
def rowValuation {V : Type*} {m n : ℕ} (G : SimpleGraph V)
    (left : Fin m → V) (right : Fin n → V) : Sat.Valuation := fun t =>
  ∃ a : Fin m, ∃ b : Fin n, t = n * a.val + b.val ∧ G.Adj (left a) (right b)

theorem rowValuation_eight {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (left : Fin m → V) (right : Fin 8 → V) (a : Fin m) (b : Fin 8) :
    rowValuation G left right (8 * a.val + b.val) ↔ G.Adj (left a) (right b) := by
  constructor
  · rintro ⟨i, j, h, hadj⟩
    have hb := b.isLt
    have hj := j.isLt
    have hi : i.val = a.val := by omega
    have hjb : j.val = b.val := by omega
    have hi' : i = a := Fin.ext hi
    have hj' : j = b := Fin.ext hjb
    simpa [hi', hj'] using hadj
  · intro h
    exact ⟨a, b, rfl, h⟩

theorem rowValuation_sixteen {V : Type*} {m : ℕ} (G : SimpleGraph V)
    (left : Fin m → V) (right : Fin 16 → V) (a : Fin m) (b : Fin 16) :
    rowValuation G left right (16 * a.val + b.val) ↔ G.Adj (left a) (right b) := by
  constructor
  · rintro ⟨i, j, h, hadj⟩
    have hb := b.isLt
    have hj := j.isLt
    have hi : i.val = a.val := by omega
    have hjb : j.val = b.val := by omega
    have hi' : i = a := Fin.ext hi
    have hj' : j = b := Fin.ext hjb
    simpa [hi', hj'] using hadj
  · intro h
    exact ⟨a, b, rfl, h⟩

/-- The symbolic sixteen-vertex template matches the actual graph block by block. -/
theorem realizes_template16 (G : SimpleGraph (Fin 16)) (code7 code8 : ℕ)
    (hrootN : ∀ a : Fin 7, G.Adj root16 (near16 a))
    (hrootF : ∀ a : Fin 8, ¬G.Adj root16 (far16 a))
    (hnear : ∀ a b : Fin 7, G.Adj (near16 a) (near16 b) ↔ (codeGraph 7 code7).Adj a b)
    (hfar : ∀ a b : Fin 8, G.Adj (far16 a) (far16 b) ↔ (codeGraph 8 code8)ᶜ.Adj a b) :
    Realizes G (template16 code7 code8) (rowValuation G near16 far16) := by
  intro u v huv
  obtain ⟨a, rfl⟩ := index16.surjective u
  obtain ⟨b, rfl⟩ := index16.surjective v
  rcases a with a | (a | a) <;> rcases b with b | (b | b)
  all_goals simp only [template16, Equiv.symm_apply_apply, Atom.eval]
  · fin_cases a
    fin_cases b
    simp
  · fin_cases a
    simpa [root16, near16] using hrootN b
  · fin_cases a
    simpa [root16, far16] using hrootF b
  · fin_cases b
    simpa [root16, near16, SimpleGraph.adj_comm] using hrootN a
  · simpa [near16] using hnear a b
  · exact (rowValuation_eight G near16 far16 a b).symm
  · fin_cases b
    simpa [root16, far16, SimpleGraph.adj_comm] using hrootF a
  · rw [rowValuation_eight]
    exact G.adj_comm
  · simpa [far16] using hfar a b

/-- The symbolic twenty-vertex template matches the actual clique/core split. -/
theorem realizes_template20 (G : SimpleGraph (Fin 20)) (code : ℕ)
    (hleft : ∀ a b : Fin 4, G.Adj (left20 a) (left20 b) ↔ a ≠ b)
    (hright : ∀ a b : Fin 16, G.Adj (right20 a) (right20 b) ↔ (codeGraph 16 code).Adj a b) :
    Realizes G (template20 code) (rowValuation G left20 right20) := by
  intro u v huv
  obtain ⟨a, rfl⟩ := index20.surjective u
  obtain ⟨b, rfl⟩ := index20.surjective v
  rcases a with a | a <;> rcases b with b | b
  all_goals simp only [template20, Equiv.symm_apply_apply, Atom.eval]
  · simpa [left20] using hleft a b
  · exact (rowValuation_sixteen G left20 right20 a b).symm
  · rw [rowValuation_sixteen]
    exact G.adj_comm
  · simpa [right20] using hright a b

#print axioms realizes_template16
#print axioms realizes_template20

end JSP000622.Certificate
