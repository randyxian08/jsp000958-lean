import JSP000622.Templates

namespace JSP000622.Certificate

/-- Two injective maps with disjoint images give an injective map from their sum. -/
theorem sumElim_injective {A B C : Type*} (f : A → C) (g : B → C)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (hf h)
  · exact (hfg x y h).elim
  · exact (hfg y x h.symm).elim
  · exact congrArg Sum.inr (hg h)

/-- A complete finite chart may be relabelled to the standard vertex type. -/
noncomputable def chartPerm {S : Type*} {n : ℕ} (index : S ≃ Fin n)
    (f : S → Fin n) (hf : Function.Injective f) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (f ∘ index.symm)
    ⟨hf.comp index.symm.injective,
      Finite.surjective_of_injective (hf.comp index.symm.injective)⟩

@[simp] theorem chartPerm_apply_index {S : Type*} {n : ℕ} (index : S ≃ Fin n)
    (f : S → Fin n) (hf : Function.Injective f) (a : S) :
    chartPerm index f hf (index a) = f a := by
  change f (index.symm (index a)) = f a
  rw [index.symm_apply_apply]

#print axioms sumElim_injective
#print axioms chartPerm_apply_index

end JSP000622.Certificate
