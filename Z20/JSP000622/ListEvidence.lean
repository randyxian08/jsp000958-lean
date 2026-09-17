import JSP000622.CertificateKernel

namespace JSP000622.Certificate

/-- Validity of two certificate lists composes without inspecting their elements.
This small lemma prevents the case splitter from accidentally unfolding concrete
rule records when append-associated disjunctions have different shapes. -/
theorem valid_append {α : Type*} {P : α → Prop} {xs ys : List α}
    (hx : ∀ x ∈ xs, P x) (hy : ∀ x ∈ ys, P x) :
    ∀ x ∈ xs ++ ys, P x := by
  intro x h
  rcases List.mem_append.mp h with h | h
  · exact hx x h
  · exact hy x h

#print axioms valid_append

end JSP000622.Certificate
