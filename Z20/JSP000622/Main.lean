/-
JSP-000622 / Erdős 758: z(20) = 6.

The final declarations below have no certificate, classification, or packing
hypotheses. Their validity still requires a successful build and axiom audit
of this complete import closure; writing these declarations is not verification.

The original two-core argument and SAT certificates come from the pinned
ipitchford/z20-cochromatic candidate. The imported small-order Lean proof comes
from the pinned plby/lean-proofs formalization. See the provenance records.
-/
import JSP000622.Foundations
import JSP000622.FiniteEvidence

namespace JSP000622

open Erdos758

/-- Every twenty-vertex graph has two disjoint homogeneous four-sets. -/
theorem two_disjoint_homogeneous_fours (G : SimpleGraph (Fin 20)) : TwoFours G := by
  exact FiniteEvidence.packing_twenty G

/-- The uniform upper bound, quantified over all labelled twenty-vertex simple graphs. -/
theorem every_twenty_vertex_graph_colorable_six (G : SimpleGraph (Fin 20)) :
    CochromaticColorable G 6 :=
  colorable_six_of_two_fours G (two_disjoint_homogeneous_fours G)

/-- The target theorem. No unproved finite-evidence assumptions occur in its type. -/
theorem z_twenty_eq_six : z 20 = 6 :=
  z_twenty_eq_six_of_two_fours two_disjoint_homogeneous_fours

/-- The extremal parameter is literally the maximum of individual cochromatic numbers. -/
theorem maximum_cochromatic_twenty_eq_six :
    (Finset.univ : Finset (SimpleGraph (Fin 20))).sup cochromaticNumber = 6 := by
  rw [← z_eq_max_cochromaticNumber]
  exact z_twenty_eq_six

/-- At least one twenty-vertex graph cannot be partitioned into five homogeneous classes. -/
theorem exists_twenty_vertex_graph_not_colorable_five :
    ∃ G : SimpleGraph (Fin 20), ¬CochromaticColorable G 5 := by
  classical
  by_contra h
  have allFive : ∀ G : SimpleGraph (Fin 20), CochromaticColorable G 5 := by
    intro G
    by_contra hG
    exact h ⟨G, hG⟩
  have hz := z_le allFive
  rw [z_twenty_eq_six] at hz
  omega

/-- The maximum is attained by an actual graph. -/
theorem exists_twenty_vertex_graph_cochromatic_six :
    ∃ G : SimpleGraph (Fin 20), cochromaticNumber G = 6 := by
  obtain ⟨G, hG⟩ := exists_twenty_vertex_graph_not_colorable_five
  refine ⟨G, ?_⟩
  have upper : cochromaticNumber G ≤ 6 :=
    (cochromaticNumber_le_iff G 6).mpr (every_twenty_vertex_graph_colorable_six G)
  have lower : ¬cochromaticNumber G ≤ 5 :=
    fun h => hG ((cochromaticNumber_le_iff G 5).mp h)
  omega

/-- The upper bound is independent of vertex labels and applies to any finite vertex type. -/
theorem colorable_six_of_card_twenty {V : Type*} [Fintype V]
    (hcard : Fintype.card V = 20) (G : SimpleGraph V) : CochromaticColorable G 6 :=
  colorable_of_card_eq hcard every_twenty_vertex_graph_colorable_six G

/-- Direct upper-bound and sharpness statement, without using the abbreviation `z`. -/
theorem JSP_000622 :
    (∀ G : SimpleGraph (Fin 20), CochromaticColorable G 6) ∧
    (∃ G : SimpleGraph (Fin 20), ¬CochromaticColorable G 5) :=
  ⟨every_twenty_vertex_graph_colorable_six, exists_twenty_vertex_graph_not_colorable_five⟩

#print axioms z_twenty_eq_six
#print axioms maximum_cochromatic_twenty_eq_six
#print axioms colorable_six_of_card_twenty
#print axioms JSP_000622

end JSP000622
