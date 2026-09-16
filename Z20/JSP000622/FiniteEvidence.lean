/-
The finite evidence records are instantiated entirely by theorem references.
This is not an axiom list: the final build must compile every imported certificate.
-/
import JSP000622.R34Seven
import JSP000622.R34Eight
import JSP000622.Class16Templates
import JSP000622.CoreTemplates
import JSP000622.NormalizeTwenty

namespace JSP000622.FiniteEvidence

open Certificate

/-- All finite inputs to the sixteen-vertex classification, with proofs. -/
def sixteen : SixteenEvidence where
  small7 := FiniteData.small7
  small8 := FiniteData.small8
  cores := FiniteData.cores
  complete7 := fun G h => R34Seven.complete G h
  complete8 := fun G h => R34Eight.complete G h
  normalized := FiniteBridges.classify_normalized
  complementClosed := FiniteData.complement_closed

/-- Both fixed-core packing proofs, combined with the complete classification. -/
def twenty : TwentyEvidence where
  classification := sixteen
  corePacking := FiniteBridges.packing_normalized

/-- There is no unproved classification hypothesis in this theorem. -/
theorem complete_sixteen (G : SimpleGraph (Fin 16))
    (h : G.CliqueFree 4 ∧ G.IndepSetFree 4) : Classified G FiniteData.cores :=
  classify_sixteen sixteen G h

/-- The closed twenty-vertex packing theorem, not conditional on supplied evidence. -/
theorem packing_twenty (G : SimpleGraph (Fin 20)) : Certificate.TwoFours G :=
  packing_twenty_of_evidence twenty G

#print axioms complete_sixteen
#print axioms packing_twenty

end JSP000622.FiniteEvidence
