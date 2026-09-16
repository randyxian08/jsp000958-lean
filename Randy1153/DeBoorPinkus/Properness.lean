import Randy1153.DeBoorPinkus.Boundary
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# From sequential boundary escape to properness

`Boundary` proves that every endpoint-array sequence with no convergent
subsequence has gap-difference norm tending to infinity.  This file supplies
the standard finite-dimensional topological bridge: conditional only on
continuity of `gapDifference`, compact target sets have compact preimages.

The proof does not identify sequential escape with properness by fiat.  It
uses the committed Euclidean homeomorphism of the endpoint-array simplex,
proves sequential compactness of the image of each compact preimage, and then
uses metrizability of the finite-dimensional function space.
-/

namespace Randy1153.DeBoorPinkus

open Filter Topology

noncomputable section

/-- A compact set in the finite-dimensional target has a uniform norm
bound.  This small wrapper keeps the contradiction in the properness proof
explicit. -/
lemma exists_norm_bound_of_isCompact {d : ℕ} {K : Set (Fin d → ℝ)}
    (hK : IsCompact K) :
    ∃ C : ℝ, ∀ y ∈ K, ‖y‖ ≤ C :=
  (isBounded_iff_forall_norm_le (s := K)).mp hK.isBounded

/-- Conditional compact-preimage bridge for `gapDifference`.

Continuity is used only to show that the limit of a convergent endpoint-array
subsequence remains in the preimage of the closed compact target set.  The
existence of the subsequence comes from the checked sequential boundary
escape theorem in `Boundary`. -/
theorem isCompact_preimage_gapDifference_of_continuous
    {d : ℕ} {A B : ℝ}
    (hcont : Continuous
      (gapDifference : EndpointArray d A B → Fin d → ℝ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    IsCompact
      ((gapDifference : EndpointArray d A B → Fin d → ℝ) ⁻¹' K) := by
  classical
  let S : Set (EndpointArray d A B) :=
    (gapDifference : EndpointArray d A B → Fin d → ℝ) ⁻¹' K
  by_cases hSne : S.Nonempty
  · let base : EndpointArray d A B := hSne.some
    have hAB : AdmissibleInterval A B := base.admissibleInterval
    let e : EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
      endpointArrayLogRatioHomeomorph hAB
    have himageSeq : IsSeqCompact (e '' S) := by
      intro z hz
      let nodes : ℕ → EndpointArray d A B := fun m ↦ e.symm (z m)
      have hnodesMem : ∀ m, nodes m ∈ S := by
        intro m
        obtain ⟨x, hxS, hx⟩ := hz m
        have hnodes : nodes m = x := by
          apply e.injective
          simp only [nodes, Homeomorph.apply_symm_apply, hx]
        simpa only [hnodes] using hxS
      have hnotNo : ¬ HasNoConvergentEndpointSubsequence nodes := by
        intro hno
        have hescape :=
          tendsto_norm_gapDifference_atTop_of_noConvergentEndpointSubsequence
            nodes hno
        obtain ⟨C, hC⟩ := exists_norm_bound_of_isCompact hK
        obtain ⟨m, hm⟩ := (hescape.eventually_ge_atTop (C + 1)).exists
        have hmem : gapDifference (nodes m) ∈ K := hnodesMem m
        linarith [hC (gapDifference (nodes m)) hmem]
      unfold HasNoConvergentEndpointSubsequence at hnotNo
      push_neg at hnotNo
      obtain ⟨φ, hφ, limit, hlim⟩ := hnotNo
      have hlimitS : limit ∈ S := by
        apply hK.isClosed.mem_of_tendsto
          ((hcont.tendsto limit).comp hlim)
        exact Eventually.of_forall fun m ↦ hnodesMem (φ m)
      refine ⟨e limit, ⟨limit, hlimitS, rfl⟩, φ, hφ, ?_⟩
      have heLim := (e.continuous.tendsto limit).comp hlim
      convert heLim using 1
      funext m
      exact (e.apply_symm_apply (z (φ m))).symm
    have himageCompact : IsCompact (e '' S) := himageSeq.isCompact
    have hSCompact : IsCompact S := e.isCompact_image.mp himageCompact
    exact hSCompact
  · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    change IsCompact S
    rw [hSempty]
    exact isCompact_empty

/-- The promised one-line packaging: once continuity of gap heights (and
hence of `gapDifference`) is available, the de Boor--Pinkus difference map is
proper. -/
theorem gapDifference_isProperMap_of_continuous
    {d : ℕ} {A B : ℝ}
    (hcont : Continuous
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, ?_⟩
  intro K hK
  exact isCompact_preimage_gapDifference_of_continuous hcont hK

/-- Ordinary proposition interface for the only remaining input.  No
inhabitant is asserted here; the active height/Jacobian lane may discharge it
without changing the properness proof. -/
def GapDifferenceContinuityStatement (d : ℕ) (A B : ℝ) : Prop :=
  Continuous (gapDifference : EndpointArray d A B → Fin d → ℝ)

/-- Continuity-to-properness packaging in the exact project-level proposition
language reserved by `Boundary`. -/
theorem gapDifference_topologicalProperness_of_continuity
    {d : ℕ} {A B : ℝ} :
    GapDifferenceContinuityStatement d A B →
      GapDifferenceTopologicalPropernessStatement d A B :=
  gapDifference_isProperMap_of_continuous

end

end Randy1153.DeBoorPinkus
