import Randy1153.DeBoorPinkus.Properness
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.Clopen

/-!
# The global-topology step in the de Boor--Pinkus argument

This file isolates the standard global inversion theorem needed after the
Jacobian and boundary arguments.  A proper local homeomorphism of a
finite-dimensional real vector space is a covering map.  Its image is both
open and closed, hence (because the target is connected) it is surjective.
A covering of a simply connected target by a connected total space has one
sheet, so the map is a homeomorphism.

The proof below spells out all three bridges.  In particular, it does not
replace properness by local injectivity or assume the desired global
bijectivity under another name.
-/

namespace Randy1153.DeBoorPinkus

open Function Topology

noncomputable section

/-! ## Proper local homeomorphisms are covering maps -/

/-- A proper local homeomorphism between Hausdorff spaces is a covering map.

Properness makes the map closed and makes each point fiber compact.  The
local charts make the fiber discrete; a compact discrete subset is finite,
which is precisely the finite-fiber input to Mathlib's evenly-covered
neighborhood constructor. -/
theorem isCoveringMap_of_isLocalHomeomorph_of_isProperMap
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [T2Space E] [T2Space X] {f : E → X}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsCoveringMap f := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  apply hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph
  · intro x hx
    have hdisc : IsDiscrete (f ⁻¹' {x}) :=
      IsDiscrete.of_openPartialHomeomorph f Set.Subset.rfl fun e he ↦ by
        obtain ⟨φ, heφ, hφ⟩ := hloc e
        exact ⟨φ, heφ, hφ.symm⟩
    exact (hproper.isCompact_preimage isCompact_singleton).finite hdisc
  · intro e he
    obtain ⟨φ, heφ, hφ⟩ := hloc e
    exact ⟨φ, heφ, hφ.symm⟩

/-! ## A connected covering of a simply connected space has one sheet -/

/-- A surjective covering map from a preconnected space to a nonempty,
simply connected, locally path-connected space is a homeomorphism.

The inverse is the unique lift of the identity map through the covering.  To
check the other inverse law, compare `s ∘ f` with the identity as two lifts
of `f`; connectedness of the total space and equality at the chosen basepoint
give equality everywhere. -/
theorem IsCoveringMap.isHomeomorph_of_surjective
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [PreconnectedSpace E] [Nonempty X]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X]
    {f : E → X} (hcover : IsCoveringMap f) (hsurj : Surjective f) :
    IsHomeomorph f := by
  let x₀ : X := Classical.arbitrary X
  obtain ⟨e₀, he₀⟩ := hsurj x₀
  let fid : C(X, X) := ContinuousMap.id X
  obtain ⟨s, hs, _⟩ :=
    hcover.existsUnique_continuousMap_lifts fid x₀ e₀ (by simpa [fid] using he₀)
  obtain ⟨hs₀, hfs⟩ := hs
  have hsf : (s : X → E) ∘ f = id := by
    refine hcover.eq_of_comp_eq
      (s.continuous.comp hcover.continuous) continuous_id ?_ e₀ ?_
    · funext e
      have hright := congrFun hfs (f e)
      simpa [fid, Function.comp_def] using hright
    · simpa [he₀] using hs₀
  rw [isHomeomorph_iff_exists_inverse]
  refine ⟨hcover.continuous, s, ?_, ?_, s.continuous⟩
  · intro e
    exact congrFun hsf e
  · intro x
    have hright := congrFun hfs x
    simpa [fid, Function.comp_def] using hright

/-! ## Euclidean global inversion -/

/-- The zero-dimensional case is completely elementary: `Fin 0 → ℝ` is a
singleton, so every local homeomorphism from it to itself is bijective. -/
theorem fin_zero_isHomeomorph_of_isLocalHomeomorph
    {f : (Fin 0 → ℝ) → (Fin 0 → ℝ)}
    (hloc : IsLocalHomeomorph f) : IsHomeomorph f := by
  have hinj : Injective f := fun _ _ _ ↦ Subsingleton.elim _ _
  have hsurj : Surjective f := fun y ↦ ⟨0, Subsingleton.elim _ _⟩
  exact (hloc.toHomeomorphOfBijective ⟨hinj, hsurj⟩).isHomeomorph

/-- A proper local homeomorphism of `Fin d → ℝ` is a global
homeomorphism.  The `d = 0` singleton case is dispatched explicitly; positive
dimensions use the covering-space argument. -/
theorem euclidean_isHomeomorph_of_isLocalHomeomorph_of_isProperMap
    {d : ℕ} {f : (Fin d → ℝ) → (Fin d → ℝ)}
    (hloc : IsLocalHomeomorph f) (hproper : IsProperMap f) :
    IsHomeomorph f := by
  cases d with
  | zero => exact fin_zero_isHomeomorph_of_isLocalHomeomorph hloc
  | succ d =>
    have hcover : IsCoveringMap f :=
      isCoveringMap_of_isLocalHomeomorph_of_isProperMap hloc hproper
    have hrangeOpen : IsOpen (Set.range f) := by
      simpa only [Set.image_univ] using hloc.isOpenMap Set.univ isOpen_univ
    have hrangeClosed : IsClosed (Set.range f) := hproper.isClosed_range
    have hrangeNonempty : (Set.range f).Nonempty :=
      ⟨f 0, 0, rfl⟩
    have hrange : Set.range f = Set.univ :=
      IsClopen.eq_univ ⟨hrangeClosed, hrangeOpen⟩ hrangeNonempty
    exact IsCoveringMap.isHomeomorph_of_surjective hcover
      (Set.range_eq_univ.mp hrange)

/-! ## Transporting the de Boor--Pinkus difference map -/

/-- The gap-difference map written in the global spacing/log-ratio chart. -/
def transportedGapDifference {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    (Fin d → ℝ) → (Fin d → ℝ) :=
  gapDifference ∘ (endpointArrayLogRatioHomeomorph hAB).symm

/-- Local-homeomorphism transport from endpoint arrays to the global
Euclidean chart. -/
theorem isLocalHomeomorph_transportedGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hloc : IsLocalHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsLocalHomeomorph (transportedGapDifference (d := d) hAB) := by
  exact hloc.comp (endpointArrayLogRatioHomeomorph (d := d) hAB).symm.isLocalHomeomorph

/-- Properness transport from endpoint arrays to the global Euclidean
chart. -/
theorem isProperMap_transportedGapDifference
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hproper : IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsProperMap (transportedGapDifference (d := d) hAB) := by
  exact hproper.comp (endpointArrayLogRatioHomeomorph (d := d) hAB).symm.isProperMap

/-- The exact global-topology packaging needed by the source theorem.  Once
the Jacobian lane supplies local homeomorphism and the boundary lane supplies
properness, no further global hypothesis is needed. -/
theorem gapDifference_isHomeomorph_of_localHomeomorph_of_proper
    {d : ℕ} {A B : ℝ} (hAB : AdmissibleInterval A B)
    (hloc : IsLocalHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ))
    (hproper : IsProperMap
      (gapDifference : EndpointArray d A B → Fin d → ℝ)) :
    IsHomeomorph
      (gapDifference : EndpointArray d A B → Fin d → ℝ) := by
  have htransport : IsHomeomorph (transportedGapDifference (d := d) hAB) :=
    euclidean_isHomeomorph_of_isLocalHomeomorph_of_isProperMap
      (isLocalHomeomorph_transportedGapDifference hAB hloc)
      (isProperMap_transportedGapDifference hAB hproper)
  have hchart : IsHomeomorph (endpointArrayLogRatioHomeomorph (d := d) hAB) :=
    (endpointArrayLogRatioHomeomorph (d := d) hAB).isHomeomorph
  have hcomp := htransport.comp hchart
  simpa only [transportedGapDifference, Function.comp_assoc,
    Homeomorph.symm_comp_self, Function.id_comp] using hcomp

/-- Ordinary proposition interface for the remaining local input.  No
inhabitant is asserted here. -/
def GapDifferenceLocalHomeomorphStatement (d : ℕ) (A B : ℝ) : Prop :=
  IsLocalHomeomorph
    (gapDifference : EndpointArray d A B → Fin d → ℝ)

/-- Project-level packaging into the reserved homeomorphism statement. -/
theorem gapDifference_homeomorphismStatement_of_localHomeomorph_of_proper
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B)
    (hproper : GapDifferenceTopologicalPropernessStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B := by
  intro hAB
  exact gapDifference_isHomeomorph_of_localHomeomorph_of_proper hAB hloc hproper

/-- Continuity plus the local-homeomorphism input suffices, using the checked
sequential boundary-escape-to-properness theorem. -/
theorem gapDifference_homeomorphismStatement_of_localHomeomorph_of_continuous
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B)
    (hcont : GapDifferenceContinuityStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph_of_proper hloc
    (gapDifference_topologicalProperness_of_continuity hcont)

/-- Final one-input topology interface.  A local homeomorphism is already
continuous, so the committed boundary-escape bridge supplies properness and
the global inversion theorem supplies the reserved source statement. -/
theorem gapDifference_homeomorphismStatement_of_localHomeomorph
    {d : ℕ} {A B : ℝ}
    (hloc : GapDifferenceLocalHomeomorphStatement d A B) :
    GapDifferenceHomeomorphismStatement d A B :=
  gapDifference_homeomorphismStatement_of_localHomeomorph_of_continuous
    hloc hloc.continuous

end

end Randy1153.DeBoorPinkus
