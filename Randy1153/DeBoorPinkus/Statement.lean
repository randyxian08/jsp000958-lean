import Randy1153.DeBoorPinkus.NodeSpace

/-!
# Exact de Boor--Pinkus theorem interfaces (unproved propositions)

This file fixes the statements that the later source formalization must
prove.  It does **not** assert them as theorems or axioms.  Each boss result is
a definition of a proposition; an eventual theorem must construct a term of
that proposition from the interlacing, Jacobian, boundary, and global
topology developed in subsequent modules.

With `d` interior nodes there are `d + 1` gap heights.  The source's map
`Γ` has `d` coordinates, formed by consecutive height differences.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Consecutive gap-height differences, the map called `Γ` in the plan and
`Γ`/`r` (depending on OCR) in source Theorem 1. -/
def gapDifference {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i => nodes.height i.succ - nodes.height i.castSucc

/-- All gap heights of an endpoint-fixed array agree. -/
def Equioscillates {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Prop :=
  ∀ i j : Fin (d + 1), nodes.height i = nodes.height j

/-- Source Theorem 1 in the topology induced by the interior coordinates.

This is only a proposition definition.  In particular, no local-Jacobian
claim is being silently promoted to a global homeomorphism. -/
def GapDifferenceHomeomorphismStatement (d : ℕ) (A B : ℝ) : Prop :=
  AdmissibleInterval A B →
    IsHomeomorph (gapDifference : EndpointArray d A B → Fin d → ℝ)

/-- Exact coordinatewise comparison/rigidity statement from source Theorem 2.
The polarity is important: if every gap of `s` is no higher than the
corresponding gap of `t`, the arrays are equal. -/
def GapHeightLeRigidityStatement (d : ℕ) (A B : ℝ) : Prop :=
  ∀ s t : EndpointArray d A B,
    (∀ i : Fin (d + 1), s.height i ≤ t.height i) → s = t

/-- Exact existence and uniqueness interface for the equioscillating
endpoint array. -/
def ExistsUniqueEquioscillatingStatement (d : ℕ) (A B : ℝ) : Prop :=
  AdmissibleInterval A B →
    ∃! nodes : EndpointArray d A B, Equioscillates nodes

/-- The only source package consumed by the later block-collapse bridge.
Keeping it as a structure makes dependency status explicit: no inhabitant is
provided in this declaration file. -/
structure ComparisonPackage (d : ℕ) (A B : ℝ) : Prop where
  gapHeight_le_rigidity : GapHeightLeRigidityStatement d A B
  exists_unique_equioscillating : ExistsUniqueEquioscillatingStatement d A B

/-!
The eventual exported theorem surface, once proved, is deliberately reserved
to have the following shapes:

```lean
theorem gapDifference_homeomorph :
    GapDifferenceHomeomorphismStatement d A B

theorem gapHeight_le_rigidity :
    GapHeightLeRigidityStatement d A B

theorem exists_unique_equioscillating :
    ExistsUniqueEquioscillatingStatement d A B
```

No declaration with one of these theorem names appears here, so downstream
code cannot consume an unproved boss result.
-/

end

end Randy1153.DeBoorPinkus
