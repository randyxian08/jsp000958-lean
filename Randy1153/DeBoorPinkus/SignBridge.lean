import Randy1153.DeBoorPinkus.Minors
import Randy1153.DeBoorPinkus.Orientation

/-!
# Sign-convention bridge for the height-Jacobian maximal minors

`Minors` proves that the zero-based row cofactors
`(-1)^omitted * deletedRowMinor` all have one strict sign.  `Orientation`
uses the source's one-based exponent `(-1)^(omitted+1)` and records the
remaining common sign explicitly as `±1`.  This file proves that these are
the same orientation statement, including dimension zero.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Convert the unconditional alternating-cofactor convention from
`Minors` to the explicit `±1`, one-based convention used by `Orientation`.

If all zero-based cofactors are negative, the witness is `+1`; if they are
positive, the witness is `-1`.  The proof is dimension-free, so the unique
minor in dimension zero is handled without a separate vacuous case. -/
theorem coherentHeightMaximalMinorSigns_of_alternating
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B)
    (h : AlternatingHeightMaximalMinorSigns nodes) :
    CoherentHeightMaximalMinorSigns nodes := by
  rcases h with hneg | hpos
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro omitted
    have hstrict := neg_pos.mpr (hneg omitted)
    calc
      0 < -((-1 : ℝ) ^ omitted.val *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted) := hstrict
      _ = (1 : ℝ) * (-1 : ℝ) ^ (omitted.val + 1) *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
        rw [pow_succ]
        ring
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro omitted
    calc
      0 < (-1 : ℝ) ^ omitted.val *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted :=
        hpos omitted
      _ = (-1 : ℝ) * (-1 : ℝ) ^ (omitted.val + 1) *
          deletedRowMinor (gapHeightJacobianModel nodes) omitted := by
        rw [pow_succ]
        ring

/-- Unconditional coherent maximal-minor orientation in the canonical
`Orientation` convention. -/
theorem coherentHeightMaximalMinorSigns_unconditional
    {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    CoherentHeightMaximalMinorSigns nodes :=
  coherentHeightMaximalMinorSigns_of_alternating nodes
    (alternatingHeightMaximalMinorSigns nodes)

end

end Randy1153.DeBoorPinkus
