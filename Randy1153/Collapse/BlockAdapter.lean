import Randy1153.Collapse.Block
import Randy1153.DeBoorPinkus.Package

/-!
# Arbitrary-cardinality wrapper for block localization

The core collapse theorem is naturally parameterized by a full array of
cardinality `q+2` and a block pattern with `d+2` nodes.  Dense-block
applications instead begin with arbitrary cardinalities `n,m` together with
proofs `2 ≤ n` and `2 ≤ m`.  This file performs exactly those two
reparameterizations, dispatches the four placements, and exposes the global
gap index as `block.start + g.val`.
-/

namespace Randy1153
namespace Collapse

open Randy1153.DeBoorPinkus

noncomputable section

namespace ConsecutiveBlock

/-- The global nodal gap corresponding to a local gap of a consecutive
block. -/
def gapIndex {n m : ℕ} (block : ConsecutiveBlock n m)
    (g : Fin (m - 1)) : Fin (n - 1) :=
  ⟨block.start + g.val, by
    have hg := g.isLt
    have hfit := block.fits
    omega⟩

@[simp]
lemma gapIndex_val {n m : ℕ} (block : ConsecutiveBlock n m)
    (g : Fin (m - 1)) :
    (block.gapIndex g).val = block.start + g.val :=
  rfl

end ConsecutiveBlock

/-- Once a placement is supplied, the unconditional de Boor--Pinkus package
and the checked `Spec` theorem give the desired internal block gap. -/
private theorem exists_blockGap_ge_equioscHeight_of_placement
    {q d : ℕ} (nodes : OrderedNodes (q + 2))
    (block : ConsecutiveBlock (q + 2) (d + 2))
    (pattern : EndpointArray d 0 1) (hequi : Equioscillates pattern)
    (place : Placement) (hplace : place.Valid block) :
    ∃ g : Fin (d + 1),
      pattern.height (0 : Fin (d + 1)) ≤
        gapHeight nodes (block.gapIndex g) := by
  let spec : Spec (q + 2) d :=
    { nodes := nodes
      block := block
      pattern := pattern
      placement := place
      placement_valid := hplace }
  obtain ⟨g, hg⟩ := spec.exists_block_gap_ge_equioscHeight
    (comparisonPackage q spec.sourceLeft spec.sourceRight) hequi
  refine ⟨g, ?_⟩
  simpa only [Spec.gapIndex, ConsecutiveBlock.gapIndex, spec] using hg

/-- General block-localization API.

For any consecutive `m`-node block in an ordered `n`-node array, an
equioscillating normalized `m`-node pattern forces one of the original
internal block gaps to have height at least the common pattern height.  The
returned global gap is literally indexed by `block.start + g.val`.
-/
theorem exists_consecutiveBlock_gap_ge_equioscHeight
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (nodes : OrderedNodes n) (block : ConsecutiveBlock n m)
    (pattern : EndpointArray (m - 2) 0 1)
    (hequi : Equioscillates pattern) :
    ∃ g : Fin (m - 1),
      pattern.height (⟨0, by omega⟩ : Fin ((m - 2) + 1)) ≤
        gapHeight nodes (block.gapIndex g) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, n = q + 2 :=
    ⟨n - 2, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, m = d + 2 :=
    ⟨m - 2, by omega⟩
  subst n
  subst m
  rcases placement_classification block with hfull | hleft | hright | hinterior
  · exact exists_blockGap_ge_equioscHeight_of_placement
      nodes block pattern hequi .full hfull
  · exact exists_blockGap_ge_equioscHeight_of_placement
      nodes block pattern hequi .leftEndpoint hleft
  · exact exists_blockGap_ge_equioscHeight_of_placement
      nodes block pattern hequi .rightEndpoint hright
  · exact exists_blockGap_ge_equioscHeight_of_placement
      nodes block pattern hequi .interior hinterior

end

end Collapse
end Randy1153
