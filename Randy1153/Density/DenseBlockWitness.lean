import Randy1153.Density.Asymptotic
import Randy1153.Density.ConsecutiveBlock
import Randy1153.Collapse.BlockAdapter
import Randy1153.DeBoorPinkus.Package

/-!
# A finite witness from the dense alternative

The central indices of an ordered array form a literal consecutive block.
When the density alternative holds and its denominator is no larger than the
ambient cardinality, that block has at least two nodes.  The unconditional
de Boor--Pinkus package therefore supplies a normalized equioscillating
pattern of the matching cardinality, and the arbitrary-block collapse
adapter places its common height below the height of an actual gap of the
original array.

This file turns that gap-height conclusion into a pointwise witness in the
original interval.  The last step uses compact attainment on the *same*
original nodal gap and the checked containment of every central-block gap in
`[a,b]`.
-/

namespace Randy1153.Density

open Set
open Randy1153.Collapse
open Randy1153.DeBoorPinkus

noncomputable section

/-- Under the dense alternative, once one density denominator fits in the
ambient cardinality, the central block contains at least two nodes. -/
lemma two_le_card_sparseIndices_of_dense {n K : ℕ}
    (nodes : OrderedNodes n) (a b : ℝ)
    (hden : densityDenominator K ≤ n)
    (hdense : DenseAt nodes.toNodeFamily a b K) :
    2 ≤ (sparseIndices nodes.toNodeFamily a b).card := by
  rw [denseAt_iff_div_lt_card] at hdense
  have hone : 1 ≤ n / densityDenominator K := by
    apply (Nat.le_div_iff_mul_le (densityDenominator_pos K)).2
    simpa only [one_mul] using hden
  omega

/-- The finite dense-block witness used by the asymptotic assembly.

Writing `m` for the number of central indices, the returned endpoint array
has exactly `m` nodes (`m - 2` interior nodes), is equioscillating, and its
common gap height is attained from below by the original Lebesgue function at
some point of `[a,b]`. -/
theorem exists_equioscillatingPattern_denseBlockWitness {n K : ℕ}
    (nodes : OrderedNodes n) {a b : ℝ} (hab : a < b)
    (hden : densityDenominator K ≤ n)
    (hdense : DenseAt nodes.toNodeFamily a b K) :
    let m := (sparseIndices nodes.toNodeFamily a b).card
    ∃ pattern : EndpointArray (m - 2) 0 1,
      Equioscillates pattern ∧
        ∃ t ∈ Set.Icc a b,
          pattern.height (⟨0, by omega⟩ : Fin ((m - 2) + 1)) ≤
            lebesgueFunction nodes.toNodeFamily t := by
  let m := (sparseIndices nodes.toNodeFamily a b).card
  have hm : 2 ≤ m := by
    exact two_le_card_sparseIndices_of_dense nodes a b hden hdense
  have hn : 2 ≤ n := (two_le_densityDenominator K).trans hden
  have hS : (sparseIndices nodes.toNodeFamily a b).Nonempty := by
    exact Finset.card_pos.mp (by simpa only [m] using (show 0 < m by omega))
  obtain ⟨pattern, hequi, _hunique⟩ :=
    existsUniqueEquioscillatingStatement (m - 2) 0 1
      (by norm_num [AdmissibleInterval])
  refine ⟨pattern, hequi, ?_⟩
  obtain ⟨g, hg⟩ := exists_consecutiveBlock_gap_ge_equioscHeight
    hn hm nodes (sparseConsecutiveBlock nodes a b hS) pattern hequi
  let globalGap : Fin (n - 1) :=
    (sparseConsecutiveBlock nodes a b hS).gapIndex g
  have hglobal :
      globalGap = sparseConsecutiveBlockGapIndex nodes a b hS g := by
    apply Fin.ext
    rfl
  obtain ⟨t, htgap, hgap, _hmax⟩ :=
    exists_lebesgueOn_eq_and_ge nodes.toNodeFamily
      (gap_left_lt_right nodes globalGap).le
  have htclosed : t ∈ closedGap nodes globalGap := by
    simpa only [closedGap] using htgap
  have htIcc : t ∈ Set.Icc a b := by
    rw [hglobal] at htclosed
    exact sparseConsecutiveBlock_closedGap_subset_Icc nodes hab hS g htclosed
  refine ⟨t, htIcc, ?_⟩
  have hgap' :
      gapHeight nodes globalGap = lebesgueFunction nodes.toNodeFamily t := by
    simpa only [gapHeight, closedGap] using hgap
  have hg' :
      pattern.height (⟨0, by omega⟩ : Fin ((m - 2) + 1)) ≤
        gapHeight nodes globalGap := by
    simpa only [globalGap] using hg
  exact hg'.trans_eq hgap'

end

end Randy1153.Density
