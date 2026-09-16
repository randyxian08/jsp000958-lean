import Randy1153.OrderedStatement
import Randy1153.Density.DenseBlockAsymptotic

/-!
# Randy 1153 proof assembly

This module closes the independent proof.  The fixed-interval sparse
construction and the dense equioscillating-block argument supply the two
branches for ordered nodes; sorting then transports the result to the frozen
public statement without quantitative loss.
-/

namespace Randy1153

noncomputable section

/-- The complete Randy 1153 theorem for strictly increasing node arrays. -/
theorem randy1153_ordered : OrderedTarget := by
  intro a b ha hab hb eps heps
  obtain ⟨K, Ns, hNs2, _hK, hsparseOrDense⟩ :=
    Density.exists_sparse_target_or_dense (ε := eps) ha hab hb
  obtain ⟨Nd, hdense⟩ :=
    Density.exists_eventual_dense_target_witness_ordered
      ClassicalBound.fullIntervalEventual K hab heps
  refine ⟨max Ns Nd, by omega, ?_⟩
  intro n hn nodes
  have hnSparse : Ns ≤ n := (le_max_left Ns Nd).trans hn
  have hnDense : Nd ≤ n := (le_max_right Ns Nd).trans hn
  rcases hsparseOrDense n hnSparse nodes.toNodeFamily with hsparse | hdenseAt
  · exact hsparse
  · exact hdense n hnDense nodes hdenseAt

/-- The frozen public Randy 1153 statement, for arbitrary node families. -/
theorem randy1153_main : Target :=
  target_of_orderedTarget randy1153_ordered

end

end Randy1153
