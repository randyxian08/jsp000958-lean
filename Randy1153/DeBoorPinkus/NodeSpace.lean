import Randy1153.GapPolynomial
import Mathlib.Topology.Algebra.Order.Support

/-!
# Endpoint-fixed node arrays

The polynomial part of de Boor--Pinkus fixes the first and last interpolation
nodes and varies the interior nodes in an open simplex.  This file records
that space without identifying it magically with Euclidean space.  The later
global-topology phase must construct and prove the required homeomorphism.

Our `EndpointArray d A B` has `d` interior nodes and therefore `d + 2` nodes
and `d + 1` nodal gaps.  It extends the project's ordered-node type, so all
nodes remain in `[-1,1]`, which is the application needed for Randy 1153.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Interval hypotheses under which the project-level endpoint array exists.
The source assumes only `A < B`; the extra bounds are exactly those inherited
from the public `NodeFamily` used by Randy 1153. -/
def AdmissibleInterval (A B : ℝ) : Prop :=
  (-1 : ℝ) ≤ A ∧ A < B ∧ B ≤ 1

/-- Index of the fixed left endpoint among `d + 2` nodes. -/
def endpointLeftIndex (d : ℕ) : Fin (d + 2) :=
  ⟨0, by omega⟩

/-- Index of the fixed right endpoint among `d + 2` nodes. -/
def endpointRightIndex (d : ℕ) : Fin (d + 2) :=
  Fin.last (d + 1)

/-- Index of interior coordinate `i` among the full endpoint-fixed array. -/
def interiorNodeIndex {d : ℕ} (i : Fin d) : Fin (d + 2) :=
  ⟨i.val + 1, by omega⟩

@[simp]
lemma endpointLeftIndex_val (d : ℕ) : (endpointLeftIndex d).val = 0 :=
  rfl

@[simp]
lemma endpointRightIndex_val (d : ℕ) : (endpointRightIndex d).val = d + 1 :=
  rfl

@[simp]
lemma interiorNodeIndex_val {d : ℕ} (i : Fin d) :
    (interiorNodeIndex i).val = i.val + 1 :=
  rfl

lemma endpointLeftIndex_lt_interior {d : ℕ} (i : Fin d) :
    endpointLeftIndex d < interiorNodeIndex i := by
  simp [Fin.lt_def]

lemma interior_lt_endpointRightIndex {d : ℕ} (i : Fin d) :
    interiorNodeIndex i < endpointRightIndex d := by
  simp [Fin.lt_def]

lemma interiorNodeIndex_strictMono {d : ℕ} :
    StrictMono (interiorNodeIndex : Fin d → Fin (d + 2)) := by
  intro i j hij
  simpa only [Fin.lt_def, interiorNodeIndex_val] using Nat.add_lt_add_right hij 1

/-- An ordered array with `d` interior nodes and fixed endpoint values `A,B`. -/
structure EndpointArray (d : ℕ) (A B : ℝ) extends OrderedNodes (d + 2) where
  left_endpoint : point (endpointLeftIndex d) = A
  right_endpoint : point (endpointRightIndex d) = B

namespace EndpointArray

/-- The interior-coordinate vector of an endpoint-fixed array. -/
def interior {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : Fin d → ℝ :=
  fun i => nodes.point (interiorNodeIndex i)

@[simp]
lemma interior_apply {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    nodes.interior i = nodes.point (interiorNodeIndex i) :=
  rfl

lemma left_lt_interior {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    A < nodes.interior i := by
  calc
    A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
    _ < nodes.point (interiorNodeIndex i) :=
      nodes.strictMono (endpointLeftIndex_lt_interior i)
    _ = nodes.interior i := rfl

lemma interior_lt_right {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (i : Fin d) :
    nodes.interior i < B := by
  calc
    nodes.interior i = nodes.point (interiorNodeIndex i) := rfl
    _ < nodes.point (endpointRightIndex d) :=
      nodes.strictMono (interior_lt_endpointRightIndex i)
    _ = B := nodes.right_endpoint

lemma interior_strictMono {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    StrictMono nodes.interior :=
  nodes.strictMono.comp interiorNodeIndex_strictMono

lemma endpoints_lt {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) : A < B := by
  calc
    A = nodes.point (endpointLeftIndex d) := nodes.left_endpoint.symm
    _ < nodes.point (endpointRightIndex d) := nodes.strictMono (by simp [Fin.lt_def])
    _ = B := nodes.right_endpoint

lemma neg_one_le_left {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    (-1 : ℝ) ≤ A := by
  rw [← nodes.left_endpoint]
  exact nodes.neg_one_le _

lemma right_le_one {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    B ≤ (1 : ℝ) := by
  rw [← nodes.right_endpoint]
  exact nodes.le_one _

lemma admissibleInterval {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    AdmissibleInterval A B :=
  ⟨nodes.neg_one_le_left, nodes.endpoints_lt, nodes.right_le_one⟩

/-- Gap height of an endpoint-fixed array.  There are `d + 1` such gaps. -/
def height {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) (g : Fin (d + 1)) : ℝ :=
  gapHeight nodes.toOrderedNodes g

end EndpointArray

/-- The source's open simplex in interior-coordinate form. -/
def endpointNodeSpace (d : ℕ) (A B : ℝ) : Set (Fin d → ℝ) :=
  {u | (∀ i, A < u i) ∧ StrictMono u ∧ ∀ i, u i < B}

lemma mem_endpointNodeSpace {d : ℕ} {A B : ℝ} {u : Fin d → ℝ} :
    u ∈ endpointNodeSpace d A B ↔
      (∀ i, A < u i) ∧ StrictMono u ∧ ∀ i, u i < B :=
  Iff.rfl

lemma EndpointArray.interior_mem_endpointNodeSpace {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    nodes.interior ∈ endpointNodeSpace d A B :=
  ⟨nodes.left_lt_interior, nodes.interior_strictMono, nodes.interior_lt_right⟩

/-- The source topology is the coordinate topology on the varying interior
nodes.  A later module must still prove that `interior` identifies
`EndpointArray` homeomorphically with the open simplex `endpointNodeSpace`. -/
instance endpointArrayTopologicalSpace (d : ℕ) (A B : ℝ) :
    TopologicalSpace (EndpointArray d A B) :=
  TopologicalSpace.induced EndpointArray.interior inferInstance

/-- The coordinate simplex is open.  This is the local-topology input; no
global Euclidean homeomorphism is claimed here. -/
lemma isOpen_endpointNodeSpace (d : ℕ) (A B : ℝ) :
    IsOpen (endpointNodeSpace d A B) := by
  have hopenLeft : IsOpen {u : Fin d → ℝ | ∀ i, A < u i} := by
    rw [show {u : Fin d → ℝ | ∀ i, A < u i} =
        ⋂ i : Fin d, {u | A < u i} by ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hopenRight : IsOpen {u : Fin d → ℝ | ∀ i, u i < B} := by
    rw [show {u : Fin d → ℝ | ∀ i, u i < B} =
        ⋂ i : Fin d, {u | u i < B} by ext u; simp]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_apply i) continuous_const
  have hopenMono : IsOpen {u : Fin d → ℝ | StrictMono u} := by
    rw [show {u : Fin d → ℝ | StrictMono u} =
        ⋂ i : Fin d, ⋂ j : Fin d, ⋂ (_h : i < j), {u | u i < u j} by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_iInter_of_finite fun j =>
        isOpen_iInter_of_finite fun _h => isOpen_lt (continuous_apply i) (continuous_apply j)
  rw [show endpointNodeSpace d A B =
      {u : Fin d → ℝ | ∀ i, A < u i} ∩
        ({u : Fin d → ℝ | StrictMono u} ∩ {u : Fin d → ℝ | ∀ i, u i < B}) by
    ext u
    simp [endpointNodeSpace]]
  exact hopenLeft.inter (hopenMono.inter hopenRight)

end

end Randy1153.DeBoorPinkus
