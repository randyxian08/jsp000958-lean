import Randy1153.DeBoorPinkus.NodeSpace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The endpoint-array simplex

This file supplies the global coordinate identification deliberately omitted
from `NodeSpace`.  An endpoint array is reconstructed from its `d` interior
coordinates, and the induced topology makes this reconstruction a
homeomorphism with the open ordered simplex.
-/

namespace Randy1153.DeBoorPinkus

noncomputable section

/-- Every full node index is the left endpoint, the right endpoint, or one
of the interior indices.  The statement remains valid when `d = 0`. -/
lemma endpoint_index_cases {d : ℕ} (k : Fin (d + 2)) :
    k = endpointLeftIndex d ∨ k = endpointRightIndex d ∨
      ∃ i : Fin d, k = interiorNodeIndex i := by
  by_cases hk0 : k.val = 0
  · exact Or.inl (Fin.ext hk0)
  by_cases hkLast : k.val = d + 1
  · exact Or.inr (Or.inl (Fin.ext hkLast))
  right
  right
  let i : Fin d := ⟨k.val - 1, by omega⟩
  exact ⟨i, Fin.ext (by simp [i]; omega)⟩

/-- Full node coordinate obtained by adjoining fixed endpoints to an
interior vector. -/
def endpointPoint {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (k : Fin (d + 2)) : ℝ :=
  if hkLeft : k = endpointLeftIndex d then A
  else if hkRight : k = endpointRightIndex d then B
  else u ⟨k.val - 1, by
    have hkPos : 0 < k.val := by
      by_contra hk
      have hk0 : k.val = 0 := Nat.eq_zero_of_not_pos hk
      exact hkLeft (Fin.ext hk0)
    have hkLt : k.val < d + 1 := by
      have := k.isLt
      have hkNe : k.val ≠ d + 1 := by
        intro hk
        exact hkRight (Fin.ext hk)
      omega
    omega⟩

@[simp]
lemma endpointPoint_left {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) :
    endpointPoint A B u (endpointLeftIndex d) = A := by
  simp [endpointPoint]

@[simp]
lemma endpointPoint_right {d : ℕ} (A B : ℝ) (u : Fin d → ℝ) :
    endpointPoint A B u (endpointRightIndex d) = B := by
  have hne : endpointRightIndex d ≠ endpointLeftIndex d := by
    intro h
    have := congrArg Fin.val h
    simp at this
  simp [endpointPoint, hne]

@[simp]
lemma endpointPoint_interior {d : ℕ} (A B : ℝ) (u : Fin d → ℝ)
    (i : Fin d) :
    endpointPoint A B u (interiorNodeIndex i) = u i := by
  have hleft : interiorNodeIndex i ≠ endpointLeftIndex d :=
    (endpointLeftIndex_lt_interior i).ne'
  have hright : interiorNodeIndex i ≠ endpointRightIndex d :=
    (interior_lt_endpointRightIndex i).ne
  simp only [endpointPoint, dif_neg hleft, dif_neg hright]
  congr 1

/-- Strict ordering of the adjoined full coordinate vector. -/
lemma endpointPoint_strictMono {d : ℕ} {A B : ℝ} {u : Fin d → ℝ}
    (hAB : A < B) (hu : u ∈ endpointNodeSpace d A B) :
    StrictMono (endpointPoint A B u) := by
  intro i j hij
  rcases endpoint_index_cases i with hi | hi | ⟨r, hi⟩
  · subst i
    rcases endpoint_index_cases j with hj | hj | ⟨s, hj⟩
    · subst j
      exact (lt_irrefl _ hij).elim
    · subst j
      simpa using hAB
    · subst j
      simpa using hu.1 s
  · subst i
    have : ¬endpointRightIndex d < j := by
      simp only [Fin.lt_def, endpointRightIndex_val]
      omega
    exact (this hij).elim
  · subst i
    rcases endpoint_index_cases j with hj | hj | ⟨s, hj⟩
    · subst j
      have : ¬interiorNodeIndex r < endpointLeftIndex d := by simp [Fin.lt_def]
      exact (this hij).elim
    · subst j
      simpa using hu.2.2 r
    · subst j
      have hrs : r < s := by
        change r.val + 1 < s.val + 1 at hij
        exact Fin.lt_def.mpr (Nat.add_lt_add_iff_right.mp hij)
      simpa using hu.2.1 hrs

/-- Every coordinate of the adjoined full vector remains in `[-1,1]`. -/
lemma endpointPoint_mem_Icc {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) {u : Fin d → ℝ}
    (hu : u ∈ endpointNodeSpace d A B) (k : Fin (d + 2)) :
    endpointPoint A B u k ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    rw [endpointPoint_left]
    exact ⟨hAB.1, le_trans hAB.2.1.le hAB.2.2⟩
  · subst k
    rw [endpointPoint_right]
    exact ⟨hAB.1.trans hAB.2.1.le, hAB.2.2⟩
  · subst k
    rw [endpointPoint_interior]
    exact ⟨hAB.1.trans (hu.1 i).le, (hu.2.2 i).le.trans hAB.2.2⟩

/-- Reconstruct an endpoint array from a point of the open coordinate
simplex. -/
def endpointArrayOfInterior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    EndpointArray d A B where
  point := endpointPoint A B u.1
  injective := (endpointPoint_strictMono hAB.2.1 u.2).injective
  mem_Icc := endpointPoint_mem_Icc hAB u.2
  strictMono := endpointPoint_strictMono hAB.2.1 u.2
  left_endpoint := endpointPoint_left A B u.1
  right_endpoint := endpointPoint_right A B u.1

@[simp]
lemma endpointArrayOfInterior_point {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B})
    (k : Fin (d + 2)) :
    (endpointArrayOfInterior hAB u).point k = endpointPoint A B u.1 k :=
  rfl

@[simp]
lemma interior_endpointArrayOfInterior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B}) :
    (endpointArrayOfInterior hAB u).interior = u.1 := by
  funext i
  exact endpointPoint_interior A B u.1 i

/-- Endpoint arrays are extensional in their full point function. -/
lemma EndpointArray.ext {d : ℕ} {A B : ℝ} {x y : EndpointArray d A B}
    (h : ∀ k, x.point k = y.point k) : x = y := by
  cases x with
  | mk x hxLeft hxRight => cases x with
    | mk x hxMono =>
      cases y with
      | mk y hyLeft hyRight => cases y with
        | mk y hyMono =>
            simp only [EndpointArray.mk.injEq, OrderedNodes.mk.injEq,
              NodeFamily.ext_iff]
            exact funext h

/-- Interior coordinates determine the endpoint array. -/
lemma EndpointArray.ext_interior {d : ℕ} {A B : ℝ}
    {x y : EndpointArray d A B} (h : x.interior = y.interior) : x = y := by
  apply EndpointArray.ext
  intro k
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    rw [x.left_endpoint, y.left_endpoint]
  · subst k
    rw [x.right_endpoint, y.right_endpoint]
  · subst k
    exact congrFun h i

@[simp]
lemma endpointArrayOfInterior_interior {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (nodes : EndpointArray d A B) :
    endpointArrayOfInterior hAB
      ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩ = nodes := by
  apply EndpointArray.ext_interior
  exact interior_endpointArrayOfInterior hAB _

/-- Exact equivalence between endpoint arrays and their interior-coordinate
open simplex. -/
def endpointArrayEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} where
  toFun nodes := ⟨nodes.interior, nodes.interior_mem_endpointNodeSpace⟩
  invFun := endpointArrayOfInterior hAB
  left_inv := endpointArrayOfInterior_interior hAB
  right_inv u := Subtype.ext (interior_endpointArrayOfInterior hAB u)

/-- The induced topology on endpoint arrays makes the coordinate equivalence
a genuine homeomorphism. -/
def endpointArrayHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} where
  toEquiv := endpointArrayEquiv hAB
  continuous_toFun := by
    exact Continuous.subtype_mk continuous_induced_dom _
  continuous_invFun := by
    rw [continuous_induced_rng]
    change Continuous (fun u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} ↦
      (endpointArrayOfInterior hAB u).interior)
    convert (continuous_subtype_val : Continuous
      (fun u : {v : Fin d → ℝ // v ∈ endpointNodeSpace d A B} ↦ u.1)) using 1
    funext u
    exact interior_endpointArrayOfInterior hAB u

/-- Canonical equispaced interior vector.  For `d = 0` this is the unique
empty function. -/
def equispacedInterior (d : ℕ) (A B : ℝ) : Fin d → ℝ :=
  fun i ↦ A + ((i.val + 1 : ℕ) : ℝ) / (d + 1 : ℕ) * (B - A)

lemma equispacedInterior_mem_endpointNodeSpace {d : ℕ} {A B : ℝ}
    (hAB : A < B) :
    equispacedInterior d A B ∈ endpointNodeSpace d A B := by
  have hden : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  have hdelta : 0 < B - A := sub_pos.mpr hAB
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hnum : (0 : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by positivity
    have hratio : 0 < ((i.val + 1 : ℕ) : ℝ) / (d + 1 : ℕ) :=
      div_pos hnum hden
    exact lt_add_of_pos_right _ (mul_pos hratio hdelta)
  · intro i j hij
    have hijNat : i.val + 1 < j.val + 1 := Nat.add_lt_add_right hij 1
    have hijReal : (((i.val + 1 : ℕ) : ℝ) < ((j.val + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hijNat
    have hratio :
        ((i.val + 1 : ℕ) : ℝ) / (d + 1 : ℕ) <
          ((j.val + 1 : ℕ) : ℝ) / (d + 1 : ℕ) :=
      (div_lt_div_iff_of_pos_right hden).2 hijReal
    unfold equispacedInterior
    simpa only [add_comm] using
      (add_lt_add_left (mul_lt_mul_of_pos_right hratio hdelta) A)
  · intro i
    have hiNat : i.val + 1 < d + 1 := Nat.add_lt_add_right i.isLt 1
    have hiReal : (((i.val + 1 : ℕ) : ℝ) < ((d + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hiNat
    have hratio : ((i.val + 1 : ℕ) : ℝ) / (d + 1 : ℕ) < 1 := by
      exact (div_lt_one hden).2 hiReal
    unfold equispacedInterior
    have hmul := mul_lt_mul_of_pos_right hratio hdelta
    linarith

/-- The coordinate simplex is nonempty on every nondegenerate interval,
including dimension zero. -/
lemma endpointNodeSpace_nonempty {d : ℕ} {A B : ℝ} (hAB : A < B) :
    (endpointNodeSpace d A B).Nonempty :=
  ⟨equispacedInterior d A B, equispacedInterior_mem_endpointNodeSpace hAB⟩

/-- The strict ordered coordinate simplex is convex. -/
lemma convex_endpointNodeSpace (d : ℕ) (A B : ℝ) :
    Convex ℝ (endpointNodeSpace d A B) := by
  rw [convex_iff_forall_pos]
  intro u hu v hv a b ha hb hab
  simp only [mem_endpointNodeSpace, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change A < a * u i + b * v i
    have huA := hu.1 i
    have hvA := hv.1 i
    have hua : a * A < a * u i := mul_lt_mul_of_pos_left huA ha
    have hvb : b * A < b * v i := mul_lt_mul_of_pos_left hvA hb
    calc
      A = a * A + b * A := by rw [← add_mul, hab, one_mul]
      _ < a * u i + b * v i := add_lt_add hua hvb
  · intro i j hij
    change a * u i + b * v i < a * u j + b * v j
    have huij := hu.2.1 hij
    have hvij := hv.2.1 hij
    exact add_lt_add (mul_lt_mul_of_pos_left huij ha)
      (mul_lt_mul_of_pos_left hvij hb)
  · intro i
    change a * u i + b * v i < B
    have huB := hu.2.2 i
    have hvB := hv.2.2 i
    have hua : a * u i < a * B := mul_lt_mul_of_pos_left huB ha
    have hvb : b * v i < b * B := mul_lt_mul_of_pos_left hvB hb
    calc
      a * u i + b * v i < a * B + b * B := add_lt_add hua hvb
      _ = B := by rw [← add_mul, hab, one_mul]

lemma isPathConnected_endpointNodeSpace {d : ℕ} {A B : ℝ} (hAB : A < B) :
    IsPathConnected (endpointNodeSpace d A B) :=
  (convex_endpointNodeSpace d A B).isPathConnected
    (endpointNodeSpace_nonempty hAB)

lemma isConnected_endpointNodeSpace {d : ℕ} {A B : ℝ} (hAB : A < B) :
    IsConnected (endpointNodeSpace d A B) :=
  (isPathConnected_endpointNodeSpace hAB).isConnected

/-- The simplex subtype is path connected. -/
lemma pathConnectedSpace_endpointNodeSpace {d : ℕ} {A B : ℝ} (hAB : A < B) :
    PathConnectedSpace {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} :=
  isPathConnected_iff_pathConnectedSpace.mp
    (isPathConnected_endpointNodeSpace hAB)

/-- Endpoint arrays inherit path connectedness through the proved
homeomorphism, not merely from openness of the coordinate image. -/
lemma pathConnectedSpace_endpointArray {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    PathConnectedSpace (EndpointArray d A B) := by
  rw [pathConnectedSpace_iff_univ]
  let e : EndpointArray d A B ≃ₜ
      {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B} :=
    endpointArrayHomeomorph hAB
  have htarget : IsPathConnected
      (Set.univ : Set {u : Fin d → ℝ // u ∈ endpointNodeSpace d A B}) :=
    pathConnectedSpace_iff_univ.mp
      (pathConnectedSpace_endpointNodeSpace hAB.2.1)
  have hpreimage := (e.isPathConnected_preimage).2 htarget
  simpa [e] using hpreimage

/-! ## Positive spacings and log-ratio coordinates -/

/-- Positive `(d+1)`-tuples with prescribed total length. -/
def positiveSpacingSimplex (d : ℕ) (L : ℝ) : Set (Fin (d + 1) → ℝ) :=
  {s | (∀ g, 0 < s g) ∧ ∑ g, s g = L}

lemma mem_positiveSpacingSimplex {d : ℕ} {L : ℝ}
    {s : Fin (d + 1) → ℝ} :
    s ∈ positiveSpacingSimplex d L ↔
      (∀ g, 0 < s g) ∧ ∑ g, s g = L :=
  Iff.rfl

/-- Softmax denominator with the last spacing used as reference. -/
def logRatioDenominator {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  1 + ∑ i, Real.exp (z i)

lemma logRatioDenominator_pos {d : ℕ} (z : Fin d → ℝ) :
    0 < logRatioDenominator z := by
  unfold logRatioDenominator
  positivity

/-- Inverse log-ratio spacings.  The final coordinate is the reference
weight `1`; the first `d` weights are `exp (z i)`. -/
def softmaxSpacing {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    Fin (d + 1) → ℝ :=
  fun g ↦ Fin.lastCases
    (L / logRatioDenominator z)
    (fun i ↦ L * Real.exp (z i) / logRatioDenominator z) g

@[simp]
lemma softmaxSpacing_last {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    softmaxSpacing L z (Fin.last d) = L / logRatioDenominator z := by
  simp [softmaxSpacing]

@[simp]
lemma softmaxSpacing_castSucc {d : ℕ} (L : ℝ) (z : Fin d → ℝ)
    (i : Fin d) :
    softmaxSpacing L z i.castSucc =
      L * Real.exp (z i) / logRatioDenominator z := by
  simp [softmaxSpacing]

lemma softmaxSpacing_pos {d : ℕ} {L : ℝ} (hL : 0 < L)
    (z : Fin d → ℝ) (g : Fin (d + 1)) :
    0 < softmaxSpacing L z g := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · rw [softmaxSpacing_last]
    exact div_pos hL (logRatioDenominator_pos z)
  · rw [softmaxSpacing_castSucc]
    exact div_pos (mul_pos hL (Real.exp_pos _)) (logRatioDenominator_pos z)

lemma sum_softmaxSpacing {d : ℕ} (L : ℝ) (z : Fin d → ℝ) :
    ∑ g, softmaxSpacing L z g = L := by
  rw [Fin.sum_univ_castSucc]
  simp only [softmaxSpacing_castSucc, softmaxSpacing_last]
  have hden : logRatioDenominator z ≠ 0 :=
    (logRatioDenominator_pos z).ne'
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  unfold logRatioDenominator at *
  field_simp
  ring

lemma softmaxSpacing_mem_positiveSpacingSimplex {d : ℕ} {L : ℝ}
    (hL : 0 < L) (z : Fin d → ℝ) :
    softmaxSpacing L z ∈ positiveSpacingSimplex d L :=
  ⟨softmaxSpacing_pos hL z, sum_softmaxSpacing L z⟩

/-- Logarithms of the first `d` spacings relative to the final spacing. -/
def spacingLogRatio {d : ℕ} (s : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i ↦ Real.log (s i.castSucc / s (Fin.last d))

@[simp]
lemma spacingLogRatio_softmaxSpacing {d : ℕ} {L : ℝ} (hL : 0 < L)
    (z : Fin d → ℝ) :
    spacingLogRatio (softmaxSpacing L z) = z := by
  funext i
  unfold spacingLogRatio
  rw [softmaxSpacing_castSucc, softmaxSpacing_last]
  have hL0 : L ≠ 0 := hL.ne'
  have hden : logRatioDenominator z ≠ 0 :=
    (logRatioDenominator_pos z).ne'
  have hratio :
      (L * Real.exp (z i) / logRatioDenominator z) /
          (L / logRatioDenominator z) = Real.exp (z i) := by
    field_simp
  rw [hratio, Real.log_exp]

lemma exp_spacingLogRatio {d : ℕ} {s : Fin (d + 1) → ℝ}
    (hs : ∀ g, 0 < s g) (i : Fin d) :
    Real.exp (spacingLogRatio s i) = s i.castSucc / s (Fin.last d) := by
  unfold spacingLogRatio
  exact Real.exp_log (div_pos (hs _) (hs _))

lemma logRatioDenominator_spacingLogRatio {d : ℕ}
    {s : Fin (d + 1) → ℝ} (hs : ∀ g, 0 < s g) :
    logRatioDenominator (spacingLogRatio s) =
      (∑ g, s g) / s (Fin.last d) := by
  unfold logRatioDenominator
  simp_rw [exp_spacingLogRatio hs]
  rw [Fin.sum_univ_castSucc]
  have href : s (Fin.last d) ≠ 0 := (hs _).ne'
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  field_simp
  ring

@[simp]
lemma softmaxSpacing_spacingLogRatio {d : ℕ} {L : ℝ} (hL : 0 < L)
    (s : Fin (d + 1) → ℝ) (hs : ∀ g, 0 < s g)
    (hsum : ∑ g, s g = L) :
    softmaxSpacing L (spacingLogRatio s) = s := by
  funext g
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · rw [softmaxSpacing_last,
      logRatioDenominator_spacingLogRatio hs, hsum]
    have hL0 : L ≠ 0 := hL.ne'
    have href : s (Fin.last d) ≠ 0 := (hs _).ne'
    field_simp
  · rw [softmaxSpacing_castSucc, exp_spacingLogRatio hs,
      logRatioDenominator_spacingLogRatio hs, hsum]
    have hL0 : L ≠ 0 := hL.ne'
    have href : s (Fin.last d) ≠ 0 := (hs _).ne'
    field_simp

/-- Positive normalized spacings are exactly log-ratio coordinates in
`Fin d → ℝ`. -/
def positiveSpacingLogRatioEquiv {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (Fin d → ℝ) ≃
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} where
  toFun z := ⟨softmaxSpacing L z, softmaxSpacing_mem_positiveSpacingSimplex hL z⟩
  invFun s := spacingLogRatio s.1
  left_inv := spacingLogRatio_softmaxSpacing hL
  right_inv s := Subtype.ext
    (softmaxSpacing_spacingLogRatio hL s.1 s.2.1 s.2.2)

lemma continuous_logRatioDenominator {d : ℕ} :
    Continuous (logRatioDenominator : (Fin d → ℝ) → ℝ) := by
  unfold logRatioDenominator
  exact continuous_const.add (continuous_finset_sum Finset.univ fun i _ ↦
    (continuous_apply i).rexp)

lemma continuous_softmaxSpacing {d : ℕ} (L : ℝ) :
    Continuous (softmaxSpacing L : (Fin d → ℝ) → Fin (d + 1) → ℝ) := by
  apply continuous_pi
  intro g
  refine Fin.lastCases ?_ (fun i ↦ ?_) g
  · have h : Continuous (((fun _ : Fin d → ℝ => L) : (Fin d → ℝ) → ℝ) / logRatioDenominator) :=
      (continuous_const : Continuous (fun _ : Fin d → ℝ => L)).div
        continuous_logRatioDenominator
        (fun z ↦ (logRatioDenominator_pos z).ne')
    convert h using 1
    funext a
    simp [softmaxSpacing_last, Pi.div_apply]
  · have h : Continuous
        ((((fun _ : Fin d → ℝ => L) : (Fin d → ℝ) → ℝ) *
          fun z => Real.exp (z i)) / logRatioDenominator) :=
      ((continuous_const : Continuous (fun _ : Fin d → ℝ => L)).mul
        (continuous_apply i).rexp).div
        continuous_logRatioDenominator
        (fun z ↦ (logRatioDenominator_pos z).ne')
    convert h using 1
    funext a
    simp [softmaxSpacing_castSucc, Pi.div_apply, Pi.mul_apply]

lemma continuous_spacingLogRatio_positive {d : ℕ} {L : ℝ} :
    Continuous (fun s :
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} ↦
        spacingLogRatio s.1) := by
  apply continuous_pi
  intro i
  let X := {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L}
  have hnum : Continuous (fun s : X ↦ s.1 i.castSucc) :=
    (continuous_apply i.castSucc).comp continuous_subtype_val
  have href : Continuous (fun s : X ↦ s.1 (Fin.last d)) :=
    (continuous_apply (Fin.last d)).comp continuous_subtype_val
  have hdiv : Continuous (fun s : X ↦ s.1 i.castSucc / s.1 (Fin.last d)) :=
    hnum.div href (fun s ↦ (s.2.1 _).ne')
  exact hdiv.log (fun s ↦ div_ne_zero (s.2.1 _).ne' (s.2.1 _).ne')

/-- Homeomorphism from Euclidean log-ratio coordinates to the positive
normalized spacing simplex. -/
def positiveSpacingLogRatioHomeomorph {d : ℕ} {L : ℝ} (hL : 0 < L) :
    (Fin d → ℝ) ≃ₜ
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d L} where
  toEquiv := positiveSpacingLogRatioEquiv hL
  continuous_toFun := Continuous.subtype_mk (continuous_softmaxSpacing L) _
  continuous_invFun := continuous_spacingLogRatio_positive

/-- Dimension zero is not hidden in the formulas: the log-ratio vector is
the unique function out of `Fin 0`. -/
lemma spacingLogRatio_zero (s : Fin 1 → ℝ) :
    spacingLogRatio s = (fun i : Fin 0 ↦ Fin.elim0 i) :=
  Subsingleton.elim _ _

/-- In dimension zero, softmax returns the single prescribed spacing. -/
lemma softmaxSpacing_zero (L : ℝ) (z : Fin 0 → ℝ) :
    softmaxSpacing L z = fun _ ↦ L := by
  funext g
  have hg : g = Fin.last 0 := by apply Fin.ext; simp
  rw [hg, softmaxSpacing_last]
  simp [logRatioDenominator]

/-! ## Endpoint arrays as normalized positive spacings -/

/-- Consecutive positive spacings of an endpoint array. -/
def endpointSpacing {d : ℕ} {A B : ℝ} (nodes : EndpointArray d A B) :
    Fin (d + 1) → ℝ :=
  fun g ↦ nodes.point (gapRightIndex g) - nodes.point (gapLeftIndex g)

lemma endpointSpacing_pos {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (g : Fin (d + 1)) :
    0 < endpointSpacing nodes g := by
  exact sub_pos.mpr (nodes.point_lt
    (gapLeftIndex_lt_rightIndex (n := d + 2) g))

lemma sum_endpointSpacing {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    ∑ g, endpointSpacing nodes g = B - A := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (d + 1), by omega⟩
  rw [Finset.sum_fin_eq_sum_range]
  have htel := Finset.sum_range_sub f (d + 1)
  rw [show f (d + 1) = nodes.point (endpointRightIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointRightIndex],
    show f 0 = nodes.point (endpointLeftIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointLeftIndex]] at htel
  calc
    (∑ i ∈ Finset.range (d + 1),
        if h : i < d + 1 then endpointSpacing nodes ⟨i, h⟩ else 0) =
        ∑ i ∈ Finset.range (d + 1), (f (i + 1) - f i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < d + 1 := Finset.mem_range.mp hi
      rw [dif_pos hi']
      unfold endpointSpacing
      simp only [gapRightIndex, gapLeftIndex, f]
      congr 2
      · apply Fin.ext
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        exact (Nat.min_eq_left hi'.le).symm
    _ = nodes.point (endpointRightIndex d) -
        nodes.point (endpointLeftIndex d) := htel
    _ = B - A := by rw [nodes.right_endpoint, nodes.left_endpoint]

lemma endpointSpacing_mem_positiveSpacingSimplex {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) :
    endpointSpacing nodes ∈ positiveSpacingSimplex d (B - A) :=
  ⟨endpointSpacing_pos nodes, sum_endpointSpacing nodes⟩

/-- Cumulative full-node coordinate associated to a spacing vector. -/
def spacingPoint {d : ℕ} (A : ℝ) (s : Fin (d + 1) → ℝ)
    (k : Fin (d + 2)) : ℝ :=
  A + ∑ i ∈ Finset.range k.val,
    if hi : i < d + 1 then s ⟨i, hi⟩ else 0

@[simp]
lemma spacingPoint_left {d : ℕ} (A : ℝ) (s : Fin (d + 1) → ℝ) :
    spacingPoint A s (endpointLeftIndex d) = A := by
  simp [spacingPoint, endpointLeftIndex]

lemma spacingPoint_strictMono {d : ℕ} (A : ℝ) {s : Fin (d + 1) → ℝ}
    (hs : ∀ g, 0 < s g) :
    StrictMono (spacingPoint A s) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change A + ∑ r ∈ Finset.range i.val,
      (if hr : r < d + 1 then s ⟨r, hr⟩ else 0) <
    A + ∑ r ∈ Finset.range (i.val + 1),
      (if hr : r < d + 1 then s ⟨r, hr⟩ else 0)
  rw [Finset.sum_range_succ, dif_pos i.isLt]
  calc
    A + ∑ r ∈ Finset.range i.val,
        (if hr : r < d + 1 then s ⟨r, hr⟩ else 0) <
        (A + ∑ r ∈ Finset.range i.val,
          (if hr : r < d + 1 then s ⟨r, hr⟩ else 0)) + s i :=
      lt_add_of_pos_right _ (hs i)
    _ = A + ((∑ r ∈ Finset.range i.val,
          if hr : r < d + 1 then s ⟨r, hr⟩ else 0) + s i) := by ring

@[simp]
lemma spacingPoint_right {d : ℕ} {A B : ℝ}
    {s : Fin (d + 1) → ℝ} (hsum : ∑ g, s g = B - A) :
    spacingPoint A s (endpointRightIndex d) = B := by
  unfold spacingPoint
  simp only [endpointRightIndex_val]
  rw [← Finset.sum_fin_eq_sum_range, hsum]
  ring

/-- Construct an endpoint array from positive spacings with total `B-A`. -/
def endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (s : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)}) :
    EndpointArray d A B where
  point := spacingPoint A s.1
  injective := (spacingPoint_strictMono A s.2.1).injective
  mem_Icc k := by
    have hmono := (spacingPoint_strictMono A s.2.1).monotone
    constructor
    · calc
        (-1 : ℝ) ≤ A := hAB.1
        _ = spacingPoint A s.1 (endpointLeftIndex d) :=
          (spacingPoint_left A s.1).symm
        _ ≤ spacingPoint A s.1 k :=
          hmono (by simp [Fin.le_iff_val_le_val])
    · calc
        spacingPoint A s.1 k ≤ spacingPoint A s.1 (endpointRightIndex d) :=
          hmono (by
            apply Fin.le_iff_val_le_val.mpr
            simp only [endpointRightIndex_val]
            omega)
        _ = B := spacingPoint_right s.2.2
        _ ≤ 1 := hAB.2.2
  strictMono := spacingPoint_strictMono A s.2.1
  left_endpoint := spacingPoint_left A s.1
  right_endpoint := spacingPoint_right s.2.2

@[simp]
lemma endpointSpacing_endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B)
    (s : {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)}) :
    endpointSpacing (endpointArrayOfSpacings hAB s) = s.1 := by
  funext g
  unfold endpointSpacing endpointArrayOfSpacings spacingPoint
  simp only [gapRightIndex_val, gapLeftIndex_val]
  rw [Finset.sum_range_succ, dif_pos g.isLt]
  ring

lemma spacingPoint_endpointSpacing {d : ℕ} {A B : ℝ}
    (nodes : EndpointArray d A B) (k : Fin (d + 2)) :
    spacingPoint A (endpointSpacing nodes) k = nodes.point k := by
  let f : ℕ → ℝ := fun i ↦
    nodes.point ⟨min i (d + 1), by omega⟩
  have hk : k.val ≤ d + 1 := by omega
  have htel := Finset.sum_range_sub f k.val
  rw [show f k.val = nodes.point k by
      apply congrArg nodes.point
      apply Fin.ext
      simp [Nat.min_eq_left hk],
    show f 0 = nodes.point (endpointLeftIndex d) by
      apply congrArg nodes.point
      apply Fin.ext
      simp [endpointLeftIndex]] at htel
  unfold spacingPoint
  calc
    A + ∑ i ∈ Finset.range k.val,
          (if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0) =
      nodes.point (endpointLeftIndex d) +
        ∑ i ∈ Finset.range k.val,
          (if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0) := by
      exact congrArg (fun x ↦ x + ∑ i ∈ Finset.range k.val,
        if hi : i < d + 1 then endpointSpacing nodes ⟨i, hi⟩ else 0)
          nodes.left_endpoint.symm
    _ = nodes.point (endpointLeftIndex d) +
        ∑ i ∈ Finset.range k.val, (f (i + 1) - f i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hiMem
      have hiK : i < k.val := Finset.mem_range.mp hiMem
      have hi : i < d + 1 := lt_of_lt_of_le hiK hk
      rw [dif_pos hi]
      unfold endpointSpacing
      simp only [gapRightIndex, gapLeftIndex, f]
      congr 2
      · apply Fin.ext
        exact (Nat.min_eq_left (by omega)).symm
      · apply Fin.ext
        exact (Nat.min_eq_left hi.le).symm
    _ = nodes.point k := by rw [htel]; ring

@[simp]
lemma endpointArrayOfSpacings_endpointSpacing {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) (nodes : EndpointArray d A B) :
    endpointArrayOfSpacings hAB
      ⟨endpointSpacing nodes, endpointSpacing_mem_positiveSpacingSimplex nodes⟩ = nodes := by
  apply EndpointArray.ext
  exact spacingPoint_endpointSpacing nodes

/-- Exact equivalence between endpoint arrays and positive normalized
spacings. -/
def endpointArraySpacingEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d (B - A)} where
  toFun nodes := ⟨endpointSpacing nodes,
    endpointSpacing_mem_positiveSpacingSimplex nodes⟩
  invFun := endpointArrayOfSpacings hAB
  left_inv := endpointArrayOfSpacings_endpointSpacing hAB
  right_inv s := Subtype.ext (endpointSpacing_endpointArrayOfSpacings hAB s)

/-- Algebraic Euclidean chart obtained by normalized spacing log ratios. -/
def endpointArrayLogRatioEquiv {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ (Fin d → ℝ) :=
  (endpointArraySpacingEquiv hAB).trans
    (positiveSpacingLogRatioEquiv (sub_pos.mpr hAB.2.1)).symm

lemma continuous_endpointArray_point {d : ℕ} {A B : ℝ}
    (k : Fin (d + 2)) :
    Continuous (fun nodes : EndpointArray d A B ↦ nodes.point k) := by
  rcases endpoint_index_cases k with hk | hk | ⟨i, hk⟩
  · subst k
    convert (continuous_const : Continuous (fun _ : EndpointArray d A B ↦ A)) using 1
    funext nodes
    exact nodes.left_endpoint
  · subst k
    convert (continuous_const : Continuous (fun _ : EndpointArray d A B ↦ B)) using 1
    funext nodes
    exact nodes.right_endpoint
  · subst k
    exact (continuous_apply i).comp
      (continuous_induced_dom : Continuous
        (fun nodes : EndpointArray d A B ↦ nodes.interior))

lemma continuous_endpointSpacing {d : ℕ} {A B : ℝ} :
    Continuous (endpointSpacing : EndpointArray d A B → Fin (d + 1) → ℝ) := by
  apply continuous_pi
  intro g
  exact (continuous_endpointArray_point (gapRightIndex g)).sub
    (continuous_endpointArray_point (gapLeftIndex g))

lemma continuous_endpointArrayOfSpacings {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    Continuous (endpointArrayOfSpacings (d := d) hAB) := by
  rw [continuous_induced_rng]
  change Continuous (fun s :
    {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
      (endpointArrayOfSpacings hAB s).interior)
  apply continuous_pi
  intro i
  change Continuous (fun s :
    {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
      spacingPoint A s.1 (interiorNodeIndex i))
  unfold spacingPoint
  apply continuous_const.add
  apply continuous_finset_sum
  intro r hr
  split_ifs with h
  · let k : Fin (d + 1) := ⟨r, h⟩
    have hc : Continuous (fun s :
        {v : Fin (d + 1) → ℝ // v ∈ positiveSpacingSimplex d (B - A)} ↦
          s.1 k) :=
      (continuous_apply k).comp continuous_subtype_val
    exact hc
  · exact continuous_const

/-- Endpoint arrays are homeomorphic to positive normalized spacings. -/
def endpointArraySpacingHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ
      {s : Fin (d + 1) → ℝ // s ∈ positiveSpacingSimplex d (B - A)} where
  toEquiv := endpointArraySpacingEquiv hAB
  continuous_toFun := Continuous.subtype_mk continuous_endpointSpacing _
  continuous_invFun := continuous_endpointArrayOfSpacings hAB

/-- Source-required global Euclidean homeomorphism, obtained by positive
spacings followed by log ratios against the final spacing. -/
def endpointArrayLogRatioHomeomorph {d : ℕ} {A B : ℝ}
    (hAB : AdmissibleInterval A B) :
    EndpointArray d A B ≃ₜ (Fin d → ℝ) :=
  (endpointArraySpacingHomeomorph hAB).trans
    (positiveSpacingLogRatioHomeomorph (sub_pos.mpr hAB.2.1)).symm

/-- In dimension zero the coordinate simplex is literally the whole
singleton function space, independent of endpoint inequalities. -/
lemma endpointNodeSpace_zero_eq_univ (A B : ℝ) :
    endpointNodeSpace 0 A B = Set.univ := by
  apply Set.eq_univ_of_forall
  intro u
  refine ⟨fun i ↦ Fin.elim0 i, ?_, fun i ↦ Fin.elim0 i⟩
  intro i
  exact Fin.elim0 i

/-- Consequently, any two zero-dimensional endpoint arrays with the same
fixed endpoints are equal. -/
lemma endpointArray_zero_unique {A B : ℝ} (x y : EndpointArray 0 A B) :
    x = y := by
  apply EndpointArray.ext_interior
  exact Subsingleton.elim _ _

end

end Randy1153.DeBoorPinkus
