import Randy1153.DeBoorPinkus.Package
import Mathlib.Tactic.NormNum

/-!
# JSP-000936 — canonical (endpoint-fixed) minimax for Lagrange interpolation

JSP-000936 asks which nodes `x_1 < … < x_n` in `[-1,1]` minimise the maximal
input-error amplification

  `Λ(x) = max_{t ∈ [-1,1]} Σ_k |ℓ_k(t)|`.

Building block: `EndpointArray d A B` is a configuration of `d + 2` nodes whose
two extreme nodes are pinned to `A` and `B`, and `height i` is the maximum of
the actual Lebesgue function on the `i`-th gap `[x_i, x_{i+1}]`.  With the
endpoints pinned to `-1` and `1` the gaps cover `[-1,1]`, so the maximal gap
height is exactly `Λ`.

What is proved below (canonical configurations, endpoints pinned):

* the equioscillating array `opt` is the **unique** configuration all of whose
  gap peaks are at most the common peak of `opt`;
* consequently `opt.height 0` is a lower bound for every upper bound of the
  gap peaks of any competitor — i.e. `opt` is the unique minimiser.

SCOPE / ATTRIBUTION — read before citing:

* The de Boor–Pinkus comparison and uniqueness theory used here is **not
  reproved**: it is imported from `Randy1153.DeBoorPinkus.Package`, whose
  author is randyxian08 (earlier attribution: Ethan Yang, the same person
  according to the author's clarification; MIT licence).
* This file covers the **endpoint-fixed (canonical)** case only.  JSP-000936
  as posed allows *free* nodes in `[-1,1]`, where the minimiser is famously
  **not unique**; that layer is NOT formalised here.  (Randy 1129 = JSP-000936.)
* These declarations are mechanically checked only when `run.sh` is executed
  to completion; the accompanying log is the evidence.
-/

namespace JSP000936

open Randy1153 Randy1153.DeBoorPinkus

noncomputable section

/-- If every gap peak of `s` is at most the common peak of the equioscillating
array `opt`, then `s` must already be `opt`. -/
theorem upper_threshold_iff
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) :
    (∀ i, s.height i ≤ opt.height 0) ↔ s = opt := by
  constructor
  · intro h
    apply (comparisonPackage d A B).gapHeight_le_rigidity s opt
    intro i
    rw [hopt i 0]
    exact h i
  · intro h
    subst s
    intro i
    exact (hopt i 0).le

/-- The optimal common peak is no larger than ANY upper bound for the peaks of
ANY competitor; in particular no larger than their maximum. -/
theorem optimal_le_any_peak_upper_bound
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (U : ℝ)
    (hU : ∀ i, s.height i ≤ U) :
    opt.height 0 ≤ U := by
  classical
  by_contra h
  have hlt : U < opt.height 0 := lt_of_not_ge h
  have heq : s = opt :=
    (upper_threshold_iff opt hopt s).mp
      (fun i => (hU i).trans hlt.le)
  have hbad := hU 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- **JSP-000936, canonical case.**  For nodes pinned at `-1` and `1` there is
an equioscillating array `opt`, it is the unique configuration whose gap peaks
all sit at or below its common peak, and its common peak is a lower bound for
every upper bound on every competitor's gap peaks — so `opt` is the unique
minimiser of the maximal amplification. -/
theorem jsp_000936_canonical (d : ℕ) :
    ∃ opt : EndpointArray d (-1 : ℝ) 1,
      Equioscillates opt ∧
      ∀ s : EndpointArray d (-1 : ℝ) 1,
        ((∀ i, s.height i ≤ opt.height 0) ↔ s = opt) ∧
        (∀ U : ℝ, (∀ i, s.height i ≤ U) → opt.height 0 ≤ U) := by
  have hAB : AdmissibleInterval (-1 : ℝ) 1 := by
    norm_num [AdmissibleInterval]
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1 : ℝ) 1 hAB
  refine ⟨opt, hopt, ?_⟩
  intro s
  exact ⟨upper_threshold_iff opt hopt s,
    fun U hU => optimal_le_any_peak_upper_bound opt hopt s U hU⟩

end

end JSP000936

#print axioms JSP000936.jsp_000936_canonical
