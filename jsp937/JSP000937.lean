import Randy1153.DeBoorPinkus.Package
import Mathlib.Tactic.NormNum

/-!
# JSP-000937 — canonical (endpoint-fixed) maximin for Lagrange interpolation

JSP-000937 asks which nodes `x_1 < … < x_n` in `[-1,1]` maximise the smallest
peak error-amplification over the gaps between consecutive nodes.  Writing
`x_0 = -1`, `x_{n+1} = 1`,

  `Υ(x) = min_{0 ≤ i ≤ n} max_{t ∈ [x_i, x_{i+1}]} Σ_k |ℓ_k(t)|`,

and the question is which `x` maximise `Υ`.

Building block: `EndpointArray d A B` is a configuration of `d + 2` nodes whose
extreme nodes are pinned to `A` and `B`, and `height i` is the maximum of the
Lebesgue function on the `i`-th gap.

What is proved below (canonical configurations, endpoints pinned):

* the equioscillating array `opt` is the **unique** configuration all of whose
  gap peaks are at least the common peak of `opt`;
* consequently every lower bound for all gap peaks of any competitor is at most
  `opt.height 0` — i.e. `opt` is the unique maximiser;
* every non-optimal configuration has one peak strictly below, and one peak
  strictly above, the optimal common peak (strict sandwich).

SCOPE / ATTRIBUTION — read before citing:

* The de Boor–Pinkus comparison and uniqueness theory used here is **not
  reproved**: it is imported from `Randy1153.DeBoorPinkus.Package`, whose
  author is randyxian08 (earlier attribution: Ethan Yang, the same person
  according to the author's clarification; MIT licence).
* This file covers the **endpoint-fixed (canonical)** case only.  JSP-000937
  as posed allows *free* nodes; for free nodes the equioscillation
  characterisation is known to fail, and that layer is NOT formalised here.
  (Randy 1130 = JSP-000937.)
* These declarations are mechanically checked only when `run.sh` is executed
  to completion; the accompanying log is the evidence.
-/

namespace JSP000937

open Randy1153 Randy1153.DeBoorPinkus

noncomputable section

/-! ## Rigidity in both directions -/

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

/-- If every gap peak of `s` is at least the common peak of the equioscillating
array `opt`, then `s` must already be `opt`. -/
theorem lower_threshold_iff
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) :
    (∀ i, opt.height 0 ≤ s.height i) ↔ s = opt := by
  constructor
  · intro h
    have heq : opt = s := by
      apply (comparisonPackage d A B).gapHeight_le_rigidity opt s
      intro i
      rw [hopt i 0]
      exact h i
    exact heq.symm
  · intro h
    subst s
    intro i
    exact (hopt i 0).symm.le

/-! ## Optimality and the strict sandwich -/

/-- ANY lower bound for all peaks of ANY competitor is no larger than the
optimal common peak.  Apply this to the minimum of the competitor's peaks. -/
theorem any_peak_lower_bound_le_optimal
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (L : ℝ)
    (hL : ∀ i, L ≤ s.height i) :
    L ≤ opt.height 0 := by
  classical
  by_contra h
  have hlt : opt.height 0 < L := lt_of_not_ge h
  have heq : s = opt :=
    (lower_threshold_iff opt hopt s).mp
      (fun i => hlt.le.trans (hL i))
  have hbad := hL 0
  rw [heq] at hbad
  exact (not_le_of_gt hlt) hbad

/-- A non-optimal array has a peak strictly BELOW and a peak strictly ABOVE the
common optimal height. -/
theorem strict_peak_sandwich
    {d : ℕ} {A B : ℝ}
    (opt : EndpointArray d A B) (hopt : Equioscillates opt)
    (s : EndpointArray d A B) (hne : s ≠ opt) :
    (∃ i, s.height i < opt.height 0) ∧
      (∃ j, opt.height 0 < s.height j) := by
  classical
  constructor
  · by_contra h
    have hbound : ∀ i, opt.height 0 ≤ s.height i := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact hne ((lower_threshold_iff opt hopt s).mp hbound)
  · by_contra h
    have hbound : ∀ i, s.height i ≤ opt.height 0 := by
      intro i
      exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
    exact hne ((upper_threshold_iff opt hopt s).mp hbound)

/-- **JSP-000937, canonical case.**  For nodes pinned at `-1` and `1` there is
an equioscillating array `opt`, it is the unique configuration whose gap peaks
all sit at or above its common peak, and its common peak dominates every lower
bound on every competitor's gap peaks — so `opt` is the unique maximiser of `Υ`.
Any non-optimal configuration has a peak strictly below and a peak strictly
above the optimal common height. -/
theorem jsp_000937_canonical (d : ℕ) :
    ∃ opt : EndpointArray d (-1 : ℝ) 1,
      Equioscillates opt ∧
      ∀ s : EndpointArray d (-1 : ℝ) 1,
        ((∀ i, opt.height 0 ≤ s.height i) ↔ s = opt) ∧
        (∀ L : ℝ, (∀ i, L ≤ s.height i) → L ≤ opt.height 0) ∧
        (s ≠ opt → (∃ i, s.height i < opt.height 0) ∧
          (∃ j, opt.height 0 < s.height j)) := by
  have hAB : AdmissibleInterval (-1 : ℝ) 1 := by
    norm_num [AdmissibleInterval]
  obtain ⟨opt, hopt, _hunique⟩ :=
    existsUniqueEquioscillatingStatement d (-1 : ℝ) 1 hAB
  refine ⟨opt, hopt, ?_⟩
  intro s
  exact ⟨lower_threshold_iff opt hopt s,
    fun L hL => any_peak_lower_bound_le_optimal opt hopt s L hL,
    fun hne => strict_peak_sandwich opt hopt s hne⟩

end

end JSP000937

#print axioms JSP000937.jsp_000937_canonical
