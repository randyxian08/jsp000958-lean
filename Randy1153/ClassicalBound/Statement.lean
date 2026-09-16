import Randy1153.Interpolation

/-!
# The sharp classical full-interval bound: statement and certificate interface

This file records the exact Phase 4 proposition without asserting it as a
theorem.  It also gives a checked polynomial certificate which is sufficient
to prove any one of its finite-`n` inequalities.

The distinction is intentional.  The pinned Tao paper cites the classical
Bernstein--Randy--Turán lower bounds, but does not contain their proofs.
-/

namespace Randy1153
namespace ClassicalBound

open Polynomial

noncomputable section

/-- The desired sharp lower bound for one cardinality and one node family. -/
def FullIntervalAt {n : ℕ} (nodes : NodeFamily n) (ε : ℝ) : Prop :=
  (2 / Real.pi - ε) * Real.log (n : ℝ) < lebesgueOn nodes (-1) 1

/-- The exact uniform epsilon/eventual classical full-interval proposition.

The threshold is chosen before `n` and before the node family.  Thus it is
uniform over every family of exactly `n` distinct nodes in `[-1,1]`.
-/
def FullIntervalEventual : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
      FullIntervalAt nodes ε

/-- The full-interval maximum formulation is equivalent to an explicit
witness point. -/
lemma fullIntervalAt_iff_exists_point {n : ℕ} (nodes : NodeFamily n) (ε : ℝ) :
    FullIntervalAt nodes ε ↔
      ∃ t ∈ Set.Icc (-1 : ℝ) 1,
        (2 / Real.pi - ε) * Real.log (n : ℝ) < lebesgueFunction nodes t := by
  exact lt_lebesgueOn_iff nodes (by norm_num)

/-- A degree-below-`n` polynomial, bounded by one at all nodes, whose value at
one point exceeds `A`.  The Lagrange inequality turns this into a lower bound
for the Lebesgue constant.
-/
def PolynomialCertificate {n : ℕ} (nodes : NodeFamily n) (A : ℝ) : Prop :=
  ∃ p : ℝ[X], ∃ t ∈ Set.Icc (-1 : ℝ) 1,
    p.degree < n ∧
      (∀ k : Fin n, |p.eval (nodes.point k)| ≤ 1) ∧
      A < |p.eval t|

/-- A polynomial certificate really does lower-bound the full-interval
Lebesgue constant. -/
lemma lt_lebesgueOn_of_polynomialCertificate {n : ℕ} {nodes : NodeFamily n}
    {A : ℝ} (hcert : PolynomialCertificate nodes A) :
    A < lebesgueOn nodes (-1) 1 := by
  rcases hcert with ⟨p, t, ht, hpdeg, hpnodes, hlarge⟩
  apply (lt_lebesgueOn_iff nodes (by norm_num)).2
  exact ⟨t, ht, hlarge.trans_le
    (abs_eval_le_lebesgueFunction nodes p hpdeg t hpnodes)⟩

/-- The certificate threshold can be weakened. -/
lemma polynomialCertificate_mono {n : ℕ} {nodes : NodeFamily n} {A B : ℝ}
    (hAB : A ≤ B) (hcert : PolynomialCertificate nodes B) :
    PolynomialCertificate nodes A := by
  rcases hcert with ⟨p, t, ht, hpdeg, hpnodes, hlarge⟩
  exact ⟨p, t, ht, hpdeg, hpnodes, hAB.trans_lt hlarge⟩

/-- Supplying sharp certificates uniformly is sufficient for the complete
classical theorem.  This theorem exposes, rather than assumes, the missing
mathematical input. -/
lemma fullIntervalEventual_of_certificates
    (hcert : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ nodes : NodeFamily n,
        PolynomialCertificate nodes
          ((2 / Real.pi - ε) * Real.log (n : ℝ))) :
    FullIntervalEventual := by
  intro ε hε
  obtain ⟨N, hN⟩ := hcert ε hε
  refine ⟨N, fun n hn nodes ↦ ?_⟩
  exact lt_lebesgueOn_of_polynomialCertificate (hN n hn nodes)

end

end ClassicalBound
end Randy1153
