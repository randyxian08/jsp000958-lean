# Exact statement and provenance: z(20) = 6

## Scope of the formal target

For a finite simple undirected graph G, its cochromatic number is the least number of parts in a partition of its vertex set such that each part is a clique or an independent set. Empty colour classes are permitted in the formal colouring representation; thus `CochromaticColorable G k` means *at most* k nonempty parts, exactly as required for the extremal parameter.

The target of this development is the **twenty-vertex sub-question associated with Erdős Problem 758 / JSP-000622**:

```lean
JSP000622.z_twenty_eq_six : Erdos758.z 20 = 6
```

The direct statement, avoiding the abbreviation `z`, is:

```lean
JSP000622.JSP_000622 :
  (∀ G : SimpleGraph (Fin 20), Erdos758.CochromaticColorable G 6) ∧
  (∃ G : SimpleGraph (Fin 20), ¬ Erdos758.CochromaticColorable G 5)
```

`Main.lean` also states that the maximum of the individual cochromatic numbers is six, that a graph attaining six exists, and that the upper bound applies to any finite vertex type of cardinality twenty. The theorem does not determine `z(n)` for arbitrary n.

The presence of these declarations in source is not a verification receipt. Read the actual complete build, exact axiom audit, and fresh-kernel replay records before calling the closed theorem verified. A proof conditional on `SixteenEvidence`, `TwentyEvidence`, or an unproved packing theorem is not the final target.

## Mathematical argument and formal correspondence

The lower bound follows from `z(16) = 6` and induced-subgraph monotonicity. These inputs are taken from the pinned upstream small-order formalization. The upper bound reduces to finding two disjoint homogeneous four-sets in every twenty-vertex graph. Those sets consume two colours, and the twelve remaining vertices consume at most four more by the upstream theorem `z(12) = 4`.

To obtain the two sets, first apply the Ramsey bound `R(4,4) ≤ 18` to find a homogeneous four-set. Complementation permits treating it as a clique. If the other sixteen vertices contain another homogeneous four-set, the packing is immediate. Otherwise they form a (4,4)-Ramsey graph on sixteen vertices.

For such a sixteen-vertex graph, every vertex has degree seven or eight: its neighbourhood is a (3,4)-graph, and the same argument applies to the complementary graph. Complementing when needed gives a root of degree seven. The seven neighbours and the complementary graph on eight non-neighbours belong to complete small catalogs with nine and three representatives. This reduces the classification to 27 normalized crossing-edge instances, each with 56 free edges. Every satisfying normalized model carries an explicit isomorphism to one of the two sixteen-vertex cores, and an LRAT refutation after blocking those models certifies coverage.

The small catalogs are not assumed complete because a graph program returned them. `ExtensionKernel.classified_step` proves the general induction from order n to n+1. Every possible new-vertex adjacency pattern is covered by a checked forbidden-set or isomorphism witness. The implementation generates 3,299 such extension patterns and 49 extension-proof modules. Together with the 27 normalized sixteen-vertex instances, this gives 76 finite classification modules.

For either sixteen-vertex core, adjoining the external four-clique leaves 64 independent crossing edges. The two original SAT refutations are trimmed by proof dependency. Every retained input clause has two explicit disjoint four-tuples and their clique/independence colours. `CertificateKernel.twoFours_of_refutation` proves that a genuine realization of the symbolic edges must have the required packing. Only soundness of the retained constraints is needed; a claim of full CNF encoding equivalence is unnecessary.

`NormalizeSixteen` and `NormalizeTwenty` construct actual vertex equivalences and graph isomorphisms. They discharge relabelling and complementation rather than silently assuming symmetry-breaking conditions. `FiniteEvidence` must instantiate every finite input with a compiled theorem. `Main` then closes the packing and extremal conclusions without extra evidence parameters.

## Trusted and untrusted components

The Python generators, NetworkX graph atlas and isomorphism search, SAT solver, C++ RUP-to-LRAT elaborator, hashes, shell scripts, and successful process-exit codes are not mathematical axioms. They construct candidate finite data and proofs. The Lean modules check the resulting proof terms, graph-semantic witnesses, cardinalities, disjointness conditions, permutations, and exact formula correspondence.

The LRAT elaborator uses Mathlib's `fromLRATAux` to reconstruct ordinary Lean proof terms. `decide` is used for finite side conditions; `native_decide` is not used for these declarations. The exact axiom audit requires each expected final declaration to be present and restricts its transitive axiom set to `propext`, `Classical.choice`, and `Quot.sound`. A fresh `leanchecker --fresh JSP000622.Main` replay checks the imported proof environment again; it is a Lean-kernel replay, not a separate independently implemented verifier.

## Fixed sources and attribution

Compiler: `leanprover/lean4:v4.33.0`.

Mathlib: `leanprover-community/mathlib4` at `db584cd6d46c92f209a44c0f1c829460d327499d`.

Small-order and Ramsey inputs: `plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`, under `src/latest/ErdosProblems/Erdos758.lean`, `src/latest/ErdosProblems/Erdos758/`, and `src/latest/Util/`. The upstream source credits Bhavik Mehta for the informal small-order result and records its own formal authors. Original source headers are retained. This development does not claim those results as new work.

Two-core reduction and original SAT certificate package: `ipitchford/z20-cochromatic` at `3c7e520fdc0615f5c700761c2b1e5108dcc836e7`. That repository describes its result as an unrefereed candidate computer-assisted proof and explains its AI-system provenance. Its original material is dedicated under CC0 1.0, subject to the scope stated there; no third-party endorsement is implied. The present formalization must be credited separately from the pre-existing mathematical reduction and certificate discovery.

Original CNF SHA-256 values:

```text
core0 cbfea7b0b2cb712ad8b4f8b129f74c7f010e879064414eaef76e74aa88be3f44
core1 d3d96a3c2a719c753242673b81aabc3977c5e435bb5996b4c58c85a82d11dc5a
```

The regenerated trimmed certificate counts are 3,601 input clauses and 1,467 RUP steps for core0, and 1,876 input clauses and 752 RUP steps for core1. The raw and trimmed files, concrete witnesses, and replay records remain distinct artifacts.

## Reproduction and prize boundary

`bash Z20/reproduce_complete.sh` creates a standalone pinned workspace, reconstructs the finite evidence, compiles `JSP000622.Main`, audits exact final axiom sets, and requests a fresh kernel replay. It does not rely on a GitHub Actions compiler cache. Required tools are Git, Python 3 with venv, a C++17 compiler, and elan/Lake.

A public prize nomination must additionally establish correspondence with the original problem, review the reproduction evidence, and resolve contribution attribution. The prize repository expressly separates candidate evidence from announced awards. Neither a source declaration, a successful build, nor this document constitutes an award decision or a right to payment. No prize submission or award is asserted here.
