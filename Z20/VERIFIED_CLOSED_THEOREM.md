# Verified closed theorem: z(20) = 6

## Actual verification receipt

The closed theorem and its complete finite-evidence aggregation compiled successfully in **GitHub Actions run 35174067645**, job **105051768678**, on 2026-09-17 (UTC). The run concluded **success**.

- Proof and driver snapshot: `3773abab463d0c58d92bdf200d5397a826385988`.
- Compiler: Lean `4.33.0`, compiler commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Small-order/Ramsey source: `plby/lean-proofs` at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- Original core certificate source: `ipitchford/z20-cochromatic` at `3c7e520fdc0615f5c700761c2b1e5108dcc836e7`.

Recorded commands and exit codes:

```text
lake build JSP000622.R34Nine          exit 0
lake build JSP000622.FiniteEvidence   exit 0
lake build JSP000622.Main             exit 0
lake env lean ClosedAudit.lean        exit 0
exact transitive axiom whitelist      PASSED
```

The final receipt records:

```json
{
  "source_commit": "3773abab463d0c58d92bdf200d5397a826385988",
  "workflow_run_id": "35174067645",
  "closed_theorem_compiled_and_axiom_audited": true,
  "fresh_kernel_replay": null,
  "fresh_replay_status": "NOT_RUN_IN_THIS_STAGE",
  "prize_awarded": false
}
```

This receipt is intentionally limited to what that job did. A separate full-environment replay was requested in run 35173223882; its outcome is not inferred here.

## Closed mathematical statements

```lean
JSP000622.z_twenty_eq_six : Erdos758.z 20 = 6

JSP000622.JSP_000622 :
  (∀ G : SimpleGraph (Fin 20), Erdos758.CochromaticColorable G 6) ∧
  (∃ G : SimpleGraph (Fin 20), ¬Erdos758.CochromaticColorable G 5)
```

Neither theorem has a classification, certificate, packing, or other unproved mathematical premise. `FiniteEvidence` supplies the inputs to the generic normalization theorems with actual checked theorem references. The result is the exact twenty-vertex sub-question; it is not a solution for all values of n.

The following eight declarations were all present and each had exactly the axiom set `[propext, Classical.choice, Quot.sound]` (the receipt sorts this set differently):

```text
JSP000622.R34Seven.complete
JSP000622.R34Eight.complete
JSP000622.FiniteEvidence.complete_sixteen
JSP000622.FiniteEvidence.packing_twenty
JSP000622.z_twenty_eq_six
JSP000622.maximum_cochromatic_twenty_eq_six
JSP000622.colorable_six_of_card_twenty
JSP000622.JSP_000622
```

In particular the final statements do not depend on `sorryAx`, a custom project axiom, or a native-reduction/compiler-trust axiom. The successful audit checks actual Lean output for each required theorem, not just absence of strings in source code.

## Finite evidence and earlier source checks

All **76 finite classification modules** passed compilation and axiom auditing in the six successful classification shards of run 35172668078. They comprise 49 extension-catalog modules covering 3,299 extension patterns and 27 normalized sixteen-vertex cases. Both complete core graph-packing modules then passed compilation and axiom auditing in run 35173223882. The aggregate small-catalog completeness, sixteen-vertex classification, twenty-vertex packing and extremal theorem all passed together in the closed build above.

The full borrowed small-order formalization and its Ramsey statements were separately rebuilt and audited before use. It is credited as existing work, not a new contribution of this development. The mathematical two-core argument and original SAT refutations are likewise attributed to the published candidate proof project.

## Inspectable artifacts

Closed theorem artifact:

```text
name: z20-closed-theorem-35174067645
GitHub artifact ID: 10477952116
bytes: 155402683
SHA-256: 87a311890369469fb8b7a8fdf59214e64801fb202caa116d17b4d9c6c2d3aada
```

It contains `CLOSED_STATUS.json`, `ClosedAudit.txt`, `ClosedAudit.json`, the three complete build logs, the exact generated proof source, tools, and finite-shard provenance. This artifact has finite retention; it is not a claim of permanent external archival. The Git commit and source generators provide reproducible source traceability independently of that artifact's retention.

```bash
gh run view 35174067645 -R randyxian08/jsp000958-lean --log
gh run download 35174067645 -R randyxian08/jsp000958-lean \
  --name z20-closed-theorem-35174067645
```

Run [35174067645](https://github.com/randyxian08/jsp000958-lean/actions/runs/35174067645) and its [artifact](https://github.com/randyxian08/jsp000958-lean/actions/runs/35174067645/artifacts/10477952116) are the underlying records. For reproduction without GitHub Actions caches, use `bash Z20/reproduce_complete.sh` at the recorded source snapshot.

## Prize and review boundary

This is an actual completed closed-theorem build and axiom audit, not a prize decision. Independent substantive review, permanent archival, minimum-safe-version assessment, attribution, recipient confirmation and the organizers' decision remain separate. Public PR #332 reports another formalization for the same target; this development does not claim first-formalization priority or guaranteed eligibility. Existing draft PR #41 preserves the earlier work-in-progress history without reserving the problem.
