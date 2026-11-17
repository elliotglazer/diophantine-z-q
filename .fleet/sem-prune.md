# sem-prune (2026-11-14)

**Result.** `ZInQ.OneProof.frozenTarget` no longer assumes `bdRInvariants` (OpenTextbookLeaves10) or
`raynaudKernelBound` (OpenResearchLeaves14); nothing added. Fields 68 → 66; strict count (kinds.tsv) 53/15 → 51/15,
strictest 51/17 → 49/17. Both were used only syntactically (gap-triage A1):
- T23 (from `bdRInvariants`) was passed to `G9Glue`, whose only proof (`g9Glue_of_fieldEmb`) ignores it. New
  `G0Galois.G9GlueNoT23` with copies of the G9 proofs without the binder; `g8_g11`, `g8_g12`, `g8_g12_of_leaves3`,
  `afterG7_of3` take it and drop `hT23`.
- `transfer_core` used only the half `h(P) ≤ h(J) + ½ log deg ψ` of R20, which follows from Faltings' printed Lemma 5
  and `kerOmegaLog_nonneg`. New `G0Split.R20Lower` / `HeightSplit.FaltingsLemma5BCLower` and their proofs, threaded
  through `sixContactMin_of_open4`…`_open11` (`_open17` supplies it from `faltingsLemma5Printed`).
Then PruneScan's set was removed from every bundle generation (16 fields, 18 assignments, 21 dead readers;
scratch/sem-prune/prune_edit.py).

**Compiles (VERIFIED).** `lake build +ZInQKernel.OneProof.Main`; frozenTarget axioms propext, Classical.choice,
Quot.sound; PruneScan 0 unused of 66; DumpCompact/cmp_hashes: removed = pruned projections + dead readers, new =
16 helpers, changed = bundle auxiliaries, the edited consumers, the sixContactMin stack and conversions
(docs/research/sem-prune.md §4). OPEN.md / open-statements.json regenerated (render_open --check ok).

**Remains / notes.** scratch/contrib-kit/DischargesTest.lean now reports one discharge, because its `t3` control
targets the removed `bdRInvariants`; a copy with `t3` on `cartierSmooth` (scratch/sem-prune/DischargesTest2.lean)
reports the expected two — contrib-kit should move its control. `HeightLeaves.faltings5` and `GaloisPieces.deRham`
(internal structures) are now off the chain but kept. Report: docs/research/sem-prune.md; log scratch/sem-prune/log.md.
