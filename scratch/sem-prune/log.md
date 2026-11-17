# sem-prune results log

- 2026-11-14 19:35 start. Base 9165959a (leaf-fold14-int). `git merge origin/wip/gap-triage`: already up to date.
- PruneScan.lean taken from origin/wip/prune-scan 095d8050 (unused-argument positions are not uses);
  DeadCascade.lean from the same branch; prune_edit.py precedent: genus-fold 98a02e43.
- Base build `lake build +ZInQKernel.OneProof.Main` started.
- Base build OK (frozenTarget: propext, Classical.choice, Quot.sound). DumpCompact on base: 13414 constants
  (scratch/sem-prune/hashes_before.txt). PruneScan on base (2 min): 68 top fields, 0 unused, prune set empty
  (*-before.txt).
- Plumbing (step 1) compiles: `lake build +ZInQKernel.OneProof.Main` OK, frozenTarget standard axioms.
  (1) `G0Galois.G9GlueNoT23` (TailA) + `g9GlueNoT23_of_g9Glue`; `g8_g11`, `g8_g12` drop `hT23` and take
  `h9g : G9GlueNoT23`; `g8_g12_of_leaves3`, `afterG7_of3` (TailD) take `h9 : G9GlueNoT23` (callers TailD/E/I/K supply
  `g9GlueNoT23_of_deRhamComparisonHT r.r10` or `..._of_abVarBaseChange`); TailC copies of g9Glue_of_fieldEmb /
  _localModel / _abVarBaseChange without the T23 binder; off-chain TailA callers use `g9GlueNoT23_of_g9Glue m.deRham t.t23`.
  (2) `G0Split.R20Lower` (LPrefix); `transfer_core` takes `r20 : R20Lower` and uses it directly (was `(abs_le.mp hvar).1`);
  `glueOutputs_of_leaves3`, `sixContactMin_of_leavesR3`, `_open4`, `_open6`, `_open7` take `h20 : R20Lower`;
  `_open8` .. `_open11` take `hF5 : HeightSplit.FaltingsLemma5BCLower`; `_open8` builds h20 by `r20Lower_of8`
  (TailZ4, from `r20Lower_of_leaves'`, TailY copy of `r20_of_leaves'`); `_open17` supplies
  `CToPrinted.faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed` (TailZ19: printed + kerOmegaLog_nonneg,
  then `ReductSplit.faltingsLemma5BCLower_final`, TailZ7 copy of faltingsLemma5BC_of_base). researchLeaves7_of_open8
  takes r18, r19, r21, r22, h5fin from `heightRowsNo20_of8` (no faltingsLemma5BC). Off-chain callers use
  `r20Lower_of_r20 r.r20` / `faltingsLemma5BCLower_of_BC r.faltingsLemma5BC`.
- PruneScan after plumbing: OpenResearchLeaves14.raynaudKernelBound and OpenTextbookLeaves10.bdRInvariants UNUSED;
  prune set 20 entries (prune-set-scan.txt): 17 fields + 3 constants. HeightLeaves.faltings5 (TailY, height-split's
  leaf structure, not a bundle generation) is not deleted (prune-set-applied.txt = scan minus that line).
  DeadCascade (on prune-set-applied): 21 dead readers (+ generated casesOn/recOn). heightLeaves_of8 and heightRows_of8
  (TailZ4) also deleted: in the closure only through the deleted r20 assignment, they read the deleted
  OpenResearchLeaves8.faltingsLemma5BC (DeadCascade skips closure constants). One assignment the first draft missed
  (TailZ15 researchLeaves9_of_open10 faltingsLemma5BC) added to prune_edit.py. The two off-chain conversions
  g9GlueNoT23_of_g9Glue and r20Lower_of_r20 lost all users and were removed.
- Step 2 (prune) compiles: `lake build +ZInQKernel.OneProof.Main` OK, frozenTarget: propext, Classical.choice, Quot.sound.
- Checks after the prune (all VERIFIED on this host, one Lean process at a time):
  * PruneScan: 34 + 14 + 17 + 1 = 66 top fields, 0 unused, prune set empty.
  * DumpCompact: frozenTarget standard axioms; 13393 constants; cmp_hashes.py: removed 37 (16 pruned field projections,
    21 dead readers), new 16 (helpers), changed 214 (176 bundle auxiliaries/projection values of the 16 edited bundles;
    38 others: the 5 edited consumers g8_g11, g8_g12, g8_g12_of_leaves3, afterG7_of3, transfer_core; the stack
    glueOutputs_of_leaves3, sixContactMin_of_leavesR3, sixContactMin_of_open4/6/7/8/9/10/11 (new binder) and
    _open12/_open17 (value); conversions researchLeaves*/textbookLeaves*/gluePieces_of_* (assignment deleted or
    afterG7_of3's new argument)). frozenTarget and sixContactMin_of_open18 unchanged hashes.
  * DischargesTest (scratch/contrib-kit): now reports ONE discharge (t1); its t3 control targets the pruned
    bdRInvariants, so it discharges nothing. Copy with t3 on `cartierSmooth` (scratch/sem-prune/DischargesTest2.lean):
    two discharges (t1, t3 flagged sorry), as expected.
  * OpenStatements.lean: 72 open hypotheses; render_open.py --check: 66 bundle fields, all classified; OPEN.md:
    strictest 49/17 (was 51/17), strict 51/15 (was 53/15).
