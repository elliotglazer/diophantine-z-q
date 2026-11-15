# leaf-fold11 and leaf-fold12: genus route, route A, cm24-value, c-to-printed

**Result.** `ZInQ.OneProof.frozenTarget` now goes through `HDec.HSyn.sixContactMin_of_open15`
(`ZInQKernel/OneProof/H/TailZ19.lean`) with 61 open fields, strict LEAF/GLUE **44/17** (after the prune: 59
fields, 40/19). Under the r5 §4.8 reading (`gonzalezRotgerCountX6Ab` a composite) it is 43/18. The TYZ and GZ
hypotheses are unchanged. The build `lake build +ZInQKernel.OneProof.Main` passes, and
`#print axioms ZInQ.OneProof.frozenTarget` is `[propext, Classical.choice, Quot.sound]`.

**Counting convention (strict).** A leaf whose published form is still pending a reading counts as GLUE. Per
the reduct-glue review v2 (K6, §4) this applies to the SGA 7 IX leaves on a general DVR, `raynaudSemistable`,
`semistablePersistsDVR`, `semistableReductionDVR` and `semistableUnipotent` (SGA 7 IX may be stated over a strictly
henselian trait, while every use is at a non-henselian number-field DVR), and to `serreTateThm2` (K2). c-to-printed's
`sga7_IX_3_3` has the same base question and counts as GLUE (c) too, and so does its `blr_1_2_4` (BLR 1.2 Prop. 4
may be printed in the strictly henselian form; the review's v1 rated `NeronLocalizesDVR` "depends"). Faltings' Lemma 5
(`faltingsLemma5Printed`) stays LEAF, flagged unread: being unread is not a weaker reading. An earlier version of this note counted these
as LEAF (50/11 here, 44/15 after the prune).

Branch `wip/leaf-fold11`, on top of w62 (`e38375b3`, which has the prune of `r3`, `serreTateThm2`, `t10`).

## 1. The four steps

| Step | Source | Fields removed | Fields added | Strict count |
| --- | --- | --- | --- | --- |
| prune (w62) | PruneScan | `r3` (comp), `t10` (c), `serreTateThm2` (c, pending) | — | 62, 40/22 → 59, 40/19 |
| genus-fold | genus-route | `genusX1Field` (comp) | — | 58, 40/18 |
| route-a-fold | r1univ-rigid | — (four fields restated, kinds unchanged) | `mumfordRigidityCore` (LEAF) | 59, 41/18 |
| cm24 (TailZ18) | cm24-value | `igusaCMValue24` (LEAF) | — | 58, 40/18 |
| c-to-printed (TailZ19) | c-to-printed | `neronLocalizesDVR`, `faltingsLemma5BC`, `semistableNeronBaseChange` (all c) | four printed leaves (LEAF), `blr_1_2_4` and `sga7_IX_3_3` (c, pending base) | 61, 44/17 |

* **genus-fold** (docs/research/genus-fold.md). `t34`'s two uses in TailD's `glueOutputs_of_leaves3` need only
  `dim J₁(N) ≤ N²`, which genus-route proves with no hypothesis (`ZInQKernel/OneProof/Genus/*`). TailD's two proof
  terms and one import change; `t34` and `genusX1Field` are then unused and are removed from every generation as
  in the prune, with their dead readers (among them LPrefix's original assembly `sixContactMin_of_leaves`,
  `_of_leaves_pin`, `_of_leaves2`, `sixContactMin_of_open`, `glueOutputs_of_leaves`, `modCurveLeaves_of_bundles`,
  none in `frozenTarget`'s closure).
* **route-a-fold** (docs/research/route-a-fold.md). `r1r2`, `shimuraFamily`, `gonzalezRotgerCountX6` and
  `deligneComponentsY3Printed` are restated on abelian schemes (`R1fpPropsAb`, the printed fine-moduli problem);
  each old field is filled by `(L_iff_ab (mumfordRigidity_of_core h)).mpr`. `ZInQKernel/HDecomp/QM/*` is untouched.
* **cm24** (`TailZ18`). cm24-value's `CM24Kernel.lean` proves the field `igusaCMValue24` from Mathlib's Jacobi
  theta functional equation and explicit algebra; `OpenAddedLeaves11` drops it.
* **c-to-printed** (`TailZ19`). `neronLocalizesDVR` from BLR 1.2 Prop. 4; `faltingsLemma5BC` from Faltings'
  Lemma 5 and Raynaud's kernel bound; `semistableNeronBaseChange` from BLR 1.2/4, SGA 3 VI_B 3.10, SGA 7 IX 3.3,
  EGA IV 8.10.5 and the textbook field `geomConnOfRationalPoint`. `OpenResearchLeaves12` replaces the three
  fields by the six printed leaves. Reading risks (c-to-printed's report): BLR 1.2/4 may be printed with strict
  henselizations; the numbers of SGA 3 3.10 and Raynaud's bound are unconfirmed; Faltings' Lemma 5 was not read.

## 2. frozenTarget's hypotheses, removed and added (since w62)

* Removed: `genusX1Field`, `igusaCMValue24`, `neronLocalizesDVR`, `faltingsLemma5BC`, `semistableNeronBaseChange`,
  and `r1r2`, `shimuraFamily`, `gonzalezRotgerCountX6`, `deligneComponentsY3Printed` in their `R1fpProps` forms.
* Added: `r1r2Ab`, `shimuraFamilyAb`, `gonzalezRotgerCountX6Ab`, `deligneComponentsY3PrintedAb` (the same
  statements on abelian schemes), `mumfordRigidityCore`, `blr_1_2_4`, `faltingsLemma5Printed`,
  `raynaudKernelBound`, `sga3_VIB_3_10`, `sga7_IX_3_3`, `egaIV_8_10_5_openImm`.

## 3. Hash guard

Compared with w62 by `scratch/one-proof/DumpCompact.lean` and `cmp_hashes.py`. Deleted constants are the removed
fields' projections and the dead readers listed above; new constants are in `OneProof/Genus/*` and
`TailZ16`-`TailZ19`; changed constants are the edited bundle structures with their generated auxiliaries, the
conversions, TailD's `glueOutputs_of_leaves3`, `frozenTarget`, and the group below.

**Accepted by the lead maintainer (11-14):** 82 constants in TailE–TailZ2 change with no source change (80 proof
terms, 2 types), because TailD's new import brings Mathlib instances such as `CommSemiring.toHopfAlgebra` into
instance search. The 2 type changes are kernel-checked `rfl`-equal to the base types
(`scratch/genus-fold/diag/DefEqCheck.lean`), the axioms are standard, and `frozenTarget`'s type is still pinned to
`lean/Frozen`.

## 4. Checks

All VERIFIED on a project build host at the branch head:

* `lake build +ZInQKernel.OneProof.Main`: passes (12913 jobs); `frozenTarget` axioms standard.
* `scratch/one-proof/PruneScan.lean`: 0 unused fields. Top bundles `OpenResearchLeaves12` (32),
  `OpenTextbookLeaves10` (15), `OpenAddedLeaves11` (13), `OpenGlue7` (1): 61 fields.
* DumpCompact against w62: 11811 → 12768 constants; 19 deleted (genus-fold's removed fields and dead readers
  with their auxiliaries, and one realized equation lemma); 976 new, all in `OneProof/Genus/*` and
  `TailZ16`-`TailZ19`; 175 changed (genus-fold's 174 of §3, and `frozenTarget`).
* No `ZInQKernel/HDecomp` or `ZInQKernel/Contrib` file changed.

## 5. Remaining strict GLUE (17)

Per leaf-fold10's table less the fields above, with the pending DVR leaves of §0 (`raynaudSemistable`, `semistablePersistsDVR`, `semistableReductionDVR`, `semistableUnipotent`, `sga7_IX_3_3`, `blr_1_2_4`; reduct-b and unipotent-b work on the first four). Among the others, running or queued: x6-glue (`r1r2Ab`, `x6ConicModel`, to use the
`LAb` forms of `scratch/r1univ-rigid/R1UnivLeaves.lean`), c-to-printed2 (`r17`, `t09SymmIsogenyExists`,
`eigenformHTNew`), theta-glue (`thetaRatiosAlgebraic`), `QuotientP1Coordinate`, `shimuraFamilyAb`
(needs global class field theory). Not splittable over Mathlib's present definitions: `r11r12` (no `B_st`), `r16`.
