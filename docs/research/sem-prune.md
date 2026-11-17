# sem-prune: two hypotheses of `ZInQ.OneProof.frozenTarget` that were used only syntactically, removed

Task sem-prune, 2026-11-14. Base 9165959a (fork main plus leaf-fold14; `frozenTarget` through
`HDec.HSyn.sixContactMin_of_open18`, 68 bundle fields). `origin/wip/gap-triage` was already merged. Source of the two
findings: docs/research/gap-triage.md §0 items 1–2 and §1 A1. Results log: scratch/sem-prune/log.md. Model work, no
human review.

Marks: **VERIFIED** = compiled or read in a named file on this host; **STANDARD** = textbook mathematics;
**SPECULATIVE** = judgement.

## 1. Main result

**`frozenTarget` loses `bdRInvariants` (OpenTextbookLeaves10) and `raynaudKernelBound` (OpenResearchLeaves14), and
gains nothing** (VERIFIED: `lake build +ZInQKernel.OneProof.Main`, `#print axioms ZInQ.OneProof.frozenTarget` =
propext, Classical.choice, Quot.sound; PruneScan finds 0 unused fields of 66).

| | fields | strict (kinds.tsv) | strictest |
|---|---|---|---|
| before (9165959a) | 68 | 53 LEAF / 15 GLUE | 51 / 17 |
| after | **66** | **51 / 15** | **49 / 17** |

Both removed fields were LEAF in both readings, so only the LEAF count drops. No other field became unused (the scan
after the prune reports 0). claims.tsv had no row for either field.

What the two fields were doing, and why they were not needed (VERIFIED by reading and by the compiled plumbing):

1. **`bdRInvariants`** (`B_dR^{G_{ℚ_p}} = ℚ_p`, Fontaine) fed T23 (`t23`, Fontaine's closure of de Rham
   representations), which reached only the G9 step: `g8_g11` / `g8_g12` (TailA) passed it on as
   `h9g hR10 hT23 …`, and every proof of `G9Glue` on the chain (`ZInQ.Contrib.G9.g9Glue_of_fieldEmb`, TailC) begins
   `intro hR10 _hT23 …` and never uses it. So the step "r|G_{ℚ_ℓ} is de Rham with weights {0, −1}" is proved without
   Fontaine's closure theorem (the descent goes through the finite-coefficient reduction `coef_descent` and the
   embedding `F' ⊆ B_dR` instead).
2. **`raynaudKernelBound`** (`log #s*Ω¹_{G/S} ≤ [K:ℚ] log deg φ`) supplied the half `h(A) ≤ h(B) + ½ log deg φ` of
   `|h(A) − h(B)| ≤ ½ log deg φ` (R20). `transfer_core` (LPrefix, E3–E4) uses R20 only as `(abs_le.mp hvar).1`,
   i.e. `h(P) ≤ h(J) + ½ log deg ψ` for the isogeny `ψ : J → P`. That half follows from Faltings' printed Lemma 5
   (`h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹`) and `0 ≤ log #s*Ω¹` (`kerOmegaLog_nonneg`, proved) alone.

### 1.1 The plumbing (step 1, compiled before any deletion)

The rule followed: signatures change only by dropping an unused argument, or by replacing a hypothesis by a weaker
one that the old one implies (`G9GlueNoT23` is implied by `G9Glue` + T23; `R20Lower` by R20; `FaltingsLemma5BCLower`
by `FaltingsLemma5BC`); no field statement changes; `frozenTarget`'s statement is untouched except for the two
deleted fields.

(1) T23:
* `HDec.G0Galois.G9GlueNoT23` (TailA, next to `G9Glue`): `G9Glue` without its T23 argument.
* `ZInQ.Contrib.G9.g9GlueNoT23_of_fieldEmb` (TailC): the proof of `g9Glue_of_fieldEmb` with `intro hR10 K …` in place
  of `intro hR10 _hT23 K …`; `g9GlueNoT23_of_localModel`, `g9GlueNoT23_of_abVarBaseChange` (TailC) and
  `HSyn.g9GlueNoT23_of_deRhamComparisonHT` (TailE) are the one-line analogues of the existing `G9Glue` versions.
* `g8_g11`, `g8_g12` drop `hT23` and take `h9g : G9GlueNoT23`; `g8_g12_of_leaves3` and `afterG7_of3` (TailD) take
  `h9 : G9GlueNoT23` and no longer read `t.t23`. The four callers of `afterG7_of3` (TailD, TailE, TailI, TailK)
  pass `g9GlueNoT23_of_deRhamComparisonHT r.r10` (or `…_of_abVarBaseChange …`), built from the same inputs as the
  `G9Glue` they already pass in `GaloisPieces`.

(2) Raynaud:
* `HSyn.G0Split.R20Lower` (LPrefix): `−½ log deg φ ≤ h_F(A) − h_F(B)`. `transfer_core` takes `r20 : R20Lower` and
  uses it where it used `(abs_le.mp hvar).1`.
* `ZInQ.HeightSplit.FaltingsLemma5Lower`, `FaltingsLemma5BCLower`, `faltingsLemma5BCLower_of_BC` and
  `r20Lower_of_leaves'` (TailY; the last is the proof of `r20_of_leaves'` verbatim, stated with `R20Lower`'s body
  because TailY does not import LPrefix).
* `ReductSplit.faltingsLemma5BCLower_final` (TailZ7): the proof of `faltingsLemma5BC_of_base` with
  `isogenyBaseChangeDeg`.
* `CToPrinted.faltingsLemma5Lower_of_printed`, `faltingsLemma5BCLower_of_printed` (TailZ19): from
  `FaltingsLemma5Printed` and `kerOmegaLog_nonneg` only.
* Threading: `glueOutputs_of_leaves3`, `sixContactMin_of_leavesR3`, `sixContactMin_of_open4`, `_open6`, `_open7`
  take `h20 : R20Lower`; `_open8`–`_open11` take `hF5 : FaltingsLemma5BCLower`; `_open8` builds `h20` by
  `HSyn.r20Lower_of8` (TailZ4: N1 from `neronSchemeExtensionExists`, SS1–SS3, exactly the inputs `heightRows_of8`
  used for R20); `_open17` supplies `faltingsLemma5BCLower_of_printed r.faltingsLemma5Printed`; `_open12` (off the
  chain) supplies `faltingsLemma5BCLower_of_BC r.faltingsLemma5BC`. `_open18` and `frozenTarget` are unchanged.
* `researchLeaves7_of_open8` takes R18, R19, R21, R22 and `h5fin` from the new `HSyn.heightRowsNo20_of8` (TailZ4,
  the other five components of `heightRows_of`, without `faltingsLemma5BC`), since `heightRows_of8` reads all of
  height-split's leaves at once.

After step 1, PruneScan (prune-scan's version 095d8050, copied to scratch/sem-prune/PruneScan.lean with outputs in
scratch/sem-prune/) reports exactly `raynaudKernelBound` and `bdRInvariants` UNUSED, prune set 20 entries
(scratch/sem-prune/prune-set-scan.txt).

### 1.2 The prune (step 2)

scratch/sem-prune/prune_edit.py (genus-fold's script adapted; deletions only; every deleted line in
prune_edit_out.txt) deleted:
* 16 fields: `TextbookLeaves.t23`, `ResearchLeaves3.r20`, `OpenResearchLeaves2.r20`, `OpenTextbookLeaves2.t23`,
  `OpenTextbookLeaves3.t23`, `OpenTextbookLeaves4.t23`, `OpenResearchLeaves5.r20`, `OpenTextbookLeaves6.t23`,
  `OpenResearchLeaves7.r20`, `OpenTextbookLeaves7.bdRInvariants`, `OpenResearchLeaves8.faltingsLemma5BC`,
  `OpenTextbookLeaves8.bdRInvariants`, `OpenResearchLeaves9.faltingsLemma5BC`, `OpenTextbookLeaves9.bdRInvariants`,
  `OpenTextbookLeaves10.bdRInvariants`, `OpenResearchLeaves14.raynaudKernelBound`;
* the 18 assignments into them;
* 21 dead readers: the 19 of DeadCascade (`g8_g12_of_leaves`, `newformG12Out_of_galois`, `afterG7_of`,
  `gluePieces_of_gluePieces2`, `sixContactMin_of_leaves3`, `sixContactMin_of_leaves3'`, `sixContactMin_of_open2`,
  `_open3`, `_open5`, `_open6_poincare`, `_openQ5`–`_openQ10`, `LinkedTate.afterG7_of_final`, `afterG7_of_linked`,
  `afterG7_of_linked'`) and `heightLeaves_of8`, `heightRows_of8` (in the closure only through the deleted `r20`
  assignment; DeadCascade skips closure constants), with their `#print axioms` lines and `example`s.

The scan's 17th field, `ZInQ.HeightSplit.HeightLeaves.faltings5` (TailY), was **not** deleted: `HeightLeaves` is
height-split's leaf structure, not a bundle generation; after the prune it is simply off the closure
(prune-set-applied.txt is the scan's set without it). The two conversions I had added for the off-chain callers
(`g9GlueNoT23_of_g9Glue`, `r20Lower_of_r20`) lost all users with those callers and were removed.
`GaloisPieces.deRham` (an internal structure, not a top bundle) is now unread on the chain; it is left as it is.

## 2. Every hypothesis (kinds.tsv after the prune; the full statements are docs/one-proof/OPEN.md)

### OpenResearchLeaves14 (34 fields)

| field | kind | strict | strictest |
|---|---|---|---|
| `babaGranathRationalAb` | published | LEAF | LEAF |
| `blr_1_2_4` | consequence | GLUE | GLUE |
| `bostLowerBound` | published | LEAF | LEAF |
| `deRhamH1AbVarT` | published | LEAF | LEAF |
| `dsThm965` | published | LEAF | LEAF |
| `dsThm966` | published | LEAF | LEAF |
| `egaIV_8_10_5_openImm` | published | LEAF | LEAF |
| `eigenformHTNew` | consequence | GLUE | GLUE |
| `elkiesEquationsX6Ab` | published | GLUE | GLUE |
| `faltingsLemma5Printed` | published | LEAF | LEAF |
| `gaudronRemondThm14` | published | LEAF | LEAF |
| `gonzalezRotgerCountX6Ab` | published | LEAF | GLUE |
| `gonzalezRotgerX6Ab` | published | LEAF | LEAF |
| `hodgeTateDecompAbVar` | published | LEAF | LEAF |
| `igusaChi10` | published | LEAF | LEAF |
| `igusaPsi4` | published | LEAF | LEAF |
| `javanpeykarBound` | published | LEAF | LEAF |
| `mumfordRigidityCore` | published | LEAF | LEAF |
| `neronSchemeModelExistsDVR` | published | LEAF | LEAF |
| `pazukiCor13Upper` | published | LEAF | LEAF |
| `r11r12` | composite | GLUE | GLUE |
| `r16` | composite | GLUE | GLUE |
| `r17` | consequence | GLUE | GLUE |
| `r7a` | published | LEAF | LEAF |
| `r9a` | published | LEAF | LEAF |
| `r9b` | published | LEAF | LEAF |
| `rayClassCMAb` | consequence | GLUE | GLUE |
| `raynaudSemistableSH` | published | LEAF | LEAF |
| `semistablePersistsSHcp` | published | LEAF | LEAF |
| `semistableUnipotent` | consequence | GLUE | GLUE |
| `sga3_VIB_3_10` | published | LEAF | LEAF |
| `sga7_IX_3_3` | consequence | GLUE | GLUE |
| `shimuraFamilyAb` | consequence | GLUE | GLUE |
| `strictHenselizationPair` | composite | GLUE | GLUE |

### OpenTextbookLeaves10 (14 fields)

| field | kind | strict | strictest |
|---|---|---|---|
| `cartierSmooth` | published | LEAF | LEAF |
| `charPolyIndepOfEllAlgClosed` | published | LEAF | LEAF |
| `gagaMorphism` | published | LEAF | LEAF |
| `geomConnOfRationalPoint` | published | LEAF | LEAF |
| `groupSchemeEquidim` | published | LEAF | LEAF |
| `homFreeFiniteAlgClosed` | published | LEAF | LEAF |
| `igusaGL2` | published | LEAF | LEAF |
| `mulEtaleAbelianScheme` | published | LEAF | LEAF |
| `mumfordTorsionAlgClosed` | published | LEAF | LEAF |
| `neronSchemeExtensionExists` | published | LEAF | LEAF |
| `poincareComplement` | published | LEAF | LEAF |
| `regularSmoothPerfect` | published | LEAF | LEAF |
| `uniformizationLeafAll` | published | LEAF | LEAF |
| `yuThm11` | published | LEAF | LEAF |

### OpenAddedLeaves13 (17 fields)

| field | kind | strict | strictest |
|---|---|---|---|
| `axSenTate` | published | LEAF | LEAF |
| `deligneComponentsX6PrintedAb` | published | LEAF | LEAF |
| `deligneComponentsY3PrintedAb` | published | GLUE | GLUE |
| `egaIV_8_10_5_xii` | published | LEAF | LEAF |
| `geomConnOfAlgClosure` | published | LEAF | LEAF |
| `milneIsogenyQuasiInverse` | published | LEAF | LEAF |
| `phiAmpleIsogeny` | published | LEAF | LEAF |
| `picRepresentableAbVar` | published | LEAF | LEAF |
| `picZeroAbVar` | published | LEAF | LEAF |
| `qmCentralizerCMC` | published | LEAF | LEAF |
| `shimizuCovolumeO1` | published | LEAF | LEAF |
| `shimuraGoodReductionNoGuard` | composite | GLUE | GLUE |
| `shimuraTaniyamaQbar` | published | LEAF | LEAF |
| `tateTwistInvariants` | published | LEAF | LEAF |
| `thetaRatiosAlgebraic` | composite | GLUE | GLUE |
| `valenceFormulaCocompactEq` | published | LEAF | LEAF |
| `weilPairingMumford` | published | LEAF | GLUE |

### OpenGlue7 (1 fields)

| field | kind | strict | strictest |
|---|---|---|---|
| `quotientP1Coordinate` | project glue | GLUE | GLUE |
## 3. The remaining leaves by the theory they come from

Unchanged from leaf-fold14 except: group **D** (Faltings 1983 and Faltings heights) loses `raynaudKernelBound`
(only Faltings' printed Lemma 5 is used, for the half `h(B) ≤ h(A) + ½ log deg φ`), and group **E** (p-adic Hodge
theory) loses `bdRInvariants` (Fontaine's `B_dR^{G_{ℚ_p}} = ℚ_p` and T23 are not used by the G9 step).

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

* Base: `lake build +ZInQKernel.OneProof.Main` OK; DumpCompact (13414 constants, scratch/sem-prune/hashes_before.txt);
  PruneScan 0 unused of 68.
* After step 1 (plumbing): build OK; PruneScan: exactly the two target fields unused.
* After step 2 (prune): `lake build +ZInQKernel.OneProof.Main` OK (12918 jobs);
  `#print axioms ZInQ.OneProof.frozenTarget`: `[propext, Classical.choice, Quot.sound]`.
* PruneScan: OpenResearchLeaves14 34, OpenTextbookLeaves10 14, OpenAddedLeaves13 17, OpenGlue7 1 = 66 fields,
  0 unused, prune set empty (scratch/sem-prune/used-fields.txt, prune-set.txt).
* DumpCompact + cmp_hashes.py (scratch/sem-prune/cmp_hashes_out.txt): before 13414, after 13393; removed 37 = the
  16 pruned fields' projections + the 21 dead readers; new 16 = the helpers of §1.1 (LPrefix 1, TailA 1, TailC 3,
  TailE 1, TailY 4, TailZ4 2, TailZ7 1, TailZ19 3); changed 214:
  - 176 generated auxiliaries and projections (value only: field index shift) of the 16 edited bundle structures;
  - the edited consumers `g8_g11`, `g8_g12`, `g8_g12_of_leaves3`, `afterG7_of3`, `transfer_core` (type);
  - the stack `glueOutputs_of_leaves3`, `sixContactMin_of_leavesR3`, `sixContactMin_of_open4`, `_open6`, `_open7`,
    `_open8`, `_open9`, `_open10`, `_open11` (type: the new binder) and `_open12`, `_open17` (value);
  - conversions (value: a deleted assignment, or the new argument of `afterG7_of3`): `gluePieces_of_gluePieces3`,
    `gluePieces_of_open2`, `_open3`, `_open4`, `researchLeaves2_of_open5`, `researchLeaves3_of`,
    `researchLeaves3_of_open2`, `researchLeaves5_of_open7`, `researchLeaves7_of_open8`, `researchLeaves8_of_open9`,
    `researchLeaves9_of_open10`, `researchLeaves9_of_open14`, `textbookLeaves2_of_open3`, `textbookLeaves3_of_open4`,
    `textbookLeaves4_of_open5`, `textbookLeaves4_of_open6`, `textbookLeaves6_of_open7`, `textbookLeaves7_of_open8`,
    `textbookLeaves8_of_open9`, `textbookLeaves9_of_open10`, `textbookLeaves_of_open`, `textbookLeaves_of_open2`.
  `frozenTarget` and `sixContactMin_of_open18` have unchanged hashes. No other constant changed.
* scratch/contrib-kit/DischargesTest.lean now reports **one** discharge (t1), not two: its control `t3` is stated
  as `OpenTextbookLeaves10.bdRInvariants`, the field this task removes, so it discharges nothing. The same test with
  `t3` moved to `cartierSmooth` (scratch/sem-prune/DischargesTest2.lean) reports the two expected discharges (t1;
  t3 flagged for `sorry`). The contrib-kit test needs that one-line update (not mine to edit).
* `lake env lean scripts/one_proof/OpenStatements.lean`: 72 open hypotheses (66 + 6);
  `render_open.py --check`: 66 bundle fields, all classified; OPEN.md regenerated (strictest 49/17, strict 51/15).
* FaithCheck: not needed (no HDec copy was replaced by a kernel declaration).

## 5. Not done, and why

* `HeightLeaves.faltings5` (§1.2) kept; `GaloisPieces.deRham` kept (both internal structures, off the top bundles).
* The older bundle generations not on the chain (`ResearchLeaves.r20`, `OpenResearchLeaves.r20`,
  `OpenTextbookLeaves.t23`, `OpenTextbookLeaves5.t23`, `OpenResearchLeaves10`–`13`'s `faltingsLemma5BC` /
  `raynaudKernelBound`) keep their fields, as in the earlier prunes (only the scan's set is removed).
* gap-triage's other items (A2–A12) are other tasks.

## 6. `frozenTarget`: removed and added hypotheses

* Removed: `OpenTextbookLeaves10.bdRInvariants : ∀ (p : ℕ) [Fact p.Prime], ZInQ.Contrib.HodgeSplit.BdRInvariants p`
  (Fontaine, Astérisque 223 Exp. II; LEAF) and `OpenResearchLeaves14.raynaudKernelBound : CToPrinted.RaynaudKernelBound`
  (Raynaud, Astérisque 127 Exp. VII Cor. 2.1.3, number UNVERIFIED; LEAF).
* Added: none. The binders of `frozenTarget` are the same four bundle types, each of the two edited ones with one
  field fewer.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| origin/wip/gap-triage | already in the base | findings §0.1–2, §1 A1 |
| origin/wip/prune-scan 095d8050 | not merged; PruneScan.lean and DeadCascade.lean copied to scratch/sem-prune/ (outputs there) | yes |
| genus-fold 98a02e43 | in the base | prune_edit.py adapted |
