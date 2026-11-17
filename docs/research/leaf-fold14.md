# leaf-fold14: reduct-b and t09-pic folded into the single proof; 68 fields, strict GLUE 15 (was 18 of 65)

Task leaf-fold14, 2026-11-14. Base 29885092 (`wip/leaf-fold13`: fork main 6df2a643 plus x6-fold; top
`HDec.HSyn.sixContactMin_of_open16`, 65 fields, strict 47/18, strictest 46/19). Merged (new files only, no conflicts):
`origin/wip/reduct-b` 85495b37, `origin/wip/unipotent-b` 24c44f3d, `origin/wip/t09-pic` 3d0f47a8. New Lean:
- `ZInQKernel/OneProof/H/TailZ23.lean` (48 KB): reduct-b's `Body.lean` (namespace `ReductB`, without its fold check
  and `#print` lines), bundle `OpenResearchLeaves14`, `sixContactMin_of_open17`;
- `ZInQKernel/OneProof/H/TailZ24.lean` (51 KB): t09-pic's `Pic.lean` (namespace `T09Pic`, without its §0 verbatim
  copy of the field type, the six-way split of L4 and the `#print` lines), bundle `OpenAddedLeaves13`,
  `sixContactMin_of_open18`, the new top;
- the switch of `ZInQKernel/OneProof/Main.lean`.

Checks and tools are in `scratch/leaf-fold14/`; the results log is `log.md`. No existing OneProof module, no other
file under `ZInQKernel/` or `blueprint/`, and no other task's files were edited, with one exception: in
`docs/one-proof/claims.tsv` the four claim rows of the removed fields (reduct-b's three, t09-pic's one) were deleted,
because `render_open.py` exits when a claim names a field that is no longer open (leaf-fold13 did the same). No HDec
copy was deleted, so FaithCheck was not needed. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator is the source report's and UNVERIFIED.

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves14) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves13)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

It depends only on `[propext, Classical.choice, Quot.sound]` (VERIFIED, `lake build +ZInQKernel.OneProof.Main`). The H
half goes through the new top (`OneProof/H/TailZ24.lean`):

```lean
theorem HDec.HSyn.sixContactMin_of_open18 (r : OpenResearchLeaves14) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves13) (g : OpenGlue7) : ZInQ.SixContactMin
```

Two folds were taken. Neither raised the strict GLUE count (kinds.tsv, `strict` column):

| step | fields | strict LEAF/GLUE | strictest LEAF/GLUE |
|---|---|---|---|
| base (leaf-fold13) | 65 | 47/18 | 46/19 |
| fold 1, reduct (`TailZ23`, `sixContactMin_of_open17`) | 65 | **49/16** (GLUE −2) | 47/18 |
| fold 2, t09-pic (`TailZ24`, `sixContactMin_of_open18`) | 68 | **53/15** (GLUE −1) | 50/18 |

**Fold 1, reduct (reduct-b).** Three strict-GLUE research fields go, and three come in (2 LEAF + 1 GLUE):
- `semistableReductionDVR` (SGA 7 IX 3.6 over a DVR) is reduct-b's **K1** (`ReductB.semistableReductionDVR_of_raynaud`):
  from 4.7 over a DVR, the textbook fields `mumfordTorsionAlgClosed` and `mulEtaleAbelianScheme`
  (`HDec.HSyn.semistableReductionDVR_of14`).
- `raynaudSemistable` (4.7 over a DVR) is `ReductB.raynaudSemistable_of_SH_pair` from the new fields
  `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` (the unrestricted strictly henselian printed form; `r6`,
  `PkgI2.RaynaudCriterion`, is stated over every field, so the `[CharZero] [PerfectField]` variant does not fit) and
  `strictHenselizationPair : ReductGlue.StrictHenselizationPair`, with `mulEtaleAbelianScheme`
  (`HDec.HSyn.raynaudSemistable_of14`).
- `semistablePersistsDVR` (3.3a over a DVR) is not re-proved: the restricted leaf cannot give it at imperfect residue
  fields. Its only two uses, SS1 (`semistableReductionThm`) and SS3 (`semistablePersists`) of leaf-fold9's bundle,
  are proved at number fields from the new field `semistablePersistsSHcp : ReductB.SemistablePersistsSHcp` and the
  pair by `ReductB.ss1_ss3_of_cp` (`HDec.HSyn.ss1_ss3_of14`), with the same glue as `TailZ15`
  (`semistableLocalGlobal` from `blr_1_2_4`, `semistableAlmostAll_of10`).

  **Consequence for the chain (VERIFIED by the build).** Since the general field cannot be produced, the new bundle
  cannot be mapped to `OpenResearchLeaves13`. `TailZ23` maps it to leaf-fold9's `OpenResearchLeaves9` (with
  leaf-fold10's `OpenAddedLeaves9`), the newest generation that has SS1 and SS3 as fields:
  `researchLeaves9_of_open14` and `addedLeaves9_of_open14` compose the maps of `TailZ22`, `TailZ19`, `TailZ18`,
  `TailZ17` and `TailZ15` by hand, with the same terms (`x6Rows_of_open14` is `x6Rows_of_open13`'s term), and
  `sixContactMin_of_open17` calls `sixContactMin_of_open11`. The generations `open12`–`open16` stay compiled and
  unchanged but are no longer on `frozenTarget`'s path. Every other field reaches `OpenResearchLeaves9` by the same
  term as before; only `r6`, SS1, SS3 and `semistableReductionDVR` changed source.

**unipotent-b: not taken (SPECULATIVE count, VERIFIED premises).** Both of its routes for `semistableUnipotent` (GLUE)
need `ReductGlue.StrictHenselizationInside`, which is in no current bundle and does not follow from
`StrictHenselizationPair` (it asks for the inertia field inside a fixed algebraic closure; read in `TailZ14`). It is
a composite like the pair, so strict GLUE:
- the recommended route (`SemistableUnipotentPrintedGen` + glue `SemiAbelianDescendsSepClosed` + `Inside` +
  `mulEtaleAbelianScheme`) is −1 GLUE +2 GLUE;
- the geometric route (`SemistableUnipotentPrintedGeom` + `Inside` + `mulEtaleAbelianScheme`) is −1 GLUE +1 GLUE, and
  `PrintedGeom` is a LEAF only under an unread reading of SGA 7 IX.
Neither lowers the strict count, so `semistableUnipotent` stays as it was.

**Fold 2, t09-pic.** The added field `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` (GLUE, "not
splittable" per av-split) is `T09Pic.t09SymmIsogenyExists_of_four` from four printed leaves over the vendored Picard
functor, the single-L4 form as the task asks: `picRepresentableAbVar : T09Pic.PicRepresentableAbVar`,
`picZeroAbVar : T09Pic.PicZeroAbVar`, `phiAmpleIsogeny : T09Pic.PhiAmpleIsogeny`,
`weilPairingMumford : T09Pic.WeilPairingMumford` (`addedLeaves12_of_open13`, the ordinary one-step map;
`sixContactMin_of_open18` calls `sixContactMin_of_open17`). Very ample ⇒ ample is proved in `TailZ24`.

### 1.1 Where the new fields' constants are declared (VERIFIED by grep and the build)

- `ReductGlue.RaynaudSemistableSH`, `ReductGlue.StrictHenselizationPair`: `OneProof/H/TailZ14.lean` (reduct-glue,
  already in the chain).
- `ReductB.SemistablePersistsSHcp`: `TailZ23` (new; reduct-b's def, unchanged text).
- `T09Pic.PicRepresentableAbVar`, `PicZeroAbVar`, `PhiAmpleIsogeny`, `WeilPairingMumford`: `TailZ24` (new; t09-pic's
  defs over `ZInQKernel/Contrib/CloudW07JacobiansCurves/` and `ZInQKernel/Contrib/FrobChain/Rigidity`, imported, not
  copied).
- **Uses** (`scratch/leaf-fold14/Uses.lean`, `uses_out.txt`): a BFS over the constants reachable from
  `sixContactMin_of_open18` (73179) finds non-bundle theorems taking each Prop the new leaves feed: SS1
  (`ZInQ.HeightSplit.r19_of_leaves`, `r21_of_leaves`, `stableHeightFinite_of`), SS3 (`r20_of_leaves'`), `r6`
  (`HDec.PkgI2.goodReduction_of_QM_rational3`, `kernelFieldExists_*`), `T09_SymmIsogenyExists`
  (`HDec.HSyn.t9_of_leaves5`, `detTate_of_leaves4`, `tatePairingZl_of_leaves4`). This shows membership in the
  closure; the live paths were not traced further (as for unipotent-b's r8 finding, a field can be in the closure and
  still be inert).

## 2. Every hypothesis

Generated by `scratch/leaf-fold14/mk_table.py` from `docs/one-proof/open-statements.json` (the build) and
`docs/one-proof/kinds.tsv`. Lean types as `#discharges` prints them. Rows of kept fields are unchanged from
leaf-fold13; the seven new rows are marked.

### OpenResearchLeaves14 (35 fields)

| field | Lean type | kind | strict | strictest | flag | new |
|---|---|---|---|---|---|---|
| `shimuraFamilyAb` | `HDec.QMSplit.Moduli.ShimuraFamilyAb` | consequence | GLUE | GLUE |  |  |
| `igusaPsi4` | `HDec.QMSplit.Theta.IgusaPsi4` | published | LEAF | LEAF |  |  |
| `igusaChi10` | `HDec.QMSplit.Theta.IgusaChi10` | published | LEAF | LEAF |  |  |
| `r7a` | `PkgI2.NeronOggShafarevich` | published | LEAF | LEAF |  |  |
| `r9a` | `PkgI3.FaltingsSemisimple` | published | LEAF | LEAF |  |  |
| `r9b` | `PkgI3.FaltingsTate` | published | LEAF | LEAF |  |  |
| `hodgeTateDecompAbVar` | `ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | published | LEAF | LEAF |  |  |
| `deRhamH1AbVarT` | `ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | published | LEAF | LEAF |  |  |
| `r11r12` | `HDec.PkgI4.PanBerger` | composite | GLUE | GLUE |  |  |
| `eigenformHTNew` | `ZInQ.Contrib.HodgeSplit.EigenformHTNew` | consequence | GLUE | GLUE |  |  |
| `dsThm965` | `ZInQ.Contrib.HodgeSplit.DSThm965` | published | LEAF | LEAF |  |  |
| `dsThm966` | `ZInQ.Contrib.HodgeSplit.DSThm966` | published | LEAF | LEAF |  |  |
| `r16` | `LeafModCurves.R16_EichlerShimuraJ1'` | composite | GLUE | GLUE |  |  |
| `r17` | `LadicCond.CarayolR17'` | consequence | GLUE | GLUE |  |  |
| `bostLowerBound` | `ZInQ.HeightSplit.BostLowerBound` | published | LEAF | LEAF |  |  |
| `javanpeykarBound` | `ZInQ.HeightSplit.JavanpeykarBound` | published | LEAF | LEAF |  |  |
| `pazukiCor13Upper` | `ZInQ.HeightSplit.PazukiCor13Upper` | published | LEAF | LEAF |  |  |
| `gaudronRemondThm14` | `ZInQ.HeightSplit.GaudronRemondThm14` | published | LEAF | LEAF |  |  |
| `semistableUnipotent` | `ReductSplit.SemistableUnipotent` | consequence | GLUE | GLUE | pending reading: base (strictly henselian trait vs number-field DVR) |  |
| `neronSchemeModelExistsDVR` | `ReductSplit.NeronSchemeModelExistsDVR` | published | LEAF | LEAF |  |  |
| `gonzalezRotgerCountX6Ab` | `ShimuraSplit.GonzalezRotgerCountX6Ab` | published | LEAF | GLUE | strictest reading: composite (frontier r5 4.8) |  |
| `mumfordRigidityCore` | `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` | published | LEAF | LEAF |  |  |
| `blr_1_2_4` | `CToPrinted.BLR_1_2_4` | consequence | GLUE | GLUE | pending reading: may be printed in the strictly henselian form |  |
| `faltingsLemma5Printed` | `CToPrinted.FaltingsLemma5Printed` | published | LEAF | LEAF | unread |  |
| `raynaudKernelBound` | `CToPrinted.RaynaudKernelBound` | published | LEAF | LEAF |  |  |
| `sga3_VIB_3_10` | `CToPrinted.SGA3_VIB_3_10` | published | LEAF | LEAF |  |  |
| `sga7_IX_3_3` | `CToPrinted.SGA7_IX_3_3` | consequence | GLUE | GLUE | pending reading: base |  |
| `egaIV_8_10_5_openImm` | `CToPrinted.EGAIV_8_10_5_openImm` | published | LEAF | LEAF |  |  |
| `babaGranathRationalAb` | `HDec.QMSplit.Moduli.BabaGranathRationalAb` | published | LEAF | LEAF | one table reading (CM assignment, section 3.1) UNVERIFIED |  |
| `gonzalezRotgerX6Ab` | `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` | published | LEAF | LEAF |  |  |
| `elkiesEquationsX6Ab` | `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab` | published | GLUE | GLUE | pending reading: the fibre clause combines Elkies with the moduli meaning of W (composite under the strict reading) |  |
| `rayClassCMAb` | `ShimuraGlue.Ray.RayClassCMAb` | consequence | GLUE | GLUE |  |  |
| `raynaudSemistableSH` | `ReductGlue.RaynaudSemistableSH` | published | LEAF | GLUE | reading risk (reduct-b §5): the print may assume an algebraically closed residue field, and then this unrestricted form is stronger than the print for imperfect residue fields (r6 is stated over every field, so the restricted form does not fit); pending review | **new** |
| `semistablePersistsSHcp` | `ReductB.SemistablePersistsSHcp` | published | LEAF | LEAF | restricted form (char K = 0, perfect hence algebraically closed residue field): a specialization of every reading of the print; pending review | **new** |
| `strictHenselizationPair` | `ReductGlue.StrictHenselizationPair` | composite | GLUE | GLUE | combines strict henselization along a finite extension with Neron models commuting with it; pending review | **new** |

### OpenTextbookLeaves10 (15 fields)

| field | Lean type | kind | strict | strictest | flag | new |
|---|---|---|---|---|---|---|
| `mulEtaleAbelianScheme` | `AvSplit.T4.MulEtaleAbelianScheme` | published | LEAF | LEAF |  |  |
| `mumfordTorsionAlgClosed` | `AvSplit.MumfordTorsionAlgClosed` | published | LEAF | LEAF |  |  |
| `homFreeFiniteAlgClosed` | `ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | published | LEAF | LEAF |  |  |
| `charPolyIndepOfEllAlgClosed` | `ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | published | LEAF | LEAF |  |  |
| `poincareComplement` | `ZInQ.Contrib.AVB1.PoincareComplement` | published | LEAF | LEAF |  |  |
| `cartierSmooth` | `AVGlue.CartierSmooth` | published | LEAF | LEAF |  |  |
| `geomConnOfRationalPoint` | `AVGlue.GeomConnOfRationalPoint` | published | LEAF | LEAF |  |  |
| `groupSchemeEquidim` | `AVGlue.GroupSchemeEquidim` | published | LEAF | LEAF |  |  |
| `uniformizationLeafAll` | `BPAnalytic.Uniformization.UniformizationLeafAll` | published | LEAF | LEAF |  |  |
| `gagaMorphism` | `ZInQ.HomLattice.GAGAMorphism` | published | LEAF | LEAF |  |  |
| `bdRInvariants` | `∀ (p : ℕ) [inst : Fact (Nat.Prime p)], ZInQ.Contrib.HodgeSplit.BdRInvariants p` | published | LEAF | LEAF |  |  |
| `yuThm11` | `HDec.QMSplit.Yu.YuThm11` | published | LEAF | LEAF |  |  |
| `regularSmoothPerfect` | `CurveSplit.RegularSmoothPerfect` | published | LEAF | LEAF |  |  |
| `igusaGL2` | `ZInQ.RLeaf.IgusaGL2` | published | LEAF | LEAF |  |  |
| `neronSchemeExtensionExists` | `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | published | LEAF | LEAF |  |  |

### OpenAddedLeaves13 (17 fields)

| field | Lean type | kind | strict | strictest | flag | new |
|---|---|---|---|---|---|---|
| `thetaRatiosAlgebraic` | `HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic` | composite | GLUE | GLUE |  |  |
| `qmCentralizerCMC` | `HDec.QMSplit.Aut.QMCentralizerCMC` | published | LEAF | LEAF |  |  |
| `tateTwistInvariants` | `ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | published | LEAF | LEAF |  |  |
| `axSenTate` | `ZInQ.Contrib.HodgeSplit.AxSenTate` | published | LEAF | LEAF |  |  |
| `milneIsogenyQuasiInverse` | `AvSplit.MilneIsogenyQuasiInverse` | published | LEAF | LEAF |  |  |
| `shimuraTaniyamaQbar` | `HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | published | LEAF | LEAF |  |  |
| `egaIV_8_10_5_xii` | `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | published | LEAF | LEAF |  |  |
| `shimuraGoodReductionNoGuard` | `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` | composite | GLUE | GLUE |  |  |
| `valenceFormulaCocompactEq` | `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` | published | LEAF | LEAF |  |  |
| `shimizuCovolumeO1` | `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` | published | LEAF | LEAF |  |  |
| `deligneComponentsY3PrintedAb` | `ShimuraGlue.DeligneComponentsY3PrintedAb` | published | GLUE | GLUE | pending reading: depends (medium), whether one display states that the PEL moduli scheme with its uniformization is the canonical model at B = (2,-3/Q), level K3 (Deligne 389 section 5, Milne 2005 section 14) |  |
| `deligneComponentsX6PrintedAb` | `ShimuraGlue.DeligneComponentsX6PrintedAb` | published | LEAF | LEAF |  |  |
| `geomConnOfAlgClosure` | `HDec.QMSplit.Moduli.GeomConnOfAlgClosure` | published | LEAF | LEAF | weakened form |  |
| `picRepresentableAbVar` | `T09Pic.PicRepresentableAbVar` | published | LEAF | LEAF | pending review (one model review, no errors) | **new** |
| `picZeroAbVar` | `T09Pic.PicZeroAbVar` | published | LEAF | LEAF | combines Mumford 13 (over Kbar) with descent to K (Kleiman 9.5.1) and geometric connectedness of the identity component (SGA 3 VI_A 2.4); pending review (one model review, no errors) | **new** |
| `phiAmpleIsogeny` | `T09Pic.PhiAmpleIsogeny` | published | LEAF | LEAF | finiteness over a non-closed K descends from Kbar (fpqc descent); Mumford's Application 1 is stated for effective D (general ample L via L^m); pending review (one model review, no errors) | **new** |
| `weilPairingMumford` | `T09Pic.WeilPairingMumford` | published | LEAF | GLUE | strictest reading: composite (one leaf bundling several printed properties of e_n: perfect, Galois, compatible, dual-adjoint, alternating on lambda_L, with values pinned to weilScalar via Kleiman 9.2.5 and Mumford 8 (iv)); sign convention immaterial; pending review (one model review, no errors) | **new** |

### OpenGlue7 (1 fields)

| field | Lean type | kind | strict | strictest | flag | new |
|---|---|---|---|---|---|---|
| `quotientP1Coordinate` | `HDec.MCRGlue.QuotientP1Coordinate` | project glue | GLUE | GLUE |  |  |


## 3. The remaining leaves by the theory they come from

Only two groups of leaf-fold10 §3 change (grouping SPECULATIVE):
- **C. Néron models, semistable reduction and monodromy.** Out: `raynaudSemistable`, `semistablePersistsDVR`,
  `semistableReductionDVR` (DVR forms, consequences). In: `raynaudSemistableSH` (4.7, printed strictly henselian base),
  `semistablePersistsSHcp` (3.3a, printed base, restricted), `strictHenselizationPair` (composite: EGA IV₄
  18.8.10/18.6.8 with BLR 1.2/2). Still there: `r7a`, `semistableUnipotent`, `neronSchemeModelExistsDVR`,
  `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `blr_1_2_4`, `sga3_VIB_3_10`, `sga7_IX_3_3`,
  `egaIV_8_10_5_openImm`.
- **B. Abelian varieties: the textbook theory.** Out: `t09SymmIsogenyExists`. In: `picRepresentableAbVar`
  (Grothendieck–Murre–Oort), `picZeroAbVar` (Mumford §13), `phiAmpleIsogeny` (Mumford §§6, 8), `weilPairingMumford`
  (Mumford §§20, 23).

## 4. Checks (all VERIFIED; one Lean process at a time)

- **Build.** The first `lake build +ZInQKernel.OneProof.Main` on the base replayed or rebuilt the chain (10 min, exit 0,
  standard axioms). `lake build +ZInQKernel.OneProof.H.TailZ23` (15 s) and `+ZInQKernel.OneProof.H.TailZ24` (26 s)
  passed with no errors, then `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` after each switch:
  exit 0, `'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Hash guard** (op-compact's `DumpCompact`; `scratch/leaf-fold14/DumpBase.lean` over `TailZ22` and `Main`'s other
  imports, `DumpNew.lean` over `Main`; `cmp_hashes.py`, `cmp_hashes_out.txt`): 13225 constants before, 13414 after,
  **0 deleted, 0 changed**, 189 new: 91 in `TailZ23`, 97 in `TailZ24`, and `ZInQ.OneProof.frozenTarget` (its statement
  changes as in §6). The before dump is identical to x6-fold's `hashes_after.txt` minus `frozenTarget` (0/0/0), so the
  rebuild on the base changed nothing.
- **Open statements.** `lake env lean scripts/one_proof/OpenStatements.lean` (74 open hypotheses: 68 H fields + 6),
  `python3 scripts/one_proof/render_open.py --check` (`ok: 68 bundle fields, all classified`), then
  `python3 scripts/one_proof/render_open.py` (`strictest 50/18`). `open-statements.json` and `OPEN.md` regenerated
  and committed after each fold.
- **Sizes.** `TailZ23` 48 KB, `TailZ24` 51 KB (limit about 150 KB).
- Not run: reduct-b's `fold_uses` (its consumers check) was not copied into the chain; the build of
  `researchLeaves9_of_open14` checks the same consumer types (`r6`, SS1, SS3, `semistableReductionDVR`) directly.

## 5. Not folded, and why

- **unipotent-b** (both routes): would not lower the strict count (§1). Its recommended route keeps the field's
  statement, so it can be folded later at no cost to the uses if `SemiAbelianDescendsSepClosed` is proved and
  `StrictHenselizationInside` becomes a leaf (or if SGA 7 IX turns out to define semistability geometrically and
  `Inside` is accepted as LEAF).
- **reduct-b option B with the unrestricted `SemistablePersistsSH`** would have mapped to `OpenResearchLeaves13`
  directly, but the task chose the restricted `SemistablePersistsSHcp`, which carries no reading risk on the residue
  field (perfect and separably closed is algebraically closed, so the `k(s)` versus geometric fibre question
  disappears).
- **t09-pic's nine-leaf split** (L4a–f): not used, as the task asks; `WeilPairingMumford` is one leaf and is flagged
  composite at the strictest reading.
- **Row r8** (`PkgI2.GrothendieckMonodromy`), reported inert by unipotent-b: still built in `OpenResearchLeaves9` from
  `semistableReductionDVR` (now K1) and `semistableUnipotent`; dropping it is a lead decision and changes nothing in
  the bundles.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves13`, `l : OpenAddedLeaves12`.
- Added: `r : OpenResearchLeaves14`, `l : OpenAddedLeaves13`.
- `t : OpenTextbookLeaves10` and `g : OpenGlue7` are unchanged.

**TYZ / GZ.** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` are unchanged.

**Fields removed (4):**
- research `semistableReductionDVR : ReductSplit.SemistableReductionDVR`: proved by K1 from `raynaudSemistable` (now a
  theorem) and the textbook fields `mumfordTorsionAlgClosed`, `mulEtaleAbelianScheme`;
- research `raynaudSemistable : ReductSplit.RaynaudSemistable`: proved from the new fields `raynaudSemistableSH`,
  `strictHenselizationPair` and the textbook field `mulEtaleAbelianScheme`;
- research `semistablePersistsDVR : ReductSplit.SemistablePersistsDVR`: no longer needed; its two uses (SS1, SS3) are
  proved from the new fields `semistablePersistsSHcp`, `strictHenselizationPair` and the existing fields
  `neronSchemeModelExistsDVR`, `blr_1_2_4`, `egaIV_8_10_5_xii` (and 3.6 by K1);
- added `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists`: proved from the four new t09-pic fields.

**Fields added (7):**
- research: `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` (LEAF; strictest GLUE: the print may assume an
  algebraically closed residue field), `semistablePersistsSHcp : ReductB.SemistablePersistsSHcp` (LEAF),
  `strictHenselizationPair : ReductGlue.StrictHenselizationPair` (GLUE, composite);
- added: `picRepresentableAbVar : T09Pic.PicRepresentableAbVar`, `picZeroAbVar : T09Pic.PicZeroAbVar`,
  `phiAmpleIsogeny : T09Pic.PhiAmpleIsogeny` (LEAF), `weilPairingMumford : T09Pic.WeilPairingMumford` (LEAF; strictest
  GLUE: one leaf for several printed properties of `ē_n`).

All seven kinds.tsv rows are marked "pending review": reduct-b had no review; t09-pic had one model review (no errors).
The strictest-reading flags added here (on `raynaudSemistableSH` and `weilPairingMumford`) mean `OPEN.md`'s phrase
"without the one strictest-reading flag" now covers three flags; the script's wording was not edited (not this task's
file).

## 7. State of the branches

| branch | `.fleet` report seen | merged | folded |
|---|---|---|---|
| reduct-b 85495b37 | yes | yes | `semistableReductionDVR`, `raynaudSemistable`, `semistablePersistsDVR` (§1) |
| unipotent-b 24c44f3d | yes | yes | not folded (§1, §5) |
| t09-pic 3d0f47a8 | yes | yes | `t09SymmIsogenyExists` (§1) |

## 8. Files (`scratch/leaf-fold14/`)

`log.md` (results log); `DumpBase.lean`, `DumpNew.lean`, `cmp_hashes.py`, `hashes_before.txt`, `hashes_after.txt`,
`cmp_hashes_out.txt`, `DumpNew_out.txt` (hash guard); `Uses.lean`, `uses_out.txt` (uses check); `mk_table.py`,
`fields14.md` (§2).
