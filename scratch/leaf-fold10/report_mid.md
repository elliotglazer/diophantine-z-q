
### 1.1 Which constants the fields are (VERIFIED, `Check10.lean`, `check10_result.txt`)

- 15 of the 62 fields have a head constant declared outside `ZInQKernel/OneProof`, i.e. a kernel constant
  (leaf-fold9: 17 of 63).
- Two of the five fields that went are kernel constants: `PkgI2.RaynaudCriterion` (`r6`) and
  `ZInQ.Contrib.CurvesG.DimJacobianEqGenus`. `ZInQ.HeightSplit.SemistableReductionThm` and `SemistablePersists` are
  declared in the chain (`TailY`), and so is `HDec.TSHecke.Y3Connected` (`TailG`).
- The four new leaves are declared in the new modules:
  - `ShimuraGlue.DeligneComponentsY3Printed` in `TailZ12`, which besides `TailZ11` imports only kernel and Mathlib
    modules;
  - `ReductGlue.NeronLocalizesDVR` in `TailZ14`;
  - `ReductSplit.RaynaudSemistable` and `SemistablePersistsDVR` in `TailZ7` (leaf-fold9's copy of reduct-split's
    file).

## 2. Every hypothesis

"Strict kind": LEAF = published form; GLUE (c) = consequence of one theorem; GLUE (comp) = composite;
GLUE (pg) = project glue. The tables are generated from `scratch/leaf-fold10/fields10.tsv` by
`mk_fields10.py shimura reduct`. The script starts from leaf-fold9's `fields9.tsv`, removes five rows and adds four.
Lean types are written as in the bundle modules, inside `namespace HDec.HSyn`.

Every kept field keeps leaf-fold9's type and form, with one exception. As the task asks, reduct-split's four DVR
leaves (`serreTateThm2`, `semistableReductionDVR`, `semistableUnipotent`, `neronSchemeModelExistsDVR`) are marked
**"published form pending the base review"** in the form column; their kind is unchanged. The two new DVR leaves
`raynaudSemistable` and `semistablePersistsDVR` carry the same mark.

The build checks the types, since each `sixContactMin_of_openN` passes the kept fields unchanged to the previous
generation. The readings and the flags of leaf-fold8 §2 and leaf-fold9 §2 apply unchanged: the Serre–Tate RISK,
`pazukiCor13Upper`, `bostLowerBound`, `faltingsLemma5BC`, `igusaCMValue24`, `valenceFormulaCocompactEq`.

<!--TABLES-->
Notes on the table.
- **The base review.** reduct-glue (§4 of its report) states each SGA 7 and Serre–Tate field also over the base on
  which it may be printed: strictly henselian for SGA 7, complete for Serre–Tate. Each printed-base version is a
  specialization of the DVR leaf (`printed_of_general`), so the DVR leaves are at least as strong as the print.
  - Three DVR leaves are Lean theorems of their printed-base forms plus strict-henselization leaves:
    - 4.7 (`raynaudSemistable_of_SH'`, with `StrictHenselizationNeron`, `mulEtaleAbelianScheme`);
    - 3.3a (`persistsFromSH_of`, with `StrictHenselizationPair`);
    - 3.5 (`unipotentFromSH_of`, with `StrictHenselizationInside`).
  - Three are not: 3.6 (`ReductionFromSH`), 3.3b and Serre–Tate (`SerreTateFromComplete`). These remain named glue
    in reduct-glue.

  If the review finds that a DVR leaf is a consequence of the print, that field's kind becomes GLUE (c). None of the
  four folds raises a count under that reading (§1).
- `deligneComponentsY3Printed` carries the clause list `R1fpProps` (Lemma QP and R1's caveat), as `r1r2` and
  `gonzalezRotgerCountX6` do. shimura-glue's two model reviews found no false or vacuous leaf, and there was no human
  review.
- `neronLocalizesDVR` is counted as a consequence (§1, fold 4).

## 3. The remaining leaves by the theory they come from

Counts are of bundle fields. `?` marks a field that is not in published form (c or comp). The grouping is
leaf-fold8's, so its boundaries are SPECULATIVE.

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves, QM abelian surfaces and Fuchsian groups** | 12 (5) | `r1r2`?, `shimuraFamily`?, `r3`?, `gonzalezRotgerCountX6`, `deligneComponentsY3Printed`, `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `shimuraGoodReductionNoGuard`?, `valenceFormulaCocompactEq`, `shimizuCovolumeO1` |
| **A′. Theta functions and Siegel modular forms of genus 2** | 4 (1) | `igusaPsi4`, `igusaChi10`, `igusaCMValue24`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** | 9 (2) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `t10`?, `uniformizationLeafAll`, `gagaMorphism`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, semistable reduction and monodromy** | 11 (2) | `r7a`, `serreTateThm2`, `semistableReductionDVR`, `semistableUnipotent`, `raynaudSemistable`, `semistablePersistsDVR`, `neronSchemeModelExistsDVR`, `neronLocalizesDVR`?, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `semistableNeronBaseChange`? |
| **C′. Schemes and group schemes over a field** | 5 (0) | `egaIV_8_10_5_xii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** | 7 (1) | `r9a`, `r9b`, `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`?, `pazukiCor13Upper`, `gaudronRemondThm14` |
| **E. p-adic Hodge theory** | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** | 5 (3) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r16`?, `r17`? |
| **G. Algebraic and modular curves** | 2 (1) | `genusX1Field`?, `igusaGL2` |
| total | **61 (16)** | plus the glue `quotientP1Coordinate` |

Against leaf-fold9 §3:
- **Group A** traded the composite `y3Connected` for Deligne's `π₀` theorem in printed form (shimura-glue).
- **Group C** lost three consequences: `r6` (Raynaud's criterion in every field) and the global SS1 and SS3. Two
  published-form DVR leaves (SGA 7 IX 4.7 and 3.3) and the consequence `neronLocalizesDVR` (BLR 1.2/4) came in.
  reduct-split's glue for them is proved (reduct-glue).
- **Group G** lost `dimJacobianEqGenus`, now a theorem with no hypotheses (dimjac-glue).

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Build of the chain.** The first `lake build +ZInQKernel.OneProof.Main` after the switch to `TailZ11` rebuilt
  the CloudW07 closure and the kernel. The harness's background time limit stopped it once with no errors. The
  rerun exited 0 (12900 jobs).
- **Hashes before.** The base's `Main.lean` was put back temporarily and built (`lake build
  ZInQKernel.OneProof.Main`, exit 0). `DumpCompact` then gave 11123 constants (`hashes_before.txt`), byte-identical
  to leaf-fold9's `hashes_after.txt`. The new `Main.lean` was then restored and rebuilt.
- **dimjac-glue.** Merged with `git merge origin/wip/dimjac-glue` (clean, after its `.fleet` report). `TailZ10`,
  `TailZ11` and the new `Main` built at the first try. Intermediate check: 11215 constants, 0 removed, 1 changed,
  92 new; 62 fields.
- **shimura-glue.**
  - `TailZ12` and `TailZ13` were first built from shimura-glue's report commit 3017e19f, before its `.fleet` report.
    Main was switched to them only after the report (14:06).
  - After `git merge origin/wip/shimura-glue` (clean), `TailZ12` was regenerated from the merged `Deligne.lean`.
    That file had gained the converses and the import `HDecomp.QM.Polar`. Both versions built at the first try.
- **reduct-glue.** Merged with `git merge origin/wip/reduct-glue` (clean, after its `.fleet` report). `TailZ14`
  (about 117 KB, which imports `CloudW03NeronSurj/Main`, i.e. all of Mathlib) and `TailZ15` built at the first try.
- **Main.** `lake build +ZInQKernel.OneProof.Main` exits 0. `#print axioms ZInQ.OneProof.frozenTarget` gives
  `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** 11835 constants. `cmp_hashes.py`: 0 removed, 1 changed (`frozenTarget`), 712 new, all in
  `TailZ10`–`TailZ15`.
- **Check10.lean.** It checks:
  - the conclusion;
  - the closure (212 917 constants, no `sorryAx`);
  - the head constant and module of all 62 fields;
  - the axioms of the new theorems (12 lines, all standard);
  - the full types of `semistableAlmostAll_of10`, `researchLeaves9_of_open10` and `addedLeaves8_of_open9`.
- **verbatim_check10.py.**
  - The three copies are verbatim.
  - reduct-glue's `Base.lean` minus `#print` lines is `TailZ7`, with the same imports.
- **Module sizes.** TailZ10 37.5 KB, TailZ11 3.4 KB, TailZ12 71.8 KB, TailZ13 4.2 KB, TailZ14 116.8 KB, TailZ15
  8.6 KB.

**No statement of a leaf, row or glue Prop was changed.**
- Every kept field keeps its type.
- Every removed field is filled by a compiled theorem whose type is exactly the old field's constant.
- No HDec copy was deleted, so no FaithCheck was needed.
- Two partial build logs went into the first two commits by mistake. They contain no host paths and were removed
  from the index; `scratch/leaf-fold10/.gitignore` now excludes build logs.

## 5. Not folded, and why

Decision rule (this task): a fold is taken only if it lowers the strict GLUE count.

- **shimura-glue, the parts not folded.** Applied to this state, where `y3Connected` is folded and `r1rec`, `r5`,
  `r5count` are leaf-fold9's:
  - `x6ConicModel` (c) would become `ElkiesConicT` (c, Elkies §3 in his coordinate `t`), with the Möbius glue
    (`MobiusCompose`, proved), `r1r2` and T5. Neutral.
  - `r1r2` (comp) would become `GeomConnOfAlgClosure`, `GonzalezRotgerX6`, `DeligneComponentsX6Printed` and
    `BabaGranathRational` (published form), with `RayClassCM` (c), via `ReciprocityCanonical`, which is proved from
    `RayClassCM` with Tau Ceti's ray class field. That is strict 1 → 1 (neutral) and lenient −1.
    - Taken with `x6ConicModel`, it is strict 2 → 2 and lenient −1.
    - It would make `r1r2`'s composite four published-form leaves plus one consequence, so it is a candidate if
      the owner accepts composite → consequence.
  - `shimuraFamily` (c) would become `ShimuraHolFamily` (c). Neutral, and unchanged by shimura-glue.
  - `r3`: not split (missing definitions: principal polarizations on `PkgI3.AbVar`, the coarse moduli bijection on
    `ℂ`-points).
- **reduct-glue, the parts not folded.**
  - `semistableNeronBaseChange` (SS2, c) would become `IdentityComponentBaseChangeDVR` (pending published form),
    `IdentityComponentOL` (SGA 3 VI_B 3.10 with VI_A 2.4: c or comp) and `OpenImmersionOfLocal` (EGA IV 8.10.5 with a
    limit argument: c), with `neronLocalizesDVR`. That is strict +1 at least.
  - `faltingsLemma5BC` (c) would become `HeightSplit.FaltingsLemma5` (c). Neutral.
  - **Printed-base forms.** The DVR leaves could be replaced by their strictly henselian forms plus strict
    henselization leaves:
    - `RaynaudSemistableSH` with `StrictHenselizationNeron` (EGA IV 18.8.8/18.8.13 with BLR 1.2/2: a combination);
    - `SemistablePersistsSH` with `StrictHenselizationPair`;
    - `SemistableUnipotentSH` with `StrictHenselizationInside`.

    Each adds a strict GLUE field (the strict-henselization leaf, a combination or a consequence), or keeps the
    count, so none was taken. They are the fallback if the base review finds a DVR leaf printed only over a strictly
    henselian base. The other three DVR leaves (3.6, 3.3b, Serre–Tate) still need reduct-glue's named glue.
- **Cloud-worker PRs W11 (`TateTwistInvariants`, `AxSenTate`), W14 (`X0Transitive`), W15 (`RegularSmoothPerfect`),
  W16 (`CartierSmooth`, `GeomConnOfRationalPoint`, `GroupSchemeEquidim`).** None was on fork main (`git log
  origin/main`) at any check up to 14:06; there were no `origin/work/cloud-w1*` branches either. Not folded.
  - SPECULATIVE: once merged, `tateTwistInvariants`, `axSenTate`, `regularSmoothPerfect`, `cartierSmooth`,
    `geomConnOfRationalPoint` and `groupSchemeEquidim` would drop as leaf-fold9 dropped `t33`.
  - These six are kernel-Prop fields of the bundles (`_root_.ZInQ.Contrib.HodgeSplit.*`, `_root_.CurveSplit.*`,
    `_root_.AVGlue.*`), so a proof plugs in directly.
  - They are LEAFs, so the strict GLUE count would not change.
- **leaf-fold9 §5 items still standing.** mcr-quot, coarse-factor, `eigenformHTNew` → `KatoRealizationCoh` + `HTDual`,
  and `r17` → `CarayolRealization` are unchanged.

## 7. State of the branches

| branch | `.fleet` report seen | merged | folded |
|---|---|---|---|
| dimjac-glue | yes (before 12:57) | yes | `dimJacobianEqGenus` (§1) |
| reduct-glue | yes (14:00) | yes | `r6`, `semistableReductionThm`, `semistablePersists` (§1); the rest not folded (§5) |
| shimura-glue | yes (14:06) | yes | `y3Connected` (§1); the rest not folded (§5) |
| cloud W11, W14, W15, W16 | not on fork main | — | — |
