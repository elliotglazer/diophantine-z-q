# leaf-fold10: dimjac-glue, shimura-glue and reduct-glue folded into the single proof; 62 fields, strict GLUE 17 (was 21 of 63)

Task leaf-fold10, 2026-11-14. Base 28b41fb3 (fork main after w60, with leaf-fold9 inside OneProof). Merged, each
after its `.fleet` report: `origin/wip/dimjac-glue`, `origin/wip/reduct-glue`, `origin/wip/shimura-glue`. New Lean:
- `ZInQKernel/OneProof/H/TailZ10.lean` (dimjac-glue's `DimJacGlue.lean`) and `TailZ11.lean` (bundle
  `OpenTextbookLeaves10`, `sixContactMin_of_open10`);
- `TailZ12.lean` (shimura-glue's `Deligne.lean`) and `TailZ13.lean` (bundle `OpenAddedLeaves9`,
  `sixContactMin_of_open11`);
- `TailZ14.lean` (reduct-glue's `Body.lean`) and `TailZ15.lean` (bundle `OpenResearchLeaves10`,
  `sixContactMin_of_open12`, the new top);
- the switch of `ZInQKernel/OneProof/Main.lean`.

Each new module is under 150 KB. Checks and tools are in `scratch/leaf-fold10/`; the results log is `log.md`. No
existing OneProof module was edited. No other file under `ZInQKernel/`, `blueprint/`, or another task's files was
edited either. No HDec copy was deleted, so FaithCheck was not needed. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source. There is no network on this host,
so every locator is the source report's. It is UNVERIFIED unless the audit `locators.md` read it.

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves10) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves9)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

The H half goes through the new top of the H assembly (`OneProof/H/TailZ15.lean`):

```lean
theorem HDec.HSyn.sixContactMin_of_open12 (r : OpenResearchLeaves10) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves9) (g : OpenGlue7) : ZInQ.SixContactMin
```

Four folds were taken. Each lowers the strict GLUE count by one, and none raises a count. Five fields went and four
leaves came in.

1. **dimjac-glue (fold (1)).** `ModularSplit.DimJac.dimJacobianEqGenus : ZInQ.Contrib.CurvesG.DimJacobianEqGenus`
   has no hypotheses. It fills the textbook field `dimJacobianEqGenus`, a composite (Milne's Jacobian varieties
   Prop. 2.1 with Serre duality). The field is dropped and nothing is added.
   - dimjac-glue identifies `H⁰(X, Ω¹_{X/ℚ})` with the holomorphic differentials of the function field. The proof
     uses Mathlib (Kähler differentials, the valuative criterion, Jacobson spaces, the DVR TFAE, sheaf gluing), the
     vendored Jacobian library `Contrib/CloudW07JacobiansCurves/` and the kernel's `Contrib/Dim/`.
   - The field's type is a kernel Prop, so the theorem fills it directly.
2. **shimura-glue (fold (2)).** The added field `y3Connected` (`TSHecke.Y3Connected`) is a composite: Deligne's
   description of `π₀` plus an orbit computation. It is replaced by `deligneComponentsY3Printed :
   ShimuraGlue.DeligneComponentsY3Printed`.
   - The new field is Deligne's theorem on the connected components of a Shimura variety, in printed form, for
     `G = B^×`, `B = (2, −3 | ℚ)`, at level `K₃`, on one fine witness `Y₃`.
   - It is stated over Mathlib's `FiniteAdeleRing ℤ ℚ`, `QuaternionAlgebra`, `cyclotomicCharacter` and
     `ConnectedComponents`.
   - The proof is `ShimuraSplit.y3Connected_of_deligne (ShimuraGlue.deligneComponentsY3_of_printed _)`:
     - shimura-glue computes in Lean that `ℚ^×_{>0}\𝔸_f^×/nrd(K₃) ≅ (ℤ/3)^×`;
     - it also shows that the cyclotomic idele maps to the mod-3 character;
     - shimura-split's orbit computation then gives connectedness.
   - shimura-glue also proves the converse: the printed leaf follows from shimura-split's form.
   - Caveat: the new field carries the witness clause list `R1fpProps`, with Lemma QP and R1's "qualified
     consequence" caveat, as `r1r2` and `gonzalezRotgerCountX6` do. Under the stricter reading it is a
     consequence. The fold is then strict 0 (comp → c) and lenient −1. No count rises under either reading.
3. **reduct-glue, `r6` (fold (2)).** The research field `r6` (`PkgI2.RaynaudCriterion.{0}`, a consequence) is
   replaced by `raynaudSemistable : ReductSplit.RaynaudSemistable` (SGA 7 IX 4.7 over a DVR).
   - The proof is `ReductGlue.raynaudCriterion_leaves` (reduct-split's `raynaudCriterion_final`).
   - The glue reduct-split had left, `FixedTorsionRationalImperfect`, is proved from the textbook field
     `mulEtaleAbelianScheme`: `A[m]` is étale, and a Galois-fixed `K̄`-point of an étale `K`-scheme is rational.
   - The proof also uses the existing fields `semistableUnipotent`, `neronSchemeModelExistsDVR` and
     `mumfordTorsionAlgClosed`.
4. **reduct-glue, SS1 and SS3 (fold (2)).** The research fields `semistableReductionThm` and `semistablePersists`
   (height-split's SS1 and SS3, both consequences) are replaced by two leaves:
   - `semistablePersistsDVR : ReductSplit.SemistablePersistsDVR` (SGA 7 IX 3.3, first assertion, over a DVR);
   - `neronLocalizesDVR : ReductGlue.NeronLocalizesDVR` (BLR §1.2 Prop. 4, "only if", over every DVR of a number
     field).

   The proofs are reduct-split's `semistableReductionThm_final` and `semistablePersists_final`, which also use the
   existing field `semistableReductionDVR`. They need two glue Props, both now proved:
   - `SemistableLocalGlobal` comes from `neronLocalizesDVR` (`ReductGlue.semistableLocalGlobal_leaf`);
   - `SemistableAlmostAll` (`ReductGlue.semistableAlmostAll_of`) comes from two results already in the chain, put
     together in `HDec.HSyn.semistableAlmostAll_of10`:
     - the kernel's `AbVarSpreadsOut` (`abVarSpreadsOut_of_ega4`, from the added field `egaIV_8_10_5_xii` and
       cloud worker W01's proofs of EGA IV 8.8.2 (ii) and 17.7.8 (ii));
     - Zariski's connectedness theorem (`properSmoothGenConnected_of_zariski4`, from cloud worker W02's proof).

   `neronLocalizesDVR` is counted as a consequence, conservatively: it is stated over every DVR of `L` rather than
   the localizations, and the identification is reduct-glue's Lean proof. If it is counted as published form (half),
   the fold is strict −2.
   - `raynaudSemistable` and `semistablePersistsDVR` are DVR leaves of the same kind as reduct-split's four. They
     are marked **"published form pending the base review"**, like those four (§2): the print may be over a
     strictly henselian base.
   - Under that reading, folds 3 and 4 are neutral (c → c). No count rises.
   - reduct-glue proves both general-DVR leaves from their strictly henselian forms plus strict-henselization leaves
     (§5).

**VERIFIED** (`scratch/leaf-fold10/log.md`):
- `lake build +ZInQKernel.OneProof.Main` exits 0.
- `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- **No existing constant changed.** op-compact's `DumpCompact` with `cmp_hashes.py` (copies in `scratch/leaf-fold10/`)
  compares 11123 OneProof constants before and 11835 after (`cmp_hashes_out.txt`):
  - the before-file was dumped on the base's `Main` and is byte-identical to leaf-fold9's after-file;
  - no constant was removed;
  - the only changed constant is `ZInQ.OneProof.frozenTarget`, the intended statement change;
  - all 712 new constants are in `TailZ10`–`TailZ15`.
- `Check10.lean` (`check10_result.txt`):
  - it compiles `example : ∀ r t l g, _root_.ZInQ.SixContactMin := sixContactMin_of_open12`;
  - the closure has 212 917 constants and no `sorryAx`;
  - there are 62 fields: 30 + 17 + 14 + 1, with 15 head constants declared outside `ZInQKernel/OneProof`;
  - `dimJacobianEqGenus`, `h0DifferentialsEqHolo`, `deligneComponentsY3_of_printed`, `y3Connected_of_deligne`,
    `raynaudCriterion_leaves`, `semistableLocalGlobal_leaf`, `semistableAlmostAll_of` and the three bundle maps
    have standard axioms (12 axiom lines).
- Sizes: `TailZ10` 37.5 KB, `TailZ11` 3.4 KB, `TailZ12` 71.8 KB, `TailZ13` 4.2 KB, `TailZ14` 116.8 KB, `TailZ15`
  8.6 KB.
- `verbatim_check10.py` (`verbatim_check10_out.txt`) checks that each copied module contains its source after the
  source's imports as one block, with only `#print axioms` lines (and one `example`) dropped:
  - `TailZ10` ← `DimJacGlue.lean`;
  - `TailZ12` ← `Deligne.lean`;
  - `TailZ14` ← `Body.lean`, whose import `ReductSplitBase` is replaced by the chain.

**Counts.** The forms are leaf-fold9's. A removed field takes its form with it. The table is printed by
`mk_fields10.py shimura reduct` (`counts10.md`).

| fold (in this order) | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |
|---|---|---|---|---|---|---|---|
| leaf-fold9 (`sixContactMin_of_open9`) | 63 | 42 | 11 | 9 | 1 | 42 / 21 | 53 / 10 |
| (1) dimjac-glue (`dimJacobianEqGenus` proved, no hypotheses) | 62 | 42 | 11 | 8 | 1 | 42 / 20 | 53 / 9 |
| (2) shimura-glue (`y3Connected` from the printed Deligne leaf on `Y3`) | 62 | 43 | 11 | 7 | 1 | 43 / 19 | 54 / 8 |
| (2) reduct-glue (`r6` from `RaynaudSemistable`) | 62 | 44 | 10 | 7 | 1 | 44 / 18 | 54 / 8 |
| (2) reduct-glue (`semistableReductionThm`, `semistablePersists` from `SemistablePersistsDVR`, `NeronLocalizesDVR`) | 62 | 45 | 9 | 7 | 1 | 45 / 17 | 54 / 8 |

**Bundles.**
- `OpenResearchLeaves10`: 30 fields (leaf-fold9's 30, with three removed and three added).
- `OpenTextbookLeaves10`: 17 fields (18 in leaf-fold9).
- `OpenAddedLeaves9`: 14 fields (leaf-fold8's 14, with one replaced).
- `OpenGlue7` (1, `QuotientP1Coordinate`): leaf-fold7's, unchanged.

**TYZ side.** Unchanged: `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3`.

**Module layout.** Each bundle module imports the module before it.
- `TailZ10` imports `TailZ9`. It holds dimjac-glue's `DimJacGlue.lean` verbatim after its five import lines, which
  are kernel `Contrib` modules (`CurvesG.GenusSplit`, two CloudW07 modules, `Dim.SmoothStalk`, `Dim.Basic`). It
  could move to `ZInQKernel/Contrib/` unchanged.
- `TailZ11`: `OpenTextbookLeaves10`, `textbookLeaves9_of_open10`, `sixContactMin_of_open10`.
- `TailZ12` imports `TailZ11` and holds shimura-glue's `Deligne.lean` verbatim after its import lines (the kernel's
  `HDecomp.QM.Leaves`, `HDecomp.QM.Polar` and nine Mathlib files). It contains:
  - shimura-glue's `Adelic.lean`;
  - shimura-split's `Y3Conn.lean`;
  - shimura-split's definition `HDec.QMSplit.Moduli.DeligneComponentsX6`, which is new in the chain;
  - shimura-glue's `parts/DeligneNew.lean`, with the converses.
- `TailZ13`: `OpenAddedLeaves9`, `addedLeaves8_of_open9`, `sixContactMin_of_open11`.
- `TailZ14` imports `TailZ13`, `Contrib/CloudW03NeronSurj/Main` and `Contrib/FrobChain/Pieces`. It holds
  reduct-glue's `Body.lean` (namespace `ReductGlue`) verbatim after its imports.
  - reduct-glue compiled the body against `Base.lean`, which is byte-identical to reduct-split's `Reduction.lean`.
    That file is `TailZ7` (leaf-fold9) minus its `#print` lines, so the import `ReductSplitBase` is replaced by the
    chain.
  - reduct-glue's single-file deliverable `ReductGlue.lean` (Base + Body) would duplicate `TailZ7`, and was not used.
- `TailZ15`: `OpenResearchLeaves10`, `semistableLocalGlobal_of10`, `semistableAlmostAll_of10`,
  `researchLeaves9_of_open10`, `sixContactMin_of_open12`.
- `Main` imports `TailZ15` in place of `TailZ9`. The chain from `LPrefix` to `TailZ9` is untouched.
- The bundle modules were written by hand, and each kept field's text and docstring were copied from the previous
  generation. `TailZ15`'s field block was copied by a script from `TailZ9`.

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

### OpenResearchLeaves10 (30 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `r1r2` | `LeafAdopt.R1R2fpRep` | GLUE (comp) | composite | R1(a,c,d), R2, R5 on one Y3, X6: Shimura 1967 Main Thms I-II; Deligne 1971 Thm 4.21, Cor. 5.7, Ex. 5.8; Baba-Granath 2008 Thm 2.1; Gonzalez-Rotger 2006 Prop. 5.6, Thm 5.12; Lemma QP | pin-apply |  |
| `shimuraFamily` | `QMSplit.Moduli.ShimuraFamily` | GLUE (c) | consequence of one theorem | Shimura 1967 Main Thm I (holomorphic family over the upper half plane) on one fine witness, composed with every algebraic pi : Y -> P1 (GAGA-level step, flagged by qm-split) | qm-split; folded by leaf-fold7 | r1b (project glue) |
| `r3` | `_root_.ZInQ.LeafPush2.R03_LinYang` | GLUE (comp) | composite | Lin-Yang 2020 Ex. 29; Baba-Granath Thm 2.1; Weil 1957; Lemma P | leaf-push2 |  |
| `igusaPsi4` | `QMSplit.Theta.IgusaPsi4` | LEAF | published form | Igusa, Amer. J. Math. 84 (1962), 86 (1964), 89 (1967): psi4 = 2^-2 sum theta_m^8 is a Siegel modular form of weight 4 (flag: Igusa defines psi4 as an Eisenstein series and prints the theta expression as a theorem) | qm-split; folded by leaf-fold7 | r4 (with igusaChi10) |
| `igusaChi10` | `QMSplit.Theta.IgusaChi10` | LEAF | published form | Igusa 1962, 1967: chi10 = -2^-14 prod theta_m^2 is a Siegel cusp form of weight 10 | qm-split; folded by leaf-fold7 | r4 (with igusaPsi4) |
| `r7a` | `_root_.PkgI2.NeronOggShafarevich.{0}` | LEAF | published form | Serre-Tate 1968 Thm 1 | pkg-I2 |  |
| `r9a` | `_root_.PkgI3.FaltingsSemisimple` | LEAF | published form | Faltings 1983 Satz 3 | pkg-I3 |  |
| `r9b` | `_root_.PkgI3.FaltingsTate` | LEAF | published form | Faltings 1983 Satz 4, Kor. 1 | pkg-I3 |  |
| `hodgeTateDecompAbVar` | `_root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar` | LEAF | published form (specialization) | C_p (x) V_p(A) = C_p(1)^g + C_p^g, G_F-equivariant (Fontaine, Invent. Math. 65 (1982); Tate 1967 4; Faltings 1988), bases of the two g-dimensional spaces chosen | hodge-split; folded by leaf-fold7 | r10 (composite), with deRhamH1AbVarT and Tate's two theorems |
| `deRhamH1AbVarT` | `_root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` | LEAF | published form (transported) | H^1_et(A_Fbar, Q_p), written Hom(V_p A, Q_p), is de Rham with the printed D_dR (Faltings 1989; Tsuji 1999; Scholze 2013 Cor. 1.8, wording read by h-leaves) | hodge-split; folded by leaf-fold7 | r10 |
| `r11r12` | `PkgI4.PanBerger` | GLUE (comp) | composite | Pan 2022 Thm 1.0.4 with Berger 2002 Thm 0.7 (not splittable: no B_st in Mathlib, hodge-split) | pkg-I4 |  |
| `eigenformHTNew` | `_root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew` | GLUE (c) | consequence of one theorem | Kato 2004 9.2-9.4 for newforms, transported to any semisimple attached rho and dualized (Kato's V_f not definable in Mathlib) | hodge-split; folded by leaf-fold7 | r13 (the same for all normalized eigenforms: a strictly smaller statement of the same form) |
| `dsThm965` | `_root_.ZInQ.Contrib.HodgeSplit.DSThm965` | LEAF | published form | Diamond-Shurman, GTM 228, Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14 for k = 2), coefficients extended along iota_L o iota_C^-1 | hodge-split; folded by leaf-fold7 | r14 (composite), with dsThm966 |
| `dsThm966` | `_root_.ZInQ.Contrib.HodgeSplit.DSThm966` | LEAF | published form | Deligne-Serre 1974 Thm 4.1; Diamond-Shurman Thm 9.6.6 (k = 1, continuous, finite image) | hodge-split; folded by leaf-fold7 | r14 |
| `r16` | `_root_.LeafModCurves.R16_EichlerShimuraJ1'` | GLUE (comp) | composite | Shimura 1973 Thm 1; Shimura 1971 Thm 7.9; Diamond-Shurman | leaf-modcurves |  |
| `r17` | `_root_.LadicCond.CarayolR17'` | GLUE (c) | consequence of one theorem | Carayol 1986 Theoreme (A) (read by the audit) | g0-mod-newform |  |
| `semistableNeronBaseChange` | `_root_.ZInQ.HeightSplit.SemistableNeronBaseChange` | GLUE (c) | consequence of one theorem | SGA 7 I Exp. IX Prop. 3.3 / Cor. 3.3.1, in the open-subgroup form of the kernel's N2 (identity component: SGA 3 VI_B 3.10) | height-split; folded by leaf-fold8 | r18-r22, h5fin (the eight together, with N1 from neronSchemeExtensionExists and T35 from h38) |
| `bostLowerBound` | `_root_.ZInQ.HeightSplit.BostLowerBound` | LEAF | published form | Bost, Sem. Bourbaki 795 (Asterisque 237, 1996): h_D(A) >= -(g/2) log 2pi, Deligne normalization (display UNVERIFIED, height-split §2) | height-split; folded by leaf-fold8 | r21 |
| `javanpeykarBound` | `_root_.ZInQ.HeightSplit.JavanpeykarBound` | LEAF | published form (specialization) | Javanpeykar, Algebra Number Theory 8 (2014) Thm 1.1.1 (read by the audit), for curves over K with a K-rational Belyi function, over the published stable height | height-split; folded by leaf-fold8 | r18 |
| `faltingsLemma5BC` | `_root_.ZInQ.HeightSplit.FaltingsLemma5BC` | GLUE (c) | consequence of one theorem | Faltings 1983 Lemma 5 in the semistable inequality form (Pazuki 2012 Rem. 2.3; Raynaud, Asterisque 127 VII Cor. 2.1.3 is the operative source, height-split §8), applied over every number field L above K | height-split; folded by leaf-fold8 | r20 |
| `pazukiCor13Upper` | `_root_.ZInQ.HeightSplit.PazukiCor13Upper` | LEAF | published form (half) | Pazuki, Bull. SMF 140 (2012) Cor. 1.3(2), upper half (read by the audit; RISK: Pazuki's level-2 coordinates, height-split §8) | height-split; folded by leaf-fold8 | r22 |
| `gaudronRemondThm14` | `_root_.ZInQ.HeightSplit.GaudronRemondThm14` | LEAF | published form | Gaudron-Remond, Duke Math. J. 163 (2014) Thm 1.4 (read by the audit), over the published stable height | height-split; folded by leaf-fold8 | r19 (same statement over the kernel infimum) |
| `serreTateThm2` | `_root_.ReductSplit.SerreTateThm2` | LEAF | published form (pending the base review) | Serre-Tate, Ann. of Math. 88 (1968) Thm 2: potential good reduction iff the image of inertia on T_l A is finite (RISK: if printed for complete K, a consequence; reduct-split §5) | reduct-split; folded by leaf-fold9 | r7b (consequence), with mumfordTorsionAlgClosed |
| `semistableReductionDVR` | `_root_.ReductSplit.SemistableReductionDVR` | LEAF | published form (specialization; pending the base review) | SGA 7 I Exp. IX Thm 3.6 over a DVR: A_K' semistable at every place above O for a finite K' (print: finite separable) | reduct-split; folded by leaf-fold9 | r8 (consequence), with the next two and mumfordTorsionAlgClosed |
| `semistableUnipotent` | `_root_.ReductSplit.SemistableUnipotent` | LEAF | published form (weakest reading; pending the base review) | SGA 7 I Exp. IX Prop. 3.5, semistable => (sigma-1)^2 = 0 on T_l for sigma in inertia, one sigma at a time | reduct-split; folded by leaf-fold9 | r8 |
| `neronSchemeModelExistsDVR` | `_root_.ReductSplit.NeronSchemeModelExistsDVR` | LEAF | published form (pending the base review) | BLR, Neron models, 1.4 Thm 3 over a DVR, scheme form (no group law) | reduct-split; folded by leaf-fold9 | r8 |
| `gonzalezRotgerCountX6` | `_root_.ShimuraSplit.GonzalezRotgerCountX6` | LEAF | published form (specialization) | Gonzalez-Rotger, J. Math. Soc. Japan 58 (2006) Prop. 5.6 (read by the audit) at (D,N) = (6,1), on the points of one canonical coarse witness X6 (with the R1fp/X6 clause lists and Lemma QP, as for r1r2) | shimura-split; folded by leaf-fold9 | r5count (consequence) |
| `raynaudSemistable` | `_root_.ReductSplit.RaynaudSemistable` | LEAF | published form (pending the base review) | SGA 7 I Exp. IX Prop. 4.7 (Raynaud's criterion; Silverberg-Zarhin 1995) over a DVR: m >= 3 invertible in O and A[m] rational over K imply semistable reduction at O (the print may be over a strictly henselian base: reduct-glue proves this leaf from RaynaudSemistableSH with StrictHenselizationNeron; other open readings, UNVERIFIED: a Galois-form conclusion, and n > 3 where the leaf allows m = 3) | reduct-split, reduct-glue; folded by leaf-fold10 | r6 (consequence), with semistableUnipotent, neronSchemeModelExistsDVR, mumfordTorsionAlgClosed and mulEtaleAbelianScheme (FixedTorsionRationalImperfect proved) |
| `semistablePersistsDVR` | `_root_.ReductSplit.SemistablePersistsDVR` | LEAF | published form (specialization; pending the base review) | SGA 7 I Exp. IX 3.3, first assertion, over a DVR, K'/K finite (the print may allow any extension of DVRs, a reading, UNVERIFIED; it may be over a strictly henselian base: reduct-glue proves it from SemistablePersistsSH with StrictHenselizationPair; other open readings, UNVERIFIED: semistability over k(s) rather than on the geometric special fibre, and S' required finite over S) | reduct-split, reduct-glue; folded by leaf-fold10 | semistablePersists (consequence) and, with semistableReductionDVR, semistableReductionThm (consequence) |
| `neronLocalizesDVR` | `_root_.ReductGlue.NeronLocalizesDVR` | GLUE (c) | consequence of one theorem | BLR, Neron models, 1.2 Prop. 4 ("only if": a Neron model over O_L localizes to a Neron model at the closed points), stated over every DVR of a number field L (every one is a localization: proved by reduct-glue) | reduct-glue; folded by leaf-fold10 | SemistableLocalGlobal (reduct-split glue, now proved), for semistableReductionThm and semistablePersists |

### OpenTextbookLeaves10 (17 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `mulEtaleAbelianScheme` | `_root_.AvSplit.T4.MulEtaleAbelianScheme` | LEAF | published form | [m] on an abelian scheme over Spec O is etale when m is a unit in O: BLR 7.3 Lemma 2; Mumford GIT 6 | av-split; folded by leaf-fold7 | t4 (consequence) |
| `mumfordTorsionAlgClosed` | `_root_.AvSplit.MumfordTorsionAlgClosed` | LEAF | published form | A(k)[n] = (Z/n)^{2g} over k algebraically closed, char k not dividing n: Mumford, Abelian varieties 4, Application 2 (iv) | av-split; folded by leaf-fold7 | t5 (consequence); with uniformizationLeafAll, t35 |
| `homFreeFiniteAlgClosed` | `_root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed` | LEAF | published form | Mumford 19 Thm 3 | av-b1 |  |
| `charPolyIndepOfEllAlgClosed` | `_root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed` | LEAF | published form | Mumford 19 Thm 4 (specialization) | av-b1 |  |
| `poincareComplement` | `_root_.ZInQ.Contrib.AVB1.PoincareComplement` | LEAF | published form | Poincare's complete reducibility, complement form: Milne 1986 Prop. 12.1; Mumford 19 Thm 1 | av-b1; folded back by leaf-fold7 | t8 (composite), with the next three |
| `cartierSmooth` | `_root_.AVGlue.CartierSmooth` | LEAF | published form | Cartier 1962; Oort 1966; Mumford 11 Thm 1; Milne, Algebraic Groups Thm 3.23; Stacks 047N | av-glue; folded by leaf-fold7 | t8 |
| `geomConnOfRationalPoint` | `_root_.AVGlue.GeomConnOfRationalPoint` | LEAF | published form (specialization) | Stacks 04KV (Varieties 33.7.14), with finite type and a rational point added | av-glue; folded by leaf-fold7 | t8 |
| `groupSchemeEquidim` | `_root_.AVGlue.GroupSchemeEquidim` | LEAF | published form (specialization) | Stacks, groupoid schemes, properties of group schemes over a field; SGA 3 VI_A 2.4 (finite type) | av-glue; folded by leaf-fold7 | t8 |
| `t10` | `_root_.T10Etale.T10_TateDuality` | GLUE (c) | consequence of one theorem | Milne 1986 Thm 15.1 | t10-etale |  |
| `uniformizationLeafAll` | `_root_.BPAnalytic.Uniformization.UniformizationLeafAll` | LEAF | published form (coordinate form) | Mumford, Abelian varieties 1 (A^an = C^g/Lambda), in bp-analytic's coordinate form (kernel leaf AN3) | bp-analytic; folded by leaf-fold7 (av-split) | t35 (with mumfordTorsionAlgClosed), homLatticeCorr (with gagaMorphism) |
| `gagaMorphism` | `_root_.ZInQ.HomLattice.GAGAMorphism` | LEAF | published form (coordinate form) | Serre, GAGA (1956), for homomorphisms of complex abelian varieties (homlattice 3.2) | homlattice, av-split; folded by leaf-fold7 | homLatticeCorr (composite) |
| `bdRInvariants` | `∀ p, _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p` | LEAF | published form | B_dR^{G_Q_p} = Q_p: Fontaine, Asterisque 223 (1994) Exp. II; Brinon-Conrad, CMI notes 4 | hodge-split; folded by leaf-fold7 | t23 (consequence) |
| `yuThm11` | `QMSplit.Yu.YuThm11` | LEAF | published form | Chia-Fu Yu, J. Pure Appl. Algebra 217 (2013) Thm 1.1 (with its splitting clause; case labels dropped) | qm-split; folded by leaf-fold7 | t27 (consequence) |
| `genusX1Field` | `_root_.ZInQ.Contrib.CurvesG.GenusX1Field` | GLUE (comp) | composite | Shimura 1971 6.7, Prop. 6.9, Prop. 1.40 (not statable in published form, curve-split 3.5) | curves-g |  |
| `regularSmoothPerfect` | `_root_.CurveSplit.RegularSmoothPerfect` | LEAF | published form (half) | Stacks 00TV (S_q regular implies S smooth at q over a perfect field) | curve-split; folded by leaf-fold7 | normalCurveSmoothQ (composite) |
| `igusaGL2` | `_root_.ZInQ.RLeaf.IgusaGL2` | LEAF | published form | Igusa's theorem: the Galois image on E_j[N] over Q(j) is GL_2(Z/N) (Igusa, Amer. J. Math. 81 (1959); Lang, Elliptic functions Ch. 6 3) | t40-igusa (kernel leaf); folded by leaf-fold7 (curve-split) | x0Transitive (consequence) |
| `neronSchemeExtensionExists` | `_root_.ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` | LEAF | published form (weakened) | BLR 1.4 Thm 3 | neron-c |  |

### OpenAddedLeaves9 (14 fields)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `thetaRatiosAlgebraic` | `G0Split.ThetaPt.ThetaRatiosAlgebraic` | GLUE (comp) | composite | Shimura 1976; Mumford Tata II IIIa 8; Igusa (qm-split: ThetaNullNonvanishing + glue, not folded) | g0-thetapoint |  |
| `qmCentralizerCMC` | `QMSplit.Aut.QMCentralizerCMC` | LEAF | published form | End_O(A) of a QM surface over C is Z or an optimally embedded order Phi^-1(O) of an imaginary quadratic k: Shimura 1967 1-3; Jordan 1981 3; Gonzalez-Rotger 2006 5 | qm-split; folded by leaf-fold7 | cmOptimalEmbedding (consequence), qmAutCard (composite), alFixedPoints (composite) |
| `tateTwistInvariants` | `_root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants` | LEAF | published form | C_p(i)^{G_K} = 0 for i != 0, K finite over Q_p in Qbar_p: Tate, p-divisible groups (1967) 3.3 Thm 2 | hodge-split; folded by leaf-fold7 | senTwist (consequence), finiteImageHT (composite), with axSenTate; also used for r10 |
| `axSenTate` | `_root_.ZInQ.Contrib.HodgeSplit.AxSenTate` | LEAF | published form | C_p^{G_K} = K: Tate 1967 3.3 Thm 1; Sen 1969; Ax 1970 | hodge-split; folded by leaf-fold7 | senTwist, finiteImageHT, r10 |
| `t09SymmIsogenyExists` | `WeilPairing.T09_SymmIsogenyExists` | GLUE (c) | consequence of one theorem | Mumford 6, 8, 20, 23 (not splittable, av-split 4.1) | weil-pairing |  |
| `milneIsogenyQuasiInverse` | `_root_.AvSplit.MilneIsogenyQuasiInverse` | LEAF | published form (weakened) | fg = [d], gf = [d] as morphisms: Milne 1986 Rem. 8.4; Milne's notes Prop. 7.1; Mumford 7 | av-split; folded by leaf-fold7 | isogenyQuasiInverse (consequence) |
| `x6ConicModel` | `X6Kummer.X6ConicModel` | GLUE (c) | consequence of one theorem | Kurihara 1979; Elkies 1998 3 | x6-kummer |  |
| `shimuraTaniyamaQbar` | `G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` | LEAF | published form (specialization) | Shimura-Taniyama 1961 12.4 Prop. 26; Milne, CM notes 7 (model over Qbar) | qm-split; folded by leaf-fold7 | stQM (consequence) |
| `egaIV_8_10_5_xii` | `_root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii` | LEAF | published form | EGA IV_3 8.10.5 (xii) | spread-out |  |
| `shimuraGoodReductionNoGuard` | `CurveSplitGR.ShimuraGoodReductionNoGuard` | GLUE (comp) | composite | vert-witness's ShimuraGoodReduction without the Qbar-point guard (redundant given r1r2): Kottwitz 1992 5; Buzzard 1997; Morita 1981; Carayol 1986 (not statable in published form today, curve-split 3.6) | curve-split; folded by leaf-fold7 | shimuraGoodReduction (a strictly smaller statement of the same form) |
| `valenceFormulaCocompactEq` | `LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` | LEAF | published form | valence formula for a cocompact Fuchsian group (Shimura 1971 Prop. 2.16, Thm 2.20; Rankin Thm 4.1.4), over Mathlib's invariant measure on the upper half plane and a genuine fundamental domain | qm-split, qm-glue; folded by leaf-fold8 | valenceFormulaGammaStar (consequence), qmHauptmodulBase3 (composite), with the next two |
| `shimizuCovolumeO1` | `LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` | LEAF | published form | iota(O^1) is cocompact Fuchsian with covolume 2pi/3 (Shimura 1971 Prop. 9.2; Shimizu 1965; Voight Thm 39.1.13) | qm-split, qm-glue; folded by leaf-fold8 | valenceFormulaGammaStar, qmHauptmodulBase3 (GammaStarFromO1 proved by qm-glue) |
| `igusaCMValue24` | `LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` | LEAF | published form | Lin-Yang 2020 eqs. (2), (14) at the Baba-Granath CM value j = -16/27 (discriminant -24; Baba-Granath 2008 Thm 2.1, Elkies 1998), Lauter-Naehrig-Yang 2015 §2.2 conventions; the manuscript's citation (l.908-923); equivalent to the old glue ThetaQuotientValue24 | qm-glue; folded by leaf-fold8 | qmHauptmodulBase3 (with igusaPsi4, igusaChi10 and the previous two) |
| `deligneComponentsY3Printed` | `_root_.ShimuraGlue.DeligneComponentsY3Printed` | LEAF | published form (specialization) | Deligne, Sem. Bourbaki 389 (1971) Thm 2.4 and 3; PSPM 33 (1979) 2.1.3, 2.6.3; Milne 2005 Thms 5.17, 13.6 (UNVERIFIED): pi0(Y x_Q Qbar) = Q_{>0}^x \ A_f^x / nrd(K3) with sigma acting by the cyclotomic idele to a fixed sign, for G = B^x, B = (2,-3|Q), at level K3, on one fine witness Y3 (with the R1fp clause list and Lemma QP, as for r1r2); over Mathlib's FiniteAdeleRing, QuaternionAlgebra, cyclotomicCharacter, ConnectedComponents | shimura-glue; folded by leaf-fold10 | y3Connected (composite) |

### OpenGlue7 (1 field)

| field | Lean type | strict kind | form | source | last task | replaces |
|---|---|---|---|---|---|---|
| `quotientP1Coordinate` | `MCRGlue.QuotientP1Coordinate` | GLUE (pg) | project glue | a finite q : Y -> Z over Z_(p) and Z = P^1_{Z_(p)} by charts with R2fp's fibre relation for the composite: the tame quotient Y/Gamma' = P^1 (SGA 1 Exp. V); no quotient schemes or P^1_{Z_(p)} in Mathlib 4.35 | mcr-glue; folded by leaf-fold7 | modelCoordinateResidue (the residue clause proved) |

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
- **Fork main's newer ruling** (STATUS.md at 485a3dc4, after this task's base; frontier r5 §4.8, not read here).
  The integrator counts `gonzalezRotgerCountX6` as a *candidate* rather than a printed statement, because it is
  stated on a fixed model of the Shimura curve together with its moduli data. `deligneComponentsY3Printed` has the
  same shape (`∃ Y Φ, R1fpProps Y Φ ∧ …`). Under that ruling:
  - both are strict GLUE, and fold (2) is strict 0;
  - leaf-fold9's count is 41 / 22 and this task's is **43 / 19** (SPECULATIVE recount by the same script with
    those two forms changed).

  The tables above keep leaf-fold9's forms, as the task asks.
- STATUS.md (same commit) says that six leaves are used only where hypotheses are repackaged: R3, T10 and the four
  reduct-split DVR leaves. After this fold, three of those four feed the proofs of the removed fields: `r6`
  (`semistableUnipotent`, `neronSchemeModelExistsDVR`), and SS1 and SS3 (`semistableReductionDVR`,
  `neronSchemeModelExistsDVR`). Whether those rows are themselves used downstream was not re-checked here
  (SPECULATIVE: STATUS.md does not list them as unused).

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

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves9`, `t : OpenTextbookLeaves9`, `l : OpenAddedLeaves8`.
- Added: `r : OpenResearchLeaves10`, `t : OpenTextbookLeaves10`, `l : OpenAddedLeaves9`.
- `g : OpenGlue7` is unchanged.

**TYZ / GZ.** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` are unchanged.

**Fields removed (5):**
- textbook `dimJacobianEqGenus` (`ZInQ.Contrib.CurvesG.DimJacobianEqGenus`): proved outright, with no hypotheses
  (dimjac-glue, `ModularSplit.DimJac.dimJacobianEqGenus`);
- added `y3Connected` (`TSHecke.Y3Connected`): proved from the new field `deligneComponentsY3Printed`
  (shimura-glue's `deligneComponentsY3_of_printed`, then shimura-split's `y3Connected_of_deligne`);
- research `r6` (`PkgI2.RaynaudCriterion.{0}`): proved from the new field `raynaudSemistable` and the existing fields
  `semistableUnipotent`, `neronSchemeModelExistsDVR`, `mumfordTorsionAlgClosed`, `mulEtaleAbelianScheme`
  (`ReductGlue.raynaudCriterion_leaves`);
- research `semistableReductionThm` (`ZInQ.HeightSplit.SemistableReductionThm`, SS1): proved from the new fields
  `semistablePersistsDVR`, `neronLocalizesDVR` and the existing fields `semistableReductionDVR`,
  `neronSchemeModelExistsDVR`, `egaIV_8_10_5_xii` (`ReductSplit.semistableReductionThm_final`,
  `HDec.HSyn.semistableLocalGlobal_of10`, `semistableAlmostAll_of10`);
- research `semistablePersists` (`ZInQ.HeightSplit.SemistablePersists`, SS3): proved from the new fields
  `semistablePersistsDVR`, `neronLocalizesDVR` and the existing field `neronSchemeModelExistsDVR`
  (`ReductSplit.semistablePersists_final`).

**Fields added (4):**
- added-leaf bundle: `deligneComponentsY3Printed : ShimuraGlue.DeligneComponentsY3Printed`;
- research bundle: `raynaudSemistable : ReductSplit.RaynaudSemistable`,
  `semistablePersistsDVR : ReductSplit.SemistablePersistsDVR`, `neronLocalizesDVR : ReductGlue.NeronLocalizesDVR`.

One removed field is proved outright, from nothing: `dimJacobianEqGenus`.

## 7. State of the branches

| branch | `.fleet` report seen | merged | folded |
|---|---|---|---|
| dimjac-glue | yes (before 12:57) | yes | `dimJacobianEqGenus` (§1) |
| reduct-glue | yes (14:00) | yes | `r6`, `semistableReductionThm`, `semistablePersists` (§1); the rest not folded (§5) |
| shimura-glue | yes (14:06) | yes | `y3Connected` (§1); the rest not folded (§5) |
| cloud W11, W14, W15, W16 | not on fork main | — | — |
