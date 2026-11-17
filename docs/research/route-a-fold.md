# route-a-fold: r1univ-rigid folded into the single proof (route A for `R1univProps`); 60 fields, strict LEAF / GLUE 45 / 15 (was 44 / 15 of 59)

Task route-a-fold, 2026-11-14. Base e38375b3 (wip/w62: fork main df98652a with leaf-fold10 inside OneProof, plus
the prune of `r3`, `serreTateThm2`, `t10`). `origin/wip/r1univ-rigid` was already merged into the base. New Lean:
- `ZInQKernel/OneProof/H/TailZ16.lean` (32.6 KB): r1univ-rigid's `R1UnivRigid.lean`, verbatim below its imports;
- `ZInQKernel/OneProof/H/TailZ17.lean` (15.7 KB): the four printed forms `LAb`, their `L_iff_ab`, the bundles
  `OpenResearchLeaves11` and `OpenAddedLeaves10`, the conversions, and `sixContactMin_of_open13` (the new top);
- the switch of `ZInQKernel/OneProof/Main.lean`.

Checks and tools are in `scratch/route-a-fold/`; the results log is `log.md`. No existing OneProof module was
edited, nor any other file under `ZInQKernel/` (in particular not `ZInQKernel/HDecomp`), `blueprint/`, or another
task's files. No HDec copy was deleted (FaithCheck not needed), and no new `OpenTextbookLeaves` generation was made.
Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no network on this host; the
locators are r1univ-rigid's and leaf-fold10's).

## 1. Main result

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves11) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves10)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

through the new top of the H assembly (`OneProof/H/TailZ17.lean`):

```lean
theorem HDec.HSyn.sixContactMin_of_open13 (r : OpenResearchLeaves11) (t : OpenTextbookLeaves10)
    (l : OpenAddedLeaves10) (g : OpenGlue7) : ZInQ.SixContactMin
```

VERIFIED: `lake build +ZInQKernel.OneProof.Main` exits 0; `#print axioms ZInQ.OneProof.frozenTarget` gives
`[propext, Classical.choice, Quot.sound]`; no existing OneProof constant changed its type or value hash except
`frozenTarget` itself (§4).

**What changed.** Exactly four fields of `frozenTarget` are stated on the kernel's clause list
`LeafQM.AV.R1fpProps`, whose universal clause `R1univProps` classifies `QMFamily S` (proper smooth families with
`ι(a)` and `η(a)` but **no group law**), whereas the published fine-moduli theorems classify abelian schemes. Each of
the four is now stated on r1univ-rigid's `LeafQM.AV.R1UnivRigid.R1fpPropsAb` (abelian schemes with `𝒪 → End_S` and
level 3: `QMAbScheme S`), i.e. in the form in which it is printed, and one leaf is added:

* `mumfordRigidityCore : LeafQM.AV.R1UnivRigid.MumfordRigidityCore` (Mumford, *GIT* Ch. 6, Thm 6.14 on each
  connected component with Cor. 6.4 over `S`; numbers UNVERIFIED).

Each old field is filled by `(L_iff_ab (mumfordRigidity_of_core r.mumfordRigidityCore)).mpr` applied to the new
field (`researchLeaves10_of_open11`, `addedLeaves9_of_open10`); every other field passes through. The four
`L_iff_ab` close by `unfold; rw [r1fpProps_eq_ab' hR]`, so each `LAb` elaborates to the same term as `L` apart from
the one constant `R1fpProps ↦ R1fpPropsAb` (VERIFIED, compiled).

Of r1univ-rigid's 18 leaves, only these four are fields of `frozenTarget` (scratch/one-proof/used-fields.txt on
`wip/prune-scan`, VERIFIED by reading); none is a textbook field. The other 14 (`GonzalezRotgerX6`,
`DeligneComponentsX6`, `BabaGranathX6'`, `ReciprocityCanonical`, `ElkiesConicX6`, `ShimuraHolFamily`,
`DeligneComponentsY3`, `DeligneComponentsX6Printed`, `BabaGranathRational`, `ElkiesConicT`, `CanonicalModelY3`,
`Y3Connected`, `R1fp`, `R1R2fp`) are not hypotheses of the current top (they are unfolded splits, older-generation
fields now proved, or kernel leaves), so nothing was done for them; their `L_iff_ab` remain in
`scratch/r1univ-rigid/R1UnivLeaves.lean` (and `R1fp`, `R1R2fp`'s are now in `TailZ16`).

### 1.1 Counts (strict and lenient LEAF / GLUE)

"Strict kind" as in leaf-fold10 §2: LEAF = published form; GLUE (c) = consequence of one theorem; GLUE (comp) =
composite; GLUE (pg) = project glue. Lenient LEAF = published + (c). The "before" row is leaf-fold10's last row
(`counts10.md`: 62 = 45 pub, 9 c, 7 comp, 1 pg) minus the three pruned fields (`r3` comp, `serreTateThm2` pub,
`t10` c), each kind read from leaf-fold10 §2.

| state | fields | published | c | comp | pg | strict LEAF / GLUE | lenient LEAF / GLUE |
|---|---|---|---|---|---|---|---|
| base (`sixContactMin_of_open12`, after the prune) | 59 | 44 | 8 | 6 | 1 | 44 / 15 | 52 / 7 |
| route-a-fold (`sixContactMin_of_open13`) | 60 | 45 | 8 | 6 | 1 | **45 / 15** | 53 / 7 |

The strict GLUE count is unchanged; the one new field is a published leaf. **No classification changes** for the
four restated fields (§2):
* `r1r2Ab` stays GLUE (comp): it is composite because it bundles Shimura's, Deligne's, Baba–Granath's and
  González–Rotger's theorems on one `Y₃`, `X₆`, not because of the family notion.
* `shimuraFamilyAb` stays GLUE (c): Shimura 1967 Main Thm I composed with every algebraic `π : Y → ℙ¹` (the GAGA-level
  step flagged by qm-split) is unchanged.
* `gonzalezRotgerCountX6Ab` and `deligneComponentsY3PrintedAb` stay LEAF (published form, specialization). The
  restatement removes one gap in that label: the old forms required `R1univProps` for families without a group law,
  a universal property *stronger* than the printed fine-moduli statement (it is derived from the printed one only
  with Mumford's rigidity, r1univ-rigid §5.1). SPECULATIVE: with the Ab form, the label "published form" is
  justified for the moduli clause; the other caveats (Lemma QP, the polarization, §5) are unchanged.

**Reading of `MumfordRigidityCore` (SPECULATIVE).** The task counts it as a published leaf, and the table does so.
Strictly, *GIT* Thm 6.14 is printed for connected `S`; the leaf allows any locally noetherian `S` and takes the
group law on each connected component (open since `S` is locally noetherian), and its hypotheses (every field fibre
an abelian variety) are stronger than printed. If a reviewer reads the per-component step as making it a
consequence of two printed statements (Thm 6.14 and Cor. 6.4), it is GLUE (c) and the count is strict 44 / 16,
lenient 53 / 7. The project only applies it over smooth curves `S/ℚ`.

## 2. Every `frozenTarget` field whose statement changes

Types as written in the bundle modules, inside `namespace HDec.HSyn`. In each row the new type is the old type's
definition text with `LeafQM.AV.R1fpProps` replaced by `LeafQM.AV.R1UnivRigid.R1fpPropsAb` (checked by `L_iff_ab`).

| bundle | old field : old type | new field : new type | strict kind (old → new) | proof of the old field |
|---|---|---|---|---|
| research | `r1r2 : LeafAdopt.R1R2fpRep` | `r1r2Ab : LeafAdopt.R1R2fpRepAb` | GLUE (comp) → GLUE (comp) | `(r1R2fpRep_iff_ab _).mpr` |
| research | `shimuraFamily : QMSplit.Moduli.ShimuraFamily` | `shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb` | GLUE (c) → GLUE (c) | `(shimuraFamily_iff_ab _).mpr` |
| research | `gonzalezRotgerCountX6 : _root_.ShimuraSplit.GonzalezRotgerCountX6` | `gonzalezRotgerCountX6Ab : _root_.ShimuraSplit.GonzalezRotgerCountX6Ab` | LEAF → LEAF | `(gonzalezRotgerCountX6_iff_ab _).mpr` |
| added | `deligneComponentsY3Printed : _root_.ShimuraGlue.DeligneComponentsY3Printed` | `deligneComponentsY3PrintedAb : _root_.ShimuraGlue.DeligneComponentsY3PrintedAb` | LEAF → LEAF | `(deligneComponentsY3Printed_iff_ab _).mpr` |
| research | — | `mumfordRigidityCore : _root_.LeafQM.AV.R1UnivRigid.MumfordRigidityCore` | new: LEAF | — (feeds the four proofs) |

The `_iff_ab` theorems are in namespace `LeafQM.AV.R1UnivRigid` (`TailZ17`); `_` is
`mumfordRigidity_of11 r = mumfordRigidity_of_core r.mumfordRigidityCore`.

The definitions, for reference (VERIFIED, `#print` in `check_result.txt`):

```lean
-- old (kernel, HDecomp/QM/Leaves.lean)            -- new (TailZ16)
R1fpProps Y Φ :=                                     R1fpPropsAb Y Φ :=
  IsProper Y.hom ∧ SmoothOfRelativeDimension 1 Y.hom   (same first four clauses) ∧
  ∧ Nonempty (fieldPt Qbar ⟶ Y) ∧ (base change) ∧        R1famAbProps Y Φ ∧ R1univAbProps Y Φ
  R1famProps Y Φ ∧ R1univProps Y Φ
-- the four leaves:
DeligneComponentsY3Printed := ∃ Y Φ, R1fpProps Y Φ ∧ DelignePi0 Y K3
DeligneComponentsY3PrintedAb := ∃ Y Φ, R1fpPropsAb Y Φ ∧ DelignePi0 Y K3
ShimuraFamily := ∃ Y Φ, R1fpProps Y Φ ∧ ∀ π : ToP1 Y.left, R1bFamily Y Φ π      (Ab: R1fpPropsAb)
GonzalezRotgerCountX6 := ∃ Y Φ X Ψ fY, R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ (count = 2^b h(R))   (Ab: R1fpPropsAb)
R1R2fpRep := ∃ Y Φ X Ψ fY π₆, R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props … ∧ R2X6PropsIff … ∧ R1recProps Y Φ ∧
  X6Surj … ∧ R5ptProps X Ψ ∧ R1pi0Props X                                          (Ab: R1fpPropsAb)
```

`R1univAbProps` is `R1univProps` with `𝒜' : QMAbScheme S.left` in place of `𝒜' : QMFamily S.left`;
`R1famAbProps` says `Φ` is induced by a `QMAbScheme` over `Y`. `QMAbScheme S extends QMFamily S` by a `GrpObj`
structure with identity `η(0)`, geometric connectedness, `ι : 𝒪 → End_S` a unital ring map into homomorphisms, `η`
an `𝒪`-linear homomorphism with `η(3b) = η(0)` and fibrewise kernel exactly `3𝒪` (r1univ-rigid §3.3).

All other 55 fields keep their types (the build checks this: each conversion passes them unchanged).

## 3. The remaining leaves by the theory they come from

leaf-fold10 §3 with the prune and this fold (grouping leaf-fold8's, boundaries SPECULATIVE; `?` = not published
form):

| group (published theory) | # (not published form) | fields |
|---|---|---|
| **A. Shimura curves, QM abelian surfaces and Fuchsian groups** | 12 (4) | `r1r2Ab`?, `shimuraFamilyAb`?, `gonzalezRotgerCountX6Ab`, `deligneComponentsY3PrintedAb`, `mumfordRigidityCore` (abelian schemes; listed here as it serves the moduli rows), `qmCentralizerCMC`, `yuThm11`, `shimuraTaniyamaQbar`, `x6ConicModel`?, `shimuraGoodReductionNoGuard`?, `valenceFormulaCocompactEq`, `shimizuCovolumeO1` |
| **A′. Theta functions and Siegel modular forms of genus 2** | 4 (1) | `igusaPsi4`, `igusaChi10`, `igusaCMValue24`, `thetaRatiosAlgebraic`? |
| **B. Abelian varieties: the textbook theory** | 8 (1) | `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`, `poincareComplement`, `uniformizationLeafAll`, `gagaMorphism`, `t09SymmIsogenyExists`?, `milneIsogenyQuasiInverse` |
| **C. Néron models, semistable reduction and monodromy** | 10 (2) | `r7a`, `semistableReductionDVR`, `semistableUnipotent`, `raynaudSemistable`, `semistablePersistsDVR`, `neronSchemeModelExistsDVR`, `neronLocalizesDVR`?, `neronSchemeExtensionExists`, `mulEtaleAbelianScheme`, `semistableNeronBaseChange`? |
| **C′. Schemes and group schemes over a field** | 5 (0) | `egaIV_8_10_5_xii`, `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`, `regularSmoothPerfect` |
| **D. Faltings 1983 and Faltings heights** | 7 (1) | `r9a`, `r9b`, `bostLowerBound`, `javanpeykarBound`, `faltingsLemma5BC`?, `pazukiCor13Upper`, `gaudronRemondThm14` |
| **E. p-adic Hodge theory** | 6 (1) | `tateTwistInvariants`, `axSenTate`, `hodgeTateDecompAbVar`, `deRhamH1AbVarT`, `bdRInvariants`, `r11r12`? |
| **F. Galois representations of modular forms** | 5 (3) | `dsThm965`, `dsThm966`, `eigenformHTNew`?, `r16`?, `r17`? |
| **G. Algebraic and modular curves** | 2 (1) | `genusX1Field`?, `igusaGL2` |
| total | **59 (14)** | plus the glue `quotientP1Coordinate` |

## 4. Checks (all VERIFIED; one Lean process at a time; times on this host)

- **Base build and hashes before.** `lake build +ZInQKernel.OneProof.Main` on the base exited 0 (12905 jobs, the
  oleans were current). `scratch/route-a-fold/DumpCompact.lean` (op-compact's tool, output path changed) gave 11811
  constants (`hashes_before.txt`, `frozenTarget_type_before.txt`).
- **New modules.** `lake build +ZInQKernel.OneProof.H.TailZ17` built `TailZ16` (8.2 s) and `TailZ17` (4.9 s) at
  the first try. `TailZ16`'s body is byte-identical to `scratch/r1univ-rigid/R1UnivRigid.lean` below its header
  (`diff` empty). The printed forms in `TailZ17` are `scratch/r1univ-rigid/parts/printed.lean` lines 23-42,
  126-138, 156-170, 183-194, verbatim. The only warnings are `ambiguousOpen` on the copied `open LeafQM LeafQM.AV`
  lines, the same as in the originals (the `_iff_ab` proofs check that the terms agree).
- **Main.** After the switch, `lake build +ZInQKernel.OneProof.Main` exits 0 (12907 jobs);
  `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
- **Hashes after.** 11940 constants. `cmp_hashes.py`: 0 removed, 1 changed (`ZInQ.OneProof.frozenTarget`, the
  statement switch), 129 new (61 in `TailZ16`, 68 in `TailZ17`).
- **CheckRAF.lean** (`check_result.txt`): the types of the four changed and the one added field, of the two
  conversions and of `sixContactMin_of_open13`; the axioms of `sixContactMin_of_open13`, the four `_iff_ab`,
  `mumfordRigidity_of_core`, `r1fpProps_iff_ab_core`, `r1univProps_of_core_ab` and `frozenTarget`, all
  `[propext, Classical.choice, Quot.sound]`; `#print` of `R1fpPropsAb` and `DeligneComponentsY3PrintedAb`.
- **Module sizes.** TailZ16 32.6 KB, TailZ17 15.7 KB.

**Statements.** Only the four fields of §2 change, each to its printed form, and one field is added. No other
leaf, row or glue Prop changed. No HDec copy was deleted or added: all new declarations are in
`LeafQM.AV.R1UnivRigid` (kernel-side namespace, names not used in `ZInQKernel/HDecomp`) or are the four `LAb` next
to their `L` (`HDec.LeafAdopt`, `HDec.QMSplit.Moduli`, `ShimuraSplit`, `ShimuraGlue`), plus the bundles.

## 5. Not done, and caveats

- **The polarization (unchanged, r1univ-rigid §5.3).** `QMAbScheme`, like the kernel's `QML3`, has no polarization
  in its datum; Deligne's and Shimura's moduli problems do. Over a field, Lemma QP gives existence and uniqueness;
  the relative statement is a further step. `R1fpPropsAb` should be read as the unpolarized moduli problem with the
  Lemma QP caveat the rows already carry.
- **The audit's "specialization of Deligne's PEL model to this functor"** remains an open human check; its object
  is now an abelian-scheme statement.
- **The other 14 of the 18 leaves** are not `frozenTarget` fields (§1), so they need no fold. If a later fold brings
  one of them in (e.g. leaf-fold10 §5's split of `r1r2` into `GonzalezRotgerX6`, `DeligneComponentsX6Printed`,
  `BabaGranathRational`), it should use its `LAb` form from `scratch/r1univ-rigid/R1UnivLeaves.lean` and the same
  `mumfordRigidityCore` field.
- **The universal glue Props** on `R1fpProps` (51 in `ZInQKernel/`, r1univ-rigid §5.1) are not fields of
  `frozenTarget`; they are untouched.

## 6. `frozenTarget`: removed and added hypotheses

**Bundles.**
- Removed: `r : OpenResearchLeaves10`, `l : OpenAddedLeaves9`.
- Added: `r : OpenResearchLeaves11`, `l : OpenAddedLeaves10`.
- `t : OpenTextbookLeaves10` and `g : OpenGlue7` are unchanged.

**TYZ / GZ.** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` are unchanged.

**Fields removed (4):**
- research `r1r2 : LeafAdopt.R1R2fpRep`: proved from `r1r2Ab` and `mumfordRigidityCore`;
- research `shimuraFamily : QMSplit.Moduli.ShimuraFamily`: proved from `shimuraFamilyAb` and `mumfordRigidityCore`;
- research `gonzalezRotgerCountX6 : ShimuraSplit.GonzalezRotgerCountX6`: proved from `gonzalezRotgerCountX6Ab` and
  `mumfordRigidityCore`;
- added `deligneComponentsY3Printed : ShimuraGlue.DeligneComponentsY3Printed`: proved from
  `deligneComponentsY3PrintedAb` and `mumfordRigidityCore`.

**Fields added (5):**
- research: `r1r2Ab : LeafAdopt.R1R2fpRepAb`, `shimuraFamilyAb : QMSplit.Moduli.ShimuraFamilyAb`,
  `gonzalezRotgerCountX6Ab : ShimuraSplit.GonzalezRotgerCountX6Ab`,
  `mumfordRigidityCore : LeafQM.AV.R1UnivRigid.MumfordRigidityCore`;
- added-leaf bundle: `deligneComponentsY3PrintedAb : ShimuraGlue.DeligneComponentsY3PrintedAb`.

Fields: 59 → 60 (research 28 → 29, textbook 16, added 14, glue 1).

## 7. State of the branches

| branch | `.fleet` report seen | merged | folded |
|---|---|---|---|
| r1univ-rigid | yes (b40823ba, "fleet note") | yes (already in the base) | `MumfordRigidityCore` and the abelian-scheme clauses (`TailZ16`); the four `frozenTarget` fields among its 18 leaves (`TailZ17`) |
