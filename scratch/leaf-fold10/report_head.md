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

<!--COUNTS-->

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
