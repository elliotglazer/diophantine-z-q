# genus-fold: `genusX1Field` dropped from the single proof; 58 fields, strict 44 LEAF / 14 GLUE (was 44 / 15 of 59)

Task genus-fold, 2026-11-14. Base e38375b3 (fork main df98652a = w61 with leaf-fold10 inside OneProof, plus the
prune of `r3`, `serreTateThm2`, `t10`; `origin/wip/genus-route` already merged). New Lean:

- `ZInQKernel/OneProof/Genus/DimJac.lean`, `GenusBound.lean`, `LocalDer.lean`: genus-route's `Closed.lean` (its proof
  of `dim J₁(N) ≤ N²` with no hypothesis) split in three, imports kernel modules only;
- `ZInQKernel/OneProof/Genus/Bridge.lean` (imports `H.TailC` and `Genus.LocalDer`): the statement in namespace
  `HDec` and the two drop-ins for TailD.

Edited existing modules (owner-approved exception): `H/TailD.lean` (one import, two proof terms) and the prune
deletions in `H/LPrefix.lean`, `TailA`, `TailE`, `TailI`, `TailK`, `TailN`, `TailO`, `TailX`, `TailZ4`, `TailZ9`,
`TailZ11`. No statement was edited. `Main.lean`, the build configuration, HDecomp, Contrib, blueprint and other
tasks' files are untouched. No HDec copy was deleted, so FaithCheck was not needed. Tools, outputs and the results
log are in `scratch/genus-fold/` (`log.md`). Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number or locator recalled without a source.

## 1. Main result

`ZInQ.OneProof.frozenTarget` keeps its statement text and still goes through `HDec.HSyn.sixContactMin_of_open12`
(H/TailZ15.lean):

```lean
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves10) (t : HDec.HSyn.OpenTextbookLeaves10) (l : HDec.HSyn.OpenAddedLeaves9)
    (g : HDec.HSyn.OpenGlue7)
    (h11 : TYZThm11Integral) (h29 : TYZLemma29Mod2) (hS : Shimura.ShimuraReciprocityModFn)
    (h33 : ZInQ.Contrib.TYZGenus.TYZSplit.TYZThm33)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget
```

but `OpenTextbookLeaves10` has lost the field `genusX1Field : ZInQ.Contrib.CurvesG.GenusX1Field` (GLUE (comp):
Shimura 1971 §6.7, Prop. 6.9, Prop. 1.40, not statable in published form). The bundles now have **58 fields:
44 LEAF and 14 GLUE** in the strict count, down from 59 (44 / 15). VERIFIED: `lake build +ZInQKernel.OneProof.Main`
exits 0, and `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`.
PruneScan finds 0 unused fields.

How it works:

1. **The two uses of `t34`.** `t34 : LeafModCurves.DimJ1Genus` (`dim J₁(N) = genus Γ₁(N)`) came from
   `t34_of_split5 t.dimJacobianEqGenus t.genusX1Field`. It was used only in `HSyn.glueOutputs_of_leaves3`
   (TailD): at E2 (`LeafModCurves.dim_J1_le t.t34 …`) and at G18 (`javanpeykarJ1 hR18 hBelyi t.t34 …`). Both
   need only `dim J₁(N) ≤ N²` (genus-route §1).
2. **The bound, with no hypothesis** (genus-route, now library code). `GenusFold.dimJ1Le : GenusFold.DimJ1Le`
   (`Genus/LocalDer.lean`) combines:
   - dimjac-glue's `dimJacobianEqGenus`;
   - genus-route's constant-field theorem (ℚ is algebraically closed in the function field of the model of
     `X₁(N)` carried by `IsJ1`);
   - the elementary bound `g(K_N) ≤ [K_N : ℚ(j)]` with the proved `localDerivation` (no Riemann–Hurwitz);
   - the kernel's `ZInQ.RLeaf.belyiX1` (`[K_N : ℚ(j)] ≤ N²`).
3. **Bridge** (`Genus/Bridge.lean`, namespace `HDec.HSyn`):
   - `DimJ1Le5` is genus-route's statement on the OneProof names.
   - `t34Le : DimJ1Le5 := GenusFold.dimJ1Le`. Lean accepts this term as it stands: after the dedupe,
     `HDec.PkgI3.AbVar` and `HDec.LeafModCurves.IsJ1` are the kernel's constants.
   - `dim_J1_le_of5` and `G0Split.javanpeykarJ1_of_le` are copied from genus-route's `Fold.lean`.
   - Two checks compile: an `example` that `dim_J1_le_of5 h` and `LeafModCurves.dim_J1_le t34` have the same
     type, and `javanpeykarJ1_of_le hR18 hB (dimJ1Le5_of_t34 t34) = javanpeykarJ1 hR18 hB t34 := rfl`.
4. **TailD.** The file gains `import ZInQKernel.OneProof.Genus.Bridge`, and two proof terms change:
   - E2: `dim_J1_le_of5 t34Le N hN0 J hJ1`;
   - G18: `javanpeykarJ1_of_le hR18 hBelyi t34Le …`.
5. **Prune** (PruneScan, then DeadCascade). The prune set is `TextbookLeaves.t34`,
   `OpenTextbookLeaves{2,3,4}.t34` and `OpenTextbookLeaves{6,7,8,9,10}.genusX1Field`. Deleted:
   - those 9 fields, with their docstrings;
   - the 10 assignments into them, including TailN's and TailO's `t34 := t34_of_split5 …` (both assign into the
     removed `OpenTextbookLeaves4.t34`);
   - the inline `genusX1Field := t.genusX1Field` in TailO's `sixContactMin_of_open6_poincare`;
   - DeadCascade's dead readers `modCurveLeaves_of_bundles`, `glueOutputs_of_leaves`, `sixContactMin_of_leaves`,
     `sixContactMin_of_leaves_pin`, `sixContactMin_of_open` (LPrefix) and `sixContactMin_of_leaves2` (TailA),
     with their `#print axioms` lines.

Namespaces: genus-route's code contains dimjac-glue's proof under the root namespaces `DimJacGlue` and
`ModularSplit.DimJac`, and leaf-fold10's `H/TailZ10.lean` declares the same names. TailD now imports the Genus
modules, so the copies were renamed `GenusFold.DimJacGlue` and `GenusFold.DimJac`, and `GenusRoute` was renamed
`GenusFold`. No other text changed (`scratch/genus-fold/split_closed.py`).

## 2. Every hypothesis

The four bundles are leaf-fold10's tables (`docs/research/leaf-fold10.md` §2), with four rows removed:
- three by the prune (`r3`, GLUE (comp); `serreTateThm2`, LEAF; `t10`, GLUE (c));
- one by this task (`genusX1Field`, GLUE (comp)).

The counts below are recomputed from `scratch/leaf-fold10/fields10.tsv` with those rows removed. They agree with
PruneScan's field counts.

| bundle | fields | strict LEAF | strict GLUE | GLUE fields |
|---|---|---|---|---|
| `OpenResearchLeaves10` | 28 | 19 | 9 | `r1r2`, `shimuraFamily`, `r11r12`, `eigenformHTNew`, `r16`, `r17`, `semistableNeronBaseChange`, `faltingsLemma5BC`, `neronLocalizesDVR` |
| `OpenTextbookLeaves10` | 15 (was 16) | 15 | 0 (was 1: `genusX1Field`) | — |
| `OpenAddedLeaves9` | 14 | 10 | 4 | `thetaRatiosAlgebraic`, `t09SymmIsogenyExists`, `x6ConicModel`, `shimuraGoodReductionNoGuard` |
| `OpenGlue7` | 1 | 0 | 1 | `quotientP1Coordinate` |
| **total** | **58** | **44** | **14** | |

(`scratch/genus-fold/counts.md`.) The textbook bundle is now all LEAF:
- `mulEtaleAbelianScheme`, `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed`, `charPolyIndepOfEllAlgClosed`,
  `poincareComplement`;
- `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim`;
- `uniformizationLeafAll`, `gagaMorphism`, `bdRInvariants`, `yuThm11`, `regularSmoothPerfect`, `igusaGL2`,
  `neronSchemeExtensionExists`.

Kinds, forms and sources of every kept field are leaf-fold10's, unchanged.

## 3. The remaining leaves by the theory they come from

This is leaf-fold10 §3 with the four removed fields taken out. The grouping boundaries are SPECULATIVE.

| group | # (not published form) | change |
|---|---|---|
| A. Shimura curves, QM abelian surfaces, Fuchsian groups | 11 (4) | −`r3` (prune) |
| A′. Theta functions, Siegel modular forms of genus 2 | 4 (1) | — |
| B. Abelian varieties, textbook theory | 8 (1) | −`t10` (prune) |
| C. Néron models, semistable reduction, monodromy | 10 (2) | −`serreTateThm2` (prune) |
| C′. Schemes and group schemes over a field | 5 (0) | — |
| D. Faltings 1983, Faltings heights | 7 (1) | — |
| E. p-adic Hodge theory | 6 (1) | — |
| F. Galois representations of modular forms | 5 (3) | — |
| G. Algebraic and modular curves | 1 (0) | −`genusX1Field` (this task); `igusaGL2` remains |
| total | **57 (13)** | plus the glue `quotientP1Coordinate` = 58 fields, 14 GLUE |

Group G now contains no composite. The genus of `X₁(N)` is no longer an input: the proof uses only
`dim J₁(N) ≤ N²`, and that bound is a theorem.

## 4. Checks (all VERIFIED; one Lean process at a time)

- **Base hashes.** `lake build +ZInQKernel.OneProof.Main` on the base (9.5 min, axioms standard); `DumpCompact`:
  11811 constants (`scratch/genus-fold/hashes_base.txt`).
- **Genus modules.** `lake build ZInQKernel.OneProof.Genus.LocalDer`: 10 s + 14 s + 15 s; `Bridge`: 4.6 s. Sizes:
  DimJac 38 KB, GenusBound 88 KB, LocalDer 56 KB, Bridge 4 KB (each under 150 KB).
- **After the TailD edit.** Main builds (8 m 45 s); axioms standard. PruneScan: `OpenTextbookLeaves10` unused
  `[genusX1Field]`, the other three bundles 0 unused; the prune set has 9 fields (`prune-set-before.txt`).
  DeadCascade: the 6 readers above plus the generated `casesOn`/`recOn` (`dead-cascade-before.txt`).
- **After the prune.** Main builds (16 min); `#print axioms ZInQ.OneProof.frozenTarget` = `[propext,
  Classical.choice, Quot.sound]`. PruneScan: **0 unused top-level fields**; prune set empty.
- **DumpCompact after** (12125 constants) and `cmp_hashes.py` against the base (`cmp_hashes_out.txt`):
  - **19 removed.** These are:
    - the 9 fields;
    - the 6 dead readers and 3 `_proof_*` auxiliaries of `glueOutputs_of_leaves`;
    - `topologicalKrullDim.eq_1`. This one is still in TailR (checked by `diag/EqLemma.lean`). It is a realized
      equation lemma that DumpCompact's enumeration of `map₁` no longer lists.
  - **333 new**, all in the new modules (Bridge 5, DimJac 67, GenusBound 177, LocalDer 84).
  - **174 changed**, listed by cause in `scratch/genus-fold/changed_constants.md`:
    - 80 bundle structures' generated auxiliaries: `mk`, `_flat_ctor`, `rec`, `casesOn`, `recOn`, and field
      projections whose index moved;
    - 11 conversions: `textbookLeaves*_of_open*` and `sixContactMin_of_open6_poincare`;
    - TailD's `glueOutputs_of_leaves3`, the edited theorem;
    - **2 theorems whose elaborated type changed with no source change**: `HDec.ZInQ.Contrib.AbVarBC.
      abVarBaseChange_of_torsionDescends` and `abVarBaseChangeK_of_torsionDescends` (TailE);
    - **80 theorems whose proof term changed with no source change**, in TailE–TailZ2 (TailG 24, TailH 21,
      TailF 9, TailE 7, TailU 6, TailJ 4, TailZ2 3, TailM 2, TailO 2, TailL 2).
  - `sixContactMin_of_open12` and `frozenTarget` keep their hashes, since they refer to the bundles by name.
- **The last two groups depend on the import, not on the edited proofs.** Through the vendored Jacobian library,
  the Genus modules import Mathlib files that the chain before TailZ10 did not import. Those files bring instances
  such as `CommSemiring.toHopfAlgebra` and `Coalgebra.IsFrobenius.*`, so typeclass search can now find other proofs
  of Prop-valued instances.
  - Example: the `IsLocalRing` proof that `FaithfulSMul` needs went through `IsRegularLocalRing` in the base. Now
    it goes through `HenselianLocalRing`, `IsArtinianRing` and `HopfAlgebra` (`diag/typeconsts_{base,after}.txt`).
  - Base tree for this check: `git archive e38375b3`, extracted outside the worktree with a reflink copy of
    `.lake/build`, then `lake build ZInQKernel.OneProof.H.TailE` (8 min).
  - **`diag/DefEqCheck.lean`** (run in this tree) states each base type, printed with `pp.all` in the base tree
    (`diag/base_type_*.txt`), as `rfl`-equal to the new type. It compiles with no error, so the elaborator and
    the kernel accept both equalities. The two statements are therefore the same Prop up to definitional
    equality.
  - `diag/Classify.lean`: among the 174 changed constants, the only data definitions are the bundles'
    `casesOn`/`recOn`. All 80 proof-only changes are theorems.
- **Not checked.** The owner's list of allowed changes does not foresee an import that changes instance search
  downstream. The 2 + 80 constants above are outside that list, and the owner should accept them explicitly. They
  cannot be avoided while TailD itself uses the proof: the proof needs the Jacobian library.
- **No host paths** in committed files (grep).

## 5. Not done, and why

- **The `dimJacobianEqGenus` fields in `OpenTextbookLeaves{6,7,8,9}`.** These are now unused inner fields
  (`unused-all.txt`). They are not in the prune set, because no unused *top* field feeds them:
  `textbookLeaves9_of_open10` fills them with dimjac-glue's theorem. Removing them would delete four inner fields
  and the assignments into them, and frozenTarget would not change. Not done, to keep to the prune set.
- **Leftover theorems.** `t34_of_split5` (TailM) is now unused, but it reads no removed field, so it stays (as
  `t10_ofK5` stayed after the prune). `OpenTextbookLeaves5.genusX1Field` and `OpenTextbookLeaves.t34` (LPrefix,
  off the chain) stay too: only the assignments out of them into removed fields were deleted, as the prune did
  for `t10`.
- **`x0Transitive`.** Still used for T40 (`t40_of_x0Transitive4`). That is outside this task (genus-route §2).
- `scratch/one-proof/prune_edit.py` does not exist on any origin ref. The deletions were scripted here instead
  (`scratch/genus-fold/prune_edit.py`; every deleted line is in `prune_edit_out.txt`).

## 6. `frozenTarget`: removed and added hypotheses

- **Bundles:** the same four (`OpenResearchLeaves10`, `OpenTextbookLeaves10`, `OpenAddedLeaves9`, `OpenGlue7`).
  **TYZ / GZ:** `h11`, `h29`, `hS`, `h33`, `hL2`, `hL3` unchanged.
- **Field removed (1):** textbook `genusX1Field : ZInQ.Contrib.CurvesG.GenusX1Field` (GLUE (comp)). Its only use,
  through `t34`, is replaced by the theorem `HDec.HSyn.t34Le`, which has no hypotheses.
- **Fields added:** none. PruneScan then found no other unused field.

## 7. State of the branches

| branch | merged | used |
|---|---|---|
| genus-route | already in the base (50a0c5ee) | `Closed.lean` → `Genus/{DimJac,GenusBound,LocalDer}.lean`; `Fold.lean`'s HDec part → `Genus/Bridge.lean` |
| prune-scan | not merged (it deletes other tasks' files); `PruneScan.lean`, `DeadCascade.lean` copied into `scratch/genus-fold/` with output paths changed | scan before and after |
