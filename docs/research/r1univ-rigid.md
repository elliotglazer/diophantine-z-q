# r1univ-rigid: the `R1univProps` gap closed by Mumford's rigidity

Task r1univ-rigid, 2026-11-14. Base df98652a (wip/w61). Lean: `scratch/r1univ-rigid/`. Results log:
`scratch/r1univ-rigid/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch
was edited. Model work, no human review.

Marks:
* **VERIFIED**: compiled, computed, or read in a file.
* **STANDARD**: published, with a reference.
* **SPECULATIVE**: a judgement.
* **UNVERIFIED**: a theorem number recalled without a source. There is no network on this host, and GIT is
  not in the repository.

## 1. Main result

**The owner's plan works. One extra leaf, Mumford's rigidity, makes every leaf stated on `R1fpProps`
equivalent to the same leaf stated on abelian schemes.** No statement changed. VERIFIED: compiled, standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

* **(1) The rigidity leaf** `LeafQM.AV.R1UnivRigid.MumfordRigidity` is stated over Mathlib's schemes and the
  kernel's `PkgI3.AbVar`.
  * Hypotheses:
    * `S` is locally noetherian.
    * `F → S` is proper, smooth, and geometrically connected (Mathlib's notions).
    * `e : S → F` is a section.
    * Every field fibre `F_s` (`s : Spec K → S`) is a `PkgI3.AbVar` whose identity point maps to `e(s)`.
  * Conclusion: `F` carries a `GrpObj` structure in `Over S` with identity `e`, such that
    * (a) every `S`-endomorphism `f` of `F` with `f ∘ e = e` is a homomorphism;
    * (b) every identification `A ≅ F_s` of an abelian variety with a fibre that carries identity to `e(s)`
      is a group homomorphism.
  * Source: Mumford, *GIT*, Ch. 6: Def. 6.1, Prop. 6.1, Cor. 6.4, Cor. 6.6 and Thm. 6.14. The numbers are
    UNVERIFIED.
  * **Clause (b) is proved** (`isGrpFibre_of_rigidity`, `mumfordRigidity_of_core`, VERIFIED). So the leaf a
    fold needs is `MumfordRigidityCore`: the existence of the group law plus (a), i.e. *GIT* Thm. 6.14 and
    Cor. 6.4 over `S`, in printed form. Clause (b) follows from the kernel's field-level rigidity
    `G0FibreSimple.rigidityHom`, applied to the base change `(Over.pullback s).obj F` with Mathlib's
    `Functor.grpObjObj`.
* **(2) The published moduli problem** `QMAbScheme S` is an abelian scheme over `S` with `𝒪`-action and
  level-3 structure. It extends the kernel's `QMFamily S` by:
  * a `GrpObj` structure with identity `η(0)`, and geometrically connected fibres;
  * `ι : 𝒪 → End_S(A)`, a unital ring homomorphism into the homomorphisms;
  * `η : 𝒪 → A(S)`, an `𝒪`-linear group homomorphism with `η(3𝒪) = 0` globally and kernel exactly `3𝒪` on
    every field fibre.

  `R1univAbProps`, `R1famAbProps` and `R1fpPropsAb` are the kernel's three clauses with "family" read as
  "abelian scheme with `𝒪`-action and level 3".
* **(3) `r1univProps_of_ab : MumfordRigidity → R1univAbProps Y Φ → R1univProps Y Φ`.**
  * `R1univProps` is used exactly as in `ZInQKernel/HDecomp/QM/Leaves.lean`: the file imports it and does
    not copy it.
  * The proof builds a `QMAbScheme` on every `QMFamily` over a proper smooth curve `S/ℚ` whose field fibres
    are objects (`exists_qmAbScheme`).
  * The group law and (a), (b) come from the leaf. The other identities are checked on field points over
    the reduced schemes `S` and `F`.
* **The clause lists agree:** `r1fpProps_iff_ab : MumfordRigidity → (R1fpProps Y Φ ↔ R1fpPropsAb Y Φ)`.
  * Hence `r1fpProps_eq_ab : MumfordRigidity → R1fpProps = R1fpPropsAb`, as predicates.
  * Without rigidity only the easy halves hold: `R1univProps → R1univAbProps` and
    `R1famAbProps → R1famProps`.
* **(4) The fold theorems.** For each of 18 leaves `L` on `R1fpProps`, `LAb` is the text of `L` with
  `R1fpPropsAb`, and `L_iff_ab : MumfordRigidity → (L ↔ LAb)` is compiled.
  * The 18 are the eight rows of frontier r5 §4.11, shimura-glue's four (two printed Deligne leaves,
    `BabaGranathRational`, `ElkiesConicT`), `R1R2fpRep` (`r1r2`), `CanonicalModelY3`, `ShimuraFamily`,
    `Y3Connected`, and leaf-qm-fp's `R1fp` and `R1R2fp`.
  * Each proof is `unfold; rw [r1fpProps_eq_ab hR]` closing by `Iff.rfl`. This also checks that the copy is
    verbatim up to the one replacement.
  * A fold swaps field `L` for field `LAb` plus one field `MumfordRigidity`, via `(L_iff_ab hR).2`.

So for the moduli rows the count changes by one: the published fine-moduli statements are now stated on
abelian schemes, as printed, and **`MumfordRigidityCore` is the one new leaf**. The same theorems with
`MumfordRigidityCore` are `r1univProps_of_core_ab` and `r1fpProps_iff_ab_core`; for the 18 leaves, compose
with `mumfordRigidity_of_core`. The Lemma QP caveat
(polarization) is unchanged (§5.3).

## 2. Library survey

Done first, as the task asked. VERIFIED by grep.
* **Rigidity over a field is proved in the kernel.**
  * `G0FibreSimple.rigidityHom` (`ZInQKernel/Contrib/FrobChain/Rigidity.lean`): a pointed morphism of
    `PkgI3.AbVar`s is a homomorphism.
  * The same result appears as `CloudW07JacobiansCurves/.../Group/Rigidity.lean`,
    `isMonHom_of_isProper_of_geometricallyIntegral`.
  * `CloudW06PoincareRigidity.rigidity_family` is the rigidity lemma over an algebraically closed field.
* **Nothing over a base scheme.** Neither `ZInQKernel/` nor its vendored code (Tau Ceti, the CloudW0*
  modules, AnthropicFLT, AxiomMath Mordell) has:
  * relative rigidity (GIT Prop. 6.1, Cor. 6.4);
  * the group structure on a smooth proper family with a section (GIT Thm. 6.14).
* **Existing notions of abelian scheme:**
  * The kernel's `PkgI2.IsAbelianScheme` (`Objects.lean:801`, GIT Def. 6.1) is a class on
    `Grp (Over (Spec O))`, so over affine bases only.
  * CloudW03's `AbelianSchemePropertyBundle` assumes a group law.

  `QMAbScheme` follows `IsAbelianScheme` (group object, proper, smooth, geometrically connected) over an
  arbitrary `S`.

## 3. The statements (`scratch/r1univ-rigid/R1UnivRigid.lean`, imports `ZInQKernel.HDecomp.QM.Leaves`)

### 3.1 Fibres

* `IsAbVarFibre F e s A g` says two things:
  * `g : A → F` makes `A → Spec K` the pullback of `F → S` along `s`;
  * `g` sends the identity `K`-point of `A` to `s ≫ e`.

  This is the shape of the kernel's `IsFibreOf` at `a = 0`, and of `IsBaseChangeOfPair`.
* `IsGrpFibre F A g`: some `φ : A ×_K A → F ×_S F` over `g × g` satisfies `μ_A ≫ g = φ ≫ μ_F`. Such a `φ` is
  unique, since `F ×_S F` is a pullback.

### 3.2 The leaf `MumfordRigidity`

```
∀ S (F : Over S) (e : S ⟶ F.left), IsLocallyNoetherian S → IsProper F.hom → Smooth F.hom →
  GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 S →
  (∀ K [Field K] (s : Spec K ⟶ S), ∃ A g, IsAbVarFibre F e s A g) →
  ∃ _ : GrpObj F, η[F].left = e ∧ (∀ f : F ⟶ F, e ≫ f.left = e → IsMonHom f) ∧
    (∀ K s A g, IsAbVarFibre F e s A g → IsGrpFibre F A g)
```

It is a **consequence of printed statements** (STANDARD, numbers UNVERIFIED):
* **Existence.** Mumford, *GIT* Thm. 6.14: if `S` is connected and locally noetherian, `F → S` is smooth and
  proper with a section, and one fibre is an abelian variety with origin `e(s)`, then `F` is an abelian
  scheme with identity `e`. The proof is Grothendieck's, through rigidity of deformations, *GIT* §6.3. The
  leaf applies this on each connected component of `S`, which is open since `S` is locally noetherian, and
  takes the disjoint union of the group laws.
* **(a)** is *GIT* Cor. 6.4: an `S`-morphism of abelian schemes that carries identity to identity is a
  homomorphism. The leaf uses it with `X = Y = F`.
* **(b).** `F_s` is an abelian scheme over `Spec K` with identity `e(s)`, so `g : A ≅ F_s` is a homomorphism
  by Cor. 6.4 over `Spec K`. Equivalently, by Mumford, *Abelian varieties*, §4 Cor. 1, which the kernel
  proves as `rigidityHom`.

The hypotheses are stronger than printed: every fibre at every field must be an abelian variety, and `S`
need not be connected. So the leaf is not stronger than its sources. It is stated over genuine definitions:
* Mathlib's `GrpObj` in `Over S` (pullback monoidal structure), `IsProper`, `Smooth`,
  `GeometricallyConnected` and `IsPullback`;
* the kernel's `AbVar`.

It is neither vacuous nor a disguised form of the conclusion: it says nothing about `𝒪`, level structures,
`Y` or `Φ`.

### 3.3 The objects `QMAbScheme S` and the abelian-scheme clauses

`QMAbScheme S extends QMFamily S` adds these fields:
* `[grp : GrpObj F]` and `geomConn : GeometricallyConnected F.hom`, so `F` is an abelian scheme of relative
  dimension 2 (*GIT* Def. 6.1);
* `one_eq : η[F].left = eta 0`;
* `iota_hom` (each `ι(a)` is a homomorphism), `iota_one`, `iota_mul : ι(ab) = ι(b) ≫ ι(a)` (that is,
  `ι(a)∘ι(b)`), and `iota_add : ι(a+b) = ι(a)·ι(b)` in the group `Hom_S(F, F)`;
* `eta_add : η(a+b) = η(a)·η(b)` in `A(S)`, `eta_linear : η(ab) = ι(a)∘η(b)`, and
  `eta_ker : s ≫ η(a) = s ≫ η(0) ↔ a ∈ 3𝒪`, at every field point `s`.

Notes on the definition:
* **Level clause.** It is the relative form of the kernel's `Level3`. In characteristic 0, an `𝒪`-linear map
  `(𝒪/3𝒪)_S → A[3]` that is injective on geometric fibres is an isomorphism (STANDARD): both sides are finite
  étale of degree `81 = #A_s[3]` (the kernel's `TorsionStructure`).
* **Injectivity of `ι`** is not a field. For `S ≠ ∅` a unital ring map `𝒪 → End_S(A)` is injective: its
  kernel is a two-sided ideal with torsion-free quotient, and `B` is simple. For `S = ∅` there is nothing to
  classify.
* **Polarization.** Not part of the datum (§5.3).

The three clauses:
* `R1univAbProps Y Φ` is `R1univProps Y Φ` with `𝒜' : QMAbScheme S.left` in place of `𝒜' : QMFamily S.left`.
  The object-fibre hypothesis is kept, which only weakens the statement. It is a consequence of the
  representability of the moduli problem on `ℚ`-schemes, as follows:
  * define `Φ` from the fibres of the universal object;
  * a family `𝒜' ≅ g^*𝒰` has fibre `P` at `s` isomorphic to the fibre of `𝒰` at `s ≫ g`;
  * that scheme isomorphism respects `ι` and `η`, and it is a group isomorphism by field rigidity
    (`rigidityHom`, proved).
* `R1famAbProps Y Φ`: `Φ` is induced by a `QMAbScheme` over `Y`, the universal object.
* `R1fpPropsAb`: the kernel's six-clause `R1fpProps` with the last two replaced by `R1famAbProps` and
  `R1univAbProps`.

## 4. The proofs

### 4.1 Glue lemmas (VERIFIED, compiled)

* `isReduced_of_smooth`: a scheme smooth over a field is reduced. Copied verbatim from curve-split; it uses
  `ZInQ.SmoothFibre.isReduced_of_smooth_of_field`.
* `hom_ext_pts`: two morphisms from a reduced scheme that agree on all field points and are equal over a
  separated base are equal. This is Mathlib's `ext_of_fromSpecResidueField_eq` at residue fields.
* `fibre_of_fieldPt`: a field point `t : Spec K → S.left` is a point of `fieldPt K` for the induced
  `ℚ`-algebra `K` (via `Spec.preimage`). So the hypothesis of `R1univProps`, stated for `ℚ`-algebras, gives
  fibres at all field points.
* `geomConn_of_fibres`: Mathlib's `GeometricallyConnected` (pullbacks along `Spec K → S`) follows from the
  fibres `P.A`, which are geometrically integral, hence irreducible, hence connected.
* `F_ext`, `sec_ext`: maps `F → F`, and sections `S → F`, are determined by the fibre identifications `g`.
  The proof lifts a field point of `F` through the pullback square.
* `lift_comp_φ`: bookkeeping for `lift` into `F ×_S F`.

### 4.2 The main construction `exists_qmAbScheme`

Over a reduced, locally noetherian `S`, let `𝒜 : QMFamily S` have reduced total space and object fibres at
every field point. Then `𝒜` underlies a `QMAbScheme`.

* The leaf applies with `e = η(0)`:
  * `Smooth` comes from `SmoothOfRelativeDimension 2`;
  * geometric connectedness is `geomConn_of_fibres`;
  * the fibre hypothesis is `IsFibreOf` at `a = 0`, using `P.e.eta 0 = 0`, so its `toMul` is the identity
    point.
* `η(0) ≫ ι(a) = η(0)` is checked on field points with `sec_ext`: `ι_P(a)` is a homomorphism, so it fixes
  the identity point. With (a), every `ι(a)` is a homomorphism.
* The ring identities are checked on fibres:
  * `ι(1)`, `ι(ab)` with `F_ext`;
  * `ι(a+b)` with `F_ext` and (b), applied to `φ`;
  * `η(a+b)` with `sec_ext` and (b);
  * `η(ab)` with `sec_ext` and the kernel's `Level3.linear`.
* `eta_ker` uses two facts:
  * maps `Spec K → P.A` over `Spec K` are determined after `g` (pullback uniqueness);
  * the kernel's `Level3.eq_iff`.
* `S` and `F` are reduced because they are smooth over `ℚ` (`reduced_of_smooth_curve`).

### 4.3 The theorems

* `r1univProps_of_ab` (3). Apply `exists_qmAbScheme` to `𝒜'`, then `R1univAbProps` to the result, whose
  `toQMFamily` is `𝒜'` by `rfl`.
* `r1famAbProps_of_r1famProps`. The family `𝒜` of `R1famProps` has object fibres at every point, since
  `Φ K y` is the class of some `P` (`Quotient.exists_rep`). So `exists_qmAbScheme` applies.
* `r1fpProps_iff_ab` combines the four directions. `r1fpProps_eq_ab` is the same statement under `funext`
  and `propext`.

## 5. Review of the statements

### 5.1 Which direction needs rigidity

* **Existential leaves** (`∃ Y Φ …, R1fpProps Y Φ ∧ …`; all 18 of §6) need `R1fpPropsAb → R1fpProps`.
  * The fam clause is free.
  * The univ clause is `r1univProps_of_ab`, which uses rigidity. This is the gap the task names.
* **Universal glue Props** (`∀ Y Φ, R1fpProps Y Φ → …`) need `R1fpProps → R1fpPropsAb` to be derived from
  their abelian-scheme forms. Of the 68 Props in `ZInQKernel/` other than `R1fpProps` whose definitions
  mention it (VERIFIED, script scan), 51 are universal, 15 are existential and 2 are neither.
  * The univ clause is free.
  * The fam clause (`r1famAbProps_of_r1famProps`) uses rigidity.

  With `r1fpProps_eq_ab`, a Prop in any position can be rewritten.

### 5.2 Faithfulness of `MumfordRigidity` (SPECULATIVE, reading)

* **Clause (b) is not part of the leaf a fold needs.** `MumfordRigidityCore` (Thm. 6.14 plus Cor. 6.4 over
  `S`) implies `MumfordRigidity` (`mumfordRigidity_of_core`, compiled). The proof, `isGrpFibre_of_rigidity`:
  * `F_s = (Over.pullback s).obj F`, with Mathlib's `Functor.grpObjObj`, is a `PkgI3.AbVar`. It is proper
    and smooth by base change, and geometrically integral through the isomorphism `A ≅ F_s`
    (`IsPullback.isoPullback`); `GeometricallyIntegral` respects isomorphisms because it is `geometrically`
    of a property.
  * `A ≅ F_s` carries `η` to `η`, computed with `obj.η_def` and `Over.ε_pullback_left`. So it is a
    homomorphism by `G0FibreSimple.rigidityHom`.
  * Its multiplicativity, through `obj.μ_def` and `Over.μ_pullback_left_fst_fst`/`_fst_snd`, gives the `φ`
    of `IsGrpFibre`.
* **Over a non-reduced `S`.** Thm. 6.14 holds over any locally noetherian connected `S` (as recalled), and
  the project only applies the leaf to smooth curves over `ℚ`. A more cautious form adds `IsReduced S` as a
  hypothesis; that would only weaken the leaf, and the proof already has `IsReduced S` available.

### 5.3 What this does not close

* **The polarization.** The frontier's "extension of the polarization" is not touched.
  * Deligne's PEL moduli problem has a principal polarization of type `μ` in its datum, as does Shimura's;
    the kernel's `QML3` and this `QMAbScheme` have none.
  * Over a field, Lemma QP (rv-qm-polar) says the polarization exists and is unique. The relative form over
    `S` (a polarization of `A/S` from those of the fibres) is a further step.
  * Buzzard (Duke 1997, §1; UNVERIFIED) states the QM moduli problem without polarization, but for level
    prime to the discriminant; here the level 3 divides `disc B = 6`, although over `ℚ` this does not matter
    for representability. The integrator should read `R1fpPropsAb` as the unpolarized moduli problem, with
    the Lemma QP caveat the rows already carry.
* **The audit's "specialization of Deligne's PEL model to this functor".** This open human check is
  unchanged, but its object is now an abelian-scheme statement.

## 6. The 18 leaves

`R1fp` and `R1R2fp` are in `R1UnivRigid.lean` §7 (`r1fp_iff_ab`, `r1R2fp_iff_ab`); the other 16 are in
`scratch/r1univ-rigid/R1UnivLeaves.lean` §8-§11.

All compiled, standard axioms (VERIFIED). Each row has `L_iff_ab : MumfordRigidity → (L ↔ LAb)`.

| row | leaf `L` | where `L` is defined | `LAb` | theorem |
|---|---|---|---|---|
| H-142 | `HDec.QMSplit.Moduli.GonzalezRotgerX6` | scratch/qm-glue/ModuliCompare.lean (copied) | `…GonzalezRotgerX6Ab` | `gonzalezRotgerX6_iff_ab` |
| H-145 | `ShimuraSplit.GonzalezRotgerCountX6` | OneProof/H/TailZ8.lean | `…Ab` | `gonzalezRotgerCountX6_iff_ab` |
| H-149 | `HDec.QMSplit.Moduli.DeligneComponentsX6` | OneProof/H/TailZ12.lean | `…Ab` | `deligneComponentsX6_iff_ab` |
| H-151 | `HDec.QMSplit.Moduli.BabaGranathX6'` | scratch/shimura-split/Rows.lean (copied) | `BabaGranathX6'Ab` | `babaGranathX6_iff_ab` |
| H-152 | `HDec.QMSplit.Moduli.ReciprocityCanonical` | Rows.lean (copied) | `…Ab` | `reciprocityCanonical_iff_ab` |
| H-153 | `HDec.QMSplit.Moduli.ElkiesConicX6` | Rows.lean (copied) | `…Ab` | `elkiesConicX6_iff_ab` |
| H-154 | `HDec.QMSplit.Moduli.ShimuraHolFamily` | scratch/shimura-split/ShimuraFam.lean (copied with `IsShimuraHolFamily`, `IsHolFamily`) | `…Ab` | `shimuraHolFamily_iff_ab` |
| H-155 | `ShimuraSplit.DeligneComponentsY3` | OneProof/H/TailZ12.lean | `…Ab` | `deligneComponentsY3_iff_ab` |
| shimura-glue | `ShimuraGlue.DeligneComponentsY3Printed` | TailZ12.lean | `…Ab` | `deligneComponentsY3Printed_iff_ab` |
| shimura-glue | `ShimuraGlue.DeligneComponentsX6Printed` | TailZ12.lean | `…Ab` | `deligneComponentsX6Printed_iff_ab` |
| shimura-glue | `HDec.QMSplit.Moduli.BabaGranathRational` | scratch/shimura-glue/parts/MobiusNew.lean (copied) | `…Ab` | `babaGranathRational_iff_ab` |
| shimura-glue | `HDec.QMSplit.Moduli.ElkiesConicT` | MobiusNew.lean (copied, with `ConicModelT`) | `…Ab` | `elkiesConicT_iff_ab` |
| H-1 (`r1r2`) | `HDec.LeafAdopt.R1R2fpRep` | OneProof/H/LPrefix.lean | `…Ab` | `r1R2fpRep_iff_ab` |
| — | `HDec.QMSplit.Moduli.CanonicalModelY3` | OneProof/H/TailU.lean | `…Ab` | `canonicalModelY3_iff_ab` |
| H-139 | `HDec.QMSplit.Moduli.ShimuraFamily` | TailU.lean | `…Ab` | `shimuraFamily_iff_ab` |
| H-59 | `HDec.TSHecke.Y3Connected` | OneProof/H/TailG.lean | `…Ab` | `y3Connected_iff_ab` |
| leaf-qm-fp | `LeafQM.AV.R1fp` | HDecomp/QM/Leaves.lean | `R1UnivRigid.R1fpAb` | `r1fp_iff_ab` |
| leaf-qm-fp | `LeafQM.AV.R1R2fp` | HDecomp/QM/Leaves.lean | `R1UnivRigid.R1R2fpAb` | `r1R2fp_iff_ab` |

How the rows are set up:
* Each `LAb` sits in `L`'s namespace with `L`'s `open`s.
* `L_iff_ab` closes by `rw [r1fpProps_eq_ab hR]` and then `Iff.rfl`, so `LAb` elaborates to the same term
  as `L`, apart from the one constant.
* The copied definitions keep their original namespaces and texts (`extract.py`). Their names do not occur
  in `ZInQKernel/`.
* shimura-glue's `RayClassCM` is not listed, because its dependencies (`residueImage`, Tau Ceti ray class
  fields) are in a scratch file. `r1fpProps_eq_ab` applies to it the same way.

## 7. What remains

1. **Done since the first draft:** the leaf has been reduced to `MumfordRigidityCore` (§5.2).
2. **Integration.** `R1UnivRigid.lean` imports `ZInQKernel.HDecomp.QM.Leaves`,
   `ZInQKernel.Contrib.FrobChain.Rigidity`, `ZInQKernel.Contrib.Dim.SmoothStalk`,
   `ZInQKernel.Contrib.SmoothFibre.Basic` and two Mathlib files. It can go to
   `ZInQKernel/HDecomp/QM/` as it stands. `R1UnivLeaves.lean` is generated (`build_leaves.sh`) and would be
   replaced in a fold by the `L_iff_ab` lines next to each leaf.
3. **The polarization step** (§5.3) remains with the Lemma QP caveat.

## 7a. Independent review

A fresh model reviewer read §1-§3 and §8 of `R1UnivRigid.lean` (not the proofs) against GIT Ch. 6 and the
kernel's definitions:
* **No PROBLEM.**
* **One RISK, now fixed.** The level clause was fibrewise only. Over a non-reduced `S` that admits objects
  the published problem does not: for `S = Spec ℚ[ε]` and `η = η₀ + ε·δ`, every field fibre has kernel
  `3𝒪`, but `η(3) ≠ 0`.
  * `QMAbScheme` now also has `eta_three : η(3b) = η(0)`, which only shrinks the class.
  * It is proved in `exists_qmAbScheme` on field points, over the reduced `S`. Everything recompiles.
* **Confirmed:**
  * `MumfordRigidityCore`'s hypotheses are stronger than Thm. 6.14 needs.
  * Clause (b) is proved.
  * No universe or quantifier issue.
  * Injectivity of `ι` and the Kottwitz condition are automatic in characteristic 0.
  * `∃ Y Φ, R1fpPropsAb Y Φ` follows from unpolarized fine moduli plus field rigidity.
* **Caveats it repeated,** both already on `R1fp`: Lemma P in families on the PEL route, and whether
  Buzzard covers full level 3.

## 8. Files and checks

* `scratch/r1univ-rigid/R1UnivRigid.lean`: §1-§8, the leaf, the objects, the glue, the theorems, the
  transfer for `R1fp` and `R1R2fp`, and the derivation of clause (b) (`MumfordRigidityCore → MumfordRigidity`).
  `check.sh` compiles it in about 11 s (VERIFIED). `#print axioms r1fpProps_iff_ab` gives
  `[propext, Classical.choice, Quot.sound]`.
* `scratch/r1univ-rigid/R1UnivLeaves.lean`: generated by `build_leaves.sh` from the core (verbatim) and
  `parts/copies.lean`, `parts/transfer.lean`, `parts/printed.lean` and `parts/thms.lean`, over
  `ZInQKernel.OneProof.H.TailZ12`. It compiles in 8.5 s and 8.6 GB (VERIFIED), and all 19 theorems of §9-§11
  use the standard axioms.
* `check.sh` uses the build of `~/dzq-check2`, which is at the same commit df98652a, because this worktree
  has no `.lake/build`.
* `extract.py` copies a definition with its docstring verbatim.
