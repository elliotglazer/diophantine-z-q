# reduct-glue: reduct-split's four glue Props proved from published leaves; the leaves over their printed bases

Task reduct-glue, 2026-11-14. Base 4e5f255b (wip/w60). Lean: `scratch/reduct-glue/ReductGlue.lean`, one file that
imports only kernel modules. It consists of `Base.lean`, a verbatim copy of `scratch/reduct-split/Reduction.lean`
(`diff` is empty; namespace `ReductSplit`; no statement changed), followed by `Body.lean` (namespace `ReductGlue`).
`mk.sh` assembles the two parts. The file has no `sorry` and no `axiom`. The 44 `#print axioms` lines at the end
all report `[propext, Classical.choice, Quot.sound]` (VERIFIED, `scratch/reduct-glue/axioms.txt`). Results log:
`scratch/reduct-glue/log.md`. Nothing under `ZInQKernel/` or `blueprint/` was edited. This is model work with no
human review.

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number recalled without a source. There is no network on this host, so BLR,
SGA 3, SGA 7, EGA, Stacks and Serre–Tate could not be consulted, and every locator below is UNVERIFIED.

## 1. Main result

**All four glue Props are proved.** reduct-split left `FixedTorsionRationalImperfect`, `SemistableLocalGlobal`,
`SemistableAlmostAll` and `SemistableNeronBaseChangeLocalGlobal` (its `ReductGlue`). Each is now a Lean theorem
from leaves (qualified below). reduct-split's seven rows (r6, r7b, r8, SS1, SS2, SS3, faltingsLemma5BC) follow from:
- its `ReductLeaves`;
- six further leaves (`ReductGlueLeaves`);
- `HeightSplit.FaltingsLemma5`, as before.

No named glue Prop is left on the general route: `rows_of_leaves_noGlue`, VERIFIED (the Lean fact only). This
holds only relative to reduct-split's `ReductLeaves`, whose six SGA 7 and Serre–Tate fields count as (b) under the
strict rule (reduct-glue review v2, §4). On the printed route three named glue Props remain (§4), and the
strict-henselization leaves combine two prints each (EGA IV 18.8 and BLR §1.2), so none of them is a single
published statement.

| reduct-split glue | Lean proof | what it rests on |
|---|---|---|
| `FixedTorsionRationalImperfect` (r6) | `fixedTorsionRationalImperfect_of_mulEtale` | bundle leaf `AvSplit.T4.MulEtaleAbelianScheme` (BLR 7.3/2, already in the leaf bundles) |
| `SemistableAlmostAll` (SS1) | `semistableAlmostAll_of` | kernel `FrobPiecesNeron.AbVarSpreadsOut` (proved in the kernel from the EGA IV leaves, `abVarSpreadsOut_of_ega4`) and kernel leaf candidate `ProperSmoothGenConnected` (Zariski connectedness); the vendored FLT-project Néron mapping property of abelian schemes (`Contrib/CloudW03NeronSurj`, proved) |
| `SemistableLocalGlobal` (SS1–SS3) | `semistableLocalGlobal_leaf` | **new leaf `NeronLocalizesDVR`** (BLR §1.2 Prop. 4) |
| `SemistableNeronBaseChangeLocalGlobal` (SS2) | `semistableNeronBaseChangeLocalGlobal_of` | **new leaves `IdentityComponentOL`** (SGA 3 VI_B 3.10) and **`OpenImmersionOfLocal`** (EGA IV₃ 8.10.5), with `NeronLocalizesDVR` and reduct-split's local leaf `IdentityComponentBaseChangeDVR` |

The bundles are `reductGlue_leaves : MulEtale → NeronLocalizesDVR → IdentityComponentOL → OpenImmersionOfLocal →
AbVarSpreadsOut → ProperSmoothGenConnected → ReductGlue` and `rows_of_leaves_noGlue (l : ReductLeaves)
(n : ReductGlueLeaves) (hF5 : HeightSplit.FaltingsLemma5)`.

**Printed bases.** Each SGA 7 and Serre–Tate field of `ReductLeaves` now also has a version over the base on which
it may be printed: strictly henselian for SGA 7, complete for Serre–Tate. The general-DVR leaf is proved from the
printed one for three fields:
- **SGA 7 IX 4.7**, the field reduct-split flagged (`raynaudSemistable_of_SH'`);
- **3.3, first assertion** (`persistsFromSH_of`);
- **3.5** (`unipotentFromSH_of`).

These proofs use three strict-henselization leaves. The other three (3.6, 3.3 second assertion, Serre–Tate) remain
named glue Props, each with a docstring that says what it needs (§4).

No statement was found false or vacuous.

## 2. The new leaves (cited; each a consequence of the print, never stronger)

These are not all single published statements: the three strict-henselization leaves each combine two prints
(EGA IV 18.8 with BLR §1.2), and under the strict rule every leaf in this table counts (b) (reduct-glue review v2,
§2).

| leaf | Lean statement (short) | source (UNVERIFIED locators) | why it is a consequence |
|---|---|---|---|
| `NeronLocalizesDVR` | `𝒩` Néron over `𝓞_L` ⇒ `toO 𝒩 O = 𝒩 ×_{𝓞_L} O` Néron over every DVR `O` of `L` | BLR, *Néron models*, §1.2 Prop. 4 (over a Dedekind base, a smooth separated finite-type model is Néron iff it is so at the local rings of the closed points) | `𝒩` is smooth and quasi-compact, so of finite type; every DVR `O` of `L` is a `(𝓞_L)_𝔭` (`mem_iff_exists`, proved). The bijectivity of the mapping property does not depend on which generic identification `toO` uses. |
| `IdentityComponentOL` | every `GroupModel` over `𝓞_L` has an open subgroup group model with connected geometric fibres at the maximal ideals | SGA 3 I, Exp. VI_B, Thm 3.10 (the identity component of a smooth group scheme is open); VI_A 2.4 (it is geometrically connected) | quasi-compactness from noetherianity; the generic fibre is `A_L`, which is connected, so the group-model identification exists |
| `OpenImmersionOfLocal` | a morphism of smooth, separated, quasi-compact `𝓞_L`-schemes that is an open immersion after base change to every DVR of `L` is an open immersion | EGA IV₃ 8.10.5 (the open-immersion item), with `Spec (𝓞_L)_𝔭 = lim U` | it is an open immersion over a neighbourhood of every closed point; these neighbourhoods also contain the generic point, and open immersions are local on the target |
| `StrictHenselizationNeron` | for a DVR `O` there is a strictly henselian DVR `O' ⊇ O` with algebraic residue extension, and Néron models base change to it | EGA IV₄ 18.8.8 and 18.8.13 (O^sh of a DVR is a strictly henselian DVR); BLR §1.2 Prop. 2 (Néron models commute with strict henselization) | the combination of the two |
| `StrictHenselizationPair` | the same for `O ⊆ O'` over a finite `K'/K`: strict henselizations `P ⊆ P'` with `[E' : E]` finite | EGA IV 18.8.10 / 18.6.8, Stacks 05WR; BLR §1.2 Prop. 2 | `O'^sh` is a local factor of `O' ⊗_O O^sh`, so `Frac O'^sh` is a factor of `K' ⊗_K Frac O^sh` |
| `StrictHenselizationInside` | inside an algebraic closure `Ω` at a place `w`: an intermediate field `E` (the inertia field) on which `w` is a strict henselization of `O`, fixed pointwise by the inertia of `w` | Stacks 0BSK–0BSL; Raynaud, *Anneaux locaux henséliens*, VIII; BLR §1.2 Prop. 2 | definition of the inertia field |

The table in §1 also uses kernel results that were already in place: `MulEtaleAbelianScheme` (a bundle leaf),
`AbVarSpreadsOut` (proved in the kernel from the EGA IV leaves) and `ProperSmoothGenConnected` (kernel leaf
candidate).

The pair `StrictHenselizationDVR` + `NeronBaseChangeUnramifiedDVR` is also stated, and
`strictHenselizationNeron_of` derives the combined leaf from it. The second member asks for Néron base change along
every unramified extension with separable residue field (BLR §7.2 Thm 1?). It is SPECULATIVE whether BLR prints
that generality. The bundles therefore use the combined leaf `StrictHenselizationNeron`, which needs only base
change to the strict henselization.

## 3. Proof notes (all VERIFIED by compilation)

- **r6, imperfect fields.** `A[m]` is the pullback `P` of `[m]` along the unit section. It is étale over `K` by base
  change of the leaf. `exists_rational_of_fixed_etale` proves that an `Aut(K̄/K)`-fixed `K̄`-point of an étale
  `K`-scheme is `K`-rational:
  - the image of an affine coordinate ring is an intermediate field that is formally unramified over `K`, hence
    separable (`FormallyUnramified.of_surjective`, `FormallyUnramified.isSeparable`);
  - a separable element fixed by `Aut(K̄/K)` lies in `K` (`mem_range_of_isSeparable_of_fixed`: the separable
    closure is Galois, then `AlgEquiv.liftNormal`).

  This proves `FixedTorsionRational` for every field, perfect or not.
- **DVRs of a number field** (§2 of Body):
  - `int_mem`: `𝓞_L ⊆ O`;
  - `center_isMaximal`;
  - `mem_iff_exists`: `O = (𝓞_L)_{𝔭_O}`, via `ValuationRing.cond` in the DVR `Localization.AtPrime 𝔭`;
  - `eq_of_center_eq`;
  - `resIso : κ(𝔭_O) ≃+* κ(O)`;
  - `barIso`, with `barIso_comp`;
  - `dvrAt 𝔭` (the `𝔭`-adic valuation ring) with `center_dvrAt`.
- **SemistableAlmostAll.** `abelianScheme_neron` bridges the vendored FLT theorem (an abelian scheme over a DVR has
  the full Néron mapping property) to the project's `Over` morphisms. `hasSemistableReduction_of_goodReduction`
  shows that the geometric special fibre is an abelian variety (kernel `FrobPieces.smoothGeomConnIntegral`). It is
  semi-abelian with `U = G`, `π = 𝟙` and torus rank 0 (`hasSemiAbelian_of_abVar`). `finite_dvr_mem_center` uses
  `Ideal.finite_factors`.
- **SemistableLocalGlobal.**
  - `neronO_unique`: Néron models over a valuation ring are unique as group schemes. Postcomposition is a
    homomorphism on `T`-points for smooth `T`.
  - `toO`: the base change `𝒩 ×_{𝓞_L} O` as a `GroupModelO`.
  - `fibreIso`: the geometric special fibre of `𝒩_O` is `σ^*` of the geometric fibre at `𝔭_O`, with `σ = barIso`.
  - `semiAbelianFieldIsoInvariant` (the transport glue, proved): `HasSemiAbelianIdentityComponent` is invariant
    under base change along a field isomorphism. Open immersion, flatness and surjectivity follow by conjugating with
    the isomorphism `pullback.fst`, connectedness through `Scheme.homeoOfIso`, and the torus through the adjunction
    bijection `Φ : (Spec R/k' ⟶ U_{k'}) ≃* (Spec R/k ⟶ U)` built from `Over.mapPullbackAdj`.
- **SS2.**
  - `𝒱 = 𝒩_{𝓞_{L'}}` and `𝒰 = 𝒩⁰_{𝓞_{L'}}` (kernel `H5Glue.GroupModel.baseChange`).
  - `j : 𝒰 → 𝒩'` extends the generic identification. It is a homomorphism by `isMonHom_of_ext`.
  - At a DVR `O'` of `L'`, with `O = O' ∩ L` (a DVR by `dvrComapFinite`), the local leaf gives an open immersion
    `j'`. `isOpenImmersion_of_neron` shows that two maps into a Néron model whose generic fibres are isomorphisms
    differ by an automorphism, so `j_{O'}` is an open immersion. `OpenImmersionOfLocal` then concludes.
  - The fibres of `U = 𝒩⁰_O` are connected: the generic fibre is `≅ A_L`, the special fibre goes through `fibreIso`
    and a homeomorphism.
- **Printed bases.**
  - `bcDVR`: the base change of a `GroupModelO` along `O ⊆ O'`.
  - `isSemistable_bcDVR_iff`: semistability is invariant when the residue extension is algebraic (`barIsoDVR`,
    `semiAbelianFieldIsoInvariant`).
  - `torsion_descends_etale`: `A_L(L̄)[m]` comes from `A(K̄)[m]`, by `exists_lift_of_etale` and `[m]` étale.
  - With `bcPt_extPt` and `extPt_extPt`, the last two give 4.7; 3.3a uses `bcbcIso` transport; 3.5 uses
    `T_ℓ(A_E) ≅ T_ℓ(A)` through `Tate.map bcPt` and the kernel's `bcPt_galAct`.

## 4. Leaves over their printed bases (every `ReductLeaves` field)

`IsStrictlyHenselianDVR O := IsDiscreteValuationRing O ∧ HenselianLocalRing O ∧ IsSepClosed (ResidueField O)`.
`IsCompleteDVR O := IsDiscreteValuationRing O ∧ IsAdicComplete 𝔪 O`. `printed_of_general` checks that each
printed-base leaf is a specialization of reduct-split's leaf, so none of them is stronger.

| `ReductLeaves` field | printed-base version | general leaf from it |
|---|---|---|
| `neronDVR` (BLR 1.4/3) | printed over an arbitrary DVR (UNVERIFIED) | no change needed |
| `sga7_3_5` | `SemistableUnipotentSH` | **proved**: `unipotentFromSH_of : StrictHenselizationInside → UnipotentFromSH` |
| `sga7_4_7` | `RaynaudSemistableSH` | **proved**: `raynaudSemistable_of_SH' : RaynaudSemistableSH → StrictHenselizationNeron → MulEtaleAbelianScheme → RaynaudSemistable` |
| `sga7_3_6` | `SemistableReductionSH` | glue `ReductionFromSH`: descend a finite `L/K^sh` to a finite `K'/K` (`K^sh` is a filtered union of fraction fields of étale `O`-algebras; Krasner); places of `K'` versus places over `O^sh`. Not in Mathlib. |
| `sga7_3_3a` | `SemistablePersistsSH` | **proved**: `persistsFromSH_of : StrictHenselizationPair → PersistsFromSH` |
| `sga7_3_3b` | `IdentityComponentBaseChangeSH` | glue `IdentityComponentFromSH`: besides the pair, fpqc descent of "open immersion" along `O' → O'^sh` (EGA IV 2.7.1), and the fact that the generic fibre of the given open subgroup `U` is all of `A_K` (an open subgroup of a connected group is closed) |
| `serreTate2` | `SerreTateThm2Complete` | glue `SerreTateFromComplete`: the completion of a DVR as a complete DVR with the same residue field (Mathlib has `Valued.Completion`, no package), identification of the inertia groups (Serre, *Corps locaux* II §3), Néron models and completion; also the descent of a finite extension `K''` of `K̂` to `K` (Krasner or density), the identification of completions, the choice of an embedding `ι` of `K̄` into an algebraic closure of `K̂`, the bijection on `A[ℓ^n]`, and, in characteristic `p`, the inseparable case, which needs Serre–Tate Thm 1 (r7a) |
| `mumford` | over an algebraically closed field (printed) | no change needed |

`reductLeaves_of_printed'' : ReductLeavesPrinted → StrictHenselizationPair → StrictHenselizationInside →
ReductPrintedGlue'' → ReductLeaves`, where `ReductPrintedGlue''` holds the three remaining reductions. The
`ReductLeavesPrinted` bundle also contains `StrictHenselizationNeron` and `MulEtaleAbelianScheme`.

**Each remaining glue Prop is as strong as the general leaf, given its printed leaf.** `ReductionFromSH`,
`IdentityComponentFromSH` and `SerreTateFromComplete` are bare implications `P_printed → P_general`, and the converse
`P_general → P_printed` is proved (`printed_of_general`). So each is equivalent to `P_printed ↔ P_general`: given its
printed leaf it is as strong as the general leaf, and it is strictly weaker only when that leaf is not given.

**Open readings besides the base** (all UNVERIFIED). The printed-base versions settle only the base; these readings
stay open:
- `SemistableUnipotentSH`, `SemistablePersistsSH`, `IdentityComponentBaseChangeSH`: SGA 7 may define semistability
  over `k(s)` rather than on the geometric special fibre, as `HasSemistableReduction` does (this matters for imperfect
  `k`);
- `SemistablePersistsSH`, `IdentityComponentBaseChangeSH`: the print may require `S'` finite over `S`;
- `SemistableUnipotentSH`: the 3.5 display may include the echelon clause;
- `RaynaudSemistableSH`: the print may state a Galois-form conclusion, and may require `n > 3` (the leaf allows
  `m = 3`);
- `SerreTateThm2Complete`: Serre–Tate may build `T_ℓ` over a separable closure `K_s`; in characteristic `p` the leaf
  (over an algebraic closure) can then be stronger than the print.

So confirming the strictly henselian base alone does not make 3.3a or 3.3b (a).

## 5. Statement review

- No statement was changed. `Base.lean` is byte-identical to reduct-split's file. The new file only adds imports in
  the header: `Contrib/CloudW03NeronSurj/Main` (which imports all of Mathlib) and `Contrib/FrobChain/Pieces`. The
  copied part still compiles with them (VERIFIED, 83 s).
- The four glue statements are true. Each is now a theorem from published leaves. They are not vacuous: their
  hypotheses are Néron models, which exist by BLR 1.4/3 and are non-trivial at the zero abelian variety
  (reduct-split §19).
- **Generality risks** (SPECULATIVE):
  - `NeronBaseChangeUnramifiedDVR` may exceed what BLR prints. It is not used in the bundles.
  - `NeronLocalizesDVR` is the "only if" direction of BLR 1.2/4, as I recall it. If the print uses strict
    henselizations instead of localizations, the leaf follows from that form together with
    `StrictHenselizationInside`-type results, but that derivation is not in Lean.
  - `OpenImmersionOfLocal` assumes that EGA IV 8.10.5 has an open-immersion item. If it does not, the leaf is the
    standard corollary for immersions together with flatness (UNVERIFIED).
  - The printed-base leaves of §4 settle only the base. The other open readings (semistability over `k(s)`, `S'`
    finite, the echelon clause, the Galois form and `n > 3` for 4.7, `K_s` in characteristic `p` for Serre–Tate)
    are listed at the end of §4.
- **Lean pitfalls found:**
  - A kernel deterministic timeout in the SS2 proof disappeared once `pbCompIso`, which contains an `eqToIso`, was
    made an `irreducible_def`.
  - Instance search fails on `IsIso 𝒰.gen.hom` when the objects are defeq but not syntactically equal. The fix is
    to pass `Iso.isIso_hom` explicitly through `@IsIso.of_isIso_comp_right`.

## 6. Checks

`scratch/reduct-glue/chk.sh` runs `mk.sh`, then `lake env lean scratch/reduct-glue/ReductGlue.lean`: about 56 s,
7.6 GB, no errors, 44 `#print axioms` lines, all standard (VERIFIED, 14:30). During development `Base.lean` and
`Body.lean` were compiled to private oleans in `/tmp/rglib` and imported by test files, one Lean process at a time.

For leaf-fold integration (SPECULATIVE count): reduct-split's 4 glue fields are now 0 glue. The leaves that this
adds are:
- in the general-DVR form: 3 new leaves (`NeronLocalizesDVR`, `IdentityComponentOL`, `OpenImmersionOfLocal`), with
  `MulEtaleAbelianScheme`, `AbVarSpreadsOut` (from the EGA leaves) and `ProperSmoothGenConnected` already in the
  kernel;
- in the printed form: `ReductLeavesPrinted` together with 2 strict-henselization leaves and 3 glue Props.
