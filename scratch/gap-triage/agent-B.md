# agent-B: groups B, C′, G (abelian varieties textbook, schemes over a field, curves)

Base e38375b3 (worktree wip/gap-triage). Read-only; nothing compiled. Marks: VERIFIED-READ = I opened the file and
saw the declaration (signature quoted or paraphrased from the line); SPECULATIVE = judgement; UNVERIFIED = theorem
number from memory. "Chain" = `ZInQ.OneProof.frozenTarget` → `sixContactMin_of_open12` (TailZ15) → ... → TailX
(leaf-fold7 conversions) → TailO (`textbookLeaves4_of_open6`, `addedLeaves4_of_open6`) → TailK
(`gluePieces_of_open4`, L291) → TailD/LPrefix (`glueOutputs_of_leaves3`).

Key observation shared by the six FREE fields: none is applied to its full generality *in substance*. Every
actual use site I read is in characteristic 0 (number fields, subfields of ℚ̄, ℂ), and mostly at the QM abelian
surfaces of the construction (the fibre surface `A`, its G7 model `A_{L'}`), with `J₁(N)_{L'}` and products only
for heights and T8. The formal generality comes from intermediate kernel Props (`PkgI2.TorsionStructure`,
`PkgI3.TateModuleFree`, `PkgI2.RaynaudCriterion`, `WeilPairing.IsogenyQuasiInverse`, ...) that quantify over all
fields. So any weakening needs a restatement of those intermediate Props in the chain, not only of the leaf.

---------------------------------------------------------------------------------------------------------------

## B1. `mulEtaleAbelianScheme` (FREE)

**1. Identity.** `_root_.AvSplit.T4.MulEtaleAbelianScheme`, defined `ZInQKernel/OneProof/H/TailQ.lean:1681`.
Frontier r5 row H-101 (feeds old H-24). Form: LEAF, published form (BLR §7.3 Lemma 2; Mumford GIT §6, UNVERIFIED).
```lean
def MulEtaleAbelianScheme : Prop :=
  ∀ (O : Type) [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] (m : ℕ),
    IsUnit (m : O) → Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left)
```

**2. Use.** Field of `OpenTextbookLeaves10` (TailZ11:18), passed unchanged to 9/8/7. Two consumers:
* (i) `AvSplit.Final.h24` (TailQ:2362) = `reductionTorsionBijective_of_mulEtale` (TailQ:2349), giving T4
  `PkgI2.ReductionTorsionBijective` at `textbookLeaves6_of_open7` (TailX:227). The leaf is used in `rho_inj`
  (TailQ:1995: only *unramified + separated* is derived from étale) and `rho_surj` (TailQ:2025: étale, for
  Hensel). T4's only chain consumer: `linkedTateLocal_of_leaves3` (TailI:99, called at TailK:343-346)
  → `FrobPiecesGood.tateBridge35_of_neron_nmp` (Contrib/FrobChain/Pieces.lean:380) → `algFrobRed_of_nmp`
  (Contrib/FrobChain/FExtend.lean:279) → `FrobTrace.AlgFrobRed` (FrobTrace.lean:241). There `O = O_w ⊂ L` with
  `L/ℚ` Galois and `w` above `p ∉ S`, `𝒜` the good model of an abelian variety over `L` (the G7 model of the QM
  surface), and `m = ℓⁿ` with `ℓ ≠ p` (TateBridge35 needs `ℓ = 5, 3`).
* (ii) `fixedTorsionRationalImperfect_of_mulEtale` (TailZ14:236, via `fixedTorsionRational_of_mulEtale` TailZ14:191)
  → `raynaudCriterion_leaves` (TailZ14:241) → `r6` in `researchLeaves9_of_open10` (TailZ15:98-99). Here `O = K` is
  a *non-perfect field* and `𝒜 = A` an abelian variety: only "`A[m] → Spec K` is étale" is used. Every use of r6
  in the project is over number fields (TailZ7:1192 docstring says so), so this use is formally required by the
  `∀ K` of `RaynaudCriterion` but vacuous in substance.

Use (b). Weakest sufficient pair (implied by the leaf):
```lean
-- (i) good-reduction DVRs of number fields, prime-power orders
def MulEtaleNF : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (O : ValuationSubring L) [IsDiscreteValuationRing O]
    (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] (ℓ n : ℕ), ℓ.Prime → IsUnit (ℓ : O) →
      Etale ((𝟙 𝒜.X ^ (ℓ ^ n) : 𝒜.X ⟶ 𝒜.X).left)
-- (ii) over a field only the kernel is needed
def KerMulEtaleField : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (m : ℕ), (m : K) ≠ 0 →
    Etale (pullback.snd (𝟙 A.X ^ m : A.X ⟶ A.X).left (η[A.X]).left)
```
(ii) is a computation plus existing kernel work (see 4). (i) is still deep as stated (flatness over `O`), but T4
can avoid it (see 6).

**3. Library coverage.**
* Mathlib `AlgebraicGeometry/Morphisms/Etale.lean:136` VERIFIED-READ:
  `lemma iff_flat_and_formallyUnramified {f : X ⟶ Y} : Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f`;
  `:95` `lemma eq_smoothOfRelativeDimension_zero : @Etale = @SmoothOfRelativeDimension 0`.
* Mathlib `Morphisms/SmoothFiber.lean:34` VERIFIED-READ: `lemma Smooth.of_smooth_fiberToSpecResidueField
  [LocallyOfFinitePresentation f] [Flat f] (h : ∀ y, Smooth (f.fiberToSpecResidueField y)) : Smooth f`
  (fibrewise smoothness *given flatness*).
* Mathlib `Morphisms/FormallyUnramified.lean:123` VERIFIED-READ: `instance isOpenImmersion_diagonal
  [FormallyUnramified f] [LocallyOfFiniteType f]`.
* Mathlib `RingTheory/Etale/Field.lean:175` VERIFIED-READ (name and binders):
  `lemma of_formallyUnramified_of_field [EssFiniteType K A] [FormallyUnramified K A]` (formally étale).
* Mathlib has **no** fibrewise flatness criterion (Stacks 039A) and **no** Cohen–Macaulay / miracle flatness
  (grep for 039A/00R4/00MP/CohenMacaulay in Mathlib: no hits). No invariant differentials or Lie algebra of a group
  scheme (SPECULATIVE, grep negative).
* Kernel, characteristic 0, VERIFIED-READ: `ZInQ.Contrib.AbVarBC.Tangent.eq_one_of_comp_intCast`
  (Contrib/AbVarBC/Tangent.lean:449; "a tangent vector at the origin killed by `[n]`, `n ≠ 0`, char 0, is
  trivial", proved from `D_zpow`: `d[n] = n` on dual-number points). Also `KerUnit.lean:98 derivation_eq_zero
  [CharZero K]` and `:300 ks_isOpenImmersion [CharZero K]`, giving `kerUnitOpen` (Main.lean:22) and
  `MulRigidity.mulUnramified_of_kerUnitOpen` (Mul.lean:318). **`[CharZero K]` enters only through
  `eq_one_of_comp_intCast`** (grep of KerUnit.lean: its one use is L168), where it only provides
  `(n : K) ≠ 0`. So `[n]` formally unramified for `(n : K) ≠ 0` in every characteristic is a mechanical
  generalization (SPECULATIVE until compiled).
* Kernel `AvSplit.T4.unramifiedSectionsEq` (TailQ:2199), `stacksHenselEtaleSection` (TailQ:2254), proved from
  Mathlib. Kernel `exists_rational_of_fixed_etale` (TailZ14:93), VERIFIED-READ.
* CloudW03 vendored FLT parts (Contrib/CloudW03NeronSurj/Vendor): regular local rings, depth,
  `Def_Patching_CohenMacaulayOfDim.lean`, `S_IsRegularLocalRing_depth_self_eq_ringKrullDim.lean` (file names
  VERIFIED-READ; contents not read). These are a start towards miracle flatness. SPECULATIVE.

**4. Missing infrastructure (route that keeps the leaf's statement).** (a) `[m]` formally unramified on an
abelian variety when `(m:K) ≠ 0` (generalize the AbVarBC proofs above); (b) fibre criterion for formal
unramifiedness over `Spec O` (Nakayama on `Ω_{[m]}` and Kähler base change); (c) flatness of `[m]` over `O`:
either miracle flatness (CM theory) plus the fibrewise criterion, or invariant differentials
(`Ω_{𝒜/O} ≅ π^*ω`, `[m]^* = m` on `ω`) plus "a morphism of smooth `S`-schemes inducing an iso on `Ω` is
étale". (c) is the deep part.

**5. Tier.** As stated: T3 (flatness theory over a DVR). With the rewiring in 6: T2.

**6. Strategy: reduce, and eliminate.**
* (ii) r6: prove `FixedTorsionRationalImperfect` from 4(a) alone. `A[m]` is lft and formally unramified over
  `K` (base change of `[m]`), flat over a field, hence étale (`Etale.of_formallyUnramified_of_flat`); then
  `exists_rational_of_fixed_etale`. T1 after 4(a).
* (i) T4 without étaleness: `rho_inj` only needs `[m]` unramified + separated over `O` (4(a) on both fibres +
  4(b)). For surjectivity use counting instead of Hensel: `#𝒜(w)[m] = #A(K̄)[m] = m^{2g}` and
  `#Ā(κ(w))[m] = m^{2g}` (`κ(w)` is algebraically closed). Both come from the leaf `mumfordTorsionAlgClosed`,
  which the bundle already has in all characteristics. Then an injection of finite sets of equal size is a
  bijection. Also needed: the special fibre is an `IsAbelianVariety` of the same dimension (T2; kernel dimension
  pieces in Contrib/Dim, scratch/infra-smooth-dim).
* Net: `mulEtaleAbelianScheme` leaves the bundle (−1 leaf). Cost: one T1 generalization, one T2 fibre lemma, one
  T2 dimension lemma, and the T4 proof rewired. The trade-off with B2's recommendation is noted there.

**7. Notes.** The leaf is honest: not vacuous, not stronger than BLR. Over a field, `[m]` étale needs flatness.
Over a field `K`, a *section* of an unramified morphism is an open immersion (kernel
`MulRigidity.isOpenImmersion_of_section`, Mul.lean). For (ii) only the kernel `A[m]` matters, and it is flat
for free.

---------------------------------------------------------------------------------------------------------------

## B2. `mumfordTorsionAlgClosed` (FREE)

**1. Identity.** `_root_.AvSplit.MumfordTorsionAlgClosed`, defined `ZInQKernel/OneProof/H/TailQ.lean:1257`. Row
H-102 (old H-25, H-38). Form: LEAF, published form (Mumford, *Abelian varieties* §4 App. 2 (iv), UNVERIFIED).
```lean
def MumfordTorsionAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    (g n : ℕ), topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : k) ≠ 0 →
      ∃ e : torsion A k n ≃ (Fin (2 * g) → ZMod n), ∀ x y h, e ⟨x.1 * y.1, h⟩ = e x + e y
```

**2. Use.** Four direct consumers. Every one goes through `AvSplit.torsionStructure_of_mumford` (T5 at `k = K̄`,
by base change), except h38:
* `AvSplit.Final.h25` (TailQ:2366) → `t5` (TailX:228) → `torsionStructure_ofK5` (TailO:2943) → T5 consumers in
  `gluePieces_of_open4` (TailK:291): `mobiusGlue_of_t5'`, `fibreCoverExists_of_propTSAll'`,
  `propTSAll_of_pieces3`, `kernelFieldExists_of_split''`, `conjTwistNontrivial_of_leaves`,
  `detTate_of_leaves4` (TailK:283), `modelG3G6_of_leaves3`, `linkedTateLocal_of_leaves3`,
  `periodMapGlue_of_leaves4` (TailK:73); `cmDescends_of6` and `heckeVertWitness_of_leaves5` (TailO:2964, TailN:44);
  and `tateModuleFree_of_t5'` (TailK:242) = T26 `PkgI3.TateModuleFree`, which is passed to many glue theorems
  as a hypothesis over all fields.
* `AvSplit.Final.h38` (TailQ:2371) → T35 (TailX:241, TailZ4:176). Inside it, `eq_dim_of_uniformization`
  (TailQ:1590) applies the leaf **only at `k = ℂ`, `n = 2`** to identify the uniformization's `g'` with `dim A`
  (VERIFIED-READ: `hT ℂ (ObjBridge.toGrp A) g 2 hg ...`).
* `raynaudCriterion_leaves` (TailZ14:241 → `raynaudCriterion_final` TailZ7:928) → r6 (TailZ15:98).
* `grothendieckMonodromy_final'` (TailZ7:1495) → r8 (TailZ9:105-106).
In r6/r8, T5 is used only for finiteness of `A(K̄)[m]` and divisibility (`exists_pow_eq`, TailZ7:66). The T5 use
sites, as read by t5-torsion §3 (docs/research/t5-torsion.md:228-245, a table of n and g per site): all
characteristic 0, at `ℚ̄`, subfields of `ℚ̄` or number fields, with `g = 2` and `n ∈ {3, 3^{2k}, ℓ^m, m}`. My
spot check of the frob chain (FrobTrace.lean:518, `tateCont_of_tateModuleFree hT` on `A` over `L'`) agrees:
there T26 is applied in characteristic 0 (SPECULATIVE for the other T26 pass-throughs).

Use (b) in substance, (a) formally (T5 and T26 are `∀ K`). Weakest sufficient:
```lean
-- all substantive uses: fields with an embedding in ℂ
def TorsionStructureC : Prop :=   -- = LF4T5.lean:458 (t5-torsion), VERIFIED-READ name
  ∀ (K : Type) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (σ : K →+* ℂ) (g n : ℕ),
    dim A = g → 0 < n → ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2*g) → ZMod n), (additive)
-- the h38 use: only the count at ℂ, n = 2
def Torsion2C : Prop := ∀ (A : AbVar ℂ) (g : ℕ), A.dim = g → Nat.card (torsion (toGrp A) ℂ 2) = 2 ^ (2*g)
```
These are a computation plus a published statement: `TorsionStructureC` is a kernel theorem from T35
(`T5Torsion.torsionStructureC_of_uniformization`, OneProof/H/LF4T5.lean:481, VERIFIED-READ). It is circular today
only because T35 itself uses `Torsion2C` to get `g' = dim A`.

**3. Library coverage** (all VERIFIED-READ by name/line in OneProof/H/LF4T5.lean, the t5-torsion work, already in the
chain's imports): `nonempty_torsionBy_addEquiv_pi` (:155, group theory from counts), `natCard_pow_eq_one` (:233,
torus counts), `natCard_torsion_eq_of_ext` (:365, char 0 descent of counts), `torsionStructure_numberField` (:1271),
`torsionStructure_subfieldQbar` (:1280), `tateModuleFree_of_torsionStructure` (:1213),
`T5Torsion.Degree.KernelDegree` (:1526, def), `natCard_torsion_of_degree` (:1541), `mulUnramified_charZero` (:1573),
`MulUnramifiedPosChar` (:1599, def), `torsionStructure_of_degree` (:1615). Kernel `ZInQ.Contrib.AbVarBC.mulIsogeny`
(Contrib/AbVarBC/Main.lean:27; `[n]` finite surjective in char 0). Mathlib `ZLattice` (Algebra/Module/ZLattice/).
Vendored CloudW07 (frenzymath Jacobian): `AlgebraicGeometry.Pic` (Jacobian/AlgebraicGeometry/Picard/Basic.lean:37,
VERIFIED-READ), coherent cohomology (`Cohomology/Finiteness.lean`, `Cohomology/Proper*`, file names only),
`Morphisms/FlatRank.lean`, `Morphisms/FiniteLocallyFree.lean` (names only). These are the ingredients any
algebraic proof of `deg [n] = n^{2g}` (theorem of the cube, Euler characteristics) would need. SPECULATIVE.

**4. Missing.** Full statement: (a) `MulUnramifiedPosChar` (the B1 4(a) generalization, T1); (b) `KernelDegree`,
`deg [n] = n^{2g}`. The latter needs line bundles, the theorem of the cube and `χ(f^*L) = deg f · χ(L)` (Mumford
§6, §8, §16), or ℓ-adic cohomology. Not in the tree. Restricted to ℂ-embeddable fields: nothing new beyond the
dimension identification `g' = dim A` (see B3).

**5. Tier.** Full: T3. Restricted (`TorsionStructureC`): T2. It is a rewiring once `uniformizationLeafAll` carries
`g = dim A`.

**6. Strategy: reduce.** (1) Restate `uniformizationLeafAll` with the conclusion `A.dim = g`. This is still the
printed Mumford §1, where `A(ℂ) ≅ ℂ^g/Λ` with `g = dim A`. Then T35 comes from the leaf alone. (2) Restate T5 and
T26 in the chain over ℂ-embeddable fields, and rewire the use sites with t5-torsion's drop-ins (`mobiusGlue_of_T35`,
`torsionCountPts_of_T35`, `torsionBound3_of_T35`, `QML3.goodReductionC`, `torsionStructure_numberField`). (3) r6/r8:
restate `RaynaudCriterion`/`GrothendieckMonodromy` over number fields (or `σ : K →+* ℂ`), or feed them
`TorsionStructureC`. Result: `mumfordTorsionAlgClosed` disappears. CONFLICT: B1's elimination route uses this
leaf at `κ(w)` (characteristic `p`). Pick one: keep Mumford (all characteristics) and drop `mulEtaleAbelianScheme`;
or keep a char-0-only chain, drop Mumford and prove (i) of B1 differently.

**7. Notes.** The leaf is honest (Mumford's own statement). t5-torsion's options (a)-(e) (doc §0) are still
valid; only (a) (T26 from T5) and (e) (drop `divisiblePoints`) were integrated.

---------------------------------------------------------------------------------------------------------------

## B3. `uniformizationLeafAll` (FREE)

**1. Identity.** `_root_.BPAnalytic.Uniformization.UniformizationLeafAll`, defined
`ZInQKernel/HDecomp/Analytic/Uniformization.lean:91`: `def UniformizationLeafAll : Prop := ∀ A : AbVar ℂ,
UniformizationLeaf A` (`UniformizationLeaf`, :86: `∃ g Λ, DiscreteTopology Λ ∧ IsZLattice ℝ Λ ∧ ∃ φ : Torus Λ ≃+
Additive (A.Pt ℂ), IsUniformization A Λ φ`, with holo / coords / open_map clauses). Row H-103. Form: LEAF,
published form (coordinate form) of Mumford §1 (bp-analytic §4).

**2. Use.** Two consumers:
* `AvSplit.Final.h38` (TailQ:2371; `mumfordUniformizationC_of` TailQ:1624, together with Mumford at ℂ, n=2)
  → T35 `ZInQ.LeafPush2.UniformizationExists` (HDecomp/LeafPush2/T.lean:33, `∀ K A σ g, A.dim = g → ∃ Λ Φ ...`)
  at TailX:241 and TailZ4:176 (`heightRows_of8` → `ZInQ.HeightGlue.heightRows_of_t35`, TailZ.lean:1498 →
  `heightGlue_of_t35` → `neronMetrizable_of_t35`: every abelian variety over a number field at every `τ`, in
  practice `A`, `J₁(N)_{L'}`, `A × Z`). T35's other consumers in TailK:291: `productMetrizationOfProductUnif_of_tangentDim`,
  `fibreQMPeriod_main_rep` (QM fibre surfaces over ℂ), `conjTwistNontrivial_of_leaves`,
  `serreRigidity3_of_T35_5` (TailN:52, over ℚ̄, dim 2).
* `AvSplit.Final.h69` (TailQ:2380, `homLatticeCorr_of_leaf_gaga`) → `homLatticeCorr` (TailX:233). The lifting
  half (AN3 at `ℂ` plus base change) is used by `conjTwistNontrivial_of_leaves` and `serreRigidity3` (`hC.1`,
  TailM:242). The realization half is used with GAGA (B4).

Use: (b) only weakly. The objects are base changes to ℂ of abelian varieties over number fields, of any dimension
(`J₁(N)`). Weakest sketch:
```lean
def UniformizationLeafNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A₀ : AbVar K) (σ : K →+* ℂ), UniformizationLeaf (A₀.baseChange σ)
```
Still deep: no simplification from the specialization. Recommended *strengthening* (still printed, Mumford §1):
add `A.dim = g` to the conclusion. This removes B2's `Torsion2C` use (see B2.6).

**3. Library coverage.** Mathlib: `ZLattice` (Algebra/Module/ZLattice/Basic.lean, Covolume.lean), real Lie groups
(Geometry/Manifold/Algebra/LieGroup.lean, GroupLieAlgebra.lean: `mulInvariantVectorField` :62), integral curves
(Geometry/Manifold/IntegralCurve/ExistUnique.lean:66 `exists_isMIntegralCurveAt_of_contMDiffAt`, UniformTime.lean).
Names VERIFIED-READ by grep. No exponential map, no complex-analytic structure on `A(ℂ)`, no GAGA.
Kernel: bp-analytic's torus theory (`BPAnalytic.Torus`, `IsUniformization.continuous_comparison`, Uniformization.lean
:96 onward, VERIFIED-READ), `BPAnalytic.exists_complexLinear_lift` (SPECULATIVE, not opened); glue
`UniformizationDim` (TailY:251, VERIFIED-READ: unproved glue saying `g = dim A`, which needs "the analytic topology
on 𝒢(ℂ)_τ and its manifold structure ... and invariance of domain").

**4. Missing.** (1) The complex manifold structure on `A(ℂ)` from smoothness (holomorphic implicit function
theorem on affine charts); (2) compactness of `A(ℂ)` (projective embedding: vendored
`exists_projective_immersion_of_algebraically_closed`, CloudW07 …/Group/QuasiProjective.lean, VERIFIED-READ,
private; then closed in `ℙ^N(ℂ)`); (3) connectedness of `A(ℂ)` in the analytic topology (irreducible ⇒ connected:
a hard theorem); (4) the exponential map of a commutative complex Lie group, surjective onto a connected group,
with discrete kernel of full rank by compactness.

**5. Tier.** T4 (research-scale formalization, roughly Mumford §1 plus the GAGA comparison for points).

**6. Strategy.** Keep cited, but restate with `g = dim A` (printed). If the dimension clause is judged
non-printed, prove `g' = dim A` from clause (ii) `coords` plus `TangentDimAtOrigin` (HDecomp/Faltings/HodgeLattice.lean:1152,
proved as `tangentDimAtOrigin_proved3`, TailI:68). The derivative of `φ` gives an injection `ℂ^{g'} → T₀A`, so
`g' ≤ dim A`. The reverse inequality needs a dimension argument (trdeg of the function field, or measure-zero
images). This is T2/T3 and removes B2's h38 dependence.

**7. Notes.** The leaf avoids analytification by quantifying over regular functions; it is "coordinate form" (a
judgement by bp-analytic/av-split, SPECULATIVE). Its three clauses are all used by `isStrongUnif_of_bp`
(TailQ:837).

---------------------------------------------------------------------------------------------------------------

## B4. `gagaMorphism` (FREE)

**1. Identity.** `_root_.ZInQ.HomLattice.GAGAMorphism`, defined `ZInQKernel/OneProof/H/TailQ.lean:875`. Row H-105.
Form: LEAF, published form (coordinate form) of Serre GAGA for homomorphisms (homlattice §3.2).
```lean
def GAGAMorphism : Prop :=
  ∀ (A B : AbVar ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (φ : BPAnalytic.Torus Λ ≃+ Additive (CPts A (RingHom.id ℂ))), IsStrongUnif A (RingHom.id ℂ) Λ φ →
    ∀ ψ : (Fin g → ℂ) → CPts B (RingHom.id ℂ), IsAnalyticHom (RingHom.id ℂ) ψ → (∀ z ∈ Λ, ψ z = 1) →
      ∃ f : A.X ⟶ B.X, ∀ z, ψ z = Additive.toMul (φ (BPAnalytic.proj Λ z)) ≫ f
```

**2. Use.** Only `AvSplit.Final.h69` (TailQ:2380) → `HomUnify.HomLatticeCorr` (Contrib/HomUnify/Corr.lean:84,
VERIFIED-READ). GAGA feeds only the realization half `.2` (over ℂ, `σ = id`). Consumers of `.2`:
`t11aRiemannHom_of_corr4` (TailK:63) → `periodMapGlue_of_leaves4` (TailK:73: `qmTwistLattice_of'`,
`cmFixedHasCM_of`), on the QM fibre surfaces of `ownY`; `HomUnify.t11a_riemannEnd_of_corr` (Corr.lean:109) →
`t11a` in `textbookLeaves2_of_open3` → `fibreQMPeriod_main_rep` (QM fibre) and `G0Galois.g8_g12`/`g8_g11`
(TailD:138,172: `A_ℂ` of the G7 model, dim 2). `serreRigidity3` uses only `.1` (TailM:242, VERIFIED-READ).

Use (b): all uses are at complex abelian **surfaces** (`A.dim = B.dim = 2`, with QM by `𝒪`). Weakest:
```lean
def GAGAMorphism2 : Prop :=
  ∀ (A B : AbVar ℂ), A.dim = 2 → B.dim = 2 → ∀ (Λ : Submodule ℤ (Fin 2 → ℂ)) [DiscreteTopology Λ] (φ ...),
    IsStrongUnif A (RingHom.id ℂ) Λ φ → ∀ ψ, IsAnalyticHom (RingHom.id ℂ) ψ → (∀ z ∈ Λ, ψ z = 1) →
      ∃ f : A.X ⟶ B.X, ∀ z, ψ z = Additive.toMul (φ (proj Λ z)) ≫ f
```
This requires `homLatticeCorr`'s realization clause and `T11a`/`T11aRiemannHom` to carry `dim = 2` (they are
only used at dim 2). Still deep.

**3. Library coverage.** None in Mathlib (no analytic spaces, no Chow theorem; grep negative, SPECULATIVE).
Kernel: homlattice's reduction `analyticMapAlgebraic_of_gaga'` (TailQ:886, VERIFIED-READ),
`exists_complexLinear_of_analytic_strong` (used there), rigidity (`G0FibreSimple.rigidityHom`). Vendored CloudW07:
projective immersion of abelian varieties (above), which a Chow-theorem route would need.

**4. Missing.** Chow's theorem (closed analytic subsets of `ℙ^N(ℂ)` are algebraic) or analytic coherent
sheaves. A torsion-point/Zariski-closure route: `Γ_ψ` is a compact subtorus; the Zariski closure `Z` of
`{(x, ψx) : x ∈ A_tors}` is an algebraic subgroup. One must show `Z ∩ (0 × B)` is finite, which needs an analytic
input. Also the analytic structure of `A(ℂ)` from B3.

**5. Tier.** T3–T4.

**6. Strategy.** Keep cited. Optionally restate at dim 2 to document the real need. No cheaper route is known.
Realizing CM endomorphisms (`cmFixedHasCM_of`) needs GAGA in substance; the QM action itself is already
algebraic in the family.

**7. Notes.** No vacuity risk: `IsStrongUnif` is implied by bp-analytic's `IsUniformization`
(`isStrongUnif_of_bp`, TailQ:837).

---------------------------------------------------------------------------------------------------------------

## B5. `t09SymmIsogenyExists` (FREE)

**1. Identity.** `WeilPairing.T09_SymmIsogenyExists` (namespace `HDec.HSyn.WeilPairing`), defined
`ZInQKernel/OneProof/H/TailB.lean:3752`: `def T09_SymmIsogenyExists : Prop := ∀ (K : Type) [Field K] (A : AbVar K),
Nonempty (SymmIsogeny A)`. `SymmIsogeny` (TailB:3660) consists of `D : WeilDual A`, `lam : Hom A D.dual`, isogeny,
`IsSymmetric`. `WeilDual` (TailB:3595) consists of an AbVar `dual`, pairings `e n`, perfect, Galois-equivariant,
compatible, and `dualEnd`. Row H-53. Form: GLUE (c), consequence of one theorem (Mumford §§6, 8, 20, 23;
existential in `D`).

**2. Use.** Field of `OpenAddedLeaves9` (TailZ13:24), passed to 8/7/6 (TailX:264, TailO:2988). Consumers:
* `detTate_of_leaves4` (TailK:283) via `tatePairingZl_of_leaves4` (TailK:256). It takes `S := h9 K A`, applies
  `IsogenyQuasiInverse` to `S.lam`, and T5 for surjectivity of `T_ℓ → A[ℓᵏ]`; with T26 it gives `G0Galois.DetTate`
  (TailA:2364: `∀ K [NumberField K] A ℓ g, A.dim = g → det (tate A ℓ σ) = cycQ ℓ (resQ K σ) ^ g`). Its only use:
  `g12Det_of` (TailA:2419), **at `ℓ = 5`, `g = 2`** (VERIFIED-READ L2475: `hDT K A 5 2 hdim σ`), with `A` the
  G7 model over a number field `K`, Galois over ℚ.
* `t9_of_leaves5` (TailN:47) → `t9 : LeafPush.T09_WeilPairing` (TailB:3806) → `g8_g12`/`g12` (TailA:2183,2233) →
  passed into `G12Det` (TailA:2050, a hypothesis of the def). But `g12Det_of` discards it (`intro _ _ K ...`,
  TailA:2421). So this use is **formal only**.

Use (b). Weakest sufficient (together with milne and T5, which feed the same path):
```lean
def TatePairingZl5 : Prop :=   -- TatePairingZl (TailB:4777) at ℓ = 5, dim 2
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = 2 →
    ∃ B : LinearMap.BilinForm ℤ_[5] (A.T 5), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      ∀ σ x y, B (A.galT σ x) (A.galT σ y) = (cyclotomicCharacter (AlgebraicClosure K) 5 σ.toRingEquiv) * B x y
-- or directly
def DetTate52 : Prop := ∀ (K) [Field K] [NumberField K] [IsGalois ℚ K] (A : PkgI3.AbVar K), A.dim = 2 →
    ∀ σ, LinearMap.det (tate A 5 σ) = (cycQ 5 (resQ K σ) : PadicAlgCl 5) ^ 2
```
`DetTate52` is implied by Mumford §20/§23 and is still deep. Removing the formal `t9` use needs `G12Det`'s statement
(a def in TailA) changed to drop `LeafPush.T09_WeilPairing →`.

**3. Library coverage.** Mathlib: no line bundles or Picard functor on schemes (av-split §4.1, VERIFIED by grep
there). **Vendored CloudW07 (frenzymath Jacobian-Challenge) changes this.** It has
`AlgebraicGeometry.Pic` (…/Jacobian/AlgebraicGeometry/Picard/Basic.lean:37, "Isomorphism classes of invertible module
sheaves", VERIFIED-READ), the Picard functor and `exists_abelianVariety_picardDegreeZero`
(…/Picard/FieldDescent.lean:260, VERIFIED-READ: `Pic⁰` of a smooth proper geometrically integral **curve** is
represented by an abelian variety), coherent cohomology (…/Cohomology/*), Chow's lemma (…/ChowLemma/*), and
projective immersion of smooth group schemes (…/Group/QuasiProjective.lean). Kernel: `WeilPairing.tatePairing*`,
`detTate_of_zl` (TailB:4860), `detTate_of_darboux` (TailB:4599), `tateGSp_of_zl`; Chebotarev `FrobeniusDense`
(T18 proved). No Weil pairing for any abelian variety.

**4. Missing (route via `Â`).** (1) `Pic⁰_{A/K}` represented by an abelian variety `Â`: generalize the vendored
curve case to abelian varieties (Mumford §8 or Grothendieck; needs the theorem of the square/cube, seesaw,
cohomology and base change). (2) The Poincaré bundle and `ē_n : A[n] × Â[n] → μ_n`: perfect, Galois-equivariant,
compatible (Mumford §20). (3) `φ_L` for `L` ample (projective immersion exists) is an isogeny, and `e^L` is
alternating (§23). (4) `dualEnd` (`f ↦ f^∨`).
*Alternative route for DetTate52 only (no duals):* `det ρ_5(Frob_p) = deg(Frob_{Ā}) = p²` at good primes
(reduction compatibility exists: `FrobTrace.AlgFrobRed`), then Chebotarev. Needs Mumford §19 Thm 4 **with** degree,
`det T_ℓ(φ) = deg φ` (the in-flight `charPolyIndepOfEllAlgClosed` is the weakened form *without* the degree), and
`deg Frob = q^g`. Both need degree theory (as in B2.4), so this route is also T3.

**5. Tier.** T3.

**6. Strategy.** Reduce to printed statements: `PicZeroAbVarRepresentable` (Mumford §8 Thm 1, or Milne 1986 Thm
10.1), `WeilPairingPoincare` (§20), `AmpleSymmetric` (§23), stated over the vendored `Pic`. The glue to
`SymmIsogeny` is then project work (T2). Alternatively keep cited, restated as `DetTate52` or `TatePairingZl5`,
which documents that only `ℓ = 5`, dim 2 is used.

**7. Notes.** Branch `origin/wip/t09-pic` = `b5ff0474` = `origin/wip/w63` = `origin/wip/integrate-w63` (same
SHA). It has no commits of its own, and its `.fleet/` has only `genus-fold.md` and `route-a-fold.md`. So it is
an empty branch created at w63 for this row (by name: Pic route). w63's leaf-fold11 §5 lists
`t09SymmIsogenyExists` among the strict GLUE rows queued for "c-to-printed2". Vacuity: `WeilDual` is existential;
the non-vacuity check is at TailB:3769 ("satisfiable at `A = 0`"). The only witness is `Â` (av-split §4.1): `D = A`
would need a principal polarization.

---------------------------------------------------------------------------------------------------------------

## B6. `milneIsogenyQuasiInverse` (FREE)

**1. Identity.** `_root_.AvSplit.MilneIsogenyQuasiInverse`, defined `ZInQKernel/OneProof/H/TailQ.lean:1207`. Row
H-104 (old H-54). Form: LEAF, published form (weakened): Milne 1986 Rem. 8.4; Mumford §7 (UNVERIFIED).
```lean
def MilneIsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A,
      f.hom ≫ g.hom = (((d : ℤ) : End A)).hom ∧ g.hom ≫ f.hom = (((d : ℤ) : End B)).hom
```

**2. Use.** Field of `OpenAddedLeaves9` (TailZ13:25). Converted by `AvSplit.Final.h54` (TailQ:2376) into
`WeilPairing.IsogenyQuasiInverse` (TailB, points form) at TailX:265 (`isogenyQuasiInverse_lf7`) and into av-glue's
copy at TailX:232 (`isogenyQuasiInverseAG_lf7`). Consumers:
* T8: `AVGlue.poincareReducibility_of_published'` (TailX:231, TailP:1245ff, `simpleSurjIsogeny_of_leaves'`
  TailP:654). It is applied to `φ : C × Z → A` over `k` with `[CharZero k]` (`PkgI3.PoincareReducibility`,
  HDecomp/Objects.lean:465, has `[CharZero k]`). T8's only use is TailD:226, with `f : A → J₁(N)_{L'}` and `A` the
  QM fibre surface over a number field.
* DetTate: `tatePairingZl_of_leaves4` (TailK:256), applied to `S.lam : A → D.dual` over a number field (used only
  at `ℓ = 5`, dim 2; see B5).
* `t9_of_leaves5` (TailN:47): formal only (see B5).

Use (b): characteristic 0 only. Weakest sufficient:
```lean
def MilneIsogenyQuasiInverse0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d, 0 < d ∧ ∃ g : Hom B A, f.hom ≫ g.hom = ((d:ℤ) : End A).hom ∧ g.hom ≫ f.hom = ((d:ℤ) : End B).hom
```
This needs `WeilPairing.IsogenyQuasiInverse` and its av-glue copy restated with `[CharZero K]` (their consumers are
char 0), and the formal `t9` use removed (B5).

**3. Library coverage.**
* scratch/coarse-factor/Factor.lean:825/834, VERIFIED-READ: `FactorThroughSurj` and `theorem factorThroughSurj`. If
  `f : Y → X` is surjective on ℚ̄-points and `f'` is constant on its ℚ̄-fibres, then `f' = f ≫ h`. Proved for
  proper smooth **curves over ℚ** by the graph / scheme-theoretic-image / finite-bijective-onto-normal route. This is
  exactly the factorization this leaf needs, in dimension 1.
* Mathlib `AlgebraicGeometry/ZariskisMainTheorem.lean` (file exists); `EffectiveEpi.lean:50`
  `effectiveEpi_base_of_flat` (topological only) and `:120 isRegularEpi_of_flat_of_surjective_of_isAffine`
  (affine only), names VERIFIED-READ.
* Kernel: `mulIsogeny` (`[n]` finite surjective, char 0); `G0FibreSimple.rigidityHom` (pointed ⇒ homomorphism);
  AbVar hom ext on points (`ext_of_isDominant_of_isSeparated`, used in Contrib/FrobChain/FExtend.lean ~L270);
  av-glue's image/kernel AbVar recipes. The in-flight `cartierSmooth` (char 0 group schemes are smooth) would make
  `ker f` étale. Mathlib `AlgebraicGeometry/Group/Smooth.lean:63`, VERIFIED-READ: `lemma smooth_of_grpObj
  [GeometricallyReduced f] : Smooth f`.

**4. Missing (char 0 route).** (1) `ker f(K̄)` finite (f finite) with `d := #ker f(K̄)`. Then Lagrange gives
`[d] y = [d] y'` whenever `f y = f y'` (pure algebra on points). (2) Generalize `FactorThroughSurj` from curves over ℚ
to abelian varieties over a char 0 field `K`: the image `Γ ⊆ B × A` of `(f, [d])`, `Γ → B` finite and bijective on
`K̄`-points, birational in char 0 (generic-fibre count = separable degree), `B` normal, ZMT ⇒ iso; `g := pr₂ ∘ (Γ ≅ B)⁻¹`.
(3) `g` is a homomorphism (rigidity), and `g ≫ f = [d]` because `f ≫ (g ≫ f) = f ≫ [d]` and `f` is dominant
(cancel). The hard step is (2) in dimension `> 1`: the birationality/degree argument and ZMT for finite birational
morphisms onto normal varieties.

**5. Tier.** T2 (one bounded new piece: higher-dimensional `FactorThroughSurj`, char 0).

**6. Strategy.** Prove directly in char 0 (restate the two `IsogenyQuasiInverse` copies with `[CharZero K]`).
Reuse coarse-factor's proof skeleton.

**7. Notes.** The leaf weakens Milne (no degree, `g` not asserted an isogeny), so it is safe. `IsIsogenyMor` =
monoid hom + finite + surjective.

---------------------------------------------------------------------------------------------------------------

## In-flight / done (status recorded; items 3-6 brief)

### C1. `homFreeFiniteAlgClosed`: IN FLIGHT (cloud)
1. `_root_.ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed`, `ZInQKernel/Contrib/AVB1/AlgClosed.lean:38`; H-70; LEAF,
   published form (Mumford §19 Thm 3 over k̄; Milne 1986 Thm 12.5).
2. `t6_of_algClosed5` (TailM:324) → T6 `PkgI3.HomFreeFinite` (TailO:2944). Used by
   `FS5NoCM.fibreComTrivialFull_of_leaves''` (TailK:299), `kernelFieldExists_of_split''` (TailK:325),
   `qmEndRank_of_leaves3` inside `linkedTateLocal_of_leaves3` (TailI:99), and `g8_g12` (TailD:138). All at the QM
   surface / G7 model over number fields (rank of End, char 0). Use (b): char 0, dim 2.
3-6. Needs Tate modules plus degree theory in general (T3); keep with the cloud worker.

### C2. `charPolyIndepOfEllAlgClosed`: IN FLIGHT (cloud)
1. `_root_.ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed`, AlgClosed.lean:51; H-71; LEAF, specialization of
   Mumford §19 Thm 4 (without `deg P = 2g` and `P(n) = deg(n − φ)`).
2. `t7_of_algClosed5` (TailM:329) → T7 → `G0AssembleMod.linkedTateData_of_local t.t7` (TailK:342): Frobenius
   char polys on the G7 model at `ℓ = 5, 3`. Use (b).
3-6. T3 (degree theory). Keep with the worker. Note B5.4: the version *with* degree would also give DetTate.

### C3. `poincareComplement`: IN FLIGHT (cloud)
1. `_root_.ZInQ.Contrib.AVB1.PoincareComplement`, `ZInQKernel/Contrib/AVB1/Poincare.lean:42`; H-72; LEAF, Milne 1986
   Prop. 12.1, weakened.
2. With `cartierSmooth`, `geomConnOfRationalPoint`, `groupSchemeEquidim` and B6:
   `AVGlue.poincareReducibility_of_published'` (TailX:231) → T8 (char 0), used once at TailD:226
   (`f : A → J₁(N)_{L'}`, `A` the QM fibre surface). Use (b).
3-6. T3 (needs polarizations or complements via line bundles). Cloud.

### C4. `cartierSmooth`: IN FLIGHT (cloud)
1. `_root_.AVGlue.CartierSmooth`, `ZInQKernel/OneProof/H/TailP.lean:305`; H-98; LEAF, published (Cartier; Mumford §11
   Thm 1; Stacks 047N).
2. Only T8 (as C3) via `poincareReducibility_of_published'`. Use (b): char 0 group schemes arising in T8's proof
   (images/kernels of homomorphisms of abelian varieties).
3. Mathlib `AlgebraicGeometry/Group/Smooth.lean:63` `smooth_of_grpObj [GeometricallyReduced f] : Smooth f`
   (VERIFIED-READ) reduces Cartier to "char 0 group schemes of finite type are (geometrically) reduced".
4-6. T2 given the Mathlib lemma (reducedness in char 0 is the content). Cloud.

### C5. `geomConnOfRationalPoint`: IN FLIGHT (cloud)
1. `_root_.AVGlue.GeomConnOfRationalPoint`, TailP.lean:910; H-99; LEAF (specialization of Stacks 04KV).
2. Only T8 (as C3). 3-6. Mathlib has `AlgebraicGeometry/Geometrically/Connected.lean` (file exists); memory
   notes record a "descend from k̄" recipe. T2. Cloud.

### C6. `groupSchemeEquidim`: IN FLIGHT (cloud)
1. `_root_.AVGlue.GroupSchemeEquidim`, TailP.lean:921; H-100; LEAF (Stacks; SGA 3 VI_A 2.4, finite type).
2. Only T8 (as C3). 3-6. Translation argument plus dimension theory. T2. Cloud.

### C7. `egaIV_8_10_5_xii`: IN FLIGHT (cloud)
1. `_root_.ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii`, `ZInQKernel/Contrib/SpreadOut/Spread.lean:49`; H-65; LEAF, EGA IV₃
   8.10.5 (xii) (descent of properness).
2. `abVarSpreadsOut_of_ega4` with W01's proofs of 8.8.2(ii), 17.7.8(ii). Used at TailK:344 (→
   `linkedTateLocal_of_leaves3`, good reduction of the G7 model) and TailZ15:88 (`semistableAlmostAll_of10` →
   `semistableReductionThm`). Use (b): abelian varieties over number fields spread out over `𝓞_L[1/N]`.
3-6. Mathlib `AlgebraicGeometry/AffineTransitionLimit.lean` (EGA IV 8.8.2, per memory notes); W01 vendored
   Stacks. T2. Cloud.

### C8. `genusX1Field`: DONE on w63 (genus-fold). Confirmed.
1. `_root_.ZInQ.Contrib.CurvesG.GenusX1Field`, `ZInQKernel/Contrib/CurvesG/GenusSplit.lean:59`; H-79; GLUE (comp),
   composite of Shimura 1971 §6.7, Prop. 6.9, Prop. 1.40.
2. At base: `t34_of_split5` (TailM:365) → T34 → TailD:231,245 (`dim J₁(N) ≤ N²`, Javanpeykar on `J₁(N)`).
   **Confirmed removed on w63**: `git show origin/wip/w63:ZInQKernel/OneProof/H/TailZ11.lean` has no
   `genusX1Field` in `OpenTextbookLeaves10` (15 fields). It survives only in the dead old bundle TailN:161 and as
   `genusX1Le_of_genusX1Field` (OneProof/Genus/GenusBound.lean:494). `docs/research/genus-fold.md` (w63): TailD's two
   `t.t34` uses were replaced by the proved `t34Le` (genus-route's `dimJ1Le`), and `t34`/`genusX1Field` were pruned
   from every generation (commits 98a02e43, c6ec1ef9). frozenTarget builds, standard axioms (as reported there).
3-6. n/a.

### C9. `regularSmoothPerfect`: IN FLIGHT (cloud)
1. `_root_.CurveSplit.RegularSmoothPerfect`, `ZInQKernel/OneProof/H/TailR.lean:1471`; H-118; LEAF (Stacks 00TV,
   ⇐ half).
2. `CurveSplit.normalCurveSmoothQ_of_regularSmooth` (TailX:243) → `normalCurveSmoothQ` → `t38_of_split5`
   (TailM:349) → T38 `X1Belyi.CurveOfFunctionFieldQ` → the X1/Belyi model of `X₁(N)` (LPrefix:11742-11758). Use
   (b): curves over ℚ (perfect field, dim 1).
3-6. Over a perfect field, regular ⇒ geometrically regular ⇒ smooth. CloudW03 vendored has regular-local-ring and
   smooth-stalk lemmas (`S_Algebra_Smooth_isDomain…`, `Def_Mathlib_RingTheory_SmoothAlgebraOverFieldRegularStalks`;
   the converse direction). T2. Cloud.

### C10. `igusaGL2`: IN FLIGHT via `X0Transitive` (cloud; a proof drops this field)
1. `_root_.ZInQ.RLeaf.IgusaGL2`, `ZInQKernel/Contrib/RLeaf/IgusaSL2.lean:120`; H-117; LEAF (Igusa 1959; Lang,
   *Elliptic functions* Ch. 6 §3).
2. `CurveSplit.x0Transitive_of_igusaGL2` (TailX:246) → `x0Transitive` → `t40_of_x0Transitive4` (TailK:150 →
   `ZInQ.RLeaf.x1RationalCusp_of_x0Transitive`) → T40 `X1Belyi.X1RationalCusp`. Use (b): only transitivity on
   `X₀`-data needed. The cloud worker targets `X0Transitive` directly, which removes `igusaGL2`.
3-6. T2-T3 (Galois image of the generic elliptic curve). Cloud.

---------------------------------------------------------------------------------------------------------------

## Summary

| field | consumers (first applying decl.) | use (a/b) | tier | strategy | best attack idea |
|---|---|---|---|---|---|
| mulEtaleAbelianScheme | `h24`/`reductionTorsionBijective_of_mulEtale` (TailQ:2349) → T4 → `linkedTateLocal_of_leaves3`/AlgFrobRed; `fixedTorsionRationalImperfect_of_mulEtale` (TailZ14:236) → r6 | b (DVRs of number fields, `m = ℓⁿ`; imperfect-field use vacuous) | T3 as stated; T2 to eliminate | reduce/eliminate | Generalize AbVarBC `eq_one_of_comp_intCast` from `CharZero` to `(n:K)≠0` (T1). That gives r6's piece. Get T4 from unramified `[m]` over `O` (fibre lemma) plus counting with Mumford at `K̄` and `κ(w)`. Drop the leaf. |
| mumfordTorsionAlgClosed | `h25` (T5, T26 and ~12 sites), `h38` (ℂ, n=2), `raynaudCriterion_final`, `grothendieckMonodromy_final'` | b in substance (char 0, ℂ-embeddable, g=2 mostly); a formally | T3 full; T2 restricted | reduce | Put `dim A = g` into `uniformizationLeafAll` (printed). Then T5 over ℂ-embeddable fields is already a kernel theorem (`torsionStructureC_of_uniformization`). Restate T5/T26/r6/r8 over ℂ-embeddable fields and drop the leaf. Conflicts with row 1's route. |
| uniformizationLeafAll | `h38` (T35: heights, period map, conj-twist, Serre rigidity), `h69` (HomLatticeCorr) | b weakly (base changes from number fields; any dim incl. `J₁(N)`) | T4 | keep cited (strengthen with `g = dim A`) | The `g = dim A` clause removes Mumford's h38 use; otherwise prove `g' = dim A` from `coords` + `TangentDimAtOrigin`. |
| gagaMorphism | `h69` → `HomLatticeCorr.2` → `T11aRiemannHom` (period map), `T11a_RiemannEnd` (QM period, `g8_g12`) | b (complex abelian surfaces with QM) | T3–T4 | keep cited (restate dim 2) | No cheap route; the dim-2 restatement documents the need. |
| t09SymmIsogenyExists | `tatePairingZl_of_leaves4` → `detTate_of_leaves4` → `g12Det_of` (ℓ=5, g=2); `t9_of_leaves5` (formal only, discarded in `g12Det_of`) | b (ℓ = 5, dim 2, G7 model over a number field) | T3 | reduce to printed Pic⁰/Weil-pairing leaves over vendored `Pic`; or keep cited as `DetTate52` | Build `Pic⁰_A` on the vendored frenzymath Picard/cohomology library (it already represents `Pic⁰` of curves). `origin/wip/t09-pic` is empty (= w63 head). |
| milneIsogenyQuasiInverse | `h54` → `IsogenyQuasiInverse` → T8 (char 0, `A → J₁(N)`), `tatePairingZl_of_leaves4`; `t9_of_leaves5` (formal) | b (char 0 only) | T2 | prove directly (char 0 restatement) | Generalize coarse-factor's `factorThroughSurj` (graph image, finite bijective onto normal, ZMT) from curves/ℚ to abelian varieties in char 0; apply with `f' = [#ker f(K̄)]`. |
| homFreeFiniteAlgClosed | `t6_of_algClosed5` → T6 | b | T3 | in flight (cloud) | n/a |
| charPolyIndepOfEllAlgClosed | `t7_of_algClosed5` → T7 → `linkedTateData_of_local` | b | T3 | in flight (cloud) | n/a |
| poincareComplement | `poincareReducibility_of_published'` → T8 | b | T3 | in flight (cloud) | n/a |
| cartierSmooth | same → T8 | b | T2 | in flight (cloud) | Mathlib `smooth_of_grpObj` (geom. reduced ⇒ smooth) |
| geomConnOfRationalPoint | same → T8 | b | T2 | in flight (cloud) | n/a |
| groupSchemeEquidim | same → T8 | b | T2 | in flight (cloud) | n/a |
| egaIV_8_10_5_xii | `abVarSpreadsOut_of_ega4` → linkedTateLocal, SS1 | b | T2 | in flight (cloud) | n/a |
| genusX1Field | `t34_of_split5` → T34 | b | n/a | DONE on w63 (genus-fold) | confirmed absent from w63 `OpenTextbookLeaves10` |
| regularSmoothPerfect | `normalCurveSmoothQ_of_regularSmooth` → T38 | b (curves/ℚ) | T2 | in flight (cloud) | n/a |
| igusaGL2 | `x0Transitive_of_igusaGL2` → T40 | b | T2–T3 | in flight (`X0Transitive`, cloud) | a proof of `X0Transitive` drops the field |
