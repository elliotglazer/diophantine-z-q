# agent-EF: groups E (p-adic Hodge theory) and F (Galois representations of modular forms)

Base e38375b3. Read-only text analysis: no Lean was run. Marks: VERIFIED-READ means I opened the file and quote the line.
SPECULATIVE means a judgement. UNVERIFIED means a theorem number from memory.

## 0. The common consumer: what these statements do in the proof

All eleven fields reach the proof through **one consumer**, the modularity range G8–G16. Its entry point is
`HDec.HSyn.G0AssembleMod.afterG7_of3` (ZInQKernel/OneProof/H/TailD.lean:156). The live chain from
`sixContactMin_of_open12` reaches it through leaf-fold6/open4. In detail: `sixContactMin_of_open6` (TailO.lean:3011)
calls `sixContactMin_of_open4` (TailK.lean:356), which calls `gluePieces_of_open4` (TailK.lean:291). Its field
`modularConstituent` is `afterG7_of3 r3 t3 ⟨burnside, r.r14, g9Glue_of_deRhamComparisonHT r.r10, g10…,
g12Weight_of_senTwist l.senTwist l.finiteImageHT, detTate…, resQFiniteIndex⟩ … r.r17 …` (TailK.lean:328-338).
`glueOutputs_of_leaves3` (TailD.lean:200) uses none of r10–r17 or t23 directly.

What the range proves (TailA.lean:1920-2250, 3456-3740). The objects:
- `P : QML3 Qbar` is a QM abelian surface of the construction (discriminant 6, level-3 structure) lying over a
  rational parameter `u`.
- `A : PkgI3.AbVar L` is its model over a Galois number field `L ⊆ L'`.
- **Infinitely many objects, one per `u`; two fixed primes, ℓ = 5 and ℓ = 3.**

The steps:
- **G8.** From G7's descent data, a 2-dimensional `r₅ : GaloisRep 5 2` with `ℚ̄₅ ⊗ V₅(A) ≅ r₅|G_{L'} ⊕ r₅|G_{L'}`, and
  the same `r₃` at ℓ = 3.
- **G9.** `r₅|G_{ℚ₅}` is de Rham with HT weights `{0, −1}` (`G9Out`).
- **G10.** `r₅` is odd.
- **G11.** `r₅` is finitely ramified.
- **G12** (`g12`, TailA.lean:2183). Pan∘Berger (`r11r12`) at p = 5 gives an eigenform `g` of some weight `k ≥ 1` and a
  twist `ψ` with `r₅ ≈ ρ_g ⊗ ψ`. Then `G12Weight` forces `k = 2`. It uses three inputs:
  - R14 (`ρ_g` exists);
  - R13 (`ρ_g` has HT weights `{0, 1−k}`);
  - SenTwist, and, for `k = 1`, Deligne–Serre with FiniteImageHT.

  Next `G12Det` (R14Det's determinant together with T9) makes `ψ` of finite order.
- **G13** (`g13`, TailA.lean:3456). Twist and newform bookkeeping gives a weight-2 newform `f` of level `N`. R16 at ℓ = 5
  (`commonConstituent_of_attached`, TailA.lean:3418) gives a common constituent of `V₅(A)` and `V₅(J₁(N)_{L'})`.
- **G14** (`g14`, TailA.lean:3511). R14 at ℓ = 5 and 3, weight 2.
- **G15** (`g15`, TailA.lean:3551). Carayol `r17` with ℓ = 5 for `p ≠ 5` and ℓ = 3 for `p = 5` bounds `v_p(N)`, so
  `N ≤ Q_D·M²` (G16).

The output feeds `glueOutputs_of_leaves3`:
- a nonzero hom `A → J₁(N)_{L'}` (`hom_of_common3`);
- Poincaré;
- Javanpeykar's height bound for `J₁(N)` (TailD.lean:200-252).

**Role.** The p-adic Hodge and modular-form inputs **do not rule out a case**. They prove the **modularity, with
controlled level, of the 2-dimensional Galois representation carried by each QM abelian surface of the construction**.
That modularity bounds the surface's Faltings height by that of `J₁(N)`. The Hodge–Tate weights enter at two places:
- Pan's hypotheses: de Rham, and distinct weights.
- The weight comparison that pins the eigenform's weight to `k = 2`, which G13 needs (Eichler–Shimura is in weight 2).

Two observations hold for all fields below:
- (i) **Every p-adic Hodge use is at p = 5 only.** At ℓ = 3 the range calls `g8_g11`, but discards G9 and G10:
  `obtain ⟨r₃, h8₃, -, -, h11₃⟩` (TailD.lean:171). The ℓ = 3 instances of R10/T23 are therefore dead. Dropping them needs
  a copy of `g8_g11` without G9 and G10 at ℓ = 3 (T1).
- (ii) **`T23` (hence `bdRInvariants`) is semantically unused.** It enters only as the second argument of
  `G0Galois.G9Glue` (TailA.lean:1989: `PkgI4.DeRhamComparison → (∀ p, T23_FontaineClosure p) → …`). The only `G9Glue`
  proof on the chain is `g9Glue_of_deRhamComparisonHT → g9Glue_of_HT → g9Glue_of_abVarBaseChange →
  g9Glue_of_localModel → g9Glue_of_fieldEmb`. It ignores that argument: `intro hR10 _hT23 K _ _ A ℓ _ r e hdim hint`
  (VERIFIED-READ, ZInQKernel/Contrib/G9/Reduction.lean:130). There is one more `.t23` use, at TailD.lean:138 and 172;
  both pass it into the same slot. PruneScan reports no unused fields because the use is syntactic.

---

## E1. `tateTwistInvariants` (IN FLIGHT, cloud workers)

1. **Identity.** Field `tateTwistInvariants : _root_.ZInQ.Contrib.HodgeSplit.TateTwistInvariants`, OpenAddedLeaves9
   (TailZ13.lean:22). Defined at ZInQKernel/OneProof/H/TailS.lean:69:
   `∀ p [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (i : ℤ), i ≠ 0 →
   ∀ x : ℂ_[p], (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • cpAct p σ x = x) → x = 0`.
   Frontier H-120. LEAF, published form (Tate 1967 §3.3 Thm 2).
2. **Use.** TailX.lean:208, 261, 263 feed it, with `axSenTate`, into three derived statements:
   - `r10` (`deRhamComparisonHT_of_leavesT`), the HT-weight clause of R10;
   - `senTwist` (`senTwist_of_tate`);
   - `finiteImageHT` (`finiteImageHT_of_tate`).

   These are consumed in `afterG7_of3`, as follows:
   - `G9Glue` uses the R10 weights at ℓ (only ℓ = 5 is live, by (i)).
   - `G12Weight` (`g12Weight_of`, TailB.lean:4998ff) calls `hSen 5 2 …` and `hFI 5 2 ρ hfin` at p = 5 only.

   In those three uses `K` is a finite extension of ℚ₅ produced by the representation. On c-to-printed2 the statement is
   also used for `HTDual` (eigenformHTNew), again at ℓ = 5. **Case (b): p = 5 only.**
   Weakest form: `TateTwistInvariants5 := ∀ K : IntermediateField ℚ_[5] (PadicAlgCl 5) [FiniteDimensional …] (i ≠ 0)
   x, (∀ σ ∈ K.fixingSubgroup, cycPow 5 σ i • cpAct 5 σ x = x) → x = 0`. This is no easier than the general case.
3. **Library.** VERIFIED-READ, Mathlib:
   - `abbrev PadicComplex := UniformSpace.Completion (PadicAlgCl p)` and `notation "ℂ_[" p "]"`
     (.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:137,140);
   - Krasner's lemma file .lake/packages/mathlib/Mathlib/Analysis/Normed/Field/Krasner.lean (exists; statement not read);
   - continuous group cohomology dir `Mathlib/RepresentationTheory/Homological/ContCohomology/` (LowDegree.lean etc.;
     statements not read).

   VERIFIED-READ, tree:
   - `def cpAct (σ : GQp p) : ℂ_[p] →+* ℂ_[p]` (ZInQKernel/Contrib/G9/I4Layer.lean:830);
   - `def cyc (σ : GQp p) : ℤ_[p]ˣ := cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv` (I4Layer.lean:844).
4. **Missing.** Tate's normalized trace on the cyclotomic `ℤ_p`-extension, and almost-étale ramification estimates of
   `K_∞/K`. Alternative: Ax's lemma, then Sen's theorem. In flight.
5. **Tier.** T2–T3. 6. **Strategy.** Prove directly (cloud). 7. **Notes.** Shared by three derived rows and HTDual. The
   ℓ = 3 instance is dead after the refactor in (i).

## E2. `axSenTate` (IN FLIGHT, cloud workers)

1. **Identity.** `_root_.ZInQ.Contrib.HodgeSplit.AxSenTate`, OpenAddedLeaves9 (TailZ13.lean:23). Defined at
   TailS.lean:79: `∀ p … K … (x : ℂ_[p]), (∀ σ ∈ K.fixingSubgroup, cpAct p σ x = x) → ∃ y : K, x = ((y : PadicAlgCl p) :
   ℂ_[p])`. H-121. LEAF (Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970).
2. **Use.** Exactly as E1, always paired with it (TailX.lean:208, 261, 263; HTDual on c-to-printed2). **Case (b): p = 5
   only**, `K` a finite extension of ℚ₅ (Galois where the proofs choose `E`/`M` Galois).
3. **Library.** As E1, plus Mathlib's Krasner. Ax's proof needs root-distance estimates for
   `∏(X − σα)` under the spectral norm. Mathlib has `spectralNorm` on `PadicAlgCl` (Complex.lean:67, VERIFIED-READ:
   `instance normedField : NormedField (PadicAlgCl p) := spectralNorm.normedField ℚ_[p] (PadicAlgCl p)`).
4. **Missing.** Ax's lemma (`|σα − α| ≤ c` for all σ ∈ G_K implies `dist(α, K) ≤ c'`), then density and completion.
5. **Tier.** T2. 6. **Strategy.** Prove directly (cloud). 7. **Notes.** Its i = 0 role in BdRInvariants: see E5.

## E3. `hodgeTateDecompAbVar`

1. **Identity.** `_root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar`, OpenResearchLeaves10 (TailZ15.lean:31). Defined
   at TailS.lean:347: `∀ p … (F) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : PkgI4.I3.AbVar F) (g : ℕ),
   A.dim = g → ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]), <G_F-equivariance with ℂ_p(1)^g ⊕
   ℂ_p^g>`. H-122. LEAF, published form (Fontaine 1982; Tate 1967 §4; Faltings 1988).
2. **Use.** TailX.lean:208 maps it, through `deRhamComparisonHT_of_leavesT`, to `r10 : DeRhamComparisonHT`. `r10` has two
   consumers:
   - (a) `g9Glue_of_deRhamComparisonHT r.r10` (TailK.lean:330). This becomes `G9Glue` and then `G9Out r₅` (TailA.lean:1930:
     `LocalIsDeRham ℓ 2 … ∧ HasHTWeightsAtSelf ℓ {0, -1}`). It is used in `g12` (TailA.lean:2195-2197) for Pan's
     "distinct HT weights" (`h9.2`) and in `G12Weight` (`hw`).
   - (b) `researchLeaves3_of_open2`: `r10 := PkgI4.deRhamComparison_of_HT r.r10` (TailE.lean:6579). This is G9Glue's
     `hR10` argument, which `g9Glue_of_fieldEmb` applies as `hR10 ℓ F A' 2`.

   The objects: `A'` is the base change of the QM surface `A` to the completion `F = locF K ℓ` (LocalModel.lean:180-183),
   so dim 2 and ℓ = 5 (ℓ = 3 dead). **Case (b).** The HT decomposition is used only for its count clause and
   finite-dimensionality. Weakest:
   ```lean
   def HTWeightsAbSurf5 : Prop := ∀ (F) [Field F] [Algebra ℚ_[5] F] [FiniteDimensional ℚ_[5] F]
     (A : PkgI4.I3.AbVar F), A.dim = 2 →
     htMultOver 5 (A.galRep 5) 0 = 2 ∧ htMultOver 5 (A.galRep 5) (-1) = 2 ∧
     ∀ w, w ≠ 0 → w ≠ -1 → htMultOver 5 (A.galRep 5) w = 0
   ```
   This is implied by the published statement together with Tate's theorems (as in `deRhamComparisonHT_of_leavesT`).
   It is still deep.
3. **Library.** No p-divisible groups, Tate–Sen theory of formal groups, or Hodge–Tate period map in Mathlib or the tree
   (SPECULATIVE, from searches for `BarsottiTate`/`pDivisible`, which found nothing relevant).
   - VERIFIED-READ: `def htMultOver (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (w : ℤ) : ℕ`
     (I4Layer.lean:1224).
   - The abelian-variety base change is proved: `g9Glue_of_abVarBaseChange` (VERIFIED-READ, Contrib/G9/LocalModel.lean:186:
     `theorem g9Glue_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) (hW : G9Bridge.R10Weights) : G9Glue`).
4. **Missing, in order.** p-divisible groups of abelian schemes; Tate's theorem `Hom(T_p G, 𝓞_ℂ)^G = t_{G'}(𝓞_K)` for
   good reduction; potential good reduction of QM surfaces (UNVERIFIED, standard); descent along finite extensions
   (Speiser, `descent_finrank`, already proved); Fontaine/Faltings for the general case.
5. **Tier.** T4 (keep cited). A good-reduction-only variant would be T3: Tate 1967 suffices because QM surfaces have
   potentially good reduction everywhere (UNVERIFIED).
6. **Strategy.** Keep cited, specialized to p = 5 and g = 2.
7. **Notes.** If the building-block route in §F3 were adopted, this field would disappear (SPECULATIVE).

## E4. `deRhamH1AbVarT`

1. **Identity.** `_root_.ZInQ.Contrib.HodgeSplit.DeRhamH1AbVarT` (TailZ15.lean:32). Defined at TailS.lean:1992:
   `∀ p … (F) … (A : PkgI4.I3.AbVar F), IsDeRhamTensorOver p (A.galRep p).dual`. H-123. LEAF, published form,
   transported (`H¹_ét` written as `Hom(V_p A, ℚ_p)`; Faltings 1989, Tsuji 1999, Scholze 2013 Cor. 1.8).
2. **Use.** Only in `r10` (TailX.lean:208–209), for the de Rham clause `IsDeRhamOver` of `DeRhamComparison`. It reaches
   `g9Glue_of_fieldEmb` (`hdR`), then `G9Out.1 = LocalIsDeRham 5 2 r₅`, which is Pan's hypothesis
   (`hPB 5 … h9.1 …`, TailA.lean:2195). **Case (b): p = 5, A' = base change of the QM surface to a finite extension of
   ℚ₅, dim 2.** Weakest:
   `∀ F/ℚ_[5] finite, ∀ A : PkgI4.I3.AbVar F, A.dim = 2 → IsDeRhamTensorOver 5 (A.galRep 5).dual`.
3. **Library.** VERIFIED-READ:
   - Mathlib `def BDeRhamPlus : Type u := AdicCompletion (RingHom.ker (fontaineThetaInvertP R p)) (Localization.Away
     (p : 𝕎 R♭))` and `def BDeRham` (.lake/packages/mathlib/Mathlib/RingTheory/Perfectoid/BDeRham.lean:75,88).
   - Tree `abbrev BdR := Localization (DR.genMonoid p 𝓞_ℂ_[p])` with `example : BdR p = BDeRham 𝓞_ℂ_[p] p := rfl` and
     `def bdrAct (σ : GQp p) : BdR p →+* BdR p` (I4Layer.lean:995-1000).
   - `theorem isField_BDeRham : IsField (BdR O p)` (ZInQKernel/Contrib/G9/KerTheta.lean:681).

   There is no `B_cris`/`B_st`, comparison theorem or étale cohomology.
4. **Missing.** The crystalline or de Rham comparison for abelian varieties (Fontaine–Messing/Faltings for good
   reduction, plus descent). Each is a major theory.
5. **Tier.** T4. 6. **Strategy.** Keep cited. 7. **Notes.** The de Rham clause is needed only because Pan's hypothesis
   is "pst/de Rham". An alternative modularity input with geometric hypotheses (§F3) would remove it.

## E5. `bdRInvariants`

1. **Identity.** Field `bdRInvariants : ∀ p [Fact p.Prime], _root_.ZInQ.Contrib.HodgeSplit.BdRInvariants p`,
   OpenTextbookLeaves10 (TailZ11.lean:28). Defined at ZInQKernel/OneProof/H/TailT.lean:1571 (VERIFIED-READ):
   `def BdRInvariants : Prop := ∀ x : BdR p, (∀ σ : GQp p, bdrAct p σ x = x) → x ∈ Set.range (qpToBdR p)`.
   H-124. LEAF (Fontaine, Astérisque 223 Exp. II; Brinon–Conrad §4).
2. **Use.** TailX.lean:235: `t23 := HodgeLF7.t23 (t23_all_of_bdrInvariants t.bdRInvariants)`. `t23` is then passed down
   unchanged (TailO.lean:2950, TailK.lean:240, TailI.lean:213, TailE.lean:6613). Its only uses are
   `g8_g12 … r.r10 t.t23 …` and `g8_g11 … r.r10 t.t23 …` (TailD.lean:138, 172). Inside these, `hT23` goes only to
   `h9g hR10 hT23 …` (TailA.lean:2220). The `G9Glue` instance ignores it (`_hT23`, Contrib/G9/Reduction.lean:130). So
   **the statement is semantically unused**: it is case (a) in form, and nothing in substance.
   Weakest statement needed: **none**.
3. **Library (if one wanted to prove it).** VERIFIED-READ, tree (bdr-kertheta, Contrib/G9/KerTheta.lean):
   - `theorem ker_fontaineTheta_Cp : RingHom.ker (fontaineTheta O p) = span {xi p}` (l. 399);
   - `theorem isDiscreteValuationRing_BDeRhamPlus : IsDiscreteValuationRing (BDeRhamPlus O p)` (l. 658);
   - `noncomputable def thetaPlusCp : BDeRhamPlus O p →+* ℂ_[p]` (l. 737);
   - `isField_BDeRham` (l. 681).

   pkg-I4 has `theorem isDeRham_trivial (hfix : …BdRInvariants-shape…) (hinj : …)` (I4Layer.lean:1133). The memory note
   says wip/pkg-I4 built θ-naturality and the `B_dR` action (SPECULATIVE whether merged; `bdrAct` is in the kernel).
4. **Missing, to prove it from E1+E2.** In order:
   - (a) `bdrAct` preserves `B_dR^+` and commutes with `thetaPlusCp`;
   - (b) `t = log[ε] ∈ Fil¹`, as a convergent ξ-adic series;
   - (c) `t` generates `ker θ`, via Fontaine's element `([ε]−1)/([ε^{1/p}]−1)`;
   - (d) `σ(t) = χ(σ)t`;
   - (e) `gr^i B_dR ≅ ℂ_p(i)` equivariantly;
   - (f) the filtration argument: invariants of `gr^i` vanish for `i ≠ 0` (E1) and equal `ℚ_p` for `i = 0` (E2);
     separatedness (`isAdicComplete_BDeRhamPlus`).
5. **Tier.** **T1 by deletion.** Copy the TailD consumers with a textbook bundle that lacks `t23`. The precedent is
   g0-assemble2's `ResearchLeaves3` (TailD.lean:12-25), which removed `r1an`/`r17` from `ResearchLeaves` by copying "the
   seven consumers". The theorems to copy:
   - `g8_g11`/`g8_g12`, with G9's output supplied by a `G9GlueHT`-type hypothesis (`Contrib/R10/Glue.lean:32` already
     states `G9GlueHT` without T23);
   - `g8_g12_of_leaves3`, `afterG7_of3`;
   - `sixContactMin_of_leavesR3`, `glueOutputs_of_leaves3`;
   - the `t3` consumers in `gluePieces_of_open4`.

   Proving it instead would be T2 from E1+E2 and bdr-kertheta.
6. **Strategy.** Drop it (refactor). Do not prove it.
7. **Notes.** Caveat: I grepped `.t23`/`hT23` only, and did not check anonymous-constructor destructuring of
   `TextbookLeaves` (SPECULATIVE that there is none). The same refactor would also drop the formal ℓ = 3 instance of
   G9 (observation (i)).

## E6. `r11r12` (Pan∘Berger)

1. **Identity.** `r11r12 : PkgI4.PanBerger`, which resolves to `_root_.PkgI4.PanBerger`: `PanBerger` is not in
   `HDec.PkgI4`'s export list (LPrefix.lean:87). Defined at ZInQKernel/OneProof/H/LPrefix.lean:2250, a verbatim copy of
   ZInQKernel/Contrib/G9/I4Layer.lean:1412: `def PanBerger : Prop := PanFor fun p [Fact p.Prime] n ρ => LocalIsDeRham p
   n ρ`. `PanFor` is at I4Layer.lean:1398 (copy at LPrefix.lean:2236): `∀ p, 5 ≤ p → ∀ ρ : GaloisRep p 2, ρ.IsIrreducible → ρ.FinitelyRamified →
   IsPst p 2 (ρ.restrictLocal p) → ρ.IsOdd → ρ.DistinctHTWeights p → ∃ N k χ g, 0 < N ∧ 1 ≤ k ∧
   IsNormalizedEigenform g χ ∧ ∃ ψ ιC ιL S, ρ.AttachedUpToTwist ψ ιC ιL g S`. H-9. GLUE, composite (Pan 2022 Thm 1.0.4
   with Berger 2002 Thm 0.7).
2. **Use.** It passes unchanged through every bundle generation to `ResearchLeaves3.r11r12`. There it enters
   `g8_g12 … r.r11r12 …` (TailD.lean:139), then `g12` (TailA.lean:2195: `hPB 5 (le_refl 5) r hirr … h9.1 h10 ⟨0, -1, …⟩`).
   **Case (b): p = 5 only, `ρ = r₅` of a QM surface of the construction.** Weakest:
   ```lean
   def PanBerger5 : Prop := ∀ ρ : GaloisRep 5 2, ρ.IsIrreducible → ρ.FinitelyRamified →
     LocalIsDeRham 5 2 (ρ.restrictLocal 5) → ρ.IsOdd → ρ.DistinctHTWeights 5 →
     ∃ N k χ g, 0 < N ∧ 1 ≤ k ∧ IsNormalizedEigenform g χ ∧ ∃ ψ ιC ιL S, ρ.AttachedUpToTwist ψ ιC ιL g S
   ```
   It is still research-scale. Restricting further to `ρ` that come from abelian surfaces makes it a building-block
   modularity statement; see the attack idea in §F3.
3. **Library.** None toward Pan or Berger: no `B_cris`, `B_st`, `(φ,Γ)`-modules, completed cohomology or patching. Only
   `BDeRham` (above).
4. **Missing.** Everything (p-adic local Langlands, completed cohomology, Berger's `(φ,Γ)`-modules/p-adic differential
   equations).
5. **Tier.** T4. 6. **Strategy.** Keep cited, specialized to p = 5.
7. **Notes.** Pan's printed conclusion (h-a011 §1.1, read from arXiv v2) is "comes from a cuspidal eigenform up to
   twist", with no weight. His Thm 7.1.1 says "regular algebraic cuspidal automorphic representation", which would give
   `2 ≤ k`. If a reviewer accepts `2 ≤ k` in `PanFor`, the k = 1 branch of `G12Weight` disappears, and `dsThm966` with
   it (see F2; SPECULATIVE reading).

---

## F1. `dsThm965` (Deligne, Diamond–Shurman 9.6.5)

1. **Identity.** `_root_.ZInQ.Contrib.HodgeSplit.DSThm965` (TailZ15.lean:35). Defined at TailS.lean:1110: `∀ ℓ ιC ιL N
   (k : ℤ) χ (g : CF N k), 0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ∃ ρ : GaloisRep ℓ 2, ∀ p, p.Prime → ¬ p ∣ N*ℓ →
   ρ.UnramifiedAt p ∧ ∃ α β, ιC α = coeff g p ∧ ιC β = χ p * p^(k-1) ∧ ∀ v σ, LiesOver v p → IsArithFrob σ v p →
   (ρ.mat σ).charpoly = X^2 - C (ιL α) * X + C (ιL β)`. H-125. LEAF, published form.
2. **Use.** TailX.lean:211–213 feeds it into two statements:
   - `r14 := r14Det_of_printed dsThm965 dsThm966` (`R14Det`, TailS.lean:1058);
   - `r13 := eigenformHT_of_kato_ds eigenformHTNew newformOfEigenform dsThm965 dsThm966`.

   `R14Det` is consumed in three places:
   - (a) `g12Det_of m.r14det` (TailD.lean:140). This is G12Det, at ℓ = 5, k = 2.
   - (b) `eigenformRepExists_of_r14Det` (TailE.lean:6582), giving `ResearchLeaves3.r14`. This in turn is used in:
     - `G12Weight`: `hR 5 ιC ιL N k χ g …` at ℓ = 5, any `k ≥ 1` (TailB.lean:5001);
     - `newformLeaves_of3`, then `iso_R14` at ℓ = 5 and ℓ = 3, k = 2 (TailA.lean:3464-3545).
   - (c) Inside `eigenformHT_of_new` at the ℓ where R13 is applied (5), `k ≥ 2`.

   **Case (b).** Only ℓ ∈ {3, 5}: at ℓ = 3 only k = 2; at ℓ = 5 every `k ≥ 2`, because `k` is whatever Pan returns.
   Weakest: `DSThm965` restricted to `ℓ = 5 ∨ (ℓ = 3 ∧ k = 2)`. The eigenforms are not specific: level `N` is unbounded at
   G12.
3. **Library.** VERIFIED-READ:
   - `abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k`
     (I4Layer.lean:1234);
   - `IsNormalizedEigenform` defined through coefficient multiplicativity, not Hecke operators (I4Layer.lean:1248).

   Mathlib `NumberTheory/ModularForms/` has q-expansions, Petersson, level one, Eisenstein series, and no Hecke
   operators (grep "Hecke" finds only "Hecke's bound" in Bounds.lean). Hecke operators, modular curves over ℚ, étale
   cohomology and Kuga–Sato varieties are all absent. The glue around the leaf is proved: `semisimplification2_proof`,
   `detFromFrobenius_proof`, `artinTransport_proof` (hodge-split §3).
4. **Missing.** `X₁(N)` over ℤ[1/N] with its universal elliptic curve, étale cohomology with `Sym^{k−2}` coefficients,
   Hecke correspondences, the Eichler–Shimura congruence, Deligne's purity for the trace. For k = 2 only (ℓ = 3 use): Tate
   modules of `J₁(N)` plus Eichler–Shimura (the same infrastructure as F4).
5. **Tier.** T4. 6. **Strategy.** Keep cited, specialized to ℓ ∈ {3, 5}.
7. **Notes.** The k ≥ 3 instances at ℓ = 5 exist only to exclude `k ≠ 2` in G12Weight. With a modularity input that
   returns weight 2 directly (§F3), only k = 2 would remain.

## F2. `dsThm966` (Deligne–Serre)

1. **Identity.** `_root_.ZInQ.Contrib.HodgeSplit.DSThm966` (TailZ15.lean:36). Defined at TailS.lean:1128 (continuous
   `ρ : GQ →* GL (Fin 2) ℂ` with finite image, unramified at `p ∤ N`, trace `a_p` and det `χ(p)` at arithmetic
   Frobenius). H-126. LEAF, published form.
2. **Use.** Three consumers:
   - `r14Det_of_printed`, for the weight-1 case `R14DetWt1` (TailS.lean:1081);
   - `r15 := ModularSplit.deligneSerreConseq_of_ds r.dsThm966` (TailZ9.lean:115);
   - `eigenformHT_of_kato_ds`, through R14Det.

   The weight-1 content is used only in the k = 1 branch of `g12Weight_of` (TailB.lean:5007-5020):
   - `hR 5 … 1 …` (R14 at ℓ = 5, k = 1);
   - `hDS 5 ιC ιL ρH N χ g …` (R15: finite image);
   - then `hFI 5 2 ρ hfin` and `hSen` give a contradiction with weights `{0, −1}`.

   **Case (b):** only ℓ = 5, k = 1, and only to show that k = 1 is impossible for `r₅`. Weakest: "for a weight-1
   normalized eigenform, some semisimple attached `ρ : GaloisRep 5 2` has finite image". Simpler still: make it
   unnecessary. If `PanBerger` is read with `2 ≤ k` (E6 note 7), `R14Det` can be replaced by `R14DetWtGe2`
   (TailS.lean:1087) and r15 dropped, so `dsThm966` leaves the bundle.
3. **Library.** `artinTransport_finite` and `attachedConj_proof` (proved, modular-split §3.1). There is nothing toward
   Deligne–Serre itself: no Rankin–Selberg bounds, no mod-ℓ representations of weight-1 forms.
4. **Missing.** Deligne's ℓ-adic representations in weight 2 (F1) and the Deligne–Serre congruence/lifting argument with
   Rankin's bound.
5. **Tier.** T4 as a theorem. T1 to remove, if the `2 ≤ k` reading of Pan is accepted. That is a statement change to
   `r11r12`, so it needs a reviewer's sign-off on the print.
6. **Strategy.** Remove through the Pan reading. Otherwise keep cited at ℓ = 5.
7. **Notes.** An elementary alternative for the k = 1 exclusion does not avoid DS: both "|a_p| ≤ 2" and finite image are
   Deligne–Serre.

## F3. `eigenformHTNew` (Kato, newforms)

1. **Identity.** `_root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew` (TailZ15.lean:34). Defined at TailS.lean:1275: `∀ ℓ ιC
   ιL N (k : ℤ) χ (f : CF N k) (ρ : GaloisRep ℓ 2), 0 < N → 2 ≤ k → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f
   → ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}`. H-127. GLUE (c), consequence of one theorem (Kato 2004 §§9.2–9.4).
2. **Use.** TailX.lean:211: `r13 := eigenformHT_of_kato_ds r.eigenformHTNew newformOfEigenformG9 dsThm965 dsThm966`
   (`PkgI4.EigenformHT`). The chain is `ResearchLeaves3.r13`, then `g8_g12 … r.r13 …` (TailD.lean:139), then `g12`
   (`hW hR14 hR13 …`, TailA.lean:2197), then `g12Weight_of`: `hHT 5 ιC ιL N k χ g ρ …` (TailB.lean:5023), in the
   k ≥ 2 branch. **Case (b): ℓ = 5 only.** The form `g` is Pan's output, of unknown level and weight. Weakest:
   ```lean
   def EigenformHTNew5 : Prop := ∀ ιC ιL N (k : ℤ) χ (f : CF N k) (ρ : GaloisRep 5 2), 0 < N → 2 ≤ k →
     IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → ρ.HasHTWeightsAtSelf 5 {0, 1 - k}
   ```
   Only the gap of the two weights matters (G12Weight takes `S' = S + s`), but stating "gap = k − 1" is no easier.

   **c-to-printed2 status** (origin/wip/c-to-printed2, .fleet/c-to-printed2.md and docs/research/c-to-printed2.md;
   compiled there on TailZ15, 0 errors, standard axioms):
   - `htDual_proof : TateTwistInvariants → AxSenTate → HTDual` closes modular-split's open glue.
   - `eigenformHTNew_of_printedSS : KatoRealizationCohSS → TateTwistInvariants → AxSenTate → EigenformHTNew`.
     `KatoRealizationCohSS` is an existential leaf: for each newform there is a semisimple continuous `ρ` whose geometric
     Frobenius traces are `a_p` and whose HT weights are `{0, k−1}`.
   - In the Tate normalization, `KatoRealization` alone suffices.
   - Equivalences: `DS → (KatoRealization ↔ EigenformHTNew)` and `DS → Tate → (KatoRealizationCohSS ↔ EigenformHTNew)`.

   So no project glue is left. The field stays GLUE (c) in the strict count. It is not merged at the base.
3. **Library.** `htMult`/`HasHTWeights` (VERIFIED-READ, I4Layer.lean:875: `def htMult (ρ : GQp p →* GL (Fin n) E) (w :
   ℤ) : ℕ`); `attachedConj_proof`, `htConj_proof` (kernel). There is nothing toward Kato's `V_f` (no étale cohomology or
   Kuga–Sato).
4. **Missing.** As F1, plus the de Rham/HT comparison for Kuga–Sato varieties (Faltings 1987 if `5 ∤ N`; Kato, Saito or
   Scholl in general).
5. **Tier.** T4. 6. **Strategy.** Fold c-to-printed2 (replace by `KatoRealizationCohSS`), then specialize to ℓ = 5, and
   keep cited.
7. **Best attack (SPECULATIVE): remove F1 (k ≥ 3), F2, F3, E3, E4 and E6 together.** Replace the Pan route by a single
   modularity statement with geometric hypotheses. In G7, `A` with its descent data (`Tm`, `c`, `ε`, `a`, `β`) is in
   effect a **building block** (a QM abelian surface over ℚ̄ that is isogenous to all its Galois conjugates, compatibly
   with `End⁰ = B`). The candidate citation is "every building block is a ℚ̄-quotient of `J₁(N)`": Ribet 1992/2004 and
   Pyle, with Serre's conjecture proved by Khare–Wintenberger 2009 (cf. their Cor. 10.2; all UNVERIFIED).

   Its conclusion is weight 2 directly: a nonzero map to `J₁(N)_{ℚ̄}`. It would replace G9–G13, including R16 for this
   use, leaving Carayol (or a conductor computation on `A`) for the level bound. This changes the argument, so it needs
   an h-trust style review. A weaker internal variant keeps Pan but drops the weight comparison; that is not possible,
   because Pan's print has no weight (E6 note 7).
   An elementary weight exclusion would work only partly. Combining `(det r)² = χ²` on `H` with
   `det ρ_g = εχ^{k−1}` gives `ψ⁴ = χ^{4−2k}`·(finite). Odd `k` is then excluded because `√p` would lie in a fixed
   number field for infinitely many `p` (SPECULATIVE sketch). Even `k ≥ 4` is not excluded without HT weights or open
   problems on ordinary primes. So the HT input is needed for even `k ≥ 4`.

## F4. `r16` (Eichler–Shimura in `J₁(N)`)

1. **Identity.** `r16 : _root_.LeafModCurves.R16_EichlerShimuraJ1'` (TailZ15.lean:37). Defined at
   ZInQKernel/HDecomp/ModCurves/Leaves.lean:179 (VERIFIED-READ): `∀ N χ (f : CF N 2) (J : AbVar ℚ), 0 < N → IsNewform f
   χ → IsJ1 N J → FiniteDimensional ℚ (coeffField f) ∧ ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
   Surjective π.hom.left ∧ A.dim = [K_f:ℚ] ∧ ∀ ℓ [Fact ℓ.Prime] (emb …), finrank (eigenFun ℓ A θ emb) = 2 ∧ ∀ p, p.Prime →
   ¬ p ∣ N*ℓ → ∀ σ, IsFrobAt σ p → (trace = emb a) ∧ (det = emb c * p)`. H-13. GLUE, composite (Shimura 1973 Thm 1;
   Shimura 1971 Thm 7.9; Diamond–Shurman).
2. **Use.** The chain is `ResearchLeaves3.r16`, then `newformLeaves_of3` (TailD.lean:150), then `g13` (TailA.lean:3456),
   then `commonConstituent_of_attached hR16 … D.i 5 D.ιC D.ι5 D.r5 …` (TailA.lean:3418-3430). That theorem destructures
   `⟨hfin, Af, π, θ, hπ, -, hrest⟩` and uses `hrest ℓ emb` with ℓ = 5: `h2` (rank 2) and `.1` (the trace clause). **The
   dim clause and the det clause are discarded.** `f` is a weight-2 newform of level `N` (unbounded at this point).
   It is also used for non-vacuity of `IsJ1` (LPrefix.lean:11758, `modCurveLeaves_of`); that is not on the live chain
   (SPECULATIVE). **Case (b): ℓ = 5, weight 2, no dim/det.** Weakest:
   ```lean
   def R16_ES5 : Prop := ∀ N χ (f : CF N 2) (J : AbVar ℚ), 0 < N → IsNewform f χ → IsJ1 N J →
     FiniteDimensional ℚ (coeffField f) ∧ ∃ (A : AbVar ℚ) (π : Hom J A) (θ : coeffField f →+* A.End0),
       Surjective π.hom.left ∧ ∀ emb : coeffField f →+* PadicAlgCl 5,
         Module.finrank (PadicAlgCl 5) (eigenFun 5 A θ emb) = 2 ∧
         ∀ p, p.Prime → ¬ p ∣ N * 5 → ∀ σ, IsFrobAt σ p →
           ∀ a : coeffField f, (a : ℂ) = coeff f p → LinearMap.trace _ _ (frobOn 5 A θ emb σ) = emb a
   ```
   This is still deep: it is Eichler–Shimura for `J₁(N)`.
3. **Library.**
   - Vendored Jacobians: CloudW07JacobiansCurves (Albanese, `Pic⁰` of curves; modular-split §3.4).
   - `IsJ1`, `eigenFun`, `frobOn`, `rhoF` (HDecomp/ModCurves).
   - E1Sub (`rhoF_subrep_of_surj`), c9_core (Brauer–Nesbitt/Chebotarev, proved).

   Missing according to modular-split §4.1: Hecke correspondences, the Hecke algebra, quotients of abelian varieties.
4. **Missing, in order.**
   - Hecke correspondences `T_p` and `⟨d⟩` on `X₁(N)`, acting on `J₁(N)` by Albanese functoriality;
   - `𝕋 ⊆ End J₁(N)` and the ideal `I_f`;
   - the quotient `J₁(N)/I_f J₁(N)`, or the image of a Hecke idempotent (av-glue's image recipe would do);
   - Eichler–Shimura `T_p = Frob + ⟨p⟩ p Frob⁻¹` mod `p`, which needs good reduction of `X₁(N)` at `p ∤ N` (Igusa) and
     Néron models;
   - the rank-2 clause (Mumford §19).
5. **Tier.** T4 (T3 at best for the Hecke-algebra part).
6. **Strategy.** Keep cited, specialized to ℓ = 5 without dim/det. That is a smaller published consequence of the same
   theorems.
7. **Notes.** The w63 report (leaf-fold11 §5) still lists r16 as "not splittable over Mathlib's present definitions".
   The building-block route in F3 would make the common constituent part of the cited conclusion.

## F5. `r17` (Carayol)

1. **Identity.** `r17 : _root_.LadicCond.CarayolR17'` (TailZ15.lean:38). Defined at
   ZInQKernel/HDecomp/Conductor/LadicCond.lean:456 (VERIFIED-READ): `∀ ℓ ιC ιL N χ (f : CF N 2) (ρ : GaloisRep ℓ 2) (p :
   ℕ) [Fact p.Prime], 0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ → condExp (ρ.restrictLocal
   p) = (N.factorization p : ℚ)`. H-21. GLUE (c), consequence of one theorem (Carayol 1986 Thm (A), with Casselman).
2. **Use.** TailK.lean:338 passes `r.r17` as `hCar` to `afterG7_of3`. From there it goes to `newformLeaves_of3` and
   `g13_g16` (TailA.lean:3732), then to `g15 lv.r17 hSw …` (TailA.lean:3551).
   - `g15` turns it into `CarayolR17` with `carayolR17_of_R17' hSw` (LadicCond.lean:466), then applies
     `factorization_eq_condAt` with `(D.ι5, D.r5)` for `p ≠ 5` and `(D.ι3, D.r3)` for `p = 5`.
   - The equality `v_p(N) = c` is then used only through upper bounds on `c` (`c ≤ E₀`, `c ≤ 2`, `c = 0` when
     unramified) to bound `v_p(N)`.

   **Case (b):** weight 2, ℓ ∈ {3, 5} (ℓ = 3 only at p = 5), and **only `v_p(N) ≤ condExp`**. Weakest:
   ```lean
   def CarayolLe35 : Prop := ∀ ℓ ∈ ({3, 5} : Set ℕ), ∀ [Fact ℓ.Prime] ιC ιL N χ (f : CF N 2) (ρ : GaloisRep ℓ 2)
     (p : ℕ) [Fact p.Prime], 0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
     (N.factorization p : ℚ) ≤ condExp (ρ.restrictLocal p)
   ```
   (`p = 3` with ℓ = 5 is covered by ℓ = 5.) The "level ≤ conductor" direction is not known to be more elementary
   (SPECULATIVE): it is still local–global compatibility.

   **c-to-printed2 status:** `R17.carayolR17'_of_realization : CarayolRealization → CarayolR17'` (modular-split,
   re-checked) and `R17.carayolRealization_iff_field` (`DS → (CarayolRealization ↔ CarayolR17')`). `CarayolRealization`
   (H-157) says: some semisimple attached `ρ` has `condExp = v_p(N)` for all `p ≠ ℓ`. No project glue is left. Still
   GLUE (c) strict, and not merged at the base.
3. **Library.** VERIFIED-READ: `condExp`, `condAt`, `swanAt` in LadicCond.lean; `SwanIndependent`, `SwanIntegral` and
   `AdaptedExists` are proved (`Swan.*_proved`, TailK.lean:339-340). There are no automorphic representations, no local
   Langlands and no Weil–Deligne representations.
4. **Missing.** The objects listed by c-to-printed2 §2.2: cuspidal automorphic representations of `GL₂(𝔸_ℚ)` with
   `f ↦ π_f`; smooth representations of `GL₂(ℚ_p)`, their conductor and LLC; Weil–Deligne representations; `σ_λ(π)` from
   Shimura-curve cohomology.
5. **Tier.** T4. 6. **Strategy.** Fold c-to-printed2 (`CarayolRealization`), restrict to ℓ ∈ {3, 5} and `≤`, and keep
   cited.
7. **Notes.** An alternative for the level bound: compute the conductor on `A` itself, which the tree already does in
   `G15Ram`/D1–D4. Then one needs only "level of `f` ≤ conductor of `ρ_f`". That is Carayol again unless the
   building-block route gives `A ~ A_f` with `cond(A_f) = N^{dim}` (also Carayol). So it stays cited.

---

## Summary table

| field | consumers (file:line) | use | tier | strategy | best attack idea |
|---|---|---|---|---|---|
| `tateTwistInvariants` | `deRhamComparisonHT_of_leavesT`, `senTwist_of_tate`, `finiteImageHT_of_tate` (TailX:208,261,263); then `g9Glue…`, `g12Weight_of` (TailB:4998ff); HTDual (c-to-printed2) | b: p = 5 only | T2–T3 | prove (in flight) | Tate's normalized trace on `ℚ_p(μ_{p^∞})`; finish the cloud PR |
| `axSenTate` | same as above | b: p = 5 only | T2 | prove (in flight) | Ax's lemma with Mathlib's spectral norm and Krasner |
| `hodgeTateDecompAbVar` | `r10`, then `g9Glue_of_fieldEmb`, `G9Out r₅`, then `g12` (TailA:2195) and G12Weight | b: p = 5, abelian surfaces (base changes of the QM `A`) | T4 | keep cited, specialized | only the HT counts at p = 5, g = 2 are needed; Tate 1967 with potential good reduction of QM surfaces (T3) |
| `deRhamH1AbVarT` | `r10`, then `hdR` in `g9Glue_of_fieldEmb`, then Pan's de Rham hypothesis (TailA:2195) | b: p = 5, same `A'` | T4 | keep cited | disappears if Pan is replaced by building-block modularity |
| `bdRInvariants` | `t23`, then `hT23` of `g8_g11`/`g8_g12` (TailD:138,172), then `G9Glue`'s 2nd argument, **ignored** (`_hT23`, Contrib/G9/Reduction.lean:130) | **unused in substance** | T1 (delete) | drop by refactor | copy the TailD consumers with a textbook bundle without `t23` (ResearchLeaves3 precedent); or prove from E1+E2 (T2: t = log[ε], gr^i ≅ ℂ_p(i)) |
| `r11r12` | `g12` `hPB 5 …` (TailA:2195) | b: p = 5, `ρ = r₅` | T4 | keep cited | building blocks are modular (Ribet/Pyle with Khare–Wintenberger; UNVERIFIED) instead of Pan∘Berger plus Hodge leaves |
| `dsThm965` | `r14Det_of_printed`, then G12Det (ℓ = 5, k = 2), G12Weight (ℓ = 5, all k), `iso_R14` (ℓ = 5, 3, k = 2); `eigenformHT_of_new` (ℓ = 5) | b: ℓ ∈ {3, 5}; k = 2 at ℓ = 3 | T4 | keep cited, specialized | k ≥ 3 only to exclude k ≠ 2; a weight-2 modularity input leaves k = 2 only |
| `dsThm966` | `R14DetWt1`, r15, then the k = 1 branch of `g12Weight_of` (TailB:5007) | b: ℓ = 5, k = 1, to show k = 1 is impossible | T4 (T1 to remove) | remove | read Pan's output as `2 ≤ k` (regular algebraic, Thm 7.1.1); then `R14DetWtGe2` suffices and r15 goes |
| `eigenformHTNew` | `r13`, then `g12` / `g12Weight_of` `hHT 5 …` (TailB:5023) | b: ℓ = 5, k ≥ 2 | T4 | fold c-to-printed2 (`KatoRealizationCohSS`), keep cited | HT gap needed for even k ≥ 4; odd k excluded by an elementary √p argument (SPECULATIVE) |
| `r16` | `commonConstituent_of_attached` (TailA:3418) via `g13` | b: ℓ = 5, weight 2, trace and rank clauses only (dim, det unused) | T4 | keep cited, drop dim/det | needs Hecke correspondences, Hecke algebra, quotients of `J₁(N)`, Eichler–Shimura |
| `r17` | `g15` (TailA:3551), `factorization_eq_condAt` | b: ℓ = 5 (p ≠ 5), ℓ = 3 (p = 5), weight 2, only `v_p(N) ≤ condExp` | T4 | fold c-to-printed2 (`CarayolRealization`), keep cited | the inequality form is the published consequence actually used |
