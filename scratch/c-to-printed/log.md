# c-to-printed results log

Base e38375b3. Compile harness: `scratch/c-to-printed/run.sh FILE.lean` (lean with LEAN_PATH on ~/ctp-lib, a copy
of the e38375b3 build). One Lean process at a time.

- T0.lean: `import ZInQKernel.OneProof.H.TailZ14; #check @ReductGlue.NeronLocalizesDVR` compiles (VERIFIED, 4.7 s).

## Field statements (VERIFIED, read in ZInQKernel/OneProof/H/)
- shimuraFamily: `QMSplit.Moduli.ShimuraFamily`, TailU.lean:1952.
- semistableNeronBaseChange: `ZInQ.HeightSplit.SemistableNeronBaseChange`, TailY.lean:145.
- faltingsLemma5BC: `ZInQ.HeightSplit.FaltingsLemma5BC`, TailY.lean:609 (base form FaltingsLemma5 :560).
- neronLocalizesDVR: `ReductGlue.NeronLocalizesDVR`, TailZ14.lean:882.

## Part N: neronLocalizesDVR (Neron.lean)
- Leaf `CToPrinted.BLR_1_2_4`: BLR 1.2 Prop. 4 (UNVERIFIED number/wording) over any Dedekind domain R with
  fraction field K, X smooth separated quasi-compact over Spec R: `IsNeronModelOver R K X ↔ ∀ maximal 𝔭, ∀ R𝔭 with
  IsLocalization.AtPrime R𝔭 𝔭 (and R → R𝔭 → K), IsNeronModelOver R𝔭 K (X ×_R R𝔭)`.
- Definition `IsNeronModelOver R K X` (BLR 1.2 Def. 1): smooth, separated, locally finite type, quasi-compact, and
  `Hom_R(Y,X) → Hom_K(Y_K,X_K)` bijective for every smooth R-scheme Y. Mathlib objects only.
- Glue proved: `isLocalization_center` (a DVR O of a number field L is `IsLocalization.AtPrime O (center O)` for
  `toOL`), `isNeronModelOver_of` (kernel `GroupModel.IsNeronModel` ⇒ printed property of `𝒩.G`).
- `neronLocalizesDVR_of_printed : BLR_1_2_4 → ReductGlue.NeronLocalizesDVR` COMPILES, axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED, ~5 s).

## Part S: semistableNeronBaseChange (SS2) (CToPrinted.lean, Neron.lean renamed)
- `semistableNeronBaseChange_of_printedBLR : BLR_1_2_4 → IdentityComponentBaseChangeDVR → IdentityComponentOL →
  OpenImmersionOfLocal → SemistableNeronBaseChange` COMPILES (VERIFIED; reduct-glue's proof with Part N).
- New definition `idCompSet G` (G⁰ as a set: x in the connected component of e(f x) in f⁻¹{f x}); Mathlib has no
  identity component over a base.
- Printed-form leaves stated (compile as defs): `SGA3_VIB_3_10` (G smooth group over S ⇒ IsOpen idCompSet),
  `SGA7_IX_3_3` (c : 𝒩 ×_O O' → 𝒩' hom with iso generic fibre, U open = idCompSet ⇒ U.ι ≫ c open immersion with
  range idCompSet 𝒩'), `EGAIV_8_10_5_openImm` (limit setting of the kernel's EGAIV_8_10_5_xii, open immersions).
- Named glue (unproved): `IdentityComponentGroupModel`, `IdentityComponentFromPrinted`, `OpenImmersionLocalization`.
- `semistableNeronBaseChange_of_printed` (4 printed leaves + 3 glue ⇒ SS2) COMPILES, standard axioms (VERIFIED).

## Part F: faltingsLemma5BC (CToPrinted.lean)
- Definitions: `kerScheme f = pullback f.left η_Y.left` (G = ker φ_𝒩), `kerUnit f hf` (unit section, from
  IsMonHom.one_hom), `kerOmegaLog f hf = ∑ᶠ P, log #(ker(s.stalkMap P)).Cotangent` (log #s*Ω¹_{G/S}, stalkwise
  conormal; Mathlib has no sheaf of relative differentials on schemes), `ExtendsIsogeny`.
- Leaves: `FaltingsLemma5Printed` (Faltings 1983 Lemma 5 identity h(B) = h(A) + ½ log deg φ − [K:ℚ]⁻¹ log #s*Ω¹,
  UNVERIFIED), `RaynaudKernelBound` (log #s*Ω¹ ≤ [K:ℚ] log deg φ, Raynaud Ast. 127 VII 2.1.3, UNVERIFIED).
- Glue proved: `exists_extension` (Néron extension of φ is a homomorphism; reduct-glue's isMonHom_of_ext),
  `kerOmegaLog_nonneg`.
- `faltingsLemma5_of_printed`, `faltingsLemma5BC_of_printed` COMPILE, standard axioms (VERIFIED).

## Part H: shimuraFamily (Shimura.lean)
- Shimura.lean = verbatim copy of scratch/shimura-split/ShimuraFam.lean (still compiles at e38375b3, VERIFIED) +
  section CToPrinted.Shimura.
- `InGamma3 x := InO x ∧ x * star x = 1 ∧ ∃ y, InO y ∧ x = 1 + 3y` (Γ_S = B^×_+ ∩ K₃).
- Leaf `ShimuraMainThmIY3`: fine witness (Y,Φ) with R1fpProps, yτ with IsShimuraHolFamily (moduli clause +
  holomorphic), and fibres of yτ = Γ(3)-orbits (GL(2,ℝ) action through BPAnalytic.QM.iota). Main Thm I minus
  reciprocity (needs global Artin map: not in Mathlib 4.35) and minus surjectivity onto V_S(ℂ) (needs V_S over
  ℚ(ζ₃) + Deligne's comparison).
- `shimuraFamily_of_mainThmI : ShimuraMainThmIY3 → HDec.QMSplit.Moduli.ShimuraFamily` COMPILES, standard axioms
  (VERIFIED); verbatim copy check `example : ShimuraFamily = HDec.QMSplit.Moduli.ShimuraFamily := rfl` passes.

## Part S, glue `OpenImmersionLocalization` PROVED (CToPrinted.lean, section OIL)
- `isOpenImmersion_pb_pb_iff` (base change along u then v ~ along u ≫ v, via Over.pullbackComp).
- Index `Idx 𝔭 = 𝔭.primeCompl` preordered by divisibility (directed, nonempty); `ringDiagP`, `specDiagP`;
  `ringCoconeOIsColimit` (O = colim_{a∉𝔭} 𝓞_L[1/a], via IsLocalization + mem_iff_exists), `specConeOIsLimit`.
- `exists_away_of_dvr`: EGA IV 8.10.5 at one DVR gives s ∉ 𝔭_O with base change to 𝓞_L[1/s] an open immersion.
- `openImmersionLocalization : EGAIV_8_10_5_openImm → ReductGlue.OpenImmersionOfLocal` COMPILES (open cover of
  Y by Y ×_S D(s_𝔭) via Cover.mkOfCovers; IsZariskiLocalAtTarget.of_openCover; pullbackRightPullbackFstIso).
- `semistableNeronBaseChange_of_printed'` (4 printed leaves + 2 glue) COMPILES. All 7 #print axioms standard.

## Part S, glue `IdentityComponentFromPrinted` reduced (CToPrinted.lean, section FromPrinted)
- `SGA7_IX_3_3` restricted to `[FiniteDimensional K K']` (specialization; safer than "any extension").
- New glue Props (topology of group schemes): `OpenSubgroupIsIdComp` (open subgroup with connected generic and
  geometric special fibres has range idCompSet), `IdCompBaseChangeDVR` (fst⁻¹ G⁰ = (G ×_O O')⁰).
- `identityComponentFromPrinted_of : OpenSubgroupIsIdComp → IdCompBaseChangeDVR → IdentityComponentFromPrinted`
  COMPILES (canonical c from bcDVR + Néron property + isMonHom_of_ext; Scheme.Pullback.range_map;
  IsOpenImmersion.isoOfRangeEq). Pitfall: `ι` is a reserved token in this import context (Cocone.mk instead of
  `where ι :=`; don't name variables ι).
- `semistableNeronBaseChange_of_printed''` (4 printed leaves + IdentityComponentGroupModel + 2 topological glue)
  COMPILES, standard axioms.

## Part S, glue `IdentityComponentGroupModel` reduced (CToPrinted.lean, namespace OpenSub, section IdCompGM)
- `OpenSub.IsSubgroupOpen G W`, `subHom`, `subFunctor`, `reprBy`, `grpG0` (GrpObj.ofRepresentableBy on the open
  subscheme `G0 W = Over.mk (W.ι ≫ G.hom)`), `isMonHom_incl` — COMPILE (general: any open closed under the group law).
- `idCompSet_one` (e(s) ∈ G⁰) proved.
- New glue Props: `IdCompSubgroup` (G⁰ closed under μ and inverse), `IdCompGenericFibre` (points over the generic
  point are in 𝒢⁰), `IdCompGeomFibres` (geometric fibres of the open subscheme 𝒢⁰ connected at maximal ideals).
- `identityComponentGroupModel_of : IdCompSubgroup → IdCompGenericFibre → IdCompGeomFibres →
  IdentityComponentGroupModel` COMPILES: qc via LocallyOfFiniteType.isLocallyNoetherian + IsNoetherian +
  quasiCompact_of_noetherianSpace_source; generic fibre iso via isIso_iff_isOpenImmersion_and_surjective and
  Scheme.Pullback.range_map.
- `semistableNeronBaseChange_of_printed_final` (4 printed leaves + 5 topological glue) COMPILES, standard axioms.
- `idCompGenericFibre : IdCompGenericFibre` PROVED (generic fibre ≅ A_L connected; its image = points over η by
  range_fst; IsPreconnected.subset_connectedComponentIn). `semistableNeronBaseChange_of_printed_final'`
  (4 printed leaves + 4 topological glue) COMPILES, standard axioms.
- `idCompGeomFibres : AVGlue.GeomConnOfRationalPoint → IdCompGeomFibres` PROVED (bundle leaf, Stacks 04KV):
  g = Spec φ ≫ fromSpecResidueField y via SpecToEquivOfField.left_inv; fibre of W over y ≃ₜ connected component of
  e(y) (fiberHomeo, IsInducing.isPreconnected_image); rational point from e; IsPullback.of_right; then
  GeometricallyConnected.geometrically_connectedSpace. `semistableNeronBaseChange_of_printed_final''`
  (4 printed leaves + bundle leaf GeomConnOfRationalPoint + 3 topological glue) COMPILES, standard axioms.
- `geomConnected_idComp` (W = G⁰ → S geometrically connected, from 04KV at every fibre) and
  `connectedSpace_pullback_idComp` refactored; `unit_bc_fst` (unit of a base change).
- `idCompBaseChangeDVR_of : SGA3_VIB_3_10 → GeomConnOfRationalPoint → IdCompBaseChangeDVR` PROVED
  (IdCompBaseChangeDVR now also assumes [QuasiCompact G.hom]; weaker, used only for Néron models).
- `idCompSubgroup_of : SGA3_VIB_3_10 → GeomConnOfRationalPoint → IdCompSubgroup` PROVED (IdCompSubgroup now assumes
  [IsNoetherian S] [QuasiCompact G.hom]; W ×_S W → S geometrically connected via GeometricallyConnected.comp).
- `semistableNeronBaseChange_of_printed_best` (4 printed leaves + bundle leaf GeomConnOfRationalPoint + one glue
  `OpenSubgroupIsIdComp`) COMPILES, standard axioms.

## Part S, FINAL: SS2 from published-form leaves only (no glue)
- `idComp_baseChange` (identity component commutes with any base change S' → S, S noetherian, G smooth qc) PROVED
  from SGA3_VIB_3_10 + GeomConnOfRationalPoint.
- `IdentityComponentOLRange` (𝒢₀ with range i = 𝒢⁰) PROVED: `identityComponentOLRange_of h3 hG`.
- `IdentityComponentBaseChangeDVRRange` (reduct-split's local form with `range i = 𝒩⁰` instead of connectedness)
  PROVED: `identityComponentBaseChangeDVRRange_of h3 h7 hG`.
- `semistableNeronBaseChange_of_printed_full : BLR_1_2_4 → SGA3_VIB_3_10 → SGA7_IX_3_3 → EGAIV_8_10_5_openImm →
  AVGlue.GeomConnOfRationalPoint → ZInQ.HeightSplit.SemistableNeronBaseChange` COMPILES, axioms
  [propext, Classical.choice, Quot.sound] (VERIFIED). Proof = reduct-glue's semistableNeronBaseChangeLocalGlobal_of
  copied with the two forms above; OpenSubgroupIsIdComp no longer needed.
- No sorry, no axiom in scratch/c-to-printed/*.lean (VERIFIED by grep).
- Bundle `CToPrintedLeaves` (6 new leaves + GeomConnOfRationalPoint); `fields_of_leaves` (3 fields) and
  `reductGlue_leaves_of_printed` (NeronLocalizesDVR ∧ IdentityComponentOL ∧ OpenImmersionOfLocal) COMPILE.
  14 #print axioms lines, all standard (VERIFIED, ~11 s).
