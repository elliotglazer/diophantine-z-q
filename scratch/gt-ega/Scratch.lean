import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
import ZInQKernel.Contrib.CloudW01Spread.StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

open CategoryTheory Limits AlgebraicGeometry

namespace GtEgaScratch

universe u

/-- Verbatim copy of `CToPrinted.EGAIV_8_10_5_openImm` (TailZ19 L281). -/
def EGAIV_8_10_5_openImm : Prop :=
  ∀ (J : Type) [Preorder J] [IsDirectedOrder J] [Nonempty J] (D : Jᵒᵖ ⥤ Scheme.{0})
    [∀ {i j : Jᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D), IsLimit c →
    ∀ (i : Jᵒᵖ) (Xi Yi : Over (D.obj i)), LocallyOfFinitePresentation Xi.hom → QuasiCompact Xi.hom →
      QuasiSeparated Xi.hom → LocallyOfFinitePresentation Yi.hom → QuasiCompact Yi.hom →
      QuasiSeparated Yi.hom → ∀ fi : Xi ⟶ Yi,
      IsOpenImmersion ((Over.pullback (c.π.app i)).map fi).left →
      ∃ (j : Jᵒᵖ) (a : j ⟶ i), IsOpenImmersion ((Over.pullback (D.map a)).map fi).left

theorem exists_isOpenImmersion_baseChange {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i : I) (Xi Yi : Over (D.obj i))
    [CompactSpace Xi.left] [QuasiSeparatedSpace Xi.left]
    [CompactSpace Yi.left] [QuasiSeparatedSpace Yi.left]
    (fi : Xi ⟶ Yi) [LocallyOfFinitePresentation fi.left]
    (h : IsOpenImmersion ((Over.pullback (c.π.app i)).map fi).left) :
    ∃ (j : I) (a : j ⟶ i), IsOpenImmersion ((Over.pullback (D.map a)).map fi).left := by
  have hAX : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i Xi).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i Xi g
  have hAY : ∀ {a b : Over i} (g : a ⟶ b), IsAffineHom ((baseChangeDiagram D i Yi).map g) :=
    fun g => isAffineHom_baseChangeDiagram_map D i Yi g
  have hCX : ∀ a, CompactSpace ((baseChangeDiagram D i Xi).obj a) :=
    compactSpace_baseChangeDiagram_obj D i Xi
  have hCY : ∀ a, CompactSpace ((baseChangeDiagram D i Yi).obj a) :=
    compactSpace_baseChangeDiagram_obj D i Yi
  have hQX : ∀ a, QuasiSeparatedSpace ((baseChangeDiagram D i Xi).obj a) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i Xi
  have hQY : ∀ a, QuasiSeparatedSpace ((baseChangeDiagram D i Yi).obj a) :=
    quasiSeparatedSpace_baseChangeDiagram_obj D i Yi
  have hcX := baseChangeConeIsLimit D hc i Xi
  have hcY := baseChangeConeIsLimit D hc i Yi
  have hinf : IsOpenImmersion (baseChangeMap (c.π.app i) Xi Yi fi) :=
    (baseChangeMap_prop_iff @IsOpenImmersion _ _ _ fi).2 h
  let finf : pullback (c.π.app i) Xi.hom ⟶ pullback (c.π.app i) Yi.hom :=
    baseChangeMap (c.π.app i) Xi Yi fi
  have : CompactSpace ↥(pullback (c.π.app i) Xi.hom : Scheme.{u}) :=
    Scheme.compactSpace_of_isLimit _ _ hcX
  -- the legs of the two limit cones, with their sources written as pullbacks
  let ℓX : ∀ a : Over i, pullback (c.π.app i) Xi.hom ⟶ (baseChangeDiagram D i Xi).obj a :=
    fun a => (baseChangeCone D c i Xi).π.app a
  let ℓY : ∀ a : Over i, pullback (c.π.app i) Yi.hom ⟶ (baseChangeDiagram D i Yi).obj a :=
    fun a => (baseChangeCone D c i Yi).π.app a
  have hsq : ∀ a, IsPullback (ℓX a) finf ((baseChangeDiagramMap D i fi).app a) (ℓY a) :=
    fun a => baseChangeCone_π_isPullback D i fi c a
  have hwY : ∀ {a b : Over i} (g : b ⟶ a), ℓY b ≫ (baseChangeDiagram D i Yi).map g = ℓY a :=
    fun g => (baseChangeCone D c i Yi).w g
  -- Step 1: the image `U` of the open immersion at the limit is a quasi-compact open; descend it.
  let U : (pullback (c.π.app i) Yi.hom : Scheme.{u}).Opens := finf.opensRange
  have hU : IsCompact (U : Set (pullback (c.π.app i) Yi.hom : Scheme.{u})) :=
    isCompact_range finf.continuous
  obtain ⟨a, V, hVc, hV⟩ :=
    exists_preimage_eq (baseChangeDiagram D i Yi) (baseChangeCone D c i Yi) hcY U hU
  replace hV : ℓY a ⁻¹ᵁ V = U := hV
  -- Step 2: `f_a⁻¹ V` pulls back to everything at the limit; so it is everything at some stage `b`.
  have hW : ℓX a ⁻¹ᵁ ⊤ ≤ ℓX a ⁻¹ᵁ ((baseChangeDiagramMap D i fi).app a ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, (hsq a).w, Scheme.Hom.comp_preimage, hV]
    intro x _
    exact ⟨x, rfl⟩
  obtain ⟨b, fba, hb⟩ := exists_map_preimage_le_map_preimage (baseChangeDiagram D i Xi)
    (baseChangeCone D c i Xi) hcX (U := ⊤) (V := (baseChangeDiagramMap D i fi).app a ⁻¹ᵁ V)
    (by simpa using isCompact_univ) hW
  -- Step 3: at stage `b`, `V_b` contains the image of `f_b` and pulls back to `U`.
  let Vb := (baseChangeDiagram D i Yi).map fba ⁻¹ᵁ V
  let fb := (baseChangeDiagramMap D i fi).app b
  have hnat := (baseChangeDiagramMap D i fi).naturality fba
  have hfb : fb ⁻¹ᵁ Vb = ⊤ := by
    apply top_le_iff.mp
    have h' := hb
    rw [← Scheme.Hom.comp_preimage, hnat, Scheme.Hom.comp_preimage] at h'
    exact le_trans (by simp) h'
  have hVbU : ℓY b ⁻¹ᵁ Vb = U := by
    rw [← hV, ← hwY fba]
    rfl
  have := hAY fba
  have hVbc : IsCompact (Vb : Set ((baseChangeDiagram D i Yi).obj b)) :=
    QuasiCompact.isCompact_preimage _ V.2 hVc
  -- Step 4: `f_b` factors through `V_b`; the factor is an isomorphism at the limit.
  have hrange : Set.range fb ⊆ Set.range Vb.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ fb ⁻¹ᵁ Vb := by rw [hfb]; trivial
    exact hx
  let g := IsOpenImmersion.lift Vb.ι fb hrange
  have hg : g ≫ Vb.ι = fb := IsOpenImmersion.lift_fac _ _ _
  let X₀ : Over ((baseChangeDiagram D i Yi).obj b) := Over.mk fb
  let Y₀ : Over ((baseChangeDiagram D i Yi).obj b) := Over.mk Vb.ι
  let f₀ : X₀ ⟶ Y₀ := Over.homMk g hg
  have : CompactSpace X₀.left := hCX b
  have : QuasiSeparatedSpace X₀.left := hQX b
  have : CompactSpace Y₀.left := isCompact_iff_compactSpace.mp hVbc
  have : QuasiSeparatedSpace Y₀.left := quasiSeparatedSpace_of_quasiSeparated Vb.ι
  have : LocallyOfFinitePresentation fb :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (baseChangeMap_isPullback (D.map b.hom) Xi Yi fi).flip inferInstance
  have : LocallyOfFinitePresentation (g ≫ Vb.ι) := by rw [hg]; infer_instance
  have : LocallyOfFinitePresentation f₀.left := locallyOfFinitePresentation_of_comp g Vb.ι
  have hiso : IsIso ((Over.pullback ((baseChangeCone D c i Yi).π.app b)).map f₀).left := by
    change IsIso ((Over.pullback (ℓY b)).map f₀).left
    have hk : ((Over.pullback (ℓY b)).map f₀).left ≫ pullback.snd Vb.ι (ℓY b) =
        pullback.snd fb (ℓY b) :=
      overPullback_map_left_snd (ℓY b) f₀
    have e1 : (hsq b).isoPullback.hom ≫ pullback.snd fb (ℓY b) = finf :=
      (hsq b).isoPullback_hom_snd
    have hr : Set.range finf = Set.range (pullback.snd Vb.ι (ℓY b)) := by
      rw [IsOpenImmersion.range_pullbackSnd, Scheme.Opens.opensRange_ι, hVbU]
      rfl
    let e := IsOpenImmersion.isoOfRangeEq finf (pullback.snd Vb.ι (ℓY b)) hr
    have : ((Over.pullback (ℓY b)).map f₀).left = (hsq b).isoPullback.inv ≫ e.hom := by
      rw [← cancel_mono (pullback.snd Vb.ι (ℓY b)), hk, Category.assoc,
        IsOpenImmersion.isoOfRangeEq_hom_fac, Iso.eq_inv_comp, e1]
    rw [this]
    infer_instance
  -- Step 5: by Stacks 081E the factor is an isomorphism at some stage `d`; then `f_d` is an open
  -- immersion.
  obtain ⟨d, hdb, hd⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange
    (baseChangeDiagram D i Yi) (baseChangeCone D c i Yi) hcY b X₀ Y₀ f₀
  have hk' : ((Over.pullback ((baseChangeDiagram D i Yi).map hdb)).map f₀).left ≫
      pullback.snd Vb.ι ((baseChangeDiagram D i Yi).map hdb) =
      pullback.snd fb ((baseChangeDiagram D i Yi).map hdb) :=
    overPullback_map_left_snd _ f₀
  have : IsOpenImmersion (pullback.snd fb ((baseChangeDiagram D i Yi).map hdb)) := by
    rw [← hk']; infer_instance
  have hsqd := baseChangeDiagramMap_isPullback D i fi hdb
  have : IsOpenImmersion ((baseChangeDiagramMap D i fi).app d) := by
    rw [← hsqd.isoPullback_hom_snd]
    infer_instance
  exact ⟨d.left, d.hom, (baseChangeMap_prop_iff @IsOpenImmersion _ _ _ fi).1 this⟩

theorem egaIV_8_10_5_openImm_proof : EGAIV_8_10_5_openImm := by
  intro J _ _ _ D _ _ _ c hc i Xi Yi hX1 hX2 hX3 hY1 hY2 hY3 fi hfi
  have : CompactSpace Xi.left := QuasiCompact.compactSpace_of_compactSpace Xi.hom
  have : CompactSpace Yi.left := QuasiCompact.compactSpace_of_compactSpace Yi.hom
  have : QuasiSeparatedSpace Xi.left := quasiSeparatedSpace_of_quasiSeparated Xi.hom
  have : QuasiSeparatedSpace Yi.left := quasiSeparatedSpace_of_quasiSeparated Yi.hom
  have : LocallyOfFinitePresentation (fi.left ≫ Yi.hom) := by rw [Over.w]; exact hX1
  have : LocallyOfFinitePresentation fi.left := locallyOfFinitePresentation_of_comp fi.left Yi.hom
  exact exists_isOpenImmersion_baseChange D c hc i Xi Yi fi hfi

end GtEgaScratch

#print axioms GtEgaScratch.egaIV_8_10_5_openImm_proof
