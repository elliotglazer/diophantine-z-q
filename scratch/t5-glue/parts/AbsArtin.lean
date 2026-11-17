
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain

/-! ## §5f. `AbsArtinSurjective` for number fields without real places, proved

The absolute Artin map `C_K → G_K^ab` is continuous (preimages of open subgroups are global norm
subgroups, open), kills the idele classes with trivial finite part (they lie in every ray
subgroup, hence in every norm group), and `C_K` is a finite union of translates of the image of
`Ô^×` (finite index of the ray subgroup of the trivial modulus) times those classes. So the image is
the image of a compact set, closed, and dense (Tau Ceti), hence everything. -/

section AbsArtin

variable (K : Type) [Field K] [NumberField K]

set_option synthInstance.maxHeartbeats 400000 in
instance zeroDim_Gab :
    ZeroDimensionalSpace (TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) :=
  inferInstance

/-- The absolute Artin map `C_K →* G_K^ab` (multiplicative form). -/
def absArt : IdeleClassGroup (𝓞 K) K →* TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K) :=
  MonoidHom.toAdditive.symm
    ((globalClassFormation K).absoluteArtinMap.comp (globalGroundEquiv K).toAddMonoidHom)

theorem ofMul_absArt (c : IdeleClassGroup (𝓞 K) K) :
    Additive.ofMul (absArt K c) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c)) :=
  rfl

theorem continuous_absArt : Continuous (absArt K) := by
  refine continuous_of_continuousAt_one (absArt K) ?_
  rw [ContinuousAt, map_one]
  intro N hN
  obtain ⟨U0, hU0N, hU0o, h1⟩ := mem_nhds_iff.1 hN
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU0o h1
  obtain ⟨V, hV⟩ := (globalClassFormation K).exists_absoluteArtinMap_mem_iff H.toOpenSubgroup
  have hpre : ∀ c, c ∈ globalNormSubgroup K V → absArt K c ∈ (H : Set _) := by
    intro c hc
    rw [mem_globalNormSubgroup_iff, ← hV] at hc
    exact hc
  rw [Filter.mem_map]
  refine Filter.mem_of_superset ((isOpen_globalNormSubgroup K V).mem_nhds (one_mem _)) ?_
  intro c hc
  exact hU0N (hH (hpre c hc))

theorem denseRange_absArt : DenseRange (absArt K) := by
  have h1 : DenseRange (fun a => Additive.toMul ((globalClassFormation K).absoluteArtinMap a)) :=
    DenseRange.comp (Additive.toMul.surjective.denseRange) (globalClassFormation K).denseRange_absoluteArtinMap
      continuous_toMul
  have h2 : Function.Surjective fun c : IdeleClassGroup (𝓞 K) K =>
      globalGroundEquiv K (Additive.ofMul c) :=
    (globalGroundEquiv K).surjective.comp Additive.ofMul.surjective
  have : (absArt K : IdeleClassGroup (𝓞 K) K → _) =
      (fun a => Additive.toMul ((globalClassFormation K).absoluteArtinMap a)) ∘
        (fun c : IdeleClassGroup (𝓞 K) K => globalGroundEquiv K (Additive.ofMul c)) := rfl
  rw [DenseRange, this, h2.range_comp]
  exact h1

/-- **Idele classes with trivial finite part are killed** (no real places). -/
theorem absArt_eq_one_of_coord (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) (x : IdeleGroup (𝓞 K) K)
    (hx : ∀ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord x = 1) :
    absArt K (x : IdeleClassGroup (𝓞 K) K) = 1 := by
  apply Additive.ofMul.injective
  rw [ofMul_absArt, ofMul_one, (globalClassFormation K).absoluteArtinMap_eq_zero_iff]
  intro V
  have hmem : (x : IdeleClassGroup (𝓞 K) K) ∈ globalNormSubgroup K V := by
    rw [globalNormSubgroup_eq_range_classField]
    apply isAdmissibleModulus_abelianConductor K (classField K V)
    rw [mem_raySubgroup_iff]
    refine ⟨x, ?_, rfl⟩
    rw [mem_ideleCongruenceSubgroup_iff]
    refine ⟨fun v _ => by simp [hx v], fun v _ => by simp [hx v], fun w _ => absurd w.2 (hK w.1)⟩
  exact hmem

/-- Units of the integral finite adeles, `Ô^×`. -/
def intUnits : Set (FiniteAdeleRing (𝓞 K) K)ˣ :=
  {w | (w : FiniteAdeleRing (𝓞 K) K) ∈ FiniteAdeleRing.integralAdeles (𝓞 K) K ∧
    ((w⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) ∈
      FiniteAdeleRing.integralAdeles (𝓞 K) K}

theorem isCompact_intUnits : IsCompact (intUnits K) := by
  have hc := FiniteAdeleRing.isCompact_integralAdeles (R := 𝓞 K) (K := K)
  have hc2 : IsCompact ((FiniteAdeleRing.integralAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)) ×ˢ
      (MulOpposite.op '' (FiniteAdeleRing.integralAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)))) :=
    hc.prod (hc.image MulOpposite.continuous_op)
  have := Units.isClosedEmbedding_embedProduct.isCompact_preimage hc2
  convert this using 1
  ext w
  simp [intUnits, Units.embedProduct]

/-- `Ô^× → 𝕀_K`, `w ↦ (1, w)`. -/
def finEmb : (FiniteAdeleRing (𝓞 K) K)ˣ →* IdeleGroup (𝓞 K) K :=
  Units.map (MonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) :
    FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K)

theorem continuous_finEmb : Continuous (finEmb K) :=
  Units.continuous_map (show Continuous fun w : FiniteAdeleRing (𝓞 K) K =>
    ((1 : InfiniteAdeleRing K), w) from continuous_const.prodMk continuous_id)

/-- The compact set `T = ⋃_q q̄·[Ô^×]` (finitely many ray-class representatives `q̄`). -/
def bigT : Set (IdeleClassGroup (𝓞 K) K) :=
  ⋃ q : IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K),
    (fun w => q.out * ((finEmb K w : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K)) '' intUnits K

theorem isCompact_bigT : IsCompact (bigT K) := by
  have : Finite (IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K)) :=
    Subgroup.finite_quotient_of_finiteIndex
  refine isCompact_iUnion fun q => (isCompact_intUnits K).image ?_
  have hmk : Continuous (QuotientGroup.mk : IdeleGroup (𝓞 K) K → IdeleClassGroup (𝓞 K) K) :=
    QuotientGroup.continuous_mk
  exact continuous_const.mul (hmk.comp (continuous_finEmb K))

theorem range_absArt_eq (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    Set.range (absArt K) = absArt K '' bigT K := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro _ ⟨c, rfl⟩
  set q : IdeleClassGroup (𝓞 K) K ⧸ raySubgroup (Modulus.one K) := QuotientGroup.mk c
  obtain ⟨⟨h, hh⟩, hq⟩ := QuotientGroup.mk_out_eq_mul (raySubgroup (Modulus.one K)) c
  -- `c = q̄ · h⁻¹` with `h⁻¹` a ray class
  have hc : c = q.out * h⁻¹ := by rw [hq, mul_inv_cancel_right]
  obtain ⟨x, hx, hxc⟩ := mem_raySubgroup_iff.1 (inv_mem hh)
  rw [mem_ideleCongruenceSubgroup_iff] at hx
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
    intro v
    refine hx.1 v ?_
    intro hdvd
    have : (Modulus.one K).finitePart = ⊤ := rfl
    rw [this, Ideal.dvd_iff_le, top_le_iff] at hdvd
    exact v.isPrime.ne_top hdvd
  set xf := IdeleGroup.toFiniteIdele (𝓞 K) K x
  have hcoord : ∀ v : HeightOneSpectrum (𝓞 K),
      ((xf : FiniteAdeleRing (𝓞 K) K) v) = (v.ideleFiniteCoord x : v.adicCompletion K) := fun v => rfl
  have hcoordi : ∀ v : HeightOneSpectrum (𝓞 K),
      ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v =
        ((v.ideleFiniteCoord x)⁻¹ : (v.adicCompletion K)ˣ) := fun v => rfl
  have hxf : xf ∈ intUnits K := by
    refine ⟨fun v => ?_, fun v => ?_⟩
    · rw [hcoord, HeightOneSpectrum.mem_adicCompletionIntegers, hv1 v]
    · rw [hcoordi, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀,
        hv1 v, inv_one]
  set y := (finEmb K xf)⁻¹ * x
  have hy : ∀ v : HeightOneSpectrum (𝓞 K), v.ideleFiniteCoord y = 1 := by
    intro v
    apply Units.ext
    show ((finEmb K xf)⁻¹ * x : IdeleGroup (𝓞 K) K).val.2 v = 1
    rw [Units.val_mul, Prod.snd_mul]
    show ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v * (x.val.2 v) = 1
    have e1 : ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) * xf = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e2 : ((xf⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) : FiniteAdeleRing (𝓞 K) K) v *
        (xf : FiniteAdeleRing (𝓞 K) K) v = 1 := by
      rw [← FiniteAdeleRing.mul_apply, e1, FiniteAdeleRing.one_apply]
    exact e2
  have hxy : x = finEmb K xf * y := by rw [mul_inv_cancel_left]
  refine ⟨q.out * ((finEmb K xf : IdeleGroup (𝓞 K) K) : IdeleClassGroup (𝓞 K) K),
    Set.mem_iUnion.2 ⟨q, xf, hxf, rfl⟩, ?_⟩
  rw [hc, ← hxc, QuotientGroup.mk'_apply, hxy, QuotientGroup.mk_mul, map_mul, map_mul, map_mul,
    absArt_eq_one_of_coord K hK y hy, mul_one]

/-- **`AbsArtinSurjective K` for number fields without real places.** -/
theorem absArtinSurjective_of_noReal (hK : ∀ w : InfinitePlace K, ¬ w.IsReal) :
    AbsArtinSurjective K := by
  have hclosed : IsClosed (Set.range (absArt K)) := by
    rw [range_absArt_eq K hK]
    exact ((isCompact_bigT K).image (continuous_absArt K)).isClosed
  intro g
  have hg : (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) ∈ Set.range (absArt K) := by
    rw [← hclosed.closure_eq]
    exact denseRange_absArt K _
  obtain ⟨c, hc⟩ := hg
  exact ⟨c, by rw [← ofMul_absArt, hc]⟩

end AbsArtin

/-- `ℚ(√−m)` has no real places. -/
theorem not_isReal_QNeg (m : ℕ) [NeZero m] (w : InfinitePlace (QNeg m)) : ¬ w.IsReal := by
  intro hw
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff] at hw
  set φ := w.embedding
  have h1 : φ QuadraticAlgebra.omega ^ 2 = -(m : ℂ) := by
    rw [← map_pow, omega_sq', map_neg, map_natCast]
  have h2 : (starRingEnd ℂ) (φ QuadraticAlgebra.omega) = φ QuadraticAlgebra.omega := by
    have := congrArg (fun ψ : QNeg m →+* ℂ => ψ QuadraticAlgebra.omega) hw
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  have him : (φ QuadraticAlgebra.omega).im = 0 := Complex.conj_eq_iff_im.1 h2
  have hre := congrArg Complex.re h1
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [sq, Complex.mul_re, him, mul_zero, sub_zero, Complex.neg_re, Complex.natCast_re] at hre
  nlinarith [sq_nonneg (φ QuadraticAlgebra.omega).re]

/-- **`AbsArtinSurjectiveQNeg`, proved.** -/
theorem absArtinSurjectiveQNeg : AbsArtinSurjectiveQNeg :=
  fun m _ _ => absArtinSurjective_of_noReal (QNeg m) (not_isReal_QNeg m)

end T5Glue
