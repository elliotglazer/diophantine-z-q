
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain

/-! ## §5e. `ArtinLift` from the surjectivity of Tau Ceti's absolute Artin map -/

/-- **GLUE ABS-ARTIN-SURJ (class field theory, over Tau Ceti's own objects).** The absolute Artin
map `C_K → G_K^ab` of Tau Ceti's global class formation is surjective: every element of the
absolute Galois group is, modulo the closure of the commutator subgroup, the absolute Artin symbol
of an idele class. (Tau Ceti proves dense image, `ClassFormation.denseRange_absoluteArtinMap`;
surjectivity for number fields follows from the compactness of `C_K` modulo its connected component
(finite class number, compactness of `Ô^×`, Artin symbols trivial on the archimedean component):
Neukirch, *Algebraic number theory*, VI.5; Artin–Tate, Ch. IX; UNVERIFIED numbers.) -/
def AbsArtinSurjective (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ g : TauCeti.AbsoluteGaloisGroup K, ∃ c : IdeleClassGroup (𝓞 K) K,
    Additive.ofMul (g : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup K)) =
      (globalClassFormation K).absoluteArtinMap (globalGroundEquiv K (Additive.ofMul c))

section Lift

variable {m : ℕ} [NeZero m]

/-- **`σ ∈ Aut(ℂ/κ(K))` restricts to an element of `Gal(Kˢ/K)` through `ιC ∘ e`.** -/
theorem exists_tau_of_sigma (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ)) (σ : ℂ ≃+* ℂ) (hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k) :
    ∃ τ : TauCeti.AbsoluteGaloisGroup (QNeg m),
      ∀ x : SeparableClosure (QNeg m), σ (ιC (e x)) = ιC (e (τ x)) := by
  set Ks := SeparableClosure (QNeg m)
  let ε : Ks →+* ℂ := ιC.comp e.toRingHom
  have hε : ∀ x, ε x = ιC (e x) := fun _ => rfl
  have hεinj : Function.Injective ε := ε.injective
  letI : Algebra Ks ℂ := ε.toAlgebra
  have hst : IsScalarTower ℚ Ks ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    simp [RingHom.algebraMap_toAlgebra]
  have halgK : Algebra.IsAlgebraic ℚ Ks := Algebra.IsAlgebraic.trans ℚ (QNeg m) Ks
  -- every algebraic number is in the range of `ε`
  have hrange : ∀ z : ℂ, IsAlgebraic ℚ z → ∃ y : Ks, ε y = z := by
    intro z hz
    have hz' : IsAlgebraic Ks z := hz.extendScalars (algebraMap ℚ Ks).injective
    obtain ⟨y, hy⟩ := mem_range_of_isAlgebraic hz'
    exact ⟨y, hy⟩
  have halg : ∀ (φ : ℂ ≃+* ℂ) (x : Ks), IsAlgebraic ℚ (φ (ε x)) := by
    intro φ x
    have h1 : IsAlgebraic ℚ (ε x) := (halgK.isAlgebraic x).algHom (ε.toRatAlgHom)
    exact h1.algHom ((φ : ℂ →+* ℂ).toRatAlgHom)
  choose τf hτf using fun x => hrange (σ (ε x)) (halg σ x)
  choose τi hτi using fun x => hrange (σ.symm (ε x)) (halg σ.symm x)
  have hK : ∀ k : QNeg m, ε (algebraMap (QNeg m) Ks k) = kappa m k := fun k =>
    kappa_eq_of_normalized e he k
  let τh : Ks →ₐ[QNeg m] Ks :=
    { toFun := τf
      map_one' := hεinj (by simp [hτf])
      map_mul' := fun x y => hεinj (by rw [hτf, map_mul, map_mul, map_mul, hτf, hτf])
      map_zero' := hεinj (by simp [hτf])
      map_add' := fun x y => hεinj (by rw [hτf, map_add, map_add, map_add, hτf, hτf])
      commutes' := fun k => hεinj (by
        show ε (τf (algebraMap (QNeg m) Ks k)) = ε (algebraMap (QNeg m) Ks k)
        rw [hτf, hK, hσK]) }
  have hbij : Function.Bijective τh := by
    refine ⟨fun x y hxy => ?_, fun y => ⟨τi y, ?_⟩⟩
    · have h := congrArg ε hxy
      change ε (τf x) = ε (τf y) at h
      rw [hτf, hτf] at h
      exact hεinj (σ.injective h)
    · apply hεinj
      change ε (τf (τi y)) = ε y
      rw [hτf, hτi, RingEquiv.apply_symm_apply]
  refine ⟨AlgEquiv.ofBijective τh hbij, fun x => ?_⟩
  show σ (ε x) = ε (τf x)
  rw [hτf]

open scoped IsMulCommutative in
/-- **`ArtinCond` from an absolute Artin symbol.** If the idele class of `s` has absolute Artin
symbol the class of `τ`, and `σ` acts on `ιC(e(Kˢ))` as `τ`, then `σ = [s, K]` on `K^ab`. -/
theorem artinCond_of_abs (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar) (σ : ℂ ≃+* ℂ)
    (τ : TauCeti.AbsoluteGaloisGroup (QNeg m))
    (hτ : ∀ x : SeparableClosure (QNeg m), σ (ιC (e x)) = ιC (e (τ x)))
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m))
    (hs : Additive.ofMul (τ : TopologicalAbelianization (TauCeti.AbsoluteGaloisGroup (QNeg m))) =
      (globalClassFormation (QNeg m)).absoluteArtinMap
        (globalGroundEquiv (QNeg m) (Additive.ofMul (icl s)))) :
    ArtinCond m e σ s := by
  intro F _ _ _ x
  have h1 := of_ideleClassArtinMap (QNeg m) F F.val (icl s)
  have h0 := globalArtinMap_eq_of_mk_eq_absoluteArtinMap (QNeg m) F F.val τ hs
  have h3 : Abelianization.of (ideleClassArtinMap (QNeg m) F (icl s)) =
      Abelianization.of (F.val.restrictNormalHom τ) := by
    rw [h1, h0, toMul_ofMul]
  have h2 : ideleClassArtinMap (QNeg m) F (icl s) = F.val.restrictNormalHom τ :=
    (Abelianization.equivOfComm (H := Gal(F/QNeg m))).injective h3
  rw [h2, hτ]
  have h4 : ((F.val.restrictNormalHom τ x : F) : SeparableClosure (QNeg m)) = τ x :=
    F.val.restrictNormalHom_commutes τ x
  rw [h4]

end Lift

/-- `AbsArtinSurjective` for the imaginary quadratic fields `ℚ(√−m)`, `m` squarefree. -/
def AbsArtinSurjectiveQNeg : Prop := ∀ (m : ℕ) [NeZero m], Squarefree m → AbsArtinSurjective (QNeg m)

/-- **`ArtinLift` from the surjectivity of the absolute Artin map** (for the fields `ℚ(√−m)`). -/
theorem artinLift_of_abs (h : AbsArtinSurjectiveQNeg) : ArtinLift := by
  intro m _ hsq e he σ hσK
  obtain ⟨τ, hτ⟩ := exists_tau_of_sigma e he σ hσK
  obtain ⟨c, hc⟩ := h m hsq τ
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  exact ⟨s, artinCond_of_abs e σ τ hτ s hc⟩

end T5Glue
