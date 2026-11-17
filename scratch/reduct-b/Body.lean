import RBBase

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)

namespace ReductB
open ReductSplit ReductGlue ZInQ.Contrib.AbVarBC

section Descent

variable {K : Type} [Field K]

/-- A separable element of `K̄` over an intermediate field `F`, fixed by `Aut(K̄/F)`, lies in `F`. -/
theorem mem_of_isSeparable_of_fixed_inter (F : IntermediateField K (AlgebraicClosure K))
    (a : AlgebraicClosure K) (ha : IsSeparable F a)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[F] AlgebraicClosure K, σ a = a) :
    a ∈ Set.range (algebraMap F (AlgebraicClosure K)) := by
  have : IsAlgClosure F (AlgebraicClosure K) :=
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := K) F⟩
  let L := separableClosure F (AlgebraicClosure K)
  have haL : a ∈ L := (mem_separableClosure_iff).mpr ha
  let a' : L := ⟨a, haL⟩
  have : a' ∈ Set.range (algebraMap F L) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro τ
    apply Subtype.ext
    have h1 := AlgEquiv.liftNormal_commutes τ (AlgebraicClosure K) a'
    have h2 : (algebraMap L (AlgebraicClosure K)) a' = a := rfl
    rw [h2, hfix] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := this
  exact ⟨c, by rw [IsScalarTower.algebraMap_apply F L (AlgebraicClosure K), hc]; rfl⟩

/-- **Galois descent to an intermediate field for points of an étale `K`-scheme**: a `K̄`-point
fixed by every `σ ∈ Aut(K̄/K)` that fixes `F` pointwise comes from an `F`-point. -/
theorem exists_rational_of_fixed_etale_inter (F : IntermediateField K (AlgebraicClosure K))
    (X : Over (Spec (CommRingCat.of K)))
    [Etale X.hom] (q : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ X)
    (hq : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      PkgI3.AbVar.galHom σ ≫ q = q) :
    ∃ y : PkgI3.AbVar.ptObj (K := K) F ⟶ X, extHom F.val ≫ y = q := by
  classical
  let q0 : Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ X.left := q.left
  have hq0 : q0 ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) :=
    Over.w q
  let p : X.left := q0 (IsLocalRing.closedPoint (AlgebraicClosure K))
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q0 ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint (AlgebraicClosure K) :=
      Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure K)) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q0 hrange
  have hq' : q' ≫ U.ι = q0 := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of (AlgebraicClosure K) := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q0 = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq0]
  have hfixφ : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      φ ≫ CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K) = φ := by
    intro σ hσ
    have h1 := congrArg Over.Hom.left (hq σ hσ)
    change Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ q0 =
      q0 at h1
    rw [hql, ← Category.assoc, ← Spec.map_comp] at h1
    have h2 := (cancel_mono (e.inv ≫ U.ι)).mp h1
    exact Spec.map_injective h2
  have hθet : RingHom.Etale θ.hom := by
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  have : Algebra.Etale K Γ(X.left, U) := hθet
  let f : Γ(X.left, U) →ₐ[K] AlgebraicClosure K :=
    { φ.hom with
      commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  have hmem : ∀ r, φ.hom r ∈ Set.range (algebraMap F (AlgebraicClosure K)) := by
    intro r
    refine mem_of_isSeparable_of_fixed_inter F _ ((isSeparable_of_etale f r).tower_top F)
      fun τ => ?_
    exact congrArg (fun f => CommRingCat.Hom.hom f r)
      (hfixφ (τ.restrictScalars K) (fun y hy => τ.commutes ⟨y, hy⟩))
  choose c hc using hmem
  have hinj := (algebraMap F (AlgebraicClosure K)).injective
  let ψ : Γ(X.left, U) →+* F :=
    { toFun := c
      map_one' := hinj (by rw [hc, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hc, map_mul, map_mul, hc, hc])
      map_zero' := hinj (by rw [hc, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hc, map_add, map_add, hc, hc]) }
  have hθψ : θ ≫ CommRingCat.ofHom ψ = CommRingCat.ofHom (algebraMap K F) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    apply hinj
    have := congrArg (fun f => CommRingCat.Hom.hom f a) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this ⊢
    rw [show algebraMap F (AlgebraicClosure K) (ψ (θ.hom a)) = φ.hom (θ.hom a) from hc _, this]
    rfl
  refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ?_, ?_⟩
  · show (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap K F))
    rw [Category.assoc, Category.assoc, ← hθ, ← Spec.map_comp, hθψ]
  · apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom ((F.val : F →ₐ[K] AlgebraicClosure K) :
        F →+* AlgebraicClosure K)) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι = q0
    rw [hql, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext r
    exact hc r

/-- **Torsion points fixed by `Aut(K̄/F)` are `F`-rational** (from the bundle leaf
`MulEtaleAbelianScheme`): the intermediate-field form of `fixedTorsionRational_of_mulEtale`. -/
theorem fixedTorsionRational_inter (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (F : IntermediateField K (AlgebraicClosure K)) (A : PkgI3.AbVar K) (m : ℕ) (hm : (m : K) ≠ 0)
    (x : A.Pt (AlgebraicClosure K)) (hx : x ^ m = 1)
    (hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      A.galAct σ x = x) :
    ∃ z : A.Pt F, extPt A F.val z = x := by
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  have hxm : x ≫ M = 1 := by rw [comp_pow_one]; exact hx
  have hw : x.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K)).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let x' : PkgI3.AbVar.ptObj (K := K) (AlgebraicClosure K) ⟶ P :=
    Over.homMk (pullback.lift x.left _ hw) (by simp [P])
  have hfix' : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, (∀ y ∈ F, σ y = y) →
      PkgI3.AbVar.galHom σ ≫ x' = x' := by
    intro σ hσ
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_fst]
      exact congrArg Over.Hom.left (hfix σ hσ)
    · simp only [x', Over.comp_left, Over.homMk_left, Category.assoc, pullback.lift_snd]
      exact Over.w (PkgI3.AbVar.galHom σ)
  obtain ⟨y', hy'⟩ := exists_rational_of_fixed_etale_inter F P x' hfix'
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let pr : P ⟶ A.X := Over.homMk (pullback.fst M.left (η[A.X]).left) hpr
  refine ⟨y' ≫ pr, ?_⟩
  change extHom _ ≫ y' ≫ pr = x
  rw [← Category.assoc, hy']
  apply Over.OverMorphism.ext
  simp [x', pr]

end Descent

/-- `3` or `4` is a unit in a local ring (`4 - 3 = 1`). -/
theorem exists_three_le_isUnit {R : Type} [CommRing R] [IsLocalRing R] :
    ∃ m : ℕ, 3 ≤ m ∧ IsUnit (m : R) := by
  by_cases h3 : IsUnit ((3 : ℕ) : R)
  · exact ⟨3, le_rfl, h3⟩
  · refine ⟨4, by norm_num, ?_⟩
    have h1 : IsUnit (((4 : ℕ) : R) + -((3 : ℕ) : R)) := by
      rw [show ((4 : ℕ) : R) + -((3 : ℕ) : R) = 1 by push_cast; ring]
      exact isUnit_one
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h | h
    · exact h
    · exact absurd (IsUnit.neg_iff _ |>.mp h) h3

/-- **K1: SGA 7 IX 3.6 over a DVR from Raynaud's criterion (4.7)**, with the bundle leaves
`MumfordTorsionAlgClosed` (finiteness of `A(K̄)[m]`) and `MulEtaleAbelianScheme` (`[m]` étale).
Take `m ∈ {3, 4}` invertible in `O`, `K'` a finite field of definition of `A(K̄)[m]`
(`torsionFieldOfDefinition_of`); at every DVR `O'` of `K'` over `O` the points of order `m` of
`A_{K'}` are `K'`-rational (`torsion_descends_etale` and `fixedTorsionRational_inter`), so Raynaud's
criterion applies to `A_{K'}` over `O'`. -/
theorem semistableReductionDVR_of_raynaud (hR : RaynaudSemistable)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVR := by
  intro K _ O _ A
  obtain ⟨m, hm3, hmu⟩ := exists_three_le_isUnit (R := O)
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  obtain ⟨K', hfin, hfix⟩ :=
    torsionFieldOfDefinition_of (AvSplit.torsionStructure_of_mumford hM) K A m hmK
  refine ⟨K', hfin, fun O' hO'dvr hO => ?_⟩
  haveI := hO'dvr
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  refine hR K' O' (A.baseChange K') m hm3 hmu' ?_
  intro x hx
  haveI : Algebra.IsAlgebraic K' (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) K'
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K')).injective
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K)).injective
  let κ' : AlgebraicClosure K →ₐ[K'] AlgebraicClosure K' := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := κ'.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := fixedTorsionRational_inter hE K' A m hmK p hp (fun σ hσ => hfix σ hσ p hp)
  refine ⟨(bcPt A K').symm z, ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt]
  have hκ : AlgHom.restrictScalars K (Algebra.ofId K' (AlgebraicClosure K')) = κ.comp K'.val := by
    refine AlgHom.ext fun a => ?_
    exact (κ'.commutes a).symm
  rw [hκ]


/-! ## Route B: 4.7 and 3.3a over a DVR from their strictly henselian forms and one
strict-henselization leaf -/

section RouteB

theorem comap_algebraMap_self {K : Type} [Field K] (O : ValuationSubring K) :
    O.comap (algebraMap K K) = O := by
  ext x
  rfl

/-- **`StrictHenselizationPair` implies `StrictHenselizationNeron`**: the instance `K' = K`,
`O' = O` of the pair; `IsSHNeronExt`'s body is `StrictHenselizationNeron`'s body. -/
theorem strictHenselizationNeron_of_pair (hPair : StrictHenselizationPair) :
    StrictHenselizationNeron := by
  intro K _ O _
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, -, -⟩ :=
    hPair K O K O (comap_algebraMap_self O)
  exact ⟨E, inferInstance, inferInstance, P, hP, hSHP⟩

/-- **SGA 7 IX 4.7 over a DVR** (`RaynaudSemistable`, the bundle field) from the strictly henselian
form, `StrictHenselizationPair` and the bundle leaf `MulEtaleAbelianScheme`. -/
theorem raynaudSemistable_of_SH_pair (hR : RaynaudSemistableSH) (hPair : StrictHenselizationPair)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistable :=
  raynaudSemistable_of_SH' hR (strictHenselizationNeron_of_pair hPair) hE

/-- **SGA 7 IX 3.3, first assertion, over a DVR** (`SemistablePersistsDVR`, the bundle field) from
the strictly henselian form and `StrictHenselizationPair`. -/
theorem semistablePersistsDVR_of_SH_pair (hP : SemistablePersistsSH)
    (hPair : StrictHenselizationPair) : SemistablePersistsDVR :=
  persistsFromSH_of hPair hP

/-- **SGA 7 IX 3.6 over a DVR** (`SemistableReductionDVR`, the bundle field) from the strictly
henselian 4.7, `StrictHenselizationPair` and the bundle leaves `MumfordTorsionAlgClosed`,
`MulEtaleAbelianScheme` (K1 composed with Route B). -/
theorem semistableReductionDVR_of_SH_pair (hR : RaynaudSemistableSH)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableReductionDVR :=
  semistableReductionDVR_of_raynaud (raynaudSemistable_of_SH_pair hR hPair hE) hM hE

/-- The three bundle fields from the printed (strictly henselian) leaves. -/
theorem three_fields_of_printed (hR : RaynaudSemistableSH) (hP : SemistablePersistsSH)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVR ∧ RaynaudSemistable ∧ SemistablePersistsDVR :=
  ⟨semistableReductionDVR_of_SH_pair hR hPair hM hE, raynaudSemistable_of_SH_pair hR hPair hE,
    semistablePersistsDVR_of_SH_pair hP hPair⟩

end RouteB

/-! ## Route B with `[CharZero K]` and `[PerfectField (ResidueField O)]` on the strictly henselian
forms (perfect + separably closed residue field = algebraically closed residue field) -/

section RouteBCP

/-- **LEAF (printed base, restricted) `RaynaudSemistableSHcp`**: Raynaud's criterion (SGA 7 I,
Exp. IX, Prop. 4.7; number UNVERIFIED) for a strictly henselian DVR `O` of a field of characteristic
`0` whose residue field is perfect (hence algebraically closed). A specialization of
`RaynaudSemistableSH`. -/
def RaynaudSemistableSHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O → ∀ (A : PkgI3.AbVar K) (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- **LEAF (printed base, restricted) `SemistablePersistsSHcp`**: SGA 7 I, Exp. IX, Prop. 3.3,
first assertion (number UNVERIFIED), over a strictly henselian base DVR `O` of a field of
characteristic `0` with perfect (hence algebraically closed) residue field. A specialization of
`SemistablePersistsSH`. -/
def SemistablePersistsSHcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)], IsStrictlyHenselianDVR O →
    ∀ (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- `RaynaudSemistable` with the two instances (the DVR form reachable from `RaynaudSemistableSHcp`). -/
def RaynaudSemistableCP : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K)
    (m : ℕ), 3 ≤ m → IsUnit (m : O) →
    (∀ x : A.Pt (AlgebraicClosure K), x ^ m = 1 →
      ∃ y : A.Pt K, ZInQ.Contrib.AbVarBC.extPt A (Algebra.ofId K (AlgebraicClosure K)) y = x) →
    SemistableNeronModels A O

/-- `SemistablePersistsDVR` with the two instances on the base. -/
def SemistablePersistsDVRcp : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

/-- The restricted printed leaves are specializations of the general-DVR forms (so not stronger). -/
theorem cp_of_general (h47 : RaynaudSemistable) (h33 : SemistablePersistsDVR) :
    RaynaudSemistableSHcp ∧ SemistablePersistsSHcp :=
  ⟨fun K _ _ O _ _ _ A m hm hmu ht => h47 K O A m hm hmu ht,
   fun K _ _ O _ _ _ K' _ _ _ O' _ hO A hA => h33 K O K' O' hO A hA⟩

theorem charZero_of_algebra (K E : Type) [Field K] [Field E] [Algebra K E] [CharZero K] :
    CharZero E :=
  charZero_of_injective_algebraMap (algebraMap K E).injective

theorem perfectField_of_isSHNeronExt {K E : Type} [Field K] [Field E] [Algebra K E]
    {O : ValuationSubring K} {P : ValuationSubring E} {hP : P.comap (algebraMap K E) = O}
    [PerfectField (IsLocalRing.ResidueField O)] (h : IsSHNeronExt O P hP) :
    PerfectField (IsLocalRing.ResidueField P) := by
  obtain ⟨-, halg, -⟩ := h
  letI := (resMap hP).toAlgebra
  exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField O)

/-- **`RaynaudSemistableCP` from `RaynaudSemistableSHcp`**, `StrictHenselizationPair` and
`MulEtaleAbelianScheme`. -/
theorem raynaudSemistableCP_of_SH (hR : RaynaudSemistableSHcp) (hPair : StrictHenselizationPair)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) : RaynaudSemistableCP := by
  intro K _ _ O _ _ A m hm3 hmu htors 𝒩 h𝒩
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP, -, -⟩ :=
    hPair K O K O (comap_algebraMap_self O)
  haveI : CharZero E := charZero_of_algebra K E
  haveI : PerfectField (IsLocalRing.ResidueField P) := perfectField_of_isSHNeronExt hSHP
  obtain ⟨hSH, halg, hbc⟩ := hSHP
  haveI : IsDiscreteValuationRing P := hSH.1
  have hmu' : IsUnit (m : P) := by
    have := hmu.map (comapHom hP)
    rwa [map_natCast] at this
  rw [isSemistable_bcDVR_iff hP halg]
  refine hR E P hSH (A.baseChange E) m hm3 hmu' ?_ _ (hbc A 𝒩 h𝒩)
  intro x hx
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E := IsAlgClosed.lift
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := htors p hp
  refine ⟨(bcPt A E).symm (extPt A (Algebra.ofId K E) z), ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure E)).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt, extPt_extPt]
  congr 1
  ext a
  simp

/-- **`SemistablePersistsDVRcp` from `SemistablePersistsSHcp`** and `StrictHenselizationPair`
(the proof of `persistsFromSH_of`, with the instances carried to the strict henselization). -/
theorem semistablePersistsDVRcp_of_SH (hSH : SemistablePersistsSHcp)
    (hPair : StrictHenselizationPair) : SemistablePersistsDVRcp := by
  intro K _ _ O _ _ K' _ _ _ O' _ hO A hA 𝒩' h𝒩'
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', hSHP0, ⟨hSHP', halgP', hbcP'⟩, hPP'⟩ :=
    hPair K O K' O' hO
  haveI : CharZero E := charZero_of_algebra K E
  haveI : PerfectField (IsLocalRing.ResidueField P) := perfectField_of_isSHNeronExt hSHP0
  obtain ⟨hSHP, halgP, hbcP⟩ := hSHP0
  haveI : IsDiscreteValuationRing P := hSHP.1
  haveI : IsDiscreteValuationRing P' := hSHP'.1
  have hAE : HasSemistableReduction (A.baseChange E) P := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hP 𝒩, hbcP A 𝒩 h𝒩, (isSemistable_bcDVR_iff hP halgP 𝒩).mp hs⟩
  have h1 : SemistableNeronModels ((A.baseChange E).baseChange E') P' :=
    hSH E P hSHP E' P' hPP' (A.baseChange E) hAE
  have he : IsMonHom (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm).hom := by
    haveI := bcbcIso_isMonHom A E E'
    have : IsMonHom (bcbcIso A K' E').inv := by
      haveI := bcbcIso_isMonHom A K' E'
      infer_instance
    exact @instIsMonHomComp _ _ _ _ _ _ _ _ _ _ _ (bcbcIso_isMonHom A E E') this
  have h2 : SemistableNeronModels ((A.baseChange K').baseChange E') P' :=
    semistableNeronModels_transport (bcbcIso A E E' ≪≫ (bcbcIso A K' E').symm) he h1
  rw [isSemistable_bcDVR_iff hP' halgP']
  exact h2 _ (hbcP' (A.baseChange K') 𝒩' h𝒩')

/-- The residue field of a DVR of a number field is finite, hence perfect. -/
theorem perfectField_residue_nf {L : Type} [Field L] [NumberField L] (O : ValuationSubring L)
    [IsDiscreteValuationRing O] : PerfectField (IsLocalRing.ResidueField O) := by
  haveI : (center O).IsMaximal := center_isMaximal O
  haveI : Finite (𝓞 L ⧸ center O) := Ideal.finiteQuotientOfFreeOfNeBot (center O) (center_ne_bot O)
  haveI : Finite (center O).ResidueField :=
    Finite.of_surjective _ (center O).bijective_algebraMap_quotient_residueField.2
  haveI : Finite (IsLocalRing.ResidueField O) := Finite.of_equiv _ (resIso O).toEquiv
  infer_instance

/-- `SemistablePersistsDVR` at number fields (the generality of every use: SS1, SS3). -/
def SemistablePersistsDVRnf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'], O'.comap (algebraMap K K') = O →
    ∀ A : PkgI3.AbVar K, HasSemistableReduction A O → SemistableNeronModels (A.baseChange K') O'

theorem persistsNF_of_cp (h : SemistablePersistsDVRcp) : SemistablePersistsDVRnf := by
  intro K _ _ O _ K' _ _ _ O' _ hO A hA
  haveI := perfectField_residue_nf O
  exact h K O K' O' hO A hA

theorem persistsNF_of_general (h : SemistablePersistsDVR) : SemistablePersistsDVRnf :=
  fun K _ _ O _ K' _ _ _ O' _ hO A hA => h K O K' O' hO A hA

/-- **SS3** (`HeightSplit.SemistablePersists`) from the number-field form of 3.3a: reduct-split's
`semistablePersists_of_leaves` with `h33` retyped (proof unchanged). -/
theorem semistablePersists_of_leaves_nf (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistablePersists := by
  intro K _ _ A L _ _ _ 𝒩 h𝒩 hss L' _ _ _ _ _ 𝒩' h𝒩'
  rw [hLG K A L 𝒩 h𝒩] at hss
  rw [hLG K A L' 𝒩' h𝒩']
  intro O' hO'
  haveI := hO'
  haveI : IsDiscreteValuationRing (O'.comap (algebraMap L L')) := hDown L L' O' hO'
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  have h1 := h33 L (O'.comap (algebraMap L L')) L' O' rfl (A.baseChange L)
    (hss _ inferInstance)
  exact hasSemistableReduction_of hN O' _
    (semistableNeronModels_transport (bcbcIso A L L') (bcbcIso_isMonHom A L L') h1)


/-- `SemistableReductionDVR` at number fields (the generality of its use in SS1; its other use, r8,
is over every field). -/
def SemistableReductionDVRnf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (A : PkgI3.AbVar K),
    ∃ K' : IntermediateField K (AlgebraicClosure K), FiniteDimensional K K' ∧
      ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
        O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O'

theorem reductionNF_of_general (h : SemistableReductionDVR) : SemistableReductionDVRnf :=
  fun K _ _ O _ A => h K O A

/-- **K1 at number fields from the restricted 4.7** (`RaynaudSemistableCP`): the proof of
`semistableReductionDVR_of_raynaud`, with `K'` a number field, so `κ(O')` is finite. -/
theorem semistableReductionDVRnf_of_raynaudCP (hR : RaynaudSemistableCP)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    SemistableReductionDVRnf := by
  intro K _ _ O _ A
  obtain ⟨m, hm3, hmu⟩ := exists_three_le_isUnit (R := O)
  have hmK : (m : K) ≠ 0 := natCast_ne_zero_of_isUnit O hmu
  obtain ⟨K', hfin, hfix⟩ :=
    torsionFieldOfDefinition_of (AvSplit.torsionStructure_of_mumford hM) K A m hmK
  refine ⟨K', hfin, fun O' hO'dvr hO => ?_⟩
  haveI := hO'dvr
  haveI : NumberField K' := NumberField.of_module_finite K K'
  haveI := perfectField_residue_nf O'
  have hmu' : IsUnit (m : O') := by
    have := hmu.map (comapHom hO)
    rwa [map_natCast] at this
  refine hR K' O' (A.baseChange K') m hm3 hmu' ?_
  intro x hx
  haveI : Algebra.IsAlgebraic K' (AlgebraicClosure K) := Algebra.IsAlgebraic.tower_top (K := K) K'
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K')).injective
  haveI : Module.IsTorsionFree K' (AlgebraicClosure K) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K' (AlgebraicClosure K)).injective
  let κ' : AlgebraicClosure K →ₐ[K'] AlgebraicClosure K' := IsAlgClosed.lift
  let κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure K' := κ'.restrictScalars K
  obtain ⟨p, hp, hpx⟩ := torsion_descends_etale hE A κ m hmK x hx
  obtain ⟨z, hz⟩ := fixedTorsionRational_inter hE K' A m hmK p hp (fun σ hσ => hfix σ hσ p hp)
  refine ⟨(bcPt A K').symm z, ?_⟩
  rw [← hpx, ← hz]
  apply (bcPt A (AlgebraicClosure K')).injective
  rw [MulEquiv.apply_symm_apply, bcPt_extPt, MulEquiv.apply_symm_apply, extPt_extPt]
  have hκ : AlgHom.restrictScalars K (Algebra.ofId K' (AlgebraicClosure K')) = κ.comp K'.val := by
    refine AlgHom.ext fun a => ?_
    exact (κ'.commutes a).symm
  rw [hκ]

/-- **SS1** (`HeightSplit.SemistableReductionThm`) from 3.6 and the number-field form of 3.3a:
reduct-split's `semistableReductionThm_of_leaves` with `h33` retyped; the only addition is the
`NumberField (F O)` instance at the one use of `h33` over `F O`. -/
theorem semistableReductionThm_of_leaves_nf (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) (hDown : DVRComapFinite) :
    ZInQ.HeightSplit.SemistableReductionThm := by
  classical
  intro K _ _ A
  set S := {O : ValuationSubring K | IsDiscreteValuationRing O ∧ ¬ HasSemistableReduction A O}
  have hS : S.Finite := hAA K A
  have hch : ∀ O : ValuationSubring K, ∃ K' : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K K' ∧ (IsDiscreteValuationRing O →
        ∀ O' : ValuationSubring K', IsDiscreteValuationRing O' →
          O'.comap (algebraMap K K') = O → SemistableNeronModels (A.baseChange K') O') := by
    intro O
    by_cases hO : IsDiscreteValuationRing O
    · obtain ⟨K', h1, h2⟩ := h36 K O A
      exact ⟨K', h1, fun _ => h2⟩
    · exact ⟨⊥, inferInstance, fun h => absurd h hO⟩
  choose F hFfin hF using hch
  let L₀ : IntermediateField K (AlgebraicClosure K) := ⨆ O ∈ hS.toFinset, F O
  haveI : FiniteDimensional K L₀ :=
    IntermediateField.finiteDimensional_iSup_of_finset' (fun O _ => hFfin O)
  haveI : NumberField L₀ := NumberField.of_module_finite K L₀
  refine ⟨L₀, inferInstance, inferInstance, inferInstance, fun 𝒩 h𝒩 => ?_⟩
  rw [hLG K A L₀ 𝒩 h𝒩]
  intro O'' hO''
  haveI := hO''
  haveI hO : IsDiscreteValuationRing (O''.comap (algebraMap K L₀)) := hDown K L₀ O'' hO''
  by_cases hOS : O''.comap (algebraMap K L₀) ∈ S
  · -- a place of bad reduction: go through `F O ≤ L₀`
    set O := O''.comap (algebraMap K L₀) with hOdef
    have hle : F O ≤ L₀ := le_iSup₂ (f := fun O _ => F O) O (hS.mem_toFinset.mpr hOS)
    letI : Algebra (F O) L₀ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    haveI : IsScalarTower K (F O) L₀ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : FiniteDimensional (F O) L₀ := by
      haveI := hFfin O
      exact FiniteDimensional.right K (F O) L₀
    haveI : NumberField (F O) := by
      haveI := hFfin O
      exact NumberField.of_module_finite K (F O)
    haveI hOi : IsDiscreteValuationRing (O''.comap (algebraMap (F O) L₀)) :=
      hDown (F O) L₀ O'' hO''
    have hc : (O''.comap (algebraMap (F O) L₀)).comap (algebraMap K (F O)) = O := by
      rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq]
    have h1 : SemistableNeronModels (A.baseChange (F O)) (O''.comap (algebraMap (F O) L₀)) :=
      hF O hO _ hOi hc
    have h2 := hasSemistableReduction_of hN _ _ h1
    have h3 := h33 (F O) (O''.comap (algebraMap (F O) L₀)) L₀ O'' rfl (A.baseChange (F O)) h2
    exact hasSemistableReduction_of hN O'' _
      (semistableNeronModels_transport (bcbcIso A (F O) L₀) (bcbcIso_isMonHom A (F O) L₀) h3)
  · -- a place of semistable reduction of `A`
    have hgood : HasSemistableReduction A (O''.comap (algebraMap K L₀)) := by
      by_contra hc
      exact hOS ⟨hO, hc⟩
    exact hasSemistableReduction_of hN O'' _ (h33 K _ L₀ O'' rfl A hgood)

/-- **SS3** from the number-field form of 3.3a, `DVRComapFinite` discharged (as
`semistablePersists_final`). -/
theorem semistablePersists_final_nf (h33 : SemistablePersistsDVRnf)
    (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal) :
    ZInQ.HeightSplit.SemistablePersists :=
  semistablePersists_of_leaves_nf h33 hN hLG dvrComapFinite

/-- **SS1** from 3.6 and the number-field form of 3.3a, `DVRComapFinite` discharged (as
`semistableReductionThm_final`). -/
theorem semistableReductionThm_final_nf (h36 : SemistableReductionDVRnf)
    (h33 : SemistablePersistsDVRnf) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) : ZInQ.HeightSplit.SemistableReductionThm :=
  semistableReductionThm_of_leaves_nf h36 h33 hN hLG hAA dvrComapFinite

/-- The two uses of 3.3a (SS1 and SS3, as in `TailZ15`) from the restricted printed leaf
`SemistablePersistsSHcp` and `StrictHenselizationPair`. -/
theorem ss1_ss3_of_cp (hSH : SemistablePersistsSHcp) (hPair : StrictHenselizationPair)
    (h36 : SemistableReductionDVR) (hN : NeronSchemeModelExistsDVR) (hLG : SemistableLocalGlobal)
    (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨semistableReductionThm_final_nf (reductionNF_of_general h36) (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair))
      hN hLG hAA,
    semistablePersists_final_nf (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG⟩

/-- **SS1 and SS3 from the restricted printed leaves only** (no general-field SGA 7 leaf):
`RaynaudSemistableSHcp`, `SemistablePersistsSHcp`, `StrictHenselizationPair`, Mumford and `[m]` étale.
(r6 and r8, the other uses of 4.7 and 3.6, are over every field and are not covered.) -/
theorem ss1_ss3_of_cp_full (hR : RaynaudSemistableSHcp) (hSH : SemistablePersistsSHcp)
    (hPair : StrictHenselizationPair) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hN : NeronSchemeModelExistsDVR)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨semistableReductionThm_final_nf
      (semistableReductionDVRnf_of_raynaudCP (raynaudSemistableCP_of_SH hR hPair hE) hM hE)
      (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG hAA,
    semistablePersists_final_nf (persistsNF_of_cp (semistablePersistsDVRcp_of_SH hSH hPair)) hN hLG⟩

end RouteBCP


/-! ## Fold check: the consumers in `TailZ15` / `TailZ9` with the three fields replaced -/

section FoldCheck

/-- The four consumers of the three fields in the OneProof chain, written with the same terms as
`TailZ15.researchLeaves9_of_open10` (r6, SS1, SS3) and `TailZ9` (r8), the three fields replaced by
the Route B theorems. New inputs: `RaynaudSemistableSH`, `SemistablePersistsSH`,
`StrictHenselizationPair`; the others are bundle fields already present. -/
theorem fold_uses (hRSH : RaynaudSemistableSH) (hPSH : SemistablePersistsSH)
    (hPair : StrictHenselizationPair) (hU : SemistableUnipotent) (hN : NeronSchemeModelExistsDVR)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    PkgI2.RaynaudCriterion.{0} ∧ PkgI2.GrothendieckMonodromy.{0} ∧
      ZInQ.HeightSplit.SemistableReductionThm ∧ ZInQ.HeightSplit.SemistablePersists :=
  ⟨raynaudCriterion_leaves (raynaudSemistable_of_SH_pair hRSH hPair hE) hU hN hM hE,
   grothendieckMonodromy_final' (semistableReductionDVR_of_SH_pair hRSH hPair hM hE) hU hN hM,
   semistableReductionThm_final (semistableReductionDVR_of_SH_pair hRSH hPair hM hE)
     (semistablePersistsDVR_of_SH_pair hPSH hPair) hN hLG hAA,
   semistablePersists_final (semistablePersistsDVR_of_SH_pair hPSH hPair) hN hLG⟩

/-- K1 alone (no Route B): the consumers with only `semistableReductionDVR` replaced. -/
theorem fold_uses_K1 (hR : RaynaudSemistable) (hP : SemistablePersistsDVR)
    (hU : SemistableUnipotent) (hN : NeronSchemeModelExistsDVR)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hLG : SemistableLocalGlobal) (hAA : SemistableAlmostAll) :
    PkgI2.GrothendieckMonodromy.{0} ∧ ZInQ.HeightSplit.SemistableReductionThm :=
  ⟨grothendieckMonodromy_final' (semistableReductionDVR_of_raynaud hR hM hE) hU hN hM,
   semistableReductionThm_final (semistableReductionDVR_of_raynaud hR hM hE) hP hN hLG hAA⟩

end FoldCheck

end ReductB

#print axioms ReductB.semistableReductionDVR_of_raynaud
#print axioms ReductB.strictHenselizationNeron_of_pair
#print axioms ReductB.three_fields_of_printed
#print axioms ReductB.raynaudSemistableCP_of_SH
#print axioms ReductB.semistablePersistsDVRcp_of_SH
#print axioms ReductB.semistablePersists_of_leaves_nf
#print axioms ReductB.ss1_ss3_of_cp
#print axioms ReductB.semistableReductionDVRnf_of_raynaudCP
#print axioms ReductB.ss1_ss3_of_cp_full
#print axioms ReductB.fold_uses
#print axioms ReductB.fold_uses_K1
