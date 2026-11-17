import ZInQKernel.OneProof.H.TailZ14

/-!
# unipotent-b: SGA 7 I Exp. IX Prop. 3.5 in printed form over a strictly henselian trait

Task unipotent-b (2026-11-14). The field `semistableUnipotent : ReductSplit.SemistableUnipotent`
(`ZInQKernel/OneProof/H/TailZ7.lean`), its strictly henselian form `ReductGlue.SemistableUnipotentSH`
and the leaf `ReductGlue.StrictHenselizationInside` (`ZInQKernel/OneProof/H/TailZ14.lean`) are
imported; §0 copies them verbatim and checks the copies by `rfl`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI2 (IsAbelianVariety IsInertia HasGoodReduction)
open ReductSplit ReductGlue ZInQ.HeightSplit

set_option linter.style.haveILetI false

namespace UnipotentB

/-! ## §0. Verbatim copies of the three Props (checked by `rfl`) -/

/-- verbatim copy of `ReductSplit.SemistableUnipotent` -/
def SemistableUnipotentCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

example : SemistableUnipotentCopy = ReductSplit.SemistableUnipotent := rfl

/-- verbatim copy of `ReductGlue.SemistableUnipotentSH` -/
def SemistableUnipotentSHCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

example : SemistableUnipotentSHCopy = ReductGlue.SemistableUnipotentSH := rfl

/-- verbatim copy of `ReductGlue.StrictHenselizationInside` -/
def StrictHenselizationInsideCopy : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O →
    ∃ (E : IntermediateField K Ω) (hE : (w.comap (algebraMap E Ω)).comap (algebraMap K E) = O),
      IsSHNeronExt O (w.comap (algebraMap E Ω)) hE ∧
      ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∀ x ∈ E, σ x = x

example : StrictHenselizationInsideCopy = ReductGlue.StrictHenselizationInside := rfl

/-! ## §1. Semistability over the residue field `k(s)` (SGA 7 IX Déf. 2.2/3.1 as printed) -/

section ResFibre

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {O : ValuationSubring K}

/-- `Spec k(s) → Spec O`. -/
abbrev sRes (O : ValuationSubring K) :
    Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶ Spec (CommRingCat.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O)))

/-- The special fibre `𝒩 ×_O k(s)` over the residue field itself (not its algebraic closure). -/
def specialFibre (𝒩 : GroupModelO A O) : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O))) :=
  (Over.pullback (sRes O)).obj 𝒩.G

instance (𝒩 : GroupModelO A O) : GrpObj (specialFibre 𝒩) := Functor.grpObjObj

/-- **Semistable special fibre over `k(s)`** (SGA 7 IX Déf. 2.2 and 3.1 read over the residue field
`k(s)`, as printed; locators UNVERIFIED): the identity component of `𝒩 ×_O k(s)` is an extension of
an abelian variety by a split torus (`HasSemiAbelianIdentityComponent`). Over a separably closed
`k(s)` every torus is split. -/
def IsSemistableRes (𝒩 : GroupModelO A O) : Prop :=
  HasSemiAbelianIdentityComponent (specialFibre 𝒩)

/-- `A` has semistable reduction at `O` in the printed sense: a Néron model whose special fibre over
`k(s)` is semistable. -/
def HasSemistableReductionRes (A : PkgI3.AbVar K) (O : ValuationSubring K) : Prop :=
  ∃ 𝒩 : GroupModelO A O, 𝒩.IsNeronModel ∧ IsSemistableRes 𝒩

/-- For an algebraically closed residue field, `k(s) → κ̄` is an isomorphism. -/
def resBarEquiv (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)] :
    IsLocalRing.ResidueField O ≃+* ResBarO O :=
  RingEquiv.ofBijective (algebraMap (IsLocalRing.ResidueField O) (ResBarO O))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

theorem spec_resBarEquiv_comp (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)] :
    Spec.map (CommRingCat.ofHom ((resBarEquiv O : _ ≃+* _) : _ →+* _)) ≫ sRes O =
      Spec.map (CommRingCat.ofHom (algebraMap O (ResBarO O))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **For an algebraically closed residue field, semistability over `k(s)` and over `κ̄` agree**
(fibre identification `κ̄ ≅ k(s)` + `semiAbelianFieldIsoInvariant`). -/
theorem isSemistableRes_iff (O : ValuationSubring K) [IsAlgClosed (IsLocalRing.ResidueField O)]
    (𝒩 : GroupModelO A O) : IsSemistableRes 𝒩 ↔ 𝒩.IsSemistable := by
  unfold IsSemistableRes GroupModelO.IsSemistable
  rw [semiAbelianFieldIsoInvariant _ _ (resBarEquiv O) (specialFibre 𝒩)]
  let E := pbCompIso _ _ _ (spec_resBarEquiv_comp O) (Grp.mk 𝒩.G)
  exact ⟨fun h => @hasSemiAbelian_of_iso _ _ _ (geomSpecialFibre 𝒩) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h,
    fun h => @hasSemiAbelian_of_iso _ _ (geomSpecialFibre 𝒩) _ _ Functor.grpObjObj
      (isoX E.symm) (inferInstanceAs (IsMonHom E.inv.hom.hom)) h⟩

theorem hasSemistableReductionRes_iff (O : ValuationSubring K)
    [IsAlgClosed (IsLocalRing.ResidueField O)] (A : PkgI3.AbVar K) :
    HasSemistableReductionRes A O ↔ HasSemistableReduction A O :=
  ⟨fun ⟨𝒩, h1, h2⟩ => ⟨𝒩, h1, (isSemistableRes_iff O 𝒩).mp h2⟩,
    fun ⟨𝒩, h1, h2⟩ => ⟨𝒩, h1, (isSemistableRes_iff O 𝒩).mpr h2⟩⟩

end ResFibre

/-! ## §2. The printed statement (leaf) and the strictly henselian field -/

/-- `I` acts unipotently on `T_ℓ`: every `σ ∈ I` has `σ - 1` nilpotent on `T_ℓ(A)`. -/
def InertiaUnipotent {K : Type} [Field K] (A : PkgI3.AbVar K) {Ω : Type} [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ → ∃ n : ℕ, (galTΩ A ℓ σ - 1) ^ n = 0

/-- **LEAF (printed form) `SemistableUnipotentPrinted`** (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5;
the number and the exact wording are from memory, **UNVERIFIED**; no network on this host). Setting
of SGA 7 IX §3 as printed: `O` a strictly henselian discrete valuation ring (a strictly local trait
`S`) with fraction field `K`, `K^s = Ω` a separable closure of `K`, `I` the inertia group (here,
`O` strictly henselian, `I = Gal(K^s/K)`; it is stated with the inertia group of the valuation `w`
of `Ω` over `O`, which is the unique one), `ℓ` a prime different from the residue characteristic,
`T_ℓ(A) = lim A(K^s)[ℓⁿ]`. Semistable reduction is read over the residue field `k(s)` itself
(`HasSemistableReductionRes`). Statement: `A` has semistable reduction iff `I` acts unipotently on
`T_ℓ(A)`, and in that case unipotently of echelon `≤ 2`: `(σ - 1)(τ - 1) = 0` on `T_ℓ(A)` for all
`σ, τ ∈ I`.

Restriction to `[CharZero K]` and `[PerfectField k(s)]` (so the leaf is the print restricted to a
subclass of its hypotheses, hence a consequence of it): in characteristic `0` an algebraic closure
is a separable closure, and over a perfect, separably closed `k(s)` the reading of "semistable"
over `k(s)` and over `κ̄` agree (`isSemistableRes_iff`, proved). Not restricted to number fields: a
strictly henselian DVR has separably closed residue field, so `[NumberField K]` would make the leaf
vacuous. -/
def SemistableUnipotentPrinted : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ [PerfectField (IsLocalRing.ResidueField O)],
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      (HasSemistableReductionRes A O ↔ InertiaUnipotent A w ℓ) ∧
      (HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0)

/-- **The used direction with the echelon clause** (a consequence of `SemistableUnipotentPrinted`). -/
def SemistableUnipotentPrintedEchelon : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O → ∀ [PerfectField (IsLocalRing.ResidueField O)],
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0

theorem echelon_of_printed (h : SemistableUnipotentPrinted) : SemistableUnipotentPrintedEchelon :=
  fun K _ _ O _ hO _ Ω _ _ _ w hw A ℓ _ hℓ => (h K O hO Ω w hw A ℓ hℓ).2

/-- `ReductGlue.SemistableUnipotentSH` with `[CharZero K]` and `[PerfectField k(s)]` added (the
strictly henselian field after the instances are added). -/
def SemistableUnipotentSH0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- `(σ - 1)² = 0` as an endomorphism gives the field's pointwise form. -/
theorem sq_form {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M] [Module ℤ_[ℓ] M] (f : M →ₗ[ℤ_[ℓ]] M)
    (h : (f - 1) * (f - 1) = 0) (t : M) : f (f t) - 2 • f t + t = 0 := by
  have := LinearMap.congr_fun h t
  simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
    LinearMap.zero_apply] at this
  rw [two_nsmul]
  rw [← this]
  abel

/-- **`SemistableUnipotentSH0` from the printed statement** (echelon clause at `σ = τ`; an algebraic
closure is a separable closure in characteristic `0`; `k(s)` separably closed and perfect is
algebraically closed, so semistability over `κ̄` is semistability over `k(s)`). -/
theorem semistableUnipotentSH0_of (h : SemistableUnipotentPrintedEchelon) :
    SemistableUnipotentSH0 := by
  intro K _ _ O _ _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsSepClosed (IsLocalRing.ResidueField O) := hO.2.2
  haveI : IsAlgClosed (IsLocalRing.ResidueField O) := IsSepClosed.isAlgClosed_of_perfectField _
  have hA' : HasSemistableReductionRes A O := (hasSemistableReductionRes_iff O A).mpr hA
  exact sq_form _ (h K O hO Ω w hw A ℓ hℓ hA' σ σ hσ hσ) t

/-! ## §3. The DVR field from the strictly henselian one -/

/-- `ReductSplit.SemistableUnipotent` with `[CharZero K]` and `[PerfectField k(s)]` added (the DVR
field after the instances are added). -/
def SemistableUnipotent0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

open ZInQ.Contrib.AbVarBC in
/-- **SGA 7 IX 3.5 over a general DVR (char. 0 field, perfect residue field) from the strictly
henselian form**: reduct-glue's `unipotentFromSH_of` with the two instances carried along. The
inertia field `E` has characteristic `0`, and its strictly henselian valuation ring has residue
field algebraic over `k(s)`, hence perfect (`Algebra.IsAlgebraic.perfectField`). -/
theorem semistableUnipotent0_of (hIn : StrictHenselizationInside) (hSH : SemistableUnipotentSH0) :
    SemistableUnipotent0 := by
  intro K _ _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  obtain ⟨E, hE, ⟨hSHP, halg, hbc⟩, hfix⟩ := hIn K O Ω w hw
  haveI : IsDiscreteValuationRing (w.comap (algebraMap E Ω)) := hSHP.1
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : PerfectField (IsLocalRing.ResidueField (w.comap (algebraMap E Ω))) := by
    letI := (resMap hE).toAlgebra
    haveI := halg
    exact Algebra.IsAlgebraic.perfectField (IsLocalRing.ResidueField O)
  have hAE : HasSemistableReduction (A.baseChange E) (w.comap (algebraMap E Ω)) := by
    obtain ⟨𝒩, h𝒩, hs⟩ := hA
    exact ⟨bcDVR hE 𝒩, hbc A 𝒩 h𝒩, (isSemistable_bcDVR_iff hE halg 𝒩).mp hs⟩
  have hℓP : IsUnit (ℓ : w.comap (algebraMap E Ω)) := by
    have := hℓ.map (comapHom hE)
    rwa [map_natCast] at this
  let σ₁ := toE E σ (hfix σ hσ)
  have hσ₁ : IsInertia w σ₁ := isInertia_toE E w σ (hfix σ hσ) hσ
  let φ : TΩ (A.baseChange E) Ω ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).toMonoidHom)
  let ψ : TΩ A Ω ℓ →ₗ[ℤ_[ℓ]] TΩ (A.baseChange E) Ω ℓ :=
    PkgI3.Tate.map (MonoidHom.toAdditive (bcPt A Ω).symm.toMonoidHom)
  have hφψ : φ (ψ t) = t := by
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((bcPt A Ω).symm (Additive.toMul (t.1 n)))) = t.1 n
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hcomm : ∀ s, φ (galTΩ (A.baseChange E) ℓ σ₁ s) = galTΩ A ℓ σ (φ s) := by
    intro s
    apply Subtype.ext
    funext n
    change Additive.ofMul (bcPt A Ω ((A.baseChange E).galAct σ₁ (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (bcPt A Ω (Additive.toMul (s.1 n))))
    rw [bcPt_galAct, toE_restrictScalars]
  have key := hSH E (w.comap (algebraMap E Ω)) hSHP Ω w rfl (A.baseChange E) hAE ℓ hℓP σ₁ hσ₁
    (ψ t)
  have := congrArg φ key
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm, hφψ] at this
  exact this

/-- **The DVR field (with the two instances) from the printed leaf and `StrictHenselizationInside`.** -/
theorem semistableUnipotent0_of_printed (hP : SemistableUnipotentPrinted)
    (hIn : StrictHenselizationInside) : SemistableUnipotent0 :=
  semistableUnipotent0_of hIn (semistableUnipotentSH0_of (echelon_of_printed hP))

/-- The old field implies the new one (the new field is weaker: it is the old one restricted). -/
theorem semistableUnipotent0_of_old (h : ReductSplit.SemistableUnipotent) : SemistableUnipotent0 :=
  fun K _ _ O _ _ Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t => h K O Ω w hw A hA ℓ hℓ σ hσ t

/-! ## §4. The unrestricted field (every field `K`): reduction to the printed leaf and two named Props

The kernel row r6 (`PkgI2.RaynaudCriterion`, proved by `ReductGlue.raynaudCriterion_leaves` from
`semistableUnipotent`) is quantified over every field, so the field itself cannot gain
`[CharZero K]` without breaking that proof (`docs/research/unipotent-b.md` §4). This section keeps
the field's statement and reduces it to the printed form over every field plus two named Props. -/

/-- **LEAF (printed form, every field) `SemistableUnipotentPrintedGen`** (SGA 7 I, Exp. IX, Prop. 3.5,
**UNVERIFIED** wording, as `SemistableUnipotentPrinted` but without `[CharZero K]` and
`[PerfectField k(s)]`): `O` strictly henselian, `Ω = K^s` a separable closure, semistability over
`k(s)`, `ℓ` invertible in `O`; semistable iff `I` unipotent, then of echelon `≤ 2`. -/
def SemistableUnipotentPrintedGen : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      (HasSemistableReductionRes A O ↔ InertiaUnipotent A w ℓ) ∧
      (HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0)

/-- `SemistableUnipotentPrintedGen` restricts to `SemistableUnipotentPrinted`. -/
theorem printed_of_printedGen (h : SemistableUnipotentPrintedGen) : SemistableUnipotentPrinted :=
  fun K _ _ O _ hO _ Ω _ _ _ w hw A ℓ _ hℓ => h K O hO Ω w hw A ℓ hℓ

/-- **GLUE `SemiAbelianDescendsSepClosed`** (the `k(s)` axis for imperfect residue fields). For a
discrete valuation ring `O` with separably closed residue field `k`, a group model whose geometric
special fibre (over `κ̄`, an algebraic closure of `k`, purely inseparable over `k`) has semi-abelian
identity component already has it over `k`. Needs: the maximal torus of the smooth connected
commutative group `G⁰_k` exists over `k` (SGA 3 II, Exp. XIV, Thm 1.1, UNVERIFIED) and its base change
is the maximal torus of `G⁰_κ̄`; the quotient `G⁰_k / T` is smooth, connected and proper after base
change to `κ̄`, hence an abelian variety (proper descends along field extensions, EGA IV₂ 2.7.1);
tori over a separably closed field are split. Proved here when `k` is perfect
(`isSemistableRes_iff`). Not in Mathlib 4.35. -/
def SemiAbelianDescendsSepClosed : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsSepClosed (IsLocalRing.ResidueField O) →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsSemistable → IsSemistableRes 𝒩

/-- `SemiAbelianDescendsSepClosed` holds for perfect residue fields (proved). -/
theorem semiAbelianDescends_of_perfect (K : Type) [Field K] (O : ValuationSubring K)
    [PerfectField (IsLocalRing.ResidueField O)] (hk : IsSepClosed (IsLocalRing.ResidueField O))
    (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O) (h : 𝒩.IsSemistable) : IsSemistableRes 𝒩 := by
  haveI := hk
  haveI : IsAlgClosed (IsLocalRing.ResidueField O) := IsSepClosed.isAlgClosed_of_perfectField _
  exact (isSemistableRes_iff O 𝒩).mpr h

/-- **GLUE `SepClosureTateRestrict`** (the `K^s` axis). `Ω` an algebraic closure of `K`,
`K^s ⊆ Ω` the separable closure, `w` a valuation ring of `Ω`, `ℓ` invertible in `K`. Every `σ` in
the inertia group of `w` restricts to `σ_s ∈ Aut(K^s/K)` in the inertia group of `w ∩ K^s`, and
`A(K^s) → A(Ω)` induces a `ℤ_ℓ`-linear surjection `T_ℓ(A)_{K^s} → T_ℓ(A)_Ω` intertwining `σ_s` and
`σ`. Needs: `AlgEquiv.restrictNormal` (`K^s/K` is normal) and the residue map of `w ∩ K^s ⊆ w` for
the inertia condition; `A[ℓⁿ]` étale (bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`) and the
version of `ReductGlue.exists_lift_of_etale` with `Ω` separably closed (separable elements of `Ω`
lie in `K^s`) for surjectivity on `A(·)[ℓⁿ]`, then the lift to `T_ℓ` level by level (the transition
maps are injective on the image). In characteristic `0`, `K^s = Ω`. -/
def SepClosureTateRestrict : Prop :=
  ∀ (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
        IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
        ∃ φ : TΩ A (separableClosure K Ω) ℓ →ₗ[ℤ_[ℓ]] TΩ A Ω ℓ, Function.Surjective φ ∧
          ∀ s, φ (galTΩ A ℓ σs s) = galTΩ A ℓ σ (φ s)

/-- **The strictly henselian field (unchanged statement, every field) from the printed leaf over every
field and the two named Props.** -/
theorem semistableUnipotentSH_of_gen (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hT : SepClosureTateRestrict) :
    ReductGlue.SemistableUnipotentSH := by
  intro K _ O _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hA' : HasSemistableReductionRes A O := by
    obtain ⟨𝒩, h1, h2⟩ := hA
    exact ⟨𝒩, h1, hD K O hO.2.2 A 𝒩 h2⟩
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isUnit O hℓ
  obtain ⟨σs, hσs, φ, hφ, hcomm⟩ := hT K Ω w A ℓ hℓK σ hσ
  have hws : (w.comap (algebraMap (separableClosure K Ω) Ω)).comap
      (algebraMap K (separableClosure K Ω)) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have key := (hP K O hO (separableClosure K Ω) _ hws A ℓ hℓ).2 hA' σs σs hσs hσs
  obtain ⟨s, rfl⟩ := hφ t
  have h2 := congrArg φ (sq_form _ key s)
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm] at h2
  exact h2

/-- **The field `semistableUnipotent` (unchanged statement, every field)** from the printed leaf over
every field, `StrictHenselizationInside` and the two named Props. -/
theorem semistableUnipotent_of_gen (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hT : SepClosureTateRestrict)
    (hIn : StrictHenselizationInside) : ReductSplit.SemistableUnipotent :=
  unipotentFromSH_of hIn (semistableUnipotentSH_of_gen hP hD hT)

/-! ## §5. `SepClosureTateRestrict` from two smaller Props -/

/-- **A Tate-module surjectivity criterion**: an injective `φ : M →+ N` onto the `ℓ`-power torsion
of `N` induces a surjection `T_ℓ M → T_ℓ N`. -/
theorem tateMap_surjective {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]
    (φ : M →+ N) (hinj : Function.Injective φ)
    (hsurj : ∀ (n : ℕ) (y : N), (ℓ ^ n) • y = 0 → ∃ x : M, φ x = y) :
    Function.Surjective (PkgI3.Tate.map (ℓ := ℓ) φ) := by
  intro t
  choose s hs using fun n => hsurj n (t.1 n) (PkgI3.Tate.pow_smul_eq_zero t.2 n)
  refine ⟨⟨s, ?_, fun n => ?_⟩, Subtype.ext (funext fun n => hs n)⟩
  · apply hinj
    rw [hs, map_zero]
    exact t.2.1
  · apply hinj
    rw [map_nsmul, hs, hs]
    exact t.2.2 n

/-- **GLUE `InertiaRestrictSepClosure`**: an element of the inertia group of `w` in `Aut(Ω/K)`
restricts to an element of the inertia group of `w ∩ K^s` in `Aut(K^s/K)` (`K^s/K` is normal;
decomposition and inertia are compatible with restriction to a normal subextension; Serre,
*Corps locaux*, I §7, UNVERIFIED locator). -/
def InertiaRestrictSepClosure : Prop :=
  ∀ (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω), IsInertia w σ →
      ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
        IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
        ∀ x : separableClosure K Ω, (σs x : Ω) = σ x

/-- **GLUE `TorsionFromSepClosure`**: for `m` invertible in `K`, every point of `A(Ω)[m]` comes from
`A(K^s)` (`A[m]` is étale over `K`, bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`; the points of an
étale `K`-scheme with values in `Ω` have separable coordinates, hence come from `K^s`: the
separably closed version of `ReductGlue.exists_lift_of_etale`). -/
def TorsionFromSepClosure : Prop :=
  ∀ (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ), (m : K) ≠ 0 → ∀ x : A.Pt Ω, x ^ m = 1 →
      ∃ y : A.Pt (separableClosure K Ω),
        ZInQ.Contrib.AbVarBC.extPt A (IsScalarTower.toAlgHom K (separableClosure K Ω) Ω) y = x

open ZInQ.Contrib.AbVarBC in
/-- **`SepClosureTateRestrict` from `InertiaRestrictSepClosure` and `TorsionFromSepClosure`.** -/
theorem sepClosureTateRestrict_of (hI : InertiaRestrictSepClosure) (hT : TorsionFromSepClosure) :
    SepClosureTateRestrict := by
  intro K _ Ω _ _ _ w A ℓ _ hℓ σ hσ
  obtain ⟨σs, hσs, hres⟩ := hI K Ω w σ hσ
  let κ := IsScalarTower.toAlgHom K (separableClosure K Ω) Ω
  let φ0 : Additive (A.Pt (separableClosure K Ω)) →+ Additive (A.Pt Ω) :=
    MonoidHom.toAdditive (extPt A κ)
  refine ⟨σs, hσs, PkgI3.Tate.map φ0, ?_, fun s => ?_⟩
  · refine tateMap_surjective φ0 (extPt_injective A κ) fun n y hy => ?_
    have hℓn : ((ℓ ^ n : ℕ) : K) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hℓ
    obtain ⟨x, hx⟩ := hT K Ω A (ℓ ^ n) hℓn (Additive.toMul y) (by
      have : Additive.toMul ((ℓ ^ n) • y) = 1 := by rw [hy]; rfl
      rwa [toMul_nsmul] at this)
    exact ⟨Additive.ofMul x, by change Additive.ofMul (extPt A κ x) = y; rw [hx]; rfl⟩
  · apply Subtype.ext
    funext n
    change Additive.ofMul (extPt A κ (A.galAct σs (Additive.toMul (s.1 n)))) =
      Additive.ofMul (A.galAct σ (extPt A κ (Additive.toMul (s.1 n))))
    rw [extPt_galAct A κ σs σ (fun x => hres x)]

/-- **The field (unchanged statement) from the printed leaf over every field,
`StrictHenselizationInside`, `SemiAbelianDescendsSepClosed` and the two smaller Props.** -/
theorem semistableUnipotent_of_gen' (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hI : InertiaRestrictSepClosure)
    (hT : TorsionFromSepClosure) (hIn : StrictHenselizationInside) :
    ReductSplit.SemistableUnipotent :=
  semistableUnipotent_of_gen hP hD (sepClosureTateRestrict_of hI hT) hIn


/-! ## §6. The two smaller Props proved (`TorsionFromSepClosure` from the bundle leaf
`AvSplit.T4.MulEtaleAbelianScheme`) -/

section SepClosure

open ZInQ.Contrib.AbVarBC

variable {K : Type} [Field K]

/-- Elements in the image of an étale `K`-algebra in any field `Ω` are separable over `K`
(`ReductGlue.isSeparable_of_etale` with `Ω` for `K̄`, same proof). -/
theorem isSeparable_of_etale' {Ω : Type} [Field Ω] [Algebra K Ω] {R : Type} [CommRing R]
    [Algebra K R] [Algebra.Etale K R] (f : R →ₐ[K] Ω) (r : R) : IsSeparable K (f r) := by
  haveI : Module.Finite K R := Algebra.FormallyUnramified.finite_of_free K R
  haveI : Algebra.IsIntegral K f.range := by
    refine ⟨fun ⟨y, hy⟩ => ?_⟩
    obtain ⟨s, rfl⟩ := hy
    have : IsIntegral K (f.rangeRestrict s) := (Algebra.IsIntegral.isIntegral (R := K) s).map _
    exact this
  let E : IntermediateField K Ω :=
    Subalgebra.toIntermediateField' f.range (isField_of_isIntegral_of_isField' (Field.toIsField K))
  let f' : R →ₐ[K] E := f.codRestrict E.toSubalgebra (fun r => ⟨r, rfl⟩)
  have hsurj : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    obtain ⟨r, hr⟩ : y ∈ f.range := hy
    exact ⟨r, Subtype.ext hr⟩
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_surjective f' hsurj
  have : Algebra.FiniteType K E := Algebra.FiniteType.of_surjective f' hsurj
  have : Algebra.IsSeparable K E := Algebra.FormallyUnramified.isSeparable K E
  have h := Algebra.IsSeparable.isSeparable K (f' r)
  have h2 : IsSeparable K (E.val (f' r)) := IsSeparable.map E.val Subtype.val_injective h
  exact h2

/-- **Points of an étale `K`-scheme with values in a field `Ω` come from the separable closure
`K^s ⊆ Ω`** (`ReductGlue.exists_lift_of_etale` with `K^s` for the algebraically closed field; the
coordinates are separable over `K`). -/
theorem exists_lift_of_etale_sep {Ω₂ : Type} [Field Ω₂] [Algebra K Ω₂]
    (X : Over (Spec (CommRingCat.of K))) [Etale X.hom]
    (q : Spec (CommRingCat.of Ω₂) ⟶ X.left)
    (hq : q ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :
    ∃ p : Spec (CommRingCat.of (separableClosure K Ω₂)) ⟶ X.left,
      Spec.map (CommRingCat.ofHom (algebraMap (separableClosure K Ω₂) Ω₂)) ≫ p = q ∧
        p ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K (separableClosure K Ω₂))) := by
  classical
  let Ω := separableClosure K Ω₂
  let κ : Ω →ₐ[K] Ω₂ := IsScalarTower.toAlgHom K Ω Ω₂
  let pt : X.left := q (IsLocalRing.closedPoint Ω₂)
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ pt) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : s = IsLocalRing.closedPoint Ω₂ :=
      Subsingleton.elim (α := PrimeSpectrum Ω₂) _ _
    rw [this]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q hrange
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of Ω₂ := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω₂) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq]
  have hθet : RingHom.Etale θ.hom := by
    have : Etale (Spec.map θ) := by rw [hθ]; infer_instance
    exact HasRingHomProperty.Spec_iff.mp this
  letI : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  have : Algebra.Etale K Γ(X.left, U) := hθet
  let f : Γ(X.left, U) →ₐ[K] Ω₂ :=
    { φ.hom with
      commutes' := fun a => congrArg (fun g => CommRingCat.Hom.hom g a) hcomp }
  have : Module.Finite K Γ(X.left, U) := Algebra.FormallyUnramified.finite_of_free K _
  have hsep : ∀ r, IsSeparable K (φ.hom r) := fun r => isSeparable_of_etale' f r
  let ψ0 : Γ(X.left, U) → Ω := fun r => ⟨φ.hom r, mem_separableClosure_iff.mpr (hsep r)⟩
  have hψ0 : ∀ r, (κ : Ω →+* Ω₂) (ψ0 r) = φ.hom r := fun r => rfl
  have hκinj : Function.Injective (κ : Ω →+* Ω₂) := (κ : Ω →+* Ω₂).injective
  let ψ : Γ(X.left, U) →+* Ω :=
    { toFun := ψ0
      map_one' := hκinj (by rw [hψ0, map_one, map_one])
      map_mul' := fun a b => hκinj (by rw [hψ0, map_mul, map_mul, hψ0, hψ0])
      map_zero' := hκinj (by rw [hψ0, map_zero, map_zero])
      map_add' := fun a b => hκinj (by rw [hψ0, map_add, map_add, hψ0, hψ0]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (κ : Ω →+* Ω₂) = φ := by
    ext r
    exact hψ0 r
  have hlift : Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫
      (Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι) = q := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, hql]
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ e.inv ≫ U.ι, hlift, ?_⟩
  haveI := epi_spec_map_field (κ : Ω →+* Ω₂)
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)))).1
  rw [← Category.assoc, hlift, hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, κ.comp_algebraMap]

/-- **Torsion points of order prime to the characteristic come from `K^s`** (from `[m]` étale, the
bundle leaf `AvSplit.T4.MulEtaleAbelianScheme`; same proof as `ReductGlue.torsion_descends_etale`). -/
theorem torsion_from_sepClosure (hE : AvSplit.T4.MulEtaleAbelianScheme) (Ω : Type) [Field Ω]
    [Algebra K Ω] (A : PkgI3.AbVar K) (m : ℕ) (hm : (m : K) ≠ 0) (x : A.Pt Ω) (hx : x ^ m = 1) :
    ∃ y : A.Pt (separableClosure K Ω),
      extPt A (IsScalarTower.toAlgHom K (separableClosure K Ω) Ω) y = x := by
  haveI : PkgI2.IsAbelianScheme (Grp.mk A.X) := ⟨inferInstanceAs (IsProper A.X.hom),
    inferInstanceAs (Smooth A.X.hom), inferInstanceAs (GeometricallyConnected A.X.hom)⟩
  have het : Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left) :=
    hE K (Grp.mk A.X) m (isUnit_iff_ne_zero.mpr hm)
  let κ := IsScalarTower.toAlgHom K (separableClosure K Ω) Ω
  let M : A.X ⟶ A.X := 𝟙 A.X ^ m
  let P : Over (Spec (CommRingCat.of K)) := Over.mk (pullback.snd M.left (η[A.X]).left)
  haveI : Etale P.hom := by
    change Etale (pullback.snd M.left (η[A.X]).left)
    infer_instance
  have hxm : x ≫ M = 1 := by rw [comp_pow_one]; exact hx
  have hw : x.left ≫ M.left =
      (PkgI3.AbVar.ptObj (K := K) Ω).hom ≫ (η[A.X]).left := by
    have h1 := congrArg Over.Hom.left hxm
    rw [Over.comp_left] at h1
    rw [h1]
    change (toUnit _ ≫ η[A.X]).left = _
    rw [Over.comp_left]
    congr 1
  let z : Spec (CommRingCat.of Ω) ⟶ P.left := pullback.lift x.left _ hw
  have hz : z ≫ P.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) :=
    pullback.lift_snd _ _ _
  obtain ⟨p0, hp0, hp0g⟩ := exists_lift_of_etale_sep P z hz
  have hpr : pullback.fst M.left (η[A.X]).left ≫ A.X.hom = P.hom := by
    change _ = pullback.snd M.left (η[A.X]).left
    rw [← Over.w M, ← Category.assoc, pullback.condition, Category.assoc, Over.w η[A.X]]
    simp
  let p : A.Pt (separableClosure K Ω) :=
    Over.homMk (p0 ≫ pullback.fst M.left (η[A.X]).left) (by
      change (p0 ≫ pullback.fst M.left (η[A.X]).left) ≫ A.X.hom = _
      rw [Category.assoc, hpr, hp0g]
      rfl)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : separableClosure K Ω →+* Ω)) ≫
    p0 ≫ pullback.fst M.left (η[A.X]).left = x.left
  rw [← Category.assoc]
  erw [hp0]
  exact pullback.lift_fst _ _ _


/-- **`TorsionFromSepClosure` from the bundle leaf `MulEtaleAbelianScheme`.** -/
theorem torsionFromSepClosure_of (hE : AvSplit.T4.MulEtaleAbelianScheme) : TorsionFromSepClosure :=
  fun _ _ Ω _ _ _ A m hm x hx => torsion_from_sepClosure hE Ω A m hm x hx

end SepClosure

open scoped Pointwise in
theorem inertiaRestrict' (K : Type) [Field K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (hσ : IsInertia w σ) :
      ∃ σs : separableClosure K Ω ≃ₐ[K] separableClosure K Ω,
        IsInertia (w.comap (algebraMap (separableClosure K Ω) Ω)) σs ∧
        ∀ x : separableClosure K Ω, (σs x : Ω) = σ x := by
  set E := separableClosure K Ω
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  let σs : E ≃ₐ[K] E := σ.restrictNormal E
  have hres : ∀ x : E, (σs x : Ω) = σ x := fun x => AlgEquiv.restrictNormal_commutes σ E x
  refine ⟨σs, ?_, hres⟩
  obtain ⟨hd, hi⟩ := hσ
  have hs : σ • w = w := hd
  set w' := w.comap (algebraMap E Ω)
  have hd' : σs ∈ w'.decompositionSubgroup K := by
    show σs • w' = w'
    ext y
    simp only [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul, Set.mem_smul_set,
      AlgEquiv.smul_def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show ((σs z : E) : Ω) ∈ w
      rw [hres, ← hs]
      exact ⟨(z : Ω), hz, rfl⟩
    · intro hy
      refine ⟨σs.symm y, ?_, σs.apply_symm_apply y⟩
      have hy' : ((y : E) : Ω) ∈ σ • w := by rw [hs]; exact hy
      have hy'' : ((y : E) : Ω) ∈ σ • (w : Set Ω) := by
        rw [← ValuationSubring.coe_pointwise_smul]; exact hy'
      obtain ⟨u, hu, hu'⟩ := Set.mem_smul_set.mp hy''
      rw [AlgEquiv.smul_def] at hu'
      have : ((σs.symm y : E) : Ω) = u := by
        apply σ.injective
        rw [← hres, σs.apply_symm_apply]
        exact hu'.symm
      show ((σs.symm y : E) : Ω) ∈ w
      rw [this]; exact hu
  refine ⟨hd', ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi ⊢
  refine RingEquiv.ext fun r => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  -- the image of `a` in `w`
  let b : w := ⟨((a : E) : Ω), a.2⟩
  have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w b)
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w b =
    IsLocalRing.residue w b at h1
  change (⟨σs, hd'⟩ : w'.decompositionSubgroup K) • IsLocalRing.residue w' a =
    IsLocalRing.residue w' a
  rw [← IsLocalRing.ResidueField.residue_smul] at h1 ⊢
  -- `c = σs a - a` maps into the maximal ideal of `w`
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1 ⊢
  let f : w' →+* w :=
    { toFun := fun x => ⟨((x : E) : Ω), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hfc : f ((⟨σs, hd'⟩ : w'.decompositionSubgroup K) • a - a) =
      (⟨σ, hd⟩ : w.decompositionSubgroup K) • b - b := by
    apply Subtype.ext
    change ((σs (a : E) : E) : Ω) - ((a : E) : Ω) = σ ((a : E) : Ω) - ((a : E) : Ω)
    rw [hres]
  intro hu
  exact h1 (by rw [← hfc]; exact hu.map f)

/-- **`InertiaRestrictSepClosure`, PROVED** (restriction `AlgEquiv.restrictNormal` to the Galois
extension `K^s/K`; decomposition by `σ • w = w`; inertia through `w ∩ K^s → w`, which maps units to
units). -/
theorem inertiaRestrictSepClosure : InertiaRestrictSepClosure := by
  intro K _ Ω _ _ _ w σ hσ
  exact inertiaRestrict' K Ω w σ hσ


/-- **The field `semistableUnipotent`, unchanged statement, over every field**, from the printed leaf
over every field, `StrictHenselizationInside`, the bundle leaf `MulEtaleAbelianScheme` and the one
glue `SemiAbelianDescendsSepClosed` (needed only for imperfect residue fields). -/
theorem semistableUnipotent_of_printedGen (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hIn : StrictHenselizationInside) : ReductSplit.SemistableUnipotent :=
  semistableUnipotent_of_gen' hP hD inertiaRestrictSepClosure (torsionFromSepClosure_of hE) hIn

/-- **The strictly henselian field `SemistableUnipotentSH`, unchanged statement**, likewise. -/
theorem semistableUnipotentSH_of_printedGen (hP : SemistableUnipotentPrintedGen)
    (hD : SemiAbelianDescendsSepClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) :
    ReductGlue.SemistableUnipotentSH :=
  semistableUnipotentSH_of_gen hP hD
    (sepClosureTateRestrict_of inertiaRestrictSepClosure (torsionFromSepClosure_of hE))


/-- **Variant `SemistableUnipotentPrintedGeom`**: `SemistableUnipotentPrintedGen` with semistability
read over `κ̄` (`HasSemistableReduction`, the geometric special fibre). It is a LEAF only if SGA 7 IX
defines semistable reduction through the geometric special fibre (UNVERIFIED; then
`SemiAbelianDescendsSepClosed` is not needed); otherwise it is `SemistableUnipotentPrintedGen` plus
`SemiAbelianDescendsSepClosed` and its converse. -/
def SemistableUnipotentPrintedGeom : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      (HasSemistableReduction A O ↔ InertiaUnipotent A w ℓ) ∧
      (HasSemistableReduction A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0)

/-- **The field (unchanged statement) from the geometric variant, `StrictHenselizationInside` and the
bundle leaf `MulEtaleAbelianScheme`; no glue.** -/
theorem semistableUnipotent_of_printedGeom (hP : SemistableUnipotentPrintedGeom)
    (hE : AvSplit.T4.MulEtaleAbelianScheme) (hIn : StrictHenselizationInside) :
    ReductSplit.SemistableUnipotent := by
  refine unipotentFromSH_of hIn ?_
  intro K _ O _ hO Ω _ _ _ w hw A hA ℓ _ hℓ σ hσ t
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hℓK : (ℓ : K) ≠ 0 := natCast_ne_zero_of_isUnit O hℓ
  obtain ⟨σs, hσs, φ, hφ, hcomm⟩ := sepClosureTateRestrict_of inertiaRestrictSepClosure
    (torsionFromSepClosure_of hE) K Ω w A ℓ hℓK σ hσ
  have hws : (w.comap (algebraMap (separableClosure K Ω) Ω)).comap
      (algebraMap K (separableClosure K Ω)) = O := by
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]
  have key := (hP K O hO (separableClosure K Ω) _ hws A ℓ hℓ).2 hA σs σs hσs hσs
  obtain ⟨s, rfl⟩ := hφ t
  have h2 := congrArg φ (sq_form _ key s)
  simp only [map_add, map_sub, map_nsmul, map_zero, hcomm] at h2
  exact h2

end UnipotentB

#print axioms UnipotentB.isSemistableRes_iff
#print axioms UnipotentB.echelon_of_printed
#print axioms UnipotentB.semistableUnipotentSH0_of
#print axioms UnipotentB.semistableUnipotent0_of
#print axioms UnipotentB.semistableUnipotent0_of_printed
#print axioms UnipotentB.semistableUnipotent0_of_old
#print axioms UnipotentB.printed_of_printedGen
#print axioms UnipotentB.semiAbelianDescends_of_perfect
#print axioms UnipotentB.semistableUnipotentSH_of_gen
#print axioms UnipotentB.semistableUnipotent_of_gen
#print axioms UnipotentB.sepClosureTateRestrict_of
#print axioms UnipotentB.semistableUnipotent_of_gen'
#print axioms UnipotentB.exists_lift_of_etale_sep
#print axioms UnipotentB.torsionFromSepClosure_of
#print axioms UnipotentB.inertiaRestrictSepClosure
#print axioms UnipotentB.semistableUnipotent_of_printedGen
#print axioms UnipotentB.semistableUnipotentSH_of_printedGen
#print axioms UnipotentB.semistableUnipotent_of_printedGeom
