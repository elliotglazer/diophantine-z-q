import GTCA3

/-!
# gt-shpair, final part: `ReductGlue.StrictHenselizationPair` from one Néron leaf
-/

open IsLocalRing

set_option linter.style.haveILetI false

namespace GTSHPair

open ReductSplit ReductGlue

/-- `O₁ ⊇ O` is an unramified strictly henselian extension with `K₁/K` separable: `O₁` is a
strictly henselian DVR, `K₁/K` is separable algebraic, a uniformizer of `O` stays a uniformizer of
`O₁` (ramification index 1), and `κ(O₁)/κ(O)` is separable. In every characteristic these conditions
characterize `O → O₁` as the strict henselization of `O` up to isomorphism over `O` (report §3). -/
def IsSHSep {K K₁ : Type} [Field K] [Field K₁] [Algebra K K₁] (O : ValuationSubring K)
    (O₁ : ValuationSubring K₁) (hO : O₁.comap (algebraMap K K₁) = O) : Prop :=
  IsStrictlyHenselianDVR O₁ ∧ Algebra.IsSeparable K K₁ ∧
    (∀ ϖ : O, Irreducible ϖ → Irreducible (comapHom hO ϖ)) ∧
    (letI := (resMap hO).toAlgebra
     Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O₁))

/-- **LEAF `NeronBaseChangeStrictHenselization`** (Néron models commute with strict
henselization: Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.2 Prop. 2 (and §7.2 Thm. 1);
numbers UNVERIFIED). `O ⊆ K` a DVR (any characteristic, any residue field) and `O₁ ⊇ O` an
unramified strictly henselian extension with `K₁/K` separable (`IsSHSep`, which pins `O₁` as the
strict henselization `O^sh` up to isomorphism over `O`, report §3); then the base change of a Néron
model of `A` over `O` is a Néron model of `A_{K₁}` over `O₁`. It is a specialization of the chain's
`ReductGlue.NeronBaseChangeUnramifiedDVR` (`neronBaseChangeStrictHenselization_of_unramified`). -/
def NeronBaseChangeStrictHenselization : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K₁ : Type) [Field K₁] [Algebra K K₁] (O₁ : ValuationSubring K₁)
    (hO : O₁.comap (algebraMap K K₁) = O), IsSHSep O O₁ hO →
    ∀ (A : PkgI3.AbVar K) (𝒩 : GroupModelO A O), 𝒩.IsNeronModel → (bcDVR hO 𝒩).IsNeronModel

/-- The new leaf is a specialization of the chain's `NeronBaseChangeUnramifiedDVR`. -/
theorem neronBaseChangeStrictHenselization_of_unramified (h : NeronBaseChangeUnramifiedDVR) :
    NeronBaseChangeStrictHenselization := by
  intro K _ O _ K₁ _ _ O₁ hO hS
  haveI : IsDiscreteValuationRing O₁ := hS.1.1
  exact h K O K₁ O₁ hO hS.2.1 hS.2.2.1 hS.2.2.2

theorem isSHNeronExt_of (hN : NeronBaseChangeStrictHenselization) {K K₁ : Type} [Field K]
    [Field K₁] [Algebra K K₁] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {O₁ : ValuationSubring K₁} {hO : O₁.comap (algebraMap K K₁) = O} (h : IsSHSep O O₁ hO) :
    IsSHNeronExt O O₁ hO := by
  refine ⟨h.1, ?_, hN K O K₁ O₁ hO h⟩
  letI := (resMap hO).toAlgebra
  have := h.2.2.2
  exact Algebra.IsSeparable.isAlgebraic _ _

/-- **The valuation ring of the inertia field is an unramified strictly henselian extension.** -/
theorem isSHSep_inertia {K : Type} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) : IsSHSep O (wE (K := K) w) (hE_eq w hw) :=
  ⟨⟨isDVR_wE w hw, henselian_wE w, isSepClosed_wE w⟩, inertiaField_isSeparable w,
    fun ϖ hϖ => irreducible_comapHom w hw ϖ hϖ, res_isSeparable w hw⟩

/-- **Extension of a valuation ring to an extension field** (Chevalley; via Mathlib's
`IsLocalRing.exists_factor_valuationRing`). -/
theorem exists_comap_eq {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (O : ValuationSubring K) :
    ∃ w : ValuationSubring Ω, w.comap (algebraMap K Ω) = O := by
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K Ω).comp O.subtype)
  refine ⟨B, le_antisymm ?_ (fun x hx => hB ⟨x, hx⟩)⟩
  intro x hx
  by_contra hxO
  have hx0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
  have hinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxO
  have hunit : IsUnit (((algebraMap K Ω).comp O.subtype).codRestrict B.toSubring hB ⟨x⁻¹, hinv⟩) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K Ω x, hx⟩, Subtype.ext ?_⟩
    change algebraMap K Ω x⁻¹ * algebraMap K Ω x = 1
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  obtain ⟨u, hu⟩ := hloc.map_nonunit _ hunit
  apply hxO
  have h1 : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 :=
    congrArg (fun z : O => (z : K)) (Units.mul_inv u)
  rw [hu] at h1
  change x⁻¹ * _ = 1 at h1
  have : (((u⁻¹ : Oˣ) : O) : K) = x := by
    rw [← inv_inv x]; exact (eq_inv_of_mul_eq_one_right h1)
  rw [← this]; exact (u⁻¹ : Oˣ).1.2

/-- **Strict henselizations along a finite extension (commutative algebra, any characteristic, any
residue field).** For `O' ⊆ K'` over `O ⊆ K` with `K'/K` finite there are unramified strictly
henselian extensions `P ⊇ O`, `P' ⊇ O'` with separable fraction field extensions (`IsSHSep`), `E'/E`
finite and `P'` over `P`: the inertia fields of one valuation ring `w` of `K̄'` over `O'`, over `K`
and over `K'`. -/
theorem shPair (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (K' : Type) [Field K'] [Algebra K K'] [FiniteDimensional K K'] (O' : ValuationSubring K')
    [IsDiscreteValuationRing O'] (hO : O'.comap (algebraMap K K') = O) :
    ∃ (E E' : Type) (_ : Field E) (_ : Field E') (_ : Algebra K E) (_ : Algebra K' E')
      (_ : Algebra E E') (_ : Algebra K E') (_ : IsScalarTower K E E') (_ : IsScalarTower K K' E')
      (_ : FiniteDimensional E E') (P : ValuationSubring E) (P' : ValuationSubring E')
      (hP : P.comap (algebraMap K E) = O) (hP' : P'.comap (algebraMap K' E') = O'),
      IsSHSep O P hP ∧ IsSHSep O' P' hP' ∧ P'.comap (algebraMap E E') = P := by
  let Ω := AlgebraicClosure K'
  haveI : IsScalarTower K K' Ω := inferInstance
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed K', Algebra.IsAlgebraic.trans K K' Ω⟩
  obtain ⟨w, hw'⟩ := exists_comap_eq (Ω := Ω) O'
  have hw : w.comap (algebraMap K Ω) = O := by
    rw [IsScalarTower.algebraMap_eq K K' Ω, ← ValuationSubring.comap_comap, hw', hO]
  let E := inertiaField (K := K) w
  let E' := inertiaField (K := K') w
  let φ : E →+* E' :=
    { toFun := fun e => ⟨e, inertiaField_le w e.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra E E' := φ.toAlgebra
  haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq (fun c => by
    apply Subtype.ext
    change algebraMap K Ω c = algebraMap E' Ω (algebraMap K E' c)
    rw [IsScalarTower.algebraMap_apply K K' E', IsScalarTower.algebraMap_apply K K' Ω]
    rfl)
  -- finiteness of `E'/E`
  let f := IsScalarTower.toAlgHom K K' Ω
  haveI : FiniteDimensional K f.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField f).toLinearEquiv
  obtain ⟨t', ht'⟩ : f.fieldRange.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  let L := IntermediateField.adjoin E (t' : Set Ω)
  haveI : FiniteDimensional E L := IntermediateField.finiteDimensional_adjoin
    (fun z _ => (Algebra.IsIntegral.isIntegral (R := K) z).tower_top)
  let ψ : E' →ₗ[E] L :=
    { toFun := fun x => ⟨x, inertiaField_le_adjoin w t' ht' x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h =>
    Subtype.ext (congrArg (fun z : L => (z : Ω)) h)
  haveI : FiniteDimensional E E' := Module.Finite.of_injective ψ hψ
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, wE (K := K) w, wE (K := K') w,
    hE_eq w hw, hE_eq w hw', isSHSep_inertia w hw, isSHSep_inertia w hw', rfl⟩

/-- **`ReductGlue.StrictHenselizationPair` from the single Néron leaf** (the commutative algebra
is proved above, in every characteristic and for every residue field). -/
theorem strictHenselizationPair_of_neron (hN : NeronBaseChangeStrictHenselization) :
    StrictHenselizationPair := by
  intro K _ O _ K' _ _ _ O' _ hO
  obtain ⟨E, E', _, _, _, _, _, _, _, _, _, P, P', hP, hP', h1, h2, h3⟩ := shPair K O K' O' hO
  exact ⟨E, E', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, P, P', hP, hP',
    isSHNeronExt_of hN h1, isSHNeronExt_of hN h2, h3⟩

/-- The same from the chain's `NeronBaseChangeUnramifiedDVR`. -/
theorem strictHenselizationPair_of_unramified (hN : NeronBaseChangeUnramifiedDVR) :
    StrictHenselizationPair :=
  strictHenselizationPair_of_neron (neronBaseChangeStrictHenselization_of_unramified hN)

end GTSHPair

#print axioms GTSHPair.strictHenselizationPair_of_neron
