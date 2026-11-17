import GTCA2

/-!
# gt-shpair, part E: separable residue fields, and strict henselizations along a finite extension
(any characteristic, any residue field)
-/

open IsLocalRing Polynomial IntermediateField

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GTSHPair

open ReductSplit ReductGlue

section ResSep

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
  [IsAlgClosure K Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]

/-- **Elements of the inertia field have separable residues** (from `key_finite`, part (b)). -/
theorem sep_poly (hw : w.comap (algebraMap K Ω) = O) (x : Ω)
    (hxE : x ∈ inertiaField (K := K) w) (hxw : x ∈ w) :
    ∃ f : O[X], (f.map (residue O)).Separable ∧
      (f.map ((algebraMap K Ω).comp O.subtype)).eval x ∈ w.nonunits := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨M, ⟨hfd, hgal⟩, hxM, hfix⟩ := hxE
  haveI := hfd
  haveI := hgal
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let W := w.comap (algebraMap M Ω)
  have hAW : ∀ a : O, algebraMap O M a ∈ W := fun a => mem_w_of_mem w hw a
  have hctr : ∀ a : O, algebraMap O M a ∈ W.nonunits ↔ a ∈ maximalIdeal O := by
    intro a
    rw [nonunits_comap]
    exact nonunits_iff_of w hw a
  have hfix' : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ ⟨x, hxM⟩ = ⟨x, hxM⟩ := by
    intro σ hσ
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : M, τ (algebraMap M Ω m) = algebraMap M Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hcond : CondM w M τ := by
      intro y hyM hyw
      have h1 := hσ ⟨y, hyM⟩ hyw
      rw [nonunits_comap, map_sub, ← hτ] at h1
      exact h1
    have := hfix τ hcond
    apply (algebraMap M Ω).injective
    rw [← hτ]
    exact this
  obtain ⟨f, hf, hfx⟩ := (key_finite (K := K) O W hAW hctr ϖ hϖ ⟨x, hxM⟩ hfix' hxw).2
  refine ⟨f, hf, ?_⟩
  rw [nonunits_comap] at hfx
  convert hfx using 1
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  rfl

/-- **The residue extension of the inertia field is separable.** -/
theorem res_isSeparable (hw : w.comap (algebraMap K Ω) = O) :
    letI := (resMap (hE_eq w hw)).toAlgebra
    Algebra.IsSeparable (ResidueField O) (ResidueField (wE (K := K) w)) := by
  letI := (resMap (hE_eq w hw)).toAlgebra
  constructor
  intro r
  obtain ⟨a, rfl⟩ := residue_surjective r
  obtain ⟨f, hf, hfx⟩ := sep_poly w hw (ιΩ w a) a.1.2 a.2
  have h0 : aeval (residue _ a) (f.map (residue O)) = 0 := by
    rw [aeval_def, eval₂_map]
    have e1 : (algebraMap (ResidueField O) (ResidueField (wE (K := K) w))).comp (residue O) =
        (residue _).comp (comapHom (hE_eq w hw)) := by
      ext b; exact resMap_residue (hE_eq w hw) b
    rw [e1, ← hom_eval₂, residue_eq_zero_iff, mem_max_comap_iff]
    convert hfx using 1
    rw [Polynomial.eval_map]
    change ιΩ w _ = _
    rw [hom_eval₂]
    rfl
  exact hf.of_dvd (minpoly.dvd _ _ h0)

/-- The inertia field is separable over `K`. -/
theorem inertiaField_isSeparable : Algebra.IsSeparable K (inertiaField (K := K) w) :=
  isSeparable_of_forall _ (fun x hx => by
    obtain ⟨M, hM, hxM, -⟩ := hx
    exact hM.isSeparable hxM)

end ResSep

section Pair

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)

/-- The elements of `Gal(M/K)` acting trivially modulo `𝔪_w` on `w ∩ M`, as a submonoid. -/
def inertSub (M : IntermediateField K Ω) : Submonoid (M ≃ₐ[K] M) where
  carrier := {σ | ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits}
  one_mem' := by
    intro y _
    simp only [AlgEquiv.one_apply, sub_self]
    exact zero_mem _
  mul_mem' := by
    intro σ ρ hσ hρ y hy
    have h1 := hρ y hy
    have hρy : ((ρ y : M) : Ω) ∈ w := by
      have : ((ρ y : M) : Ω) = (y : Ω) + (((ρ y : M) : Ω) - y) := by ring
      rw [this]; exact add_mem hy (ValuationSubring.nonunits_le h1)
    have h2 := hσ (ρ y) hρy
    have : (((σ * ρ) y : M) : Ω) - y = (((σ (ρ y)) : M) : Ω) - (ρ y : M) +
        (((ρ y : M) : Ω) - y) := by
      rw [AlgEquiv.mul_apply]; ring
    rw [this]
    exact add_mem h2 h1

/-- The inertia subgroup of `Gal(M/K)` (a submonoid of a finite group is a subgroup). -/
def inertM (M : IntermediateField K Ω) [FiniteDimensional K M] : Subgroup (M ≃ₐ[K] M) :=
  { inertSub w M with
    inv_mem' := by
      intro σ hσ
      have hn := orderOf_pos σ
      have h : σ⁻¹ = σ ^ (orderOf σ - 1) := by
        symm
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
      change σ⁻¹ ∈ inertSub w M
      rw [h]
      exact (inertSub w M).pow_mem hσ _ }

theorem mem_inertM {M : IntermediateField K Ω} [FiniteDimensional K M] {σ : M ≃ₐ[K] M} :
    σ ∈ inertM w M ↔ ∀ y : M, (y : Ω) ∈ w → ((σ y : M) : Ω) - y ∈ w.nonunits := Iff.rfl

/-- **`x^(q^n) ∈ F` and `x` separable over `F` imply `x ∈ F`.** -/
theorem mem_range_of_pow_mem {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]
    {x : E} (hsep : IsSeparable F x) (n : ℕ) (h : x ^ q ^ n ∈ (algebraMap F E).range) :
    x ∈ (algebraMap F E).range := by
  haveI : Algebra.IsSeparable F F⟮x⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F E).2 hsep
  haveI : IsPurelyInseparable F F⟮x⟯ :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem F E q).2 ⟨n, h⟩
  have hx' := IntermediateField.mem_adjoin_simple_self F x
  rw [IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable F⟮x⟯,
    IntermediateField.mem_bot] at hx'
  obtain ⟨y, hy⟩ := hx'
  exact ⟨y, hy⟩

variable [IsAlgClosure K Ω]
variable {K' : Type} [Field K'] [Algebra K K'] [FiniteDimensional K K'] [Algebra K' Ω]
  [IsScalarTower K K' Ω] [IsAlgClosure K' Ω]

/-- The inertia field over `K` lies in the inertia field over `K'`. -/
theorem inertiaField_le {x : Ω} (hx : x ∈ inertiaField (K := K) w) :
    x ∈ inertiaField (K := K') w := by
  obtain ⟨M, hMfg, hxM, hfix⟩ := hx
  haveI := hMfg.1
  obtain ⟨t, ht⟩ : M.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  haveI : FiniteDimensional K' (IntermediateField.adjoin K' (t : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun z _ => Algebra.IsIntegral.isIntegral z)
  have htM : ∀ z ∈ (t : Set Ω), z ∈ M := fun z hz => by
    rw [← ht]; exact IntermediateField.subset_adjoin K _ hz
  haveI : Algebra.IsSeparable K' (IntermediateField.adjoin K' (t : Set Ω)) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K' Ω).mpr
      (fun z hz => (hMfg.isSeparable (htM z hz)).tower_top K')
  obtain ⟨M', hM', hNM'⟩ := isFG_of (K := K') (IntermediateField.adjoin K' (t : Set Ω))
  have hMM' : ∀ y ∈ M, y ∈ M' := by
    intro y hy
    rw [← ht] at hy
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ M'.restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr
        (fun z hz => hNM' (IntermediateField.subset_adjoin K' _ hz))
    exact hle hy
  exact ⟨M', hM', hMM' x hxM, fun τ hτ =>
    hfix (τ.restrictScalars K) (fun y hy hyw => hτ y (hMM' y hy) hyw)⟩

/-- **The inertia field over `K'` lies in `E(t')`** for `E` the inertia field over `K` and `t'` a
finite set generating `K'` over `K` (any characteristic: for `x` in the inertia field over `K'`, a
power `x^(p^n)` lies in a finite Galois extension of `K`, is fixed by the inertia subgroup fixing
`K' ∩ N`, hence lies in `E(t')`; and `x` is separable over `E(t') ⊇ K'`). -/
theorem inertiaField_le_adjoin (t' : Finset Ω)
    (ht' : IntermediateField.adjoin K (t' : Set Ω) = (IsScalarTower.toAlgHom K K' Ω).fieldRange)
    {x : Ω} (hx : x ∈ inertiaField (K := K') w) :
    x ∈ IntermediateField.adjoin (inertiaField (K := K) w) (t' : Set Ω) := by
  classical
  set E := inertiaField (K := K) w
  set L := IntermediateField.adjoin E (t' : Set Ω)
  obtain ⟨M', hM'fg, hxM', hfix'⟩ := hx
  haveI := hM'fg.1
  haveI := hM'fg.2
  haveI : FiniteDimensional K M' := FiniteDimensional.trans K K' M'
  haveI : FiniteDimensional K (M'.restrictScalars K) := inferInstanceAs (FiniteDimensional K M')
  set p := ringExpChar K
  haveI : ExpChar Ω p := expChar_of_injective_algebraMap (algebraMap K Ω).injective p
  -- the separable part of `M'` over `K`, and a finite Galois `N ⊇ S`
  let S : IntermediateField K Ω := M'.restrictScalars K ⊓ separableClosure K Ω
  haveI : FiniteDimensional K S :=
    Module.Finite.of_injective (IntermediateField.inclusion (inf_le_left : S ≤ _)).toLinearMap
      (IntermediateField.inclusion (inf_le_left : S ≤ _)).injective
  haveI : Algebra.IsSeparable K S := (le_separableClosure_iff K Ω S).mp inf_le_right
  obtain ⟨N, hNfg, hSN⟩ := isFG_of S
  haveI := hNfg.1
  haveI := hNfg.2
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  haveI : ExpChar (separableClosure K Ω) p :=
    expChar_of_injective_algebraMap (algebraMap K _).injective p
  have hpow : ∀ y ∈ M', ∃ n : ℕ, y ^ p ^ n ∈ N := by
    intro y hy
    obtain ⟨n, hn⟩ := (isPurelyInseparable_iff_pow_mem (separableClosure K Ω) p).mp
      inferInstance y
    refine ⟨n, hSN ⟨?_, ?_⟩⟩
    · exact pow_mem (show y ∈ M'.restrictScalars K from hy) _
    · obtain ⟨z, hz⟩ := hn
      rw [← hz]; exact z.2
  have frob_inj : ∀ (n : ℕ) (a b : Ω), a ^ p ^ n = b ^ p ^ n → a = b := fun n a b h =>
    iterateFrobenius_inj Ω p n (by rw [iterateFrobenius_def, iterateFrobenius_def]; exact h)
  let I := inertM w N
  let F := IntermediateField.fixedField I
  let K'Ω : IntermediateField K Ω := (IsScalarTower.toAlgHom K K' Ω).fieldRange
  let K'N : IntermediateField K N := K'Ω.comap N.val
  obtain ⟨n₀, hn₀⟩ := hpow x hxM'
  let x' : N := ⟨x ^ p ^ n₀, hn₀⟩
  have hx' : x' ∈ IntermediateField.fixedField (IntermediateField.fixingSubgroup (F ⊔ K'N)) := by
    rw [IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]
    rintro ⟨σ, hσI, hσK'⟩
    let τ : Ω ≃ₐ[K] Ω := σ.liftNormal Ω
    have hτ : ∀ m : N, τ (algebraMap N Ω m) = algebraMap N Ω (σ m) := fun m =>
      AlgEquiv.liftNormal_commutes σ Ω m
    have hτK' : ∀ c : K', τ (algebraMap K' Ω c) = algebraMap K' Ω c := by
      intro c
      obtain ⟨n, hn⟩ := hpow _ (M'.algebraMap_mem c)
      have hmem : (⟨_, hn⟩ : N) ∈ K'N := show algebraMap K' Ω c ^ p ^ n ∈ K'Ω from
        pow_mem (show algebraMap K' Ω c ∈ K'Ω from ⟨c, rfl⟩) (p ^ n)
      have h2 : σ ⟨_, hn⟩ = ⟨_, hn⟩ :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσK' _ hmem
      have h1 := hτ ⟨_, hn⟩
      rw [h2] at h1
      apply frob_inj n
      rw [← map_pow]; exact h1
    let τ' : Ω ≃ₐ[K'] Ω := { τ.toRingEquiv with commutes' := hτK' }
    have hcond : CondM w M' τ' := by
      intro y hy hyw
      obtain ⟨n, hn⟩ := hpow y hy
      have h1 := hσI ⟨_, hn⟩ (pow_mem hyw _)
      have h2 := hτ ⟨_, hn⟩
      change τ y - y ∈ w.nonunits
      have h3 : ((σ ⟨_, hn⟩ : N) : Ω) - y ^ p ^ n = (τ y - y) ^ p ^ n := by
        rw [sub_pow_expChar_pow, ← map_pow]
        exact congrArg (· - y ^ p ^ n) h2.symm
      rw [h3, ValuationSubring.mem_nonunits_iff, map_pow] at h1
      rw [ValuationSubring.mem_nonunits_iff]
      by_contra hc
      exact absurd h1 (not_lt.mpr (one_le_pow₀ (not_lt.mp hc)))
    have h3 : τ x = x := hfix' τ' hcond
    apply Subtype.ext
    change algebraMap N Ω (σ x') = algebraMap N Ω x'
    rw [← hτ]
    change τ (x ^ p ^ n₀) = x ^ p ^ n₀
    rw [map_pow, h3]
  rw [IsGalois.fixedField_fixingSubgroup] at hx'
  have hK'L : ∀ c : K', algebraMap K' Ω c ∈ L := fun c => by
    have h1 : algebraMap K' Ω c ∈ IntermediateField.adjoin K (t' : Set Ω) := by
      rw [ht']; exact ⟨c, rfl⟩
    have h2 : IntermediateField.adjoin K (t' : Set Ω) ≤ L.restrictScalars K :=
      IntermediateField.adjoin_le_iff.mpr (fun z hz => IntermediateField.subset_adjoin E _ hz)
    exact h2 h1
  have hle : F ⊔ K'N ≤ (L.restrictScalars K).comap N.val := by
    apply sup_le
    · intro f hf
      have hfE : (f : Ω) ∈ E := by
        refine ⟨N, hNfg, f.2, fun τ hτ => ?_⟩
        let σ : N ≃ₐ[K] N := τ.restrictNormal N
        have hσ : ∀ m : N, algebraMap N Ω (σ m) = τ (algebraMap N Ω m) := fun m =>
          AlgEquiv.restrictNormal_commutes τ N m
        have hσI : σ ∈ I := by
          intro y hyw
          change algebraMap N Ω (σ y) - y ∈ w.nonunits
          rw [hσ]
          exact hτ y y.2 hyw
        have := (IntermediateField.mem_fixedField_iff _ _).mp hf σ hσI
        change τ (algebraMap N Ω f) = algebraMap N Ω f
        rw [← hσ, this]
      exact L.algebraMap_mem ⟨_, hfE⟩
    · rintro m ⟨c, hc⟩
      change (m : Ω) ∈ L
      have : (m : Ω) = algebraMap K' Ω c := hc.symm
      rw [this]
      exact hK'L c
  have hxpow : x ^ p ^ n₀ ∈ L := hle hx'
  -- `x` is separable over `L ⊇ K'`
  have hsepK' : IsSeparable K' x := hM'fg.isSeparable hxM'
  have hsepL : IsSeparable L x := by
    obtain ⟨mL, hmL⟩ : (minpoly K' x).map (algebraMap K' Ω) ∈ Polynomial.lifts (algebraMap L Ω) :=
      (lifts_iff_coeff_lifts _).mpr (fun n => ⟨⟨((minpoly K' x).map (algebraMap K' Ω)).coeff n,
        by rw [coeff_map]; exact hK'L _⟩, rfl⟩)
    have hmL' : mL.map (algebraMap L Ω) = (minpoly K' x).map (algebraMap K' Ω) := hmL
    have hsepm : mL.Separable := by
      rw [← Polynomial.separable_map (algebraMap L Ω), hmL', Polynomial.separable_map]
      exact hsepK'
    have h0 : aeval x mL = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, hmL', eval_map, ← aeval_def, minpoly.aeval]
    exact hsepm.of_dvd (minpoly.dvd L x h0)
  haveI : ExpChar L p := (algebraMap L Ω).expChar (algebraMap L Ω).injective p
  obtain ⟨y, hy⟩ := mem_range_of_pow_mem p hsepL n₀ ⟨⟨_, hxpow⟩, rfl⟩
  rw [← hy]; exact y.2

end Pair

end GTSHPair
