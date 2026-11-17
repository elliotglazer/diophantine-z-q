/-! # x6-glue Part 3: `ConicModelT` from `ElkiesCharts` -/

namespace X6Glue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

section Proof

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}

/-- The point of `X` under a `ℚ̄`-point. -/
noncomputable abbrev pt {X : Over (Spec (CommRingCat.of ℚ))} (y : Spec (CommRingCat.of Qbar) ⟶ X.left) :
    X.left :=
  (Scheme.SpecToEquivOfField Qbar X.left y).1

theorem memV_of_not_memU (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (h : ¬ (pt y) ∈ t.U) : (pt y) ∈ t.V := by
  have hc : (pt y) ∈ (t.U ⊔ t.V) := by rw [t.cover]; trivial
  rcases hc with hc | hc
  · exact absurd hc h
  · exact hc

/-- At a point outside `t.U`, the section `t.g = 1/t` vanishes. -/
theorem ev_g_eq_zero (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (h : ¬ (pt y) ∈ t.U) (hv : (pt y) ∈ t.V) :
    ev t.V y hv t.g = 0 := by
  rw [ev_apply]
  have : X.left.evaluation t.V _ hv t.g = 0 := by
    rw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen, t.basicOpen_g]
    exact fun hm => h hm.1
  rw [this, map_zero]

/-- At a point of `t.V` where `t.g` vanishes, the point is outside `t.U`. -/
theorem not_memU_of_ev_g (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (hv : (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ t.V) (h0 : ev t.V y hv t.g = 0) :
    ¬ (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ t.U := by
  intro hu
  have hb : (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ X.left.basicOpen t.g := by
    rw [t.basicOpen_g]; exact ⟨hu, hv⟩
  rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen _ _ hv] at hb
  rw [ev_apply] at h0
  exact hb ((map_eq_zero_iff _ (RingHom.injective _)).mp h0)

variable (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V))

/-- The composite `ElkiesRing → Γ(t.U) → ℚ̄` at a point of `t.U`. -/
noncomputable def psiU (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (h : (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ t.U) : ElkiesRing →+* Qbar :=
  (ev t.U y h).comp (φU : ElkiesRing →+* Γ(X.left, t.U))

noncomputable def psiV (y : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (h : (Scheme.SpecToEquivOfField Qbar X.left y).1 ∈ t.V) : ElkiesRing →+* Qbar :=
  (ev t.V y h).comp (φV : ElkiesRing →+* Γ(X.left, t.V))

theorem conic_rel (ψ : ElkiesRing →+* Qbar) : ψ eR ^ 2 + 3 * ψ eS ^ 2 + 3 = 0 := by
  have e1 := congrArg ψ rel1
  have e2 := congrArg ψ rel2
  simp only [map_add, map_pow, map_zero, map_sub, map_mul, map_one, map_ofNat] at e1 e2
  linear_combination e2 + 3 * e1

theorem inf_rel (ψ : ElkiesRing →+* Qbar) (h0 : ψ eT = 0) : ψ eR ^ 2 = -3 := by
  have e2 := congrArg ψ rel2
  simp only [map_pow, map_sub, map_mul, map_one, map_ofNat, map_zero, h0] at e2
  linear_combination e2

theorem s_zero (ψ : ElkiesRing →+* Qbar) (h0 : ψ eT = 0) : ψ eS = 0 := by
  have e1 := congrArg ψ rel1
  simp only [map_add, map_pow, map_zero, h0, add_zero] at e1
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e1

variable (hTg : φV eT = t.g)

include hTg in
theorem psiV_T (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (h : ¬ (pt y) ∈ t.U) (hv : (pt y) ∈ t.V) :
    psiV φV y hv eT = 0 := by
  simp only [psiV, RingHom.comp_apply, RingHom.coe_coe, hTg]
  exact ev_g_eq_zero y h hv

open Classical in
/-- The map `X(ℚ̄) → C(ℚ̄)`: `(s, r)` on `t.U`, and `b` (with `[X : Y : Z] = [1 : b : 0]`) off `t.U`. -/
noncomputable def conicMapL (y : Spec (CommRingCat.of Qbar) ⟶ X.left) : HDec.X6Kummer.ConicPt :=
  if h : (pt y) ∈ t.U then
    Sum.inl ⟨(psiU φU y h eS, psiU φU y h eR), conic_rel _⟩
  else
    Sum.inr ⟨psiV φV y (memV_of_not_memU y h) eR,
      inf_rel _ (psiV_T φV hTg y h (memV_of_not_memU y h))⟩

theorem psiU_comp (σ : Qbar →+* Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (h : (pt y) ∈ t.U)
    (h' : (pt (Spec.map (CommRingCat.ofHom σ) ≫ y)) ∈ t.U) (a : ElkiesRing) :
    psiU φU (Spec.map (CommRingCat.ofHom σ) ≫ y) h' a = σ (psiU φU y h a) :=
  ev_comp σ t.U y h h' _

theorem psiV_comp (σ : Qbar →+* Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (h : (pt y) ∈ t.V)
    (h' : (pt (Spec.map (CommRingCat.ofHom σ) ≫ y)) ∈ t.V) (a : ElkiesRing) :
    psiV φV (Spec.map (CommRingCat.ofHom σ) ≫ y) h' a = σ (psiV φV y h a) :=
  ev_comp σ t.V y h h' _

/-- **Galois equivariance.** -/
theorem conicMapL_comp (σ : Qbar ≃ₐ[ℚ] Qbar) (y : Spec (CommRingCat.of Qbar) ⟶ X.left) :
    conicMapL φU φV hTg (Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y) =
      HDec.X6Kummer.conicGal σ (conicMapL φU φV hTg y) := by
  by_cases h : pt y ∈ t.U
  · have h' : pt (Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y) ∈ t.U :=
      (mem_comp_iff _ _ _).mpr h
    rw [conicMapL, dif_pos h', conicMapL, dif_pos h]
    simp only [HDec.X6Kummer.conicGal]
    congr 1
    apply Subtype.ext
    simp only
    rw [psiU_comp φU _ y h h', psiU_comp φU _ y h h']
    rfl
  · have h' : ¬ pt (Spec.map (CommRingCat.ofHom ((σ : Qbar →ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫ y) ∈ t.U :=
      fun hh => h ((mem_comp_iff _ _ _).mp hh)
    rw [conicMapL, dif_neg h', conicMapL, dif_neg h]
    simp only [HDec.X6Kummer.conicGal]
    congr 1
    apply Subtype.ext
    simp only
    rw [psiV_comp φV _ y (memV_of_not_memU y h) (memV_of_not_memU _ h')]
    rfl

variable (hT : φU eT = t.f)

include hT in
/-- **The value of `t` on the affine part**: `t = −s²`. -/
theorem val_of_inl (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (p)
    (hp : conicMapL φU φV hTg y = Sum.inl p) : t.val y = OnePoint.some (-(p.1.1 ^ 2)) := by
  by_cases h : pt y ∈ t.U
  · rw [conicMapL, dif_pos h] at hp
    have hp' := Sum.inl_injective hp
    subst hp'
    simp only [ToP1.val]
    rw [dif_pos h]
    congr 1
    change ev t.U y h t.f = _
    rw [← hT]
    change psiU φU y h eT = _
    have e1 := congrArg (psiU φU y h) rel1
    simp only [map_add, map_pow, map_zero] at e1
    linear_combination e1
  · rw [conicMapL, dif_neg h] at hp
    exact absurd hp (by simp)

/-- **`t = ∞` at the two points at infinity.** -/
theorem val_of_inr (y : Spec (CommRingCat.of Qbar) ⟶ X.left) (b)
    (hb : conicMapL φU φV hTg y = Sum.inr b) : t.val y = OnePoint.infty := by
  by_cases h : pt y ∈ t.U
  · rw [conicMapL, dif_pos h] at hb
    exact absurd hb (by simp)
  · simp only [ToP1.val]
    rw [dif_neg h]

omit hT in
theorem conicMapL_injective (hU : IsAffineOpen t.U) (hV : IsAffineOpen t.V)
    (y₁ y₂ : Spec (CommRingCat.of Qbar) ⟶ X.left)
    (e : conicMapL φU φV hTg y₁ = conicMapL φU φV hTg y₂) : y₁ = y₂ := by
  by_cases h₁ : pt y₁ ∈ t.U <;> by_cases h₂ : pt y₂ ∈ t.U
  · rw [conicMapL, dif_pos h₁, conicMapL, dif_pos h₂] at e
    have e' := congrArg Subtype.val (Sum.inl_injective e)
    simp only [Prod.mk.injEq] at e'
    have hψ : psiU φU y₁ h₁ = psiU φU y₂ h₂ := elkies_hom_ext _ _ e'.1 e'.2
    apply ev_injective t.U hU y₁ y₂ h₁ h₂
    ext s
    have := congrArg (fun ψ => ψ (φU.symm s)) hψ
    simpa [psiU] using this
  · rw [conicMapL, dif_pos h₁, conicMapL, dif_neg h₂] at e
    exact absurd e (by simp)
  · rw [conicMapL, dif_neg h₁, conicMapL, dif_pos h₂] at e
    exact absurd e (by simp)
  · rw [conicMapL, dif_neg h₁, conicMapL, dif_neg h₂] at e
    have e' := congrArg Subtype.val (Sum.inr_injective e)
    simp only at e'
    have v₁ := memV_of_not_memU y₁ h₁
    have v₂ := memV_of_not_memU y₂ h₂
    have hψ : psiV φV y₁ v₁ = psiV φV y₂ v₂ := by
      apply elkies_hom_ext _ _ _ e'
      rw [s_zero _ (psiV_T φV hTg y₁ h₁ v₁), s_zero _ (psiV_T φV hTg y₂ h₂ v₂)]
    apply ev_injective t.V hV y₁ y₂ v₁ v₂
    ext s
    have := congrArg (fun ψ => ψ (φV.symm s)) hψ
    simpa [psiV] using this

omit hT in
theorem conicMapL_surjective (hU : IsAffineOpen t.U) (hV : IsAffineOpen t.V)
    (c : HDec.X6Kummer.ConicPt) : ∃ y, conicMapL φU φV hTg y = c := by
  rcases c with ⟨⟨a, b⟩, hab⟩ | ⟨b, hb⟩
  · let ψ := elkiesLift (K := Qbar) (-(a ^ 2)) a b (by ring) (by simp only at hab; linear_combination hab)
    obtain ⟨y, h, hy⟩ := ev_surjective t.U hU (ψ.comp (φU.symm : Γ(X.left, t.U) →+* ElkiesRing))
    refine ⟨y, ?_⟩
    have hp : psiU φU y h = ψ := by
      unfold psiU; rw [hy]; exact RingHom.ext fun z => by simp
    rw [conicMapL, dif_pos h]
    congr 1
    apply Subtype.ext
    simp only [hp, ψ, elkiesLift_S, elkiesLift_R]
  · let ψ := elkiesLift (K := Qbar) 0 0 b (by ring) (by linear_combination hb)
    obtain ⟨y, hv, hy⟩ := ev_surjective t.V hV (ψ.comp (φV.symm : Γ(X.left, t.V) →+* ElkiesRing))
    have hp : psiV φV y hv = ψ := by
      unfold psiV; rw [hy]; exact RingHom.ext fun z => by simp
    have h0 : ev t.V y hv t.g = 0 := by
      rw [← hTg]
      change psiV φV y hv eT = 0
      rw [hp, elkiesLift_T]
    have h := not_memU_of_ev_g y hv h0
    refine ⟨y, ?_⟩
    rw [conicMapL, dif_neg h]
    congr 1
    apply Subtype.ext
    simp only [hp, ψ, elkiesLift_R]

end Proof

/-- **The conic model on `ℚ̄`-points from Elkies' equations** (`ConicModelT X t`, shimura-glue's
points form, from the chart form `ElkiesCharts X t`). -/
theorem conicModelT_of_charts {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}
    (h : ElkiesCharts X t) : HDec.QMSplit.Moduli.ConicModelT X t := by
  obtain ⟨hU, hV, φU, φV, hT, hTg, -, -⟩ := h
  let F : (fieldPt Qbar ⟶ X) → HDec.X6Kummer.ConicPt := fun x => conicMapL φU φV hTg x.left
  have hinj : Function.Injective F := fun x₁ x₂ e =>
    Over.OverMorphism.ext (conicMapL_injective φU φV hTg hU hV _ _ e)
  have hsurj : Function.Surjective F := fun c => by
    obtain ⟨y, hy⟩ := conicMapL_surjective φU φV hTg hU hV c
    exact ⟨Over.homMk y (specQ_hom_ext _ _), hy⟩
  refine ⟨Equiv.ofBijective F ⟨hinj, hsurj⟩, fun σ x => ?_, fun x p hp => ?_, fun x b hb => ?_⟩
  · exact conicMapL_comp φU φV hTg σ x.left
  · exact val_of_inl φU φV hTg hT x.left p hp
  · exact val_of_inr φU φV hTg x.left b hb

end X6Glue
