import ZInQKernel.HDecomp.QM.Leaves
/-! dev copy of `HDec.X6Kummer.ConicPt`, `conicGal` (TailE, verbatim) and shimura-glue's `ConicModelT` -/
namespace HDec.X6Kummer
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
abbrev ConicPt : Type :=
  {p : Qbar × Qbar // p.2 ^ 2 + 3 * p.1 ^ 2 + 3 = 0} ⊕ {b : Qbar // b ^ 2 = -3}
def conicGal (σ : Qbar ≃ₐ[ℚ] Qbar) : ConicPt → ConicPt
  | Sum.inl p => Sum.inl ⟨(σ p.1.1, σ p.1.2), by
      have h := congrArg σ p.2
      simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
      exact h⟩
  | Sum.inr b => Sum.inr ⟨σ b.1, by
      have h := congrArg σ b.2
      simp only [map_pow, map_neg, map_ofNat] at h
      exact h⟩
end HDec.X6Kummer
namespace HDec.QMSplit.Moduli
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
def ConicModelT (X : Over (Spec (CommRingCat.of ℚ))) (t : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ HDec.X6Kummer.ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = HDec.X6Kummer.conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      t.val (K := Qbar) x.left = OnePoint.some (-(p.1.1 ^ 2))) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → t.val (K := Qbar) x.left = OnePoint.infty)
end HDec.QMSplit.Moduli
/-! # x6-glue Part 1: values of sections at field points of an affine open

For an affine open `U ⊆ X` and a field `K`, the `K`-points of `X` lying in `U` are in bijection with
the ring homs `Γ(X, U) → K`, by "values of sections" (`ev`). Mathlib only. -/

namespace X6Glue

open CategoryTheory AlgebraicGeometry Limits

section Generic

variable {X : Scheme.{0}} {K : Type} [Field K]

/-- The value of sections over `U` at a `K`-point `y` lying in `U`: the same recipe as the kernel's
`ToP1.val` (evaluation in `κ(x)`, then `κ(x) → K`). -/
noncomputable def ev (U : X.Opens) (y : Spec (CommRingCat.of K) ⟶ X)
    (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U) : Γ(X, U) →+* K :=
  ((Scheme.SpecToEquivOfField K X y).2).hom.comp (X.evaluation U _ h).hom

theorem ev_apply (U : X.Opens) (y : Spec (CommRingCat.of K) ⟶ X)
    (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U) (s : Γ(X, U)) :
    ev U y h s = (Scheme.SpecToEquivOfField K X y).2 (X.evaluation U _ h s) := rfl

theorem pt_mem_top (U : X.Opens) (y : Spec (CommRingCat.of K) ⟶ X)
    (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U) : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ y ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem y h).ge

/-- The ring hom `Γ(X, U) → K` of a point in `U`, through `appLE`. -/
noncomputable def psi (U : X.Opens) (y : Spec (CommRingCat.of K) ⟶ X)
    (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U) : Γ(X, U) ⟶ CommRingCat.of K :=
  y.appLE U ⊤ (pt_mem_top U y h) ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom

/-- **A point in an affine open is `Spec` of its ring hom.** -/
theorem eq_specMap_psi (U : X.Opens) (hU : IsAffineOpen U) (y : Spec (CommRingCat.of K) ⟶ X)
    (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U) :
    y = Spec.map (psi U y h) ≫ hU.fromSpec := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec y hU (isAffineOpen_top _) (pt_mem_top U y h)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [psi, Spec.map_comp, Category.assoc, e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

/-- **`ev` is `psi`.** -/
theorem ev_eq_psi (U : X.Opens) (y : Spec (CommRingCat.of K) ⟶ X)
    (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U) : ev U y h = (psi U y h).hom := by
  have key : X.presheaf.germ U _ h ≫ Scheme.stalkClosedPointTo y = psi U y h := by
    refine (Scheme.germ_stalkClosedPointTo y U h).trans ?_
    rw [psi, Scheme.Hom.appLE]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc]
    rfl
  ext s
  exact congrArg (fun φ => φ.hom s) key

theorem ev_injective (U : X.Opens) (hU : IsAffineOpen U) (y₁ y₂ : Spec (CommRingCat.of K) ⟶ X)
    (h₁ : (Scheme.SpecToEquivOfField K X y₁).1 ∈ U) (h₂ : (Scheme.SpecToEquivOfField K X y₂).1 ∈ U)
    (e : ev U y₁ h₁ = ev U y₂ h₂) : y₁ = y₂ := by
  rw [eq_specMap_psi U hU y₁ h₁, eq_specMap_psi U hU y₂ h₂]
  rw [ev_eq_psi, ev_eq_psi] at e
  rw [CommRingCat.hom_ext e]

theorem ev_surjective (U : X.Opens) (hU : IsAffineOpen U) (φ : Γ(X, U) →+* K) :
    ∃ (y : Spec (CommRingCat.of K) ⟶ X) (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U),
      ev U y h = φ := by
  let y := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have h : (Scheme.SpecToEquivOfField K X y).1 ∈ U := by
    have hr : (Scheme.SpecToEquivOfField K X y).1 ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  refine ⟨y, h, ?_⟩
  have e := eq_specMap_psi U hU y h
  have e2 : Spec.map (psi U y h) = Spec.map (CommRingCat.ofHom φ) :=
    (cancel_mono hU.fromSpec).mp e.symm
  rw [ev_eq_psi, Spec.map_inj.mp e2]
  rfl

/-- **Naturality of `ev`** in the field. -/
theorem ev_comp {L : Type} [Field L] (f : K →+* L) (U : X.Opens)
    (y : Spec (CommRingCat.of K) ⟶ X) (h : (Scheme.SpecToEquivOfField K X y).1 ∈ U)
    (h' : (Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom f) ≫ y)).1 ∈ U)
    (s : Γ(X, U)) :
    ev U (Spec.map (CommRingCat.ofHom f) ≫ y) h' s = f (ev U y h s) := by
  rw [ev_apply, ev_apply]
  generalize hp : Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom f) ≫ y) = p at h'
  rw [LeafQM.AV.specToEquivOfField_comp] at hp
  subst hp
  rfl

theorem mem_comp_iff {L : Type} [Field L] (f : K →+* L) (U : X.Opens)
    (y : Spec (CommRingCat.of K) ⟶ X) :
    (Scheme.SpecToEquivOfField L X (Spec.map (CommRingCat.ofHom f) ≫ y)).1 ∈ U ↔
      (Scheme.SpecToEquivOfField K X y).1 ∈ U := by
  rw [LeafQM.AV.specToEquivOfField_comp]

end Generic

/-- Morphisms `Spec K → Spec ℚ` are unique (ring homs out of `ℚ` are unique). -/
theorem specQ_hom_ext {K : Type} [Field K] (a b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ)) :
    a = b := by
  rw [← Spec.map_preimage a, ← Spec.map_preimage b]
  congr 1
  ext1
  exact RingHom.ext_rat _ _

end X6Glue
/-! # x6-glue Part 2: Elkies' equations over the `t`-line, and the conic model on `ℚ̄`-points

`ElkiesCharts X t`: over each of the two standard opens of the `t`-line, `X` is the affine curve
`s² = −t, r² = 3(t − 1)`, glued by `s ↦ 1/s, r ↦ r/s`. `conicModelT_of_charts` derives shimura-glue's
points form `ConicModelT X t` from it. -/

namespace X6Glue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- The ideal of Elkies' affine equations `s² = −t`, `r² = 3(t − 1)` in `ℚ[t, s, r]`
(variables `t = X 0`, `s = X 1`, `r = X 2`). -/
noncomputable def elkiesIdeal : Ideal (MvPolynomial (Fin 3) ℚ) :=
  Ideal.span {MvPolynomial.X 1 ^ 2 + MvPolynomial.X 0,
    MvPolynomial.X 2 ^ 2 - 3 * (MvPolynomial.X 0 - 1)}

/-- `ℚ[t, s, r]/(s² + t, r² − 3(t − 1))`, the coordinate ring of `X*(6)(√−t, √(3(t − 1)))` over the
affine `t`-line. -/
abbrev ElkiesRing : Type := MvPolynomial (Fin 3) ℚ ⧸ elkiesIdeal

/-- The coordinates `t, s, r` in `ElkiesRing`. -/
noncomputable abbrev eT : ElkiesRing := Ideal.Quotient.mk _ (MvPolynomial.X 0)
noncomputable abbrev eS : ElkiesRing := Ideal.Quotient.mk _ (MvPolynomial.X 1)
noncomputable abbrev eR : ElkiesRing := Ideal.Quotient.mk _ (MvPolynomial.X 2)

theorem rel1 : eS ^ 2 + eT = 0 := by
  rw [← map_pow, ← map_add, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert _ _)

theorem rel2 : eR ^ 2 - 3 * (eT - 1) = 0 := by
  have : eR ^ 2 - 3 * (eT - 1) = Ideal.Quotient.mk elkiesIdeal
      (MvPolynomial.X 2 ^ 2 - 3 * (MvPolynomial.X 0 - 1)) := by
    simp only [map_sub, map_pow, map_mul, map_one, map_ofNat]
  rw [this, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

/-- Ring homs out of `ElkiesRing` agree if they agree on `s` and `r` (then also on `t = −s²`). -/
theorem elkies_hom_ext {A : Type*} [CommRing A] (ψ₁ ψ₂ : ElkiesRing →+* A)
    (hS : ψ₁ eS = ψ₂ eS) (hR : ψ₁ eR = ψ₂ eR) : ψ₁ = ψ₂ := by
  have hT : ψ₁ eT = ψ₂ eT := by
    have e1 := congrArg ψ₁ rel1
    have e2 := congrArg ψ₂ rel1
    simp only [map_add, map_pow, map_zero] at e1 e2
    rw [hS] at e1
    linear_combination e1 - e2
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    exact congrArg (fun φ : ℚ →+* A => φ c) (RingHom.ext_rat ((ψ₁.comp _).comp MvPolynomial.C)
      ((ψ₂.comp _).comp MvPolynomial.C))
  · intro i
    fin_cases i
    · exact hT
    · exact hS
    · exact hR

/-- The ring hom `ElkiesRing → K` of a solution `(t, s, r)`. -/
noncomputable def elkiesLift {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K)
    (h1 : s ^ 2 + t = 0) (h2 : r ^ 2 - 3 * (t - 1) = 0) : ElkiesRing →+* K :=
  Ideal.Quotient.lift elkiesIdeal (MvPolynomial.aeval ![t, s, r]).toRingHom (by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => (MvPolynomial.aeval ![t, s, r]).toRingHom a = 0)
      ?_ ?_ ?_ ?_ ha
    · rintro x (rfl | rfl)
      · simpa using h1
      · simpa using h2
    · simp
    · intro x y _ _ hx hy; simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hx hy ⊢
      rw [map_add, hx, hy, add_zero]
    · intro c x _ hx; simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smul_eq_mul] at hx ⊢
      rw [map_mul, hx, mul_zero])

theorem elkiesLift_T {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K) h1 h2 :
    elkiesLift t s r h1 h2 eT = t := by simp [elkiesLift]
theorem elkiesLift_S {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K) h1 h2 :
    elkiesLift t s r h1 h2 eS = s := by simp [elkiesLift]
theorem elkiesLift_R {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K) h1 h2 :
    elkiesLift t s r h1 h2 eR = r := by simp [elkiesLift]

/-- **Elkies' equations as charts of `X` over the `t`-line.** For a `ℚ`-scheme `X` with `t : X → P¹`
(the kernel's charts `t.U = {t ≠ ∞}`, `t.V = {t ≠ 0}`, `t.f = t`, `t.g = 1/t`):
* `t.U` and `t.V` are affine;
* `Γ(t.U) ≅ ℚ[t, s, r]/(s² + t, r² − 3(t − 1))` with `t ↦ t.f` (that is, over `t ≠ ∞`, `X` is the
  curve `s² = −t`, `r² = 3(t − 1)`);
* `Γ(t.V) ≅ ℚ[u, a, b]/(a² + u, b² − 3(u − 1))` with `u ↦ t.g = 1/t` (over `t ≠ 0`, with
  `a = 1/s`, `b = r/s`: `a² = −1/t`, `b² = 3(t − 1)/(−t) = 3(1/t − 1)`);
* on `t.U ∩ t.V`: `s·a = 1` and `r·a = b` (the gluing).
This is the curve `X*(6)(√−t, √(3(t − 1)))` over the `t`-line, written in the two standard charts. -/
def ElkiesCharts (X : Over (Spec (CommRingCat.of ℚ))) (t : ToP1 X.left) : Prop :=
  IsAffineOpen t.U ∧ IsAffineOpen t.V ∧
  ∃ (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V)),
    φU eT = t.f ∧ φV eT = t.g ∧
    X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eS) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) = 1 ∧
    X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eR) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) =
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eR)

end X6Glue
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
#print axioms X6Glue.conicModelT_of_charts
