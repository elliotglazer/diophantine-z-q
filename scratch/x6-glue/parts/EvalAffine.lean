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
