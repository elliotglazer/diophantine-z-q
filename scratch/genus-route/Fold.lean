import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Curve.CanonicalDegree
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.Dim.Basic
import ZInQKernel.Contrib.RLeaf.BelyiX1
import ZInQKernel.Contrib.RLeaf.T40
import ZInQKernel.HDecomp.ModCurves.X1Belyi
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.SmoothFibre.Basic
import ZInQKernel.OneProof.H.TailM

/-! # genus-route (fold form)

`Closed.lean` verbatim (dimjac-glue's `DimJacGlue.lean`, then genus-route's `LocalDer.lean`), plus, in namespace
`HDec.HSyn`, drop-in replacements for the two uses of `t34`: `t34Le : DimJ1Le5` (no hypothesis), `dim_J1_le_of5`
(for `TailD.lean:236`) and `G0Split.javanpeykarJ1_of_le` (for `TailD.lean:250`). -/


/-! # genus-route: `dim J₁(N) ≤ N²` with no hypothesis

Two files concatenated verbatim (minus `import` and `#print` lines): dimjac-glue's
`scratch/dimjac-glue/DimJacGlue.lean` (branch `wip/dimjac-glue`, commit 24435c82; proves
`ZInQ.Contrib.CurvesG.DimJacobianEqGenus`), then genus-route's `LocalDer.lean` (proves
`DimJacobianEqGenus → DimJ1Le`). Result: `GenusRoute.dimJ1Le : DimJ1Le`. -/


/-! # dimjac-glue: `ModularSplit.DimJac.H0DifferentialsEqHolo` is a theorem

`H0DifferentialsEqHolo` (modular-split, `scratch/modular-split/DimJac.lean`) is copied verbatim below and
**proved** (`ModularSplit.DimJac.h0DifferentialsEqHolo`), with no hypotheses, from Mathlib, the vendored
Jacobian library (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`) and `ZInQKernel/Contrib/Dim/`. With
modular-split's reduction (copied verbatim) this proves the bundle row
`ZInQ.Contrib.CurvesG.DimJacobianEqGenus` (`ModularSplit.DimJac.dimJacobianEqGenus`). No sorry; axioms
`propext, Classical.choice, Quot.sound`.

Proof. Let `g : X → Spec ℚ`, `Ω = Ω¹_{X/ℚ}`, `e : K(X) ≃+* F`, `ψ_U : Γ(X, U) → F` the germ at the generic
point followed by `e`.
1. `Φ U : Γ(Ω, U) → Ω_{F/ℚ}` for `U` affine nonempty: the library's `kaehlerSectionsEquiv`
   (`Ω_{Γ(U)/ℚ} ≃ Γ(Ω, U)`) followed by `KaehlerDifferential.map ℚ ℚ Γ(U) F`; `Φ U (a • d b) = ψ a • D (ψ b)`.
2. `Φ U` is injective (`kaehlerToFractionFieldInjective`: `Ω_A` projective for `A` smooth, `Ω_K` its
   localization, `Γ(U)` smooth over `ℚ` and `F` its fraction field) and compatible with restriction.
3. The global `ΦG : Γ(Ω, X) → Ω_{F/ℚ}` (restrict to one affine open; independent of the choice since any two
   nonempty opens meet in the generic point) is injective by sheaf locality.
4. Image ⊆ `holoDiff F`: every valuation subring `w ⊇ ℚ` contains some `ψ_V(Γ(X, V))`, `V` affine
   (`valuationCenter`, from Mathlib's valuative criterion for the proper `g`).
5. Image ⊇ `holoDiff F`: for `V` affine and `𝔪 ⊂ Γ(V)` maximal, the point is closed (`X` Jacobson), its stalk
   is a valuation ring (regular local of dimension one: `Contrib.Dim.finrank_cotangentSpace_of_...` and
   Mathlib's DVR TFAE), so `ω` regular everywhere has `ψ(t) • ω ∈ im Φ V` for some `t ∉ 𝔪`; hence
   `ω ∈ im Φ V`; the local preimages glue (sheaf condition).
6. `H⁰ = Γ` (library `H.zeroLinearEquiv`); additive maps of `ℚ`-vector spaces are `ℚ`-linear
   (`map_rat_smul`), so `finrankH ℚ 0 = finrank ℚ (holoDiff F) = fieldGenus F`. -/

set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
noncomputable section
open CategoryTheory AlgebraicGeometry

namespace DimJacGlue

variable {X : Scheme.{0}} [IsIntegral X] (g : X ⟶ Spec (CommRingCat.of ℚ))
  {F : Type} [Field F] [Algebra ℚ F] (e : X.functionField ≃+* F)

lemma generic_mem (U : X.Opens) (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU)

/-- `Γ(X, U) → F`, the germ at the generic point followed by `e`. -/
def ψ (U : X.Opens) (hU : (U : Set X).Nonempty) : Γ(X, U) →+* F :=
  e.toRingHom.comp (X.presheaf.germ U (genericPoint X) (generic_mem U hU)).hom

/-- `Φ_U : Γ(Ω, U) → Ω_{F/ℚ}` for an affine nonempty open `U`. -/
def Φ (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    Γ(g.relativeDifferentials, U) →+ Ω[F⁄ℚ] :=
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  (KaehlerDifferential.map ℚ ℚ Γ(X, U) F).toAddMonoidHom.comp
    (g.kaehlerSectionsEquiv U rfl hU).symm.toLinearMap.toAddMonoidHom


variable {g e}

lemma kse_smul_D (U : X.Opens) (hU : IsAffineOpen U) (a b : Γ(X, U)) :
    letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
    g.kaehlerSectionsEquiv U rfl hU (a • KaehlerDifferential.D ℚ Γ(X, U) b) = a • g.sectionsD U b := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  rw [LinearEquiv.map_smul, Scheme.Hom.kaehlerSectionsEquiv_D]

/-- Induction principle for sections of `Ω¹` over an affine open. -/
lemma induction_affine (U : X.Opens) (hU : IsAffineOpen U) (P : Γ(g.relativeDifferentials, U) → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ a b : Γ(X, U), P (a • g.sectionsD U b)) (s : Γ(g.relativeDifferentials, U)) : P s := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  obtain ⟨η, rfl⟩ := (g.kaehlerSectionsEquiv U rfl hU).surjective s
  suffices H : ∀ c : Γ(X, U), P (g.kaehlerSectionsEquiv U rfl hU (c • η)) by simpa using H 1
  have hη : η ∈ Submodule.span Γ(X, U) (Set.range (KaehlerDifferential.D ℚ Γ(X, U))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hη using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    intro c; rw [kse_smul_D]; exact hgen c b
  | zero => intro c; simpa using h0
  | add x y _ _ hx hy => intro c; rw [smul_add, map_add]; exact hadd _ _ (hx c) (hy c)
  | smul a x _ hx => intro c; rw [smul_smul]; exact hx _

lemma Φ_smul_D (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a b : Γ(X, U)) :
    Φ g e U hU hne (a • g.sectionsD U b) = ψ e U hne a • KaehlerDifferential.D ℚ F (ψ e U hne b) := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  have := kse_smul_D (g := g) U hU a b
  simp only [Φ, AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
    LinearEquiv.coe_coe]
  rw [← this, LinearEquiv.symm_apply_apply, LinearMap.map_smul, KaehlerDifferential.map_D]
  rfl

lemma Φ_smul (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a : Γ(X, U))
    (s : Γ(g.relativeDifferentials, U)) :
    Φ g e U hU hne (a • s) = ψ e U hne a • Φ g e U hU hne s := by
  induction s using induction_affine U hU with
  | h0 => simp
  | hadd x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | hgen c b => rw [smul_smul, Φ_smul_D, Φ_smul_D, map_mul, mul_smul]


lemma ψ_res {U V : X.Opens} (h : V ≤ U) (hV : (V : Set X).Nonempty) (a : Γ(X, U)) :
    ψ e V hV (X.presheaf.map (homOfLE h).op a) =
      ψ e U (hV.mono h) a := by
  simp only [ψ, RingHom.coe_comp, Function.comp_apply]
  congr 1
  exact X.presheaf.germ_res_apply (homOfLE h) _ _ a

lemma Φ_res {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hne : (V : Set X).Nonempty) (s : Γ(g.relativeDifferentials, U)) :
    Φ g e V hV hne (g.relativeDifferentials.presheaf.map (homOfLE h).op s) =
      Φ g e U hU (hne.mono h) s := by
  induction s using induction_affine U hU with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | hgen a b =>
    rw [Scheme.Modules.map_smul, ← Scheme.Hom.sectionsD_map, Φ_smul_D, Φ_smul_D, ψ_res, ψ_res]


/-- **GLUE (proved below, `kaehlerToFractionFieldInjective`).** For a domain `A` smooth over `ℚ` with fraction
field `K`, `Ω_{A/ℚ} → Ω_{K/ℚ}` is injective (`Ω_A` is projective, hence torsion-free, and `Ω_K` is its
localization). -/
def KaehlerToFractionFieldInjective : Prop :=
  ∀ (A K : Type) [CommRing A] [IsDomain A] [Algebra ℚ A] [Algebra.Smooth ℚ A] [Field K] [Algebra ℚ K]
    [Algebra A K] [IsScalarTower ℚ A K] [IsFractionRing A K],
    Function.Injective (KaehlerDifferential.map ℚ ℚ A K)

theorem kaehlerToFractionFieldInjective : KaehlerToFractionFieldInjective := by
  intro A K _ _ _ _ _ _ _ _ _
  have hloc : IsLocalizedModule (nonZeroDivisors A) (KaehlerDifferential.map ℚ ℚ A K) :=
    KaehlerDifferential.isLocalizedModule_map ℚ A K (nonZeroDivisors A)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨r, hr⟩, hrx⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors A) _).mp hx
  have hreg : IsRegular r := IsRegular.of_ne_zero (nonZeroDivisors.ne_zero hr)
  exact Module.Flat.isSMulRegular_of_isRegular (M := Ω[A⁄ℚ]) hreg (by simpa using hrx)


omit [IsIntegral X] in
lemma smooth_sections [Smooth g] (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
    Algebra.Smooth ℚ Γ(X, U) := by
  have h1 : RingHom.Smooth (g.appLE ⊤ U le_top).hom :=
    HasRingHomProperty.appLE @Smooth g ‹_› ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h2 : RingHom.Smooth (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom :=
    RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have : RingHom.Smooth (g.specStructureMap U).hom := by
    have := RingHom.Smooth.comp h2 h1
    simpa [Scheme.Hom.specStructureMap] using this
  exact this

lemma isFractionRing_ψ (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
    IsFractionRing Γ(X, U) F := by
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : Nonempty U := hne.to_subtype
  have h := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors Γ(X, U))
    (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

lemma Φ_injective [Smooth g] (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    Function.Injective (Φ g e U hU hne) := by
  letI : Algebra ℚ Γ(X, U) := (g.specStructureMap U).hom.toAlgebra
  letI : Algebra Γ(X, U) F := (ψ e U hne).toAlgebra
  haveI : IsScalarTower ℚ Γ(X, U) F := IsScalarTower.of_algebraMap_eq (fun q =>
    congrArg (· q) (RingHom.ext_rat (algebraMap ℚ F) ((ψ e U hne).comp (g.specStructureMap U).hom)))
  haveI := smooth_sections (g := g) U hU
  haveI := isFractionRing_ψ (e := e) U hU hne
  haveI : IsDomain Γ(X, U) := by
    haveI : Nonempty U := hne.to_subtype
    infer_instance
  exact (kaehlerToFractionFieldInjective Γ(X, U) F).comp (g.kaehlerSectionsEquiv U rfl hU).symm.injective


omit [IsIntegral X] in
lemma res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(g.relativeDifferentials, U)) :
    g.relativeDifferentials.presheaf.map (homOfLE h₂).op
        (g.relativeDifferentials.presheaf.map (homOfLE h₁).op s) =
      g.relativeDifferentials.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma exists_affine_generic (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ V : X.Opens, IsAffineOpen V ∧ genericPoint X ∈ V ∧ V ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (generic_mem W hW) W.2
  exact ⟨V, hV, hηV, hVW⟩

lemma univ_nonempty : (Set.univ : Set X).Nonempty := Set.univ_nonempty

/-- A fixed nonempty affine open. -/
def U₀ (X : Scheme.{0}) [IsIntegral X] : X.Opens :=
  Classical.choose (exists_affine_generic (X := X) ⊤ (by simp))

lemma U₀_spec : IsAffineOpen (U₀ X) ∧ genericPoint X ∈ U₀ X :=
  ⟨(Classical.choose_spec (exists_affine_generic (X := X) ⊤ (by simp))).1,
   (Classical.choose_spec (exists_affine_generic (X := X) ⊤ (by simp))).2.1⟩

variable (g e) in
/-- The global map `Φ : Γ(X, Ω¹) → Ω_{F/ℚ}`. -/
def ΦG : Γ(g.relativeDifferentials, ⊤) →+ Ω[F⁄ℚ] :=
  (Φ g e (U₀ X) U₀_spec.1 ⟨_, U₀_spec.2⟩).comp
    (g.relativeDifferentials.presheaf.map (homOfLE (le_top : U₀ X ≤ ⊤)).op).hom

lemma Φ_eq_of_affine {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUne : (U : Set X).Nonempty) (hVne : (V : Set X).Nonempty) {T : X.Opens} (hUT : U ≤ T) (hVT : V ≤ T)
    (s : Γ(g.relativeDifferentials, T)) :
    Φ g e U hU hUne (g.relativeDifferentials.presheaf.map (homOfLE hUT).op s) =
      Φ g e V hV hVne (g.relativeDifferentials.presheaf.map (homOfLE hVT).op s) := by
  have hUV : ((U ⊓ V : X.Opens) : Set X).Nonempty :=
    ⟨genericPoint X, (show genericPoint X ∈ U ⊓ V from ⟨generic_mem U hUne, generic_mem V hVne⟩)⟩
  obtain ⟨W, hW, hηW, hWUV⟩ := exists_affine_generic (U ⊓ V) hUV
  have hWne : (W : Set X).Nonempty := ⟨_, hηW⟩
  rw [← Φ_res (hWUV.trans inf_le_left) hU hW hWne, ← Φ_res (hWUV.trans inf_le_right) hV hW hWne,
    res_res, res_res]

lemma ΦG_eq (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty)
    (s : Γ(g.relativeDifferentials, ⊤)) :
    ΦG g e s = Φ g e V hV hne (g.relativeDifferentials.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) :=
  Φ_eq_of_affine _ _ _ _ _ _ s


omit [IsIntegral X] in
/-- Locality of sections of `Ω¹` along the affine opens. -/
lemma eq_of_affine_restrict (T : X.Opens) (s t : Γ(g.relativeDifferentials, T))
    (h : ∀ V : X.Opens, IsAffineOpen V → (V : Set X).Nonempty → ∀ hVT : V ≤ T,
      g.relativeDifferentials.presheaf.map (homOfLE hVT).op s =
        g.relativeDifferentials.presheaf.map (homOfLE hVT).op t) : s = t := by
  let ι := {V : X.Opens // IsAffineOpen V ∧ (V : Set X).Nonempty ∧ V ≤ T}
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨g.relativeDifferentials.presheaf, g.relativeDifferentials.isSheaf⟩
    (fun i : ι => i.1) T (fun i => homOfLE i.2.2.2) ?_ s t (fun i => h i.1 i.2.1 i.2.2.1 i.2.2.2)
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx T.2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨x, hxV⟩, hVT⟩, hxV⟩

lemma ΦG_injective [Smooth g] : Function.Injective (ΦG g e) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine eq_of_affine_restrict ⊤ s 0 (fun V hV hne hVT => ?_)
  rw [map_zero]
  apply Φ_injective (e := e) V hV hne
  rw [map_zero, ← hs, ΦG_eq V hV hne]

omit [IsIntegral X] in
/-- Gluing of sections of `Ω¹` given on the affine opens. -/
lemma exists_glue (T : X.Opens)
    (σ : ∀ V : X.Opens, IsAffineOpen V → (V : Set X).Nonempty → V ≤ T → Γ(g.relativeDifferentials, V))
    (compat : ∀ (V V' W : X.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hW : IsAffineOpen W)
      (hVne : (V : Set X).Nonempty) (hV'ne : (V' : Set X).Nonempty) (hWne : (W : Set X).Nonempty)
      (hVT : V ≤ T) (hV'T : V' ≤ T) (hWV : W ≤ V) (hWV' : W ≤ V'),
      g.relativeDifferentials.presheaf.map (homOfLE hWV).op (σ V hV hVne hVT) =
        g.relativeDifferentials.presheaf.map (homOfLE hWV').op (σ V' hV' hV'ne hV'T)) :
    ∃ s : Γ(g.relativeDifferentials, T), ∀ (V : X.Opens) (hV : IsAffineOpen V)
      (hne : (V : Set X).Nonempty) (hVT : V ≤ T),
      g.relativeDifferentials.presheaf.map (homOfLE hVT).op s = σ V hV hne hVT := by
  let ι := {V : X.Opens // IsAffineOpen V ∧ (V : Set X).Nonempty ∧ V ≤ T}
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ⟨g.relativeDifferentials.presheaf, g.relativeDifferentials.isSheaf⟩
    (fun i : ι => i.1) T (fun i => homOfLE i.2.2.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVT⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx T.2
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, ⟨x, hxV⟩, hVT⟩, hxV⟩)
    (fun i => σ i.1 i.2.1 i.2.2.1 i.2.2.2) (by
      intro i j
      refine eq_of_affine_restrict (g := g) (i.1 ⊓ j.1) _ _ (fun W hW hWne hWij => ?_)
      change g.relativeDifferentials.presheaf.map (homOfLE hWij).op
          (g.relativeDifferentials.presheaf.map (homOfLE inf_le_left).op _) =
        g.relativeDifferentials.presheaf.map (homOfLE hWij).op
          (g.relativeDifferentials.presheaf.map (homOfLE inf_le_right).op _)
      rw [res_res, res_res]
      exact compat _ _ W i.2.1 j.2.1 hW i.2.2.1 j.2.2.1 hWne i.2.2.2 j.2.2.2 _ _)
  exact ⟨s, fun V hV hne hVT => hs ⟨V, hV, hne, hVT⟩⟩


/-- The image of `Φ_U` lies in `regularAt F w` as soon as `ψ_U(Γ(X, U)) ⊆ w`. -/
lemma Φ_mem_regularAt (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (w : ValuationSubring F) (hw : ∀ a, ψ e U hne a ∈ w) (s : Γ(g.relativeDifferentials, U)) :
    Φ g e U hU hne s ∈ ZInQ.Contrib.CurvesG.regularAt F w := by
  induction s using induction_affine U hU with
  | h0 => rw [map_zero]; exact zero_mem _
  | hadd x y hx hy => rw [map_add]; exact add_mem hx hy
  | hgen a b =>
    rw [Φ_smul_D]
    exact AddSubgroup.subset_closure ⟨_, _, hw a, hw b, rfl⟩

/-- **GLUE (proved below, `valuationCenter`): every place of the function field of a proper integral
`ℚ`-scheme has a center.** For `X` integral and proper over `ℚ` and a valuation subring `w` of the function
field containing `ℚ`, the coordinate ring of some affine open `V` maps into `w` (valuative criterion of
properness, Mathlib `UniversallyClosed.eq_valuativeCriterion`; Hartshorne II.4.7, UNVERIFIED number). -/
def ValuationCenter : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (g : X ⟶ Spec (CommRingCat.of ℚ)) [IsProper g]
    (w : ValuationSubring X.functionField), (∀ q : ℚ, (q : X.functionField) ∈ w) →
    ∃ (V : X.Opens) (hη : genericPoint X ∈ V), IsAffineOpen V ∧
      ∀ a : Γ(X, V), X.presheaf.germ V (genericPoint X) hη a ∈ w

theorem valuationCenter : ValuationCenter := by
  intro X _ g _ w hw
  have hE : ValuativeCriterion.Existence g := by
    have hU : UniversallyClosed g := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hU
    exact hU.1
  let φ₀ : ℚ →+* X.functionField :=
    (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp (g.specStructureMap ⊤).hom
  have hφ₀ : ∀ q, φ₀ q ∈ w.toSubring := fun q => by
    have : φ₀ q = (q : X.functionField) := eq_ratCast φ₀ q
    rw [this]; exact hw q
  let φ : ℚ →+* w := φ₀.codRestrict w.toSubring hφ₀
  let S : ValuativeCommSq g :=
    { R := w
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom φ)
      commSq := ⟨Spec.homEquiv.injective (CommRingCat.hom_ext (RingHom.ext_rat _ _))⟩ }
  obtain ⟨⟨l, hl1₀, -⟩⟩ := hE S
  have hl1 : Spec.map (CommRingCat.ofHom (algebraMap w X.functionField)) ≫ l =
      X.fromSpecStalk (genericPoint X) := hl1₀
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (l (IsLocalRing.closedPoint w)))
      isOpen_univ
  have hlV : l ⁻¹ᵁ V = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem l hxV
  have hη : genericPoint X ∈ V := generic_mem V ⟨_, hxV⟩
  refine ⟨V, hη, hV, fun a => ?_⟩
  have h2 : ∀ (f : Spec (CommRingCat.of X.functionField) ⟶ X)
      (_ : Spec.map (CommRingCat.ofHom (algebraMap w X.functionField)) ≫ l = f) (e),
      f.appLE V ⊤ e = l.appLE V ⊤ hlV.ge ≫
        (Spec.map (CommRingCat.ofHom (algebraMap w X.functionField))).appTop := by
    rintro f rfl e
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (algebraMap w X.functionField))) l
      V ⊤ ⊤ hlV.ge (by simp)]
    congr 1
  have he : (⊤ : (Spec (CommRingCat.of X.functionField)).Opens) ≤
      X.fromSpecStalk (genericPoint X) ⁻¹ᵁ V := by
    rw [← hl1]
    intro p _
    show l _ ∈ V
    rw [← Scheme.Hom.mem_preimage, hlV]
    trivial
  have h1 : (X.fromSpecStalk (genericPoint X)).appLE V ⊤ he ≫
      (Scheme.ΓSpecIso _).hom = X.presheaf.germ V (genericPoint X) hη := by
    have hid : ∀ (f : (Opposite.op (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens)) ⟶
        Opposite.op ⊤), (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map f = 𝟙 _ := fun f => by
      rw [Subsingleton.elim f (𝟙 _), CategoryTheory.Functor.map_id]
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hη, Category.assoc, Category.assoc, Category.assoc,
      ← Functor.map_comp_assoc, hid, Category.id_comp, Iso.inv_hom_id, Category.comp_id]
  have key := h1
  rw [h2 _ hl1, Category.assoc, Scheme.ΓSpecIso_naturality] at key
  rw [← key]
  exact Subtype.prop _

lemma ΦG_mem_holo [IsProper g] (s : Γ(g.relativeDifferentials, ⊤)) :
    ΦG g e s ∈ ZInQ.Contrib.CurvesG.holoDiff F := by
  refine Submodule.subset_span (fun w hw => ?_)
  obtain ⟨V, hη, hV, hw'⟩ := valuationCenter X g (w.comap e.toRingHom) (fun q => by
    rw [ValuationSubring.mem_comap]
    simpa [map_ratCast] using hw q)
  have hne : (V : Set X).Nonempty := ⟨_, hη⟩
  rw [ΦG_eq V hV hne]
  exact Φ_mem_regularAt V hV hne w (fun a => hw' a) _

/-- **Stalks at closed points of a smooth curve are valuation rings** (proved: regular local of
dimension one, `ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension` and Mathlib's
DVR TFAE). -/
lemma valuationRing_stalk [SmoothOfRelativeDimension 1 g] (x : X) (hx : IsClosed ({x} : Set X)) :
    ValuationRing (X.presheaf.stalk x) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have h := ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension g 1 x hx
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain
    (X.presheaf.stalk x)).out 6 2).mp h.le


omit [Algebra ℚ F] in
/-- The image of a valuation ring `R` in a field `F` that is a fraction field of `R` is a valuation
subring of `F`. -/
def imageVS {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R] (f : R →+* F)
    (hf : ∀ z : F, ∃ a b : R, f b ≠ 0 ∧ z * f b = f a) : ValuationSubring F where
  toSubring := f.range
  mem_or_inv_mem' z := by
    obtain ⟨a, b, hb, hz⟩ := hf z
    obtain ⟨c, hc | hc⟩ := ValuationRing.cond a b
    · by_cases ha : f a = 0
      · left
        have : z * f b = 0 := hz.trans ha
        rw [mul_eq_zero] at this
        rcases this with h | h
        · exact ⟨0, by rw [map_zero, h]⟩
        · exact absurd h hb
      · right
        refine ⟨c, ?_⟩
        have h1 : z * f a * f c = f a := by rw [mul_assoc, ← map_mul, hc, hz]
        have h2 : z * f c = 1 := mul_left_cancel₀ ha (by linear_combination h1)
        exact eq_inv_of_mul_eq_one_right h2
    · left
      refine ⟨c, ?_⟩
      have : f b * f c = f b * z := by rw [← map_mul, hc, ← hz, mul_comm]
      exact mul_left_cancel₀ hb this

omit [IsIntegral X] in
lemma key_identity (a b c d s u : F) (hc : c * s = a) (hd : d * u = b) :
    (s * u * u) • (c • KaehlerDifferential.D ℚ F d) =
      a • (u • KaehlerDifferential.D ℚ F b - b • KaehlerDifferential.D ℚ F u) := by
  subst hc hd
  rw [Derivation.leibniz]
  simp only [smul_add, smul_sub, smul_smul]
  module


lemma Φ_range_smul (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) (a : Γ(X, U))
    {η : Ω[F⁄ℚ]} (h : η ∈ (Φ g e U hU hne).range) : ψ e U hne a • η ∈ (Φ g e U hU hne).range := by
  obtain ⟨σ, rfl⟩ := h
  exact ⟨a • σ, Φ_smul U hU hne a σ⟩

/-- A maximal ideal of `Γ(X, V)` gives a closed point of `X` (`X` is Jacobson). -/
lemma isClosed_fromSpec [SmoothOfRelativeDimension 1 g] (V : X.Opens) (hV : IsAffineOpen V)
    (y : PrimeSpectrum Γ(X, V)) (hy : y.asIdeal.IsMaximal) : IsClosed ({hV.fromSpec y} : Set X) := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace g
  have hyc : IsClosed ({y} : Set (PrimeSpectrum Γ(X, V))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mpr hy
  have h := hV.fromSpec.isOpenEmbedding.preimage_closedPoints
  have hmem : y ∈ closedPoints (Spec Γ(X, V)) := hyc
  rw [← h] at hmem
  exact hmem

/-- **Local–global step.** A differential regular at every place lies in the image of `Φ_V`. -/
lemma mem_range_Φ_of_regular [SmoothOfRelativeDimension 1 g] (V : X.Opens) (hV : IsAffineOpen V)
    (hne : (V : Set X).Nonempty) (ω : Ω[F⁄ℚ])
    (hω : ∀ w : ValuationSubring F, (∀ c : ℚ, algebraMap ℚ F c ∈ w) →
      ω ∈ ZInQ.Contrib.CurvesG.regularAt F w) :
    ω ∈ (Φ g e V hV hne).range := by
  classical
  by_contra hnot
  let I : Ideal Γ(X, V) :=
    { carrier := {a | ψ e V hne a • ω ∈ (Φ g e V hV hne).range}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add, add_smul] at *
        exact add_mem ha hb
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero, zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, mul_smul] at *
        exact Φ_range_smul V hV hne c ha }
  have hI : I ≠ ⊤ := fun h => hnot (by
    have : (1 : Γ(X, V)) ∈ I := h ▸ Submodule.mem_top
    simpa [I] using this)
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hI
  let y : PrimeSpectrum Γ(X, V) := ⟨𝔪, h𝔪.isPrime⟩
  have hyV : hV.fromSpec y ∈ V := hV.range_fromSpec.subset ⟨y, rfl⟩
  have hxc := isClosed_fromSpec (g := g) V hV y h𝔪
  haveI := valuationRing_stalk (g := g) (hV.fromSpec y) hxc
  letI : Algebra Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) := (X.presheaf.germ V _ hyV).hom.toAlgebra
  haveI hloc : IsLocalization y.asIdeal.primeCompl (X.presheaf.stalk (hV.fromSpec y)) :=
    hV.isLocalization_stalk' y hyV
  haveI : Nonempty V := hne.to_subtype
  let f : X.presheaf.stalk (hV.fromSpec y) →+* F :=
    e.toRingHom.comp (algebraMap (X.presheaf.stalk (hV.fromSpec y)) X.functionField)
  have hf_germ : ∀ a, f (algebraMap Γ(X, V) (X.presheaf.stalk (hV.fromSpec y)) a) = ψ e V hne a := by
    intro a
    change e (algebraMap _ X.functionField (X.presheaf.germ V _ hyV a)) = _
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    rfl
  have hfrac : ∀ z : F, ∃ a b, f b ≠ 0 ∧ z * f b = f a := by
    intro z
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (hV.fromSpec y))
      (e.symm z)
    refine ⟨a, b, ?_, ?_⟩
    · exact fun h => (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := X.functionField) hb)
        (e.injective (h.trans (map_zero e).symm))
    · have hb' : algebraMap _ X.functionField b ≠ 0 :=
        IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := X.functionField) hb
      have h1 : algebraMap _ X.functionField a = e.symm z * algebraMap _ X.functionField b := by
        rw [← hab, div_mul_cancel₀ _ hb']
      have h2 := congrArg e h1
      rw [map_mul, RingEquiv.apply_symm_apply] at h2
      exact h2.symm
  let w := imageVS f hfrac
  have hwQ : ∀ c : ℚ, algebraMap ℚ F c ∈ w := by
    intro c
    refine ⟨(X.presheaf.germ V _ hyV).hom ((g.specStructureMap V).hom c), ?_⟩
    exact congrArg (· c) (RingHom.ext_rat
      (f.comp ((X.presheaf.germ V _ hyV).hom.comp (g.specStructureMap V).hom)) (algebraMap ℚ F))
  have key : ∀ η ∈ ZInQ.Contrib.CurvesG.regularAt F w,
      ∃ t : Γ(X, V), t ∉ 𝔪 ∧ ψ e V hne t • η ∈ (Φ g e V hV hne).range := by
    intro η hη
    induction hη using AddSubgroup.closure_induction with
    | mem η hη =>
      obtain ⟨c, d, ⟨c', rfl⟩, ⟨d', rfl⟩, rfl⟩ := hη
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl c'
      obtain ⟨⟨b, u⟩, rfl⟩ := IsLocalization.mk'_surjective y.asIdeal.primeCompl d'
      have hc : f (IsLocalization.mk' _ a s) * ψ e V hne s = ψ e V hne a := by
        rw [← hf_germ, ← hf_germ, ← map_mul, IsLocalization.mk'_spec]
      have hd : f (IsLocalization.mk' _ b u) * ψ e V hne u = ψ e V hne b := by
        rw [← hf_germ, ← hf_germ, ← map_mul, IsLocalization.mk'_spec]
      refine ⟨s * u * u, ?_, ?_⟩
      · have hs : (s : Γ(X, V)) ∉ 𝔪 := s.2
        have hu : (u : Γ(X, V)) ∉ 𝔪 := u.2
        intro h
        rcases h𝔪.isPrime.mem_or_mem h with h | h
        · rcases h𝔪.isPrime.mem_or_mem h with h | h
          · exact hs h
          · exact hu h
        · exact hu h
      · rw [map_mul, map_mul, key_identity _ _ _ _ _ _ hc hd]
        refine ⟨a • ((u : Γ(X, V)) • g.sectionsD V b - b • g.sectionsD V (u : Γ(X, V))), ?_⟩
        rw [Φ_smul, map_sub, Φ_smul_D, Φ_smul_D]
    | zero => exact ⟨1, fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
    | add η₁ η₂ _ _ h₁ h₂ =>
      obtain ⟨t₁, ht₁, h₁⟩ := h₁
      obtain ⟨t₂, ht₂, h₂⟩ := h₂
      refine ⟨t₁ * t₂, fun h => (h𝔪.isPrime.mem_or_mem h).elim ht₁ ht₂, ?_⟩
      have e1 := Φ_range_smul V hV hne t₂ h₁
      have e2 := Φ_range_smul V hV hne t₁ h₂
      have : ψ e V hne (t₁ * t₂) • (η₁ + η₂) =
          ψ e V hne t₂ • (ψ e V hne t₁ • η₁) + ψ e V hne t₁ • (ψ e V hne t₂ • η₂) := by
        rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm (ψ e V hne t₂)]
      rw [this]
      exact add_mem e1 e2
    | neg η _ h =>
      obtain ⟨t, ht, h⟩ := h
      exact ⟨t, ht, by rw [smul_neg]; exact neg_mem h⟩
  obtain ⟨t, ht, htω⟩ := key ω (hω w hwQ)
  exact ht (hI𝔪 htω)


/-- **Surjectivity onto the regular differentials**, by gluing the local preimages. -/
lemma mem_range_ΦG_of_regular [SmoothOfRelativeDimension 1 g] (ω : Ω[F⁄ℚ])
    (hω : ∀ w : ValuationSubring F, (∀ c : ℚ, algebraMap ℚ F c ∈ w) →
      ω ∈ ZInQ.Contrib.CurvesG.regularAt F w) :
    ω ∈ (ΦG g e).range := by
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  choose σ hσ using fun (V : X.Opens) (hV : IsAffineOpen V) (hne : (V : Set X).Nonempty) =>
    mem_range_Φ_of_regular (g := g) (e := e) V hV hne ω hω
  obtain ⟨s, hs⟩ := exists_glue (g := g) ⊤ (fun V hV hne _ => σ V hV hne) (by
    intro V V' W hV hV' hW hVne hV'ne hWne _ _ hWV hWV'
    apply Φ_injective (e := e) W hW hWne
    rw [Φ_res hWV hV hW hWne, Φ_res hWV' hV' hW hWne, hσ, hσ])
  refine ⟨s, ?_⟩
  rw [ΦG_eq (U₀ X) U₀_spec.1 ⟨_, U₀_spec.2⟩, hs (U₀ X) U₀_spec.1 ⟨_, U₀_spec.2⟩]
  exact hσ _ _ _

end DimJacGlue

namespace ModularSplit.DimJac

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves ZInQ.Contrib.CurvesG

/-- **GLUE (named, unproved): `H⁰(X, Ω¹_{X/ℚ})` is the space of differentials of the function field
regular at every place.** For a smooth proper geometrically connected integral curve `X/ℚ` and a field `F`
isomorphic to its function field, `dim_ℚ H⁰(X, Ω¹_{X/ℚ}) = g(F)` (`CurvesG.fieldGenus`, Chevalley's
definition). Needs: `H⁰(X, M) = Γ(X, M)` for the library's sheaf cohomology; `Γ(X, Ω¹) = ⋂_x Ω_{𝒪_{X,x}/ℚ}`
inside `Ω_{F/ℚ}` (`Ω¹` locally free of rank one, `X` integral; on affine opens `Γ(U, Ω¹) = Ω_{Γ(U)/ℚ}` is the
library's `Scheme.Hom.kaehlerSectionsEquiv`, then localization); the image of `Ω_{𝒪_{X,x}/ℚ}` in `Ω_{F/ℚ}` is
`CurvesG.regularAt F 𝒪_{X,x}`; every valuation subring of `F` containing `ℚ` other than `F` is a local ring
`𝒪_{X,x}` at a closed point (`X` proper: valuative criterion; `X` normal of dimension one: `𝒪_{X,x}` is a
DVR), and conversely. Standard (Hartshorne II.8, II.6.7, II.4.7; Stichtenoth 1.5; UNVERIFIED numbers);
project glue, no published-theorem content beyond textbook sheaf theory. -/
def H0DifferentialsEqHolo : Prop :=
  ∀ (X : Over SpecQ) (_ : IsCurve X) (_ : IsIntegral X.left) (F : Type) [Field F] [Algebra ℚ F],
    Nonempty (X.left.functionField ≃+* F) →
    letI : X.left.Over SpecQ := ⟨X.hom⟩
    (X.left ↘ SpecQ).relativeDifferentials.finrankH ℚ 0 = fieldGenus F

open DimJacGlue in
/-- **`H0DifferentialsEqHolo` holds** (Lean proof, no hypotheses). -/
theorem h0DifferentialsEqHolo : H0DifferentialsEqHolo := by
  intro X hX hI F _ _ he
  obtain ⟨e⟩ := he
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  have : IsProper (X.left ↘ SpecQ) := hX.proper
  have : SmoothOfRelativeDimension 1 (X.left ↘ SpecQ) := hX.smooth
  have : Smooth (X.left ↘ SpecQ) := SmoothOfRelativeDimension.smooth 1 _
  let g := X.left ↘ SpecQ
  let E1 := (Scheme.Modules.H.zeroLinearEquiv g.relativeDifferentials).toAddEquiv
  let Ψ : g.relativeDifferentials.H 0 →+ Ω[F⁄ℚ] := (ΦG g e).comp E1.toAddMonoidHom
  let L : g.relativeDifferentials.H 0 →ₗ[ℚ] Ω[F⁄ℚ] :=
    { toFun := Ψ
      map_add' := map_add Ψ
      map_smul' := map_rat_smul Ψ }
  have hL : Function.Injective L := (ΦG_injective (e := e)).comp E1.injective
  have hrange : LinearMap.range L = holoDiff F := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ΦG_mem_holo _
    · refine Submodule.span_le.mpr (fun ω hω => ?_)
      obtain ⟨s, hs⟩ := mem_range_ΦG_of_regular (g := g) (e := e) ω hω
      exact ⟨E1.symm s, by simp [L, Ψ, hs]⟩
  unfold Scheme.Modules.finrankH fieldGenus
  rw [← hrange]
  exact (LinearEquiv.ofInjective L hL).finrank_eq

/-- **Lean, from the vendored library: a Jacobian has dimension `arithmeticGenus = dim H¹(X, 𝒪_X)`.** -/
theorem dim_jacobian_eq_arithmeticGenus (X : Over SpecQ) (hX : IsCurve X) (P₀ : RatPt X)
    (J : PkgI3.AbVar ℚ) (aj : X ⟶ J.X) (hJ : IsJacobian X P₀ J aj) :
    letI : X.left.Over SpecQ := ⟨X.hom⟩
    J.dim = ((X.left.arithmeticGenus ℚ : ℕ) : WithBot ℕ∞) := by
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible X.hom := inferInstance
  have : SmoothOfRelativeDimension 1 (X.left ↘ SpecQ) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ SpecQ) := inferInstanceAs (IsProper X.hom)
  have : GeometricallyIntegral (X.left ↘ SpecQ) :=
    inferInstanceAs (GeometricallyIntegral X.hom)
  obtain ⟨variety, representation, tensorCompatible, hsm⟩ :=
    exists_abelianVariety_picardDegreeZero (baseField := ℚ) X.left
  let aj' : X ⟶ variety.group.X :=
    Curve.abelJacobiMap ⟨X⟩ P₀.left (by simp) representation
  have alb : IsAlbanese P₀ variety aj' :=
    Curve.isAlbanese_abelJacobiMap ⟨X⟩ P₀ variety representation tensorCompatible
  have : GeometricallyIntegral variety.group.X.hom :=
    Smooth.geometricallyIntegral variety.group.X.hom
  let J' : PkgI3.AbVar ℚ :=
    { X := variety.group.X
      grp := variety.group.grp
      proper := variety.proper
      smooth := variety.smooth
      geomInt := inferInstance }
  have hJ' : IsJacobian X P₀ J' aj' := by
    refine ⟨alb.1, ?_⟩
    intro A f hf
    obtain ⟨g, hg, huniq⟩ := alb.existsUnique_schemeMap f hf
    have pointed : η[variety.group.X] ≫ g = η[A.X] := by
      rw [← alb.1, Category.assoc, ← hg, hf]
    have : IsMonHom g := isMonHom_of_isProper_of_geometricallyIntegral g pointed
    exact ⟨g, ⟨inferInstance, hg.symm⟩, fun φ hφ => huniq φ hφ.2.symm⟩
  obtain ⟨e, -, -, -⟩ := IsJacobian.unique hJ hJ'
  have hiso : J.X.left ≅ variety.group.X.left := (Over.forget _).mapIso e
  have hne : Nonempty variety.group.X.left := by
    have : Nonempty (Spec (CommRingCat.of ℚ)) := inferInstance
    obtain ⟨x⟩ := this
    exact ⟨(η[variety.group.X] : 𝟙_ (Over SpecQ) ⟶ variety.group.X).left.base x⟩
  change topologicalKrullDim J.X.left = _
  rw [ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_iso hiso,
    ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension variety.group.X.hom
      (X.left.arithmeticGenus ℚ)]

/-- **Row dimJacobianEqGenus from the one glue statement `H0DifferentialsEqHolo`.** -/
theorem dimJacobianEqGenus_of_glue (hG : H0DifferentialsEqHolo) : DimJacobianEqGenus := by
  intro X hX P₀ J aj hJ hI F _ _ he
  letI : X.left.Over SpecQ := ⟨X.hom⟩
  have : IsProper X.hom := hX.proper
  have : SmoothOfRelativeDimension 1 X.hom := hX.smooth
  have : GeometricallyConnected X.hom := hX.geomConnected
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have : GeometricallyIntegral X.hom :=
    TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral X.hom
  have : GeometricallyIrreducible (X.left ↘ SpecQ) :=
    inferInstanceAs (GeometricallyIrreducible X.hom)
  have : SmoothOfRelativeDimension 1 (X.left ↘ SpecQ) :=
    inferInstanceAs (SmoothOfRelativeDimension 1 X.hom)
  have : IsProper (X.left ↘ SpecQ) := inferInstanceAs (IsProper X.hom)
  rw [dim_jacobian_eq_arithmeticGenus X hX P₀ J aj hJ,
    ← Scheme.Modules.finrankH_relativeDifferentials_zero_eq_genus (baseField := ℚ) (source := X.left),
    hG X hX hI F he]

/-- **The row `dimJacobianEqGenus` (bundle field, `ZInQ.Contrib.CurvesG.DimJacobianEqGenus`) holds**:
modular-split's reduction applied to `h0DifferentialsEqHolo`. -/
theorem dimJacobianEqGenus : DimJacobianEqGenus :=
  dimJacobianEqGenus_of_glue h0DifferentialsEqHolo

end ModularSplit.DimJac

example : ZInQ.Contrib.CurvesG.DimJacobianEqGenus := ModularSplit.DimJac.dimJacobianEqGenus





-- genus-route (LocalDer.lean, verbatim) follows

/-! # genus-route: `dim J₁(N) ≤ N²` without `GenusX1Field` and without `X0Transitive`

The single proof uses T34 (`DimJ1Genus`, assembled from `DimJacobianEqGenus` and `GenusX1Field`) only
through `LeafModCurves.dim_J1_le` (`dim J₁(N) ≤ N²`), at its two consumers (TailD E2 and
`javanpeykarJ1`). This file proves that bound, `DimJ1Le`, from

* `DimJacobianEqGenus` (kernel `ZInQ.Contrib.CurvesG`, proved outright by dimjac-glue) and
* `RiemannHurwitzQj` (leaf: Stichtenoth Thm 3.4.13 with Thm 3.5.1, over Mathlib's valuation subrings),

with no other hypothesis: `dimJ1Le_of_rh_curve`.

Contents.
1. (copied from `scratch/curve-split/CurveBij.lean`, verbatim up to the namespace) integral smooth
   curves over a field are normal.
2. (new, proved) `constantFieldIsQ_of_curve`: `ℚ` is algebraically closed in the function field of a
   smooth proper geometrically connected integral curve over `ℚ`. This replaces curve-split's use of
   `X0Transitive` (through `x1ConstantField_of_x0Transitive`): the constant field of `K_N` is read off
   from the model `X` of `X₁(N)` that `IsJ1` already provides.
3. (copied from `scratch/curve-split/GenusBound.lean`, verbatim up to the namespace `CurveSplit` →
   `GenusRoute`) `belyiGenusBound_of_rh : RiemannHurwitzQj → BelyiGenusBound` (the fundamental identity
   at `j = 0, 1728, ∞` is proved there from Mathlib).
4. (new, proved) `dimJ1Le_of_rh_curve : DimJacobianEqGenus → RiemannHurwitzQj → DimJ1Le`.
5. (new, proved; `GenusElem.lean` only) `dimJ1Le_of_localDerivation : DimJacobianEqGenus →
   LocalDerivation → DimJ1Le`: the genus bound `g(K_N) ≤ [K_N : ℚ(j)]` from the local leaf
   `LocalDerivation` (`d/dπ` preserves `𝒪_P` for a local parameter `π`), with no Riemann–Hurwitz:
   holomorphic differentials are `h · dj` with `h` in an explicit space `V`, and `V` injects into
   `OF / j·OF ≅ ℚ^d` (`OF` the integral closure of `ℚ[j]`).
6. (new, proved; `LocalDer.lean`) `localDerivation : LocalDerivation`, hence
   `dimJ1Le_of_dimJacobianEqGenus : DimJacobianEqGenus → DimJ1Le` (no literature leaf). Proof: `d/dj`
   exists (`Ω_{F/ℚ} = F·dj ≠ 0`, since `F/ℚ` is not formally unramified); it is bounded on `𝒪_P` (a
   `ℚ[j]`-basis of `OF` and `𝒪_P = OF_𝔭`); the residue field `OF/𝔭` is finite over `ℚ` (Zariski) with a
   primitive element `θ̄`; writing `x = p(θ) + π y`, `g(θ) = π z` improves the bound step by step, which
   forces `δ_j(π) ≠ 0` and `δ_j(𝒪_P) ⊆ δ_j(π)·𝒪_P`; `δ = δ_j / δ_j(π)`. Places over `∞`: twist `j ↦ 1/j`.

No `sorry`, no `axiom`. -/

noncomputable section





namespace GenusRoute

open CategoryTheory AlgebraicGeometry Limits Polynomial
open scoped TensorProduct

/-- `⊤` is nonempty on a nonempty scheme. -/
instance instNonemptyTop (X : Scheme) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Nonempty.some ‹_›, trivial⟩⟩

/-- `Spec k`. -/
abbrev SpecK (k : Type) [Field k] : Scheme := Spec (CommRingCat.of k)

/-! ## Normality of integral smooth curves (copied verbatim from `scratch/curve-split/CurveBij.lean`) -/

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- In a Jacobson space of dimension `≤ 1`, the closure of a non-closed point is an irreducible
component. -/
theorem closure_mem_irreducibleComponents [JacobsonSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {a : X} (ha : ¬ IsClosed ({a} : Set X)) : closure {a} ∈ irreducibleComponents X := by
  let A : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩
  obtain ⟨p, hpA, hpc⟩ := nonempty_inter_closedPoints (Z := closure ({a} : Set X))
    ⟨a, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hpc' : IsClosed ({p} : Set X) := hpc
  let P : TopologicalSpace.IrreducibleCloseds X := ⟨{p}, isIrreducible_singleton, hpc'⟩
  have hPA : P < A := by
    refine lt_of_le_of_ne ?_ ?_
    · show ({p} : Set X) ⊆ closure {a}
      exact Set.singleton_subset_iff.mpr hpA
    · intro h
      have h' : ({p} : Set X) = closure {a} := congrArg (fun Z : TopologicalSpace.IrreducibleCloseds X => (Z : Set X)) h
      apply ha
      have : a ∈ ({p} : Set X) := h' ▸ subset_closure rfl
      rw [Set.mem_singleton_iff.mp this]; exact hpc'
  have hmax : IsMax A := by
    rcases (Order.krullDim_le_one_iff.mp hdim) A with h | h
    · exact absurd (h hPA.le) (not_le_of_gt hPA)
    · exact h
  refine ⟨isIrreducible_singleton.closure, fun s hs hsub => ?_⟩
  let S : TopologicalSpace.IrreducibleCloseds X := ⟨closure s, hs.closure, isClosed_closure⟩
  have hAS : A ≤ S := hsub.trans subset_closure
  have := hmax hAS
  exact subset_closure.trans this

end Topo

section Curves

open IsLocalRing

/-- **A Noetherian local ring of Krull dimension 1 with principal maximal ideal is a domain.**
Copied from `scratch/curve-glue/CIproof.lean.part` (`CurveGlueCI.isDomain_of_dim_one`). -/
theorem isDomain_of_dim_one {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (hspan : (maximalIdeal R).spanFinrank = 1) : IsDomain R := by
  classical
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  obtain ⟨s, hs, hspan'⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
  rw [hspan] at hs
  obtain ⟨π, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
  have hπ : ∀ n : ℕ, π ^ n ≠ 0 := by
    intro n hn
    have hsub : ∀ p : PrimeSpectrum R, p.asIdeal = maximalIdeal R := by
      intro p
      refine le_antisymm (le_maximalIdeal p.2.ne_top) ?_
      rw [← hspan', Ideal.span_le, Set.singleton_subset_iff]
      exact p.2.mem_of_pow_mem n (by rw [hn]; exact p.asIdeal.zero_mem)
    have : Subsingleton (PrimeSpectrum R) :=
      ⟨fun p q => PrimeSpectrum.ext ((hsub p).trans (hsub q).symm)⟩
    have h0 : ringKrullDim R = 0 := Order.krullDim_eq_zero
    rw [hdim] at h0
    norm_num at h0
  have hdec : ∀ a : R, a ≠ 0 → ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
    intro a ha
    have hex : ∃ k : ℕ, a ∉ maximalIdeal R ^ k := by
      by_contra! h
      apply ha
      have := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
      rw [← Submodule.mem_bot R, ← this, Submodule.mem_iInf]
      exact h
    let k := Nat.find hex
    have hk : a ∉ maximalIdeal R ^ k := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      apply hk
      rw [h0, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := Nat.exists_eq_succ_of_ne_zero hk0
    have hmem : a ∈ maximalIdeal R ^ n := by
      have := Nat.find_min hex (show n < k by omega)
      push Not at this
      exact this
    rw [← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
    obtain ⟨u, hu⟩ := hmem
    refine ⟨n, u, ?_, by rw [← hu, mul_comm]⟩
    by_contra hu'
    have hum : u ∈ maximalIdeal R := (mem_maximalIdeal u).2 hu'
    rw [← hspan', Ideal.mem_span_singleton'] at hum
    obtain ⟨w, hw⟩ := hum
    apply hk
    rw [hn, ← hspan', Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    exact ⟨w, by rw [← hu, ← hw]; ring⟩
  have : NoZeroDivisors R := by
    refine ⟨fun {a b} hab => ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n, u, hu, rfl⟩ := hdec a hne.1
    obtain ⟨m, v, hv, rfl⟩ := hdec b hne.2
    have : π ^ (n + m) * (u * v) = 0 := by rw [← hab]; ring
    exact hπ (n + m) ((hu.mul hv).mul_left_eq_zero.mp this)
  exact NoZeroDivisors.to_isDomain R

variable {k : Type} [Field k]

/-- The local ring at a closed point of a smooth curve over a field is a discrete valuation ring
(domain, integrally closed). -/
theorem stalk_closed_normal {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨h1, h2⟩ := ZInQ.Contrib.Dim.ringKrullDim_stalk_of_smoothOfRelativeDimension f 1 x hx
  have hd : IsDomain (X.presheaf.stalk x) :=
    isDomain_of_dim_one (by exact_mod_cast h1) (by exact_mod_cast h2)
  have h3 := ZInQ.Contrib.Dim.finrank_cotangentSpace_of_smoothOfRelativeDimension f 1 x hx
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp h3
  exact ⟨hd, inferInstance⟩

/-- A smooth curve over a field has topological dimension `≤ 1`. -/
theorem topDim_le_one {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f] :
    topologicalKrullDim X ≤ 1 := by
  rcases isEmpty_or_nonempty X with hE | hN
  · have : IsEmpty (TopologicalSpace.IrreducibleCloseds X) :=
      ⟨fun Z => hE.elim Z.2.nonempty.some⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  · rw [ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_smoothOfRelativeDimension f 1]
    rfl

/-- An integral smooth curve over a field is normal. -/
theorem isNormal_of_integral {X : Scheme} (f : X ⟶ SpecK k) [SmoothOfRelativeDimension 1 f]
    [IsIntegral X] : ZInQ.Contrib.CurvesG.IsNormalScheme X := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro x
  by_cases hx : IsClosed ({x} : Set X)
  · exact (stalk_closed_normal f x hx).2
  · have hC := closure_mem_irreducibleComponents (topDim_le_one f) hx
    have huniv : closure ({x} : Set X) = Set.univ :=
      (hC.eq_of_subset (IrreducibleSpace.isIrreducible_univ X) (Set.subset_univ _)).symm ▸ rfl
    have hgx : IsGenericPoint x Set.univ := huniv
    have : x = genericPoint X := hgx.eq (genericPoint_spec X)
    subst this
    show IsIntegrallyClosed X.functionField
    infer_instance

end Curves

/-- The ring of sections of a normal integral scheme over a nonempty affine open is integrally
closed. -/
theorem isIntegrallyClosed_of_normal {Y : Scheme} [IsIntegral Y]
    (hN : ZInQ.Contrib.CurvesG.IsNormalScheme Y) {V : Y.Opens} (hV : IsAffineOpen V)
    [Nonempty V] : IsIntegrallyClosed Γ(Y, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP => ?_
  let y : PrimeSpectrum Γ(Y, V) := ⟨P, hP.isPrime⟩
  have hy : hV.fromSpec y ∈ V := by
    have h := hV.range_fromSpec
    rw [Set.ext_iff] at h
    exact (h _).mp ⟨y, rfl⟩
  let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨hV.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime (Y.presheaf.stalk (hV.fromSpec y)) P :=
    hV.isLocalization_stalk' y hy
  have : IsIntegrallyClosed (Y.presheaf.stalk (hV.fromSpec y)) := hN _
  exact IsIntegrallyClosed.of_equiv
    (IsLocalization.algEquiv P.primeCompl (Y.presheaf.stalk (hV.fromSpec y))
      (Localization.AtPrime P)).toRingEquiv


/-! ## Algebraic elements of the function field are global sections -/

section Sections

/-- **Gluing (proved).** On an integral scheme, an element of the function field that comes from
`Γ(X, U)` for every nonempty affine open `U` comes from `Γ(X, ⊤)`. -/
theorem exists_global_section {X : Scheme} [IsIntegral X] (y : X.functionField)
    (h : ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U],
      ∃ s : Γ(X, U), X.germToFunctionField U s = y) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = y := by
  let ι := {U : X.Opens // IsAffineOpen U ∧ Nonempty U}
  let V : ι → X.Opens := fun i => i.1
  have hne : ∀ i : ι, Nonempty (V i) := fun i => i.2.2
  have h' : ∀ i : ι, ∃ s : Γ(X, V i), X.germToFunctionField (V i) s = y :=
    fun i => @h i.1 i.2.1 i.2.2
  choose sf hsf using h'
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW, ⟨⟨x, hxW⟩⟩⟩, hxW⟩
  have hinter : ∀ i j : ι, Nonempty ((V i ⊓ V j : X.Opens) : Set X) := by
    intro i j
    obtain ⟨x, hx⟩ := nonempty_preirreducible_inter (V i).isOpen (V j).isOpen
      ⟨_, (hne i).some.2⟩ ⟨_, (hne j).some.2⟩
    exact ⟨⟨x, hx⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 V sf := by
    intro i j
    apply @Scheme.germToFunctionField_injective X _ (V i ⊓ V j) (hinter i j)
    change X.presheaf.germ _ _ _ (X.presheaf.map _ (sf i)) =
      X.presheaf.germ _ _ _ (X.presheaf.map _ (sf j))
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply]
    exact (hsf i).trans (hsf j).symm
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcover sf hcompat
  let s' : Γ(X, ⊤) := s
  refine ⟨s', ?_⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let i : ι := ⟨W, hW, ⟨⟨x, hxW⟩⟩⟩
  have := hne i
  have hsi : X.presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s' = sf i := hs i
  rw [← hsf i, ← hsi, X.presheaf.germ_res_apply]

/-- **Integrality (proved).** On a normal integral scheme, an element of the function field
integral over `Γ(X, U)` for every nonempty affine open `U` is a global section. -/
theorem exists_global_of_isIntegral {X : Scheme} [IsIntegral X]
    (hN : ZInQ.Contrib.CurvesG.IsNormalScheme X) (y : X.functionField)
    (hy : ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U], IsIntegral Γ(X, U) y) :
    ∃ s : Γ(X, ⊤), X.germToFunctionField ⊤ s = y := by
  apply exists_global_section
  intro U hU _
  haveI := isIntegrallyClosed_of_normal hN hU
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hy U hU)
  exact ⟨s, hs⟩

end Sections

/-! ## The constant field -/

section ConstField

/-- Morphisms to `Spec ℚ` are unique. -/
theorem hom_specQ_ext {X : Scheme} (f g : X ⟶ SpecK ℚ) : f = g := by
  apply ext_of_isAffine
  have h : f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom =
      g.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom := RingHom.ext_rat _ _
  ext a
  have := congrArg (fun φ => φ ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).hom a)) h
  simpa using this

/-- The prime spectrum of a field is a single point. -/
theorem subsingleton_primeSpectrum_field (A : Type) [Field A] : Subsingleton (PrimeSpectrum A) := by
  refine ⟨fun p q => PrimeSpectrum.ext ?_⟩
  have hp : p.asIdeal = ⊥ := (Ideal.eq_bot_or_top p.asIdeal).resolve_right p.2.ne_top
  have hq : q.asIdeal = ⊥ := (Ideal.eq_bot_or_top q.asIdeal).resolve_right q.2.ne_top
  rw [hp, hq]

/-- **Two distinct roots give two points (proved).** If a polynomial `q` over `ℚ` with `ℚ[T]/(q)`
a field has two distinct roots in `ℚ̄`, then `Spec (ℚ̄ ⊗ ℚ[T]/(q))` has two distinct points. -/
theorem not_subsingleton_of_roots (q : ℚ[X]) [Fact (Irreducible q)] {α β : AlgebraicClosure ℚ}
    (hα : q.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) α = 0)
    (hβ : q.eval₂ (algebraMap ℚ (AlgebraicClosure ℚ)) β = 0) (hne : α ≠ β) :
    ¬ Subsingleton (PrimeSpectrum (AlgebraicClosure ℚ ⊗[ℚ] AdjoinRoot q)) := by
  intro hS
  let Qb := AlgebraicClosure ℚ
  have hα' : q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) α = 0 := hα
  have hβ' : q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) β = 0 := hβ
  let χ : ∀ γ : Qb, q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) γ = 0 → (Qb ⊗[ℚ] AdjoinRoot q →ₐ[ℚ] Qb) :=
    fun γ hγ => Algebra.TensorProduct.productMap (AlgHom.id ℚ Qb)
        (AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ Qb) γ hγ)
  let P : ∀ γ : Qb, q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) γ = 0 → PrimeSpectrum (Qb ⊗[ℚ] AdjoinRoot q) :=
    fun γ hγ => ⟨RingHom.ker (χ γ hγ : Qb ⊗[ℚ] AdjoinRoot q →+* Qb), RingHom.ker_isPrime _⟩
  let z : Qb ⊗[ℚ] AdjoinRoot q := 1 ⊗ₜ AdjoinRoot.root q - α ⊗ₜ 1
  have hz : ∀ γ (hγ : q.eval₂ ((Algebra.ofId ℚ Qb : ℚ →ₐ[ℚ] Qb) : ℚ →+* Qb) γ = 0), χ γ hγ z = γ - α := by
    intro γ hγ
    have e1 : χ γ hγ (1 ⊗ₜ AdjoinRoot.root q) = γ := by
      change (1 : Qb) * AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ Qb) γ hγ (AdjoinRoot.root q) = γ
      rw [AdjoinRoot.liftAlgHom_root, one_mul]
    have e2 : χ γ hγ (α ⊗ₜ 1) = α := by
      change α * AdjoinRoot.liftAlgHom q (Algebra.ofId ℚ Qb) γ hγ 1 = α
      rw [map_one, mul_one]
    simp only [z, map_sub, e1, e2]
  have h1 : z ∈ (P α hα').asIdeal := by
    show (χ α hα' : Qb ⊗[ℚ] AdjoinRoot q →+* Qb) z = 0
    simp [hz α hα']
  have h2 : z ∉ (P β hβ').asIdeal := by
    show ¬ (χ β hβ' : Qb ⊗[ℚ] AdjoinRoot q →+* Qb) z = 0
    simp only [AlgHom.coe_toRingHom, hz β hβ']
    exact sub_ne_zero.mpr hne.symm
  exact h2 (Subsingleton.elim (P α hα') (P β hβ') ▸ h1)

/-- **The constant field of a smooth geometrically connected integral curve over `ℚ` is `ℚ`
(proved).** An element of `K(X)` algebraic over `ℚ` is rational. -/
theorem algebraic_mem_range {X : Scheme} (p : X ⟶ SpecK ℚ) [IsIntegral X]
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p] (ι : ℚ →+* X.functionField) (y : X.functionField) (f : ℚ[X])
    (hf : f ≠ 0) (hy : f.eval₂ ι y = 0) : y ∈ Set.range ι := by
  letI : Algebra ℚ X.functionField := ι.toAlgebra
  have hint : IsIntegral ℚ y := (show IsAlgebraic ℚ y from ⟨f, hf, by rwa [aeval_def]⟩).isIntegral
  have hN := isNormal_of_integral p
  let ιΓ : ℚ →+* Γ(X, ⊤) := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom
  have hyU : ∀ U : X.Opens, IsAffineOpen U → ∀ [Nonempty U], IsIntegral Γ(X, U) y := by
    intro U hU _
    let g : ℚ →+* Γ(X, U) := (X.presheaf.map (homOfLE le_top).op).hom.comp ιΓ
    refine ⟨(minpoly ℚ y).map g, (minpoly.monic hint).map g, ?_⟩
    rw [eval₂_map]
    have : (algebraMap Γ(X, U) X.functionField).comp g = algebraMap ℚ X.functionField :=
      RingHom.ext_rat _ _
    rw [this, ← aeval_def, minpoly.aeval]
  obtain ⟨s, hs⟩ := exists_global_of_isIntegral hN y hyU
  set q := minpoly ℚ y with hqdef
  haveI : Fact (Irreducible q) := ⟨minpoly.irreducible hint⟩
  have hqs : q.eval₂ ιΓ s = 0 := by
    apply X.germToFunctionField_injective ⊤
    rw [map_zero, hom_eval₂, hs]
    have : (X.germToFunctionField ⊤).hom.comp ιΓ = algebraMap ℚ X.functionField :=
      RingHom.ext_rat _ _
    rw [this, ← aeval_def, minpoly.aeval]
  let A := AdjoinRoot q
  let ψ : A →+* Γ(X, ⊤) := AdjoinRoot.lift ιΓ s hqs
  let φ : X ⟶ Spec (CommRingCat.of A) := X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  let π : Spec (CommRingCat.of A) ⟶ SpecK ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ A))
  let Qb := AlgebraicClosure ℚ
  let ι' : SpecK Qb ⟶ SpecK ℚ := Spec.map (CommRingCat.ofHom (algebraMap ℚ Qb))
  have hp : p = φ ≫ π := hom_specQ_ext _ _
  haveI : GeometricallyConnected (φ ≫ π) := hp ▸ inferInstance
  have hc1 : ConnectedSpace ↥(pullback (φ ≫ π) ι') :=
    GeometricallyConnected.geometrically_connectedSpace ι' (pullback.fst _ _) (pullback.snd _ _)
      (IsPullback.of_hasPullback _ _)
  have hc2 : ConnectedSpace ↥(pullback φ (pullback.fst π ι')) :=
    (pullbackRightPullbackFstIso π ι' φ).hom.homeomorph.connectedSpace_iff.mpr hc1
  haveI : Subsingleton (Spec (CommRingCat.of A)) := subsingleton_primeSpectrum_field A
  haveI : Surjective φ := ⟨fun a => ⟨(inferInstance : Nonempty X).some, Subsingleton.elim _ _⟩⟩
  have hsurj : Function.Surjective (pullback.snd φ (pullback.fst π ι')) :=
    (inferInstance : Surjective (pullback.snd φ (pullback.fst π ι'))).surj
  have hc3 : ConnectedSpace ↥(pullback π ι') :=
    hsurj.connectedSpace (pullback.snd φ (pullback.fst π ι')).continuous
  have hc4 : ConnectedSpace ↥(pullback ι' π) :=
    (pullbackSymmetry π ι').hom.homeomorph.connectedSpace_iff.mp hc3
  have hc5 : ConnectedSpace (PrimeSpectrum (Qb ⊗[ℚ] A)) :=
    (pullbackSpecIso ℚ Qb A).hom.homeomorph.connectedSpace_iff.mp hc4
  haveI : IsArtinianRing (Qb ⊗[ℚ] A) := IsArtinianRing.of_finite Qb (Qb ⊗[ℚ] A)
  have hsub : Subsingleton (PrimeSpectrum (Qb ⊗[ℚ] A)) :=
    ⟨fun a b => isPreconnected_univ.subsingleton (Set.mem_univ a) (Set.mem_univ b)⟩
  have hdeg : q.natDegree ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have hsep : q.Separable := (minpoly.irreducible hint).separable
    have hcard := card_rootSet_eq_natDegree (K := Qb) hsep (IsAlgClosed.splits _)
    obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩, hne⟩ := Fintype.exists_pair_of_one_lt_card (by rw [hcard]; omega)
    have hα' := (mem_rootSet.mp hα).2
    have hβ' := (mem_rootSet.mp hβ).2
    rw [aeval_def] at hα' hβ'
    exact not_subsingleton_of_roots q hα' hβ' (fun h => hne (Subtype.ext h)) hsub
  have h1 : q.natDegree = 1 := le_antisymm hdeg (minpoly.natDegree_pos hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h1
  exact ⟨c, hc⟩

end ConstField

/-- **`ConstantFieldIsQ` for every field isomorphic to the function field of a curve (proved).**
For a smooth proper geometrically connected integral curve `X/ℚ` and a field `F ≅ K(X)` over
`ℚ(j)`, `ℚ` is algebraically closed in `F`. -/
theorem constantFieldIsQ_of_curve (X : Over LeafModCurves.SpecQ) (hC : LeafModCurves.IsCurve X)
    [IsIntegral X.left] (F : Type) [Field F] [Algebra LeafModCurves.Qj F]
    (e : X.left.functionField ≃+* F) : X1Belyi.ConstantFieldIsQ F := by
  rintro x ⟨f, hf, hx⟩
  haveI : SmoothOfRelativeDimension 1 X.hom := hC.smooth
  haveI : GeometricallyConnected X.hom := hC.geomConnected
  let ι : ℚ →+* X.left.functionField := e.symm.toRingHom.comp (X1Belyi.ratHom F)
  have hy : f.eval₂ ι (e.symm x) = 0 := by
    have := hom_eval₂ f (X1Belyi.ratHom F) e.symm.toRingHom x
    rw [hx, map_zero] at this
    exact this.symm
  obtain ⟨c, hc⟩ := algebraic_mem_range X.hom ι (e.symm x) f hf hy
  refine ⟨c, ?_⟩
  have := congrArg e hc
  simpa [ι] using this

end GenusRoute







namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-- **GLUE (lit-composite): the Riemann–Hurwitz bound for Belyi functions.** Let `F` be a finite
extension of `ℚ(j)` (`Qj = RatFunc ℚ`) in which `ℚ` is algebraically closed, and suppose
`t = j/1728` is a Belyi function on `F` over `ℚ` (`IsBelyiFunction`: unramified over every finite
place of `ℚ(t)` other than `t = 0, 1`). Then `2 g(F) + 1 ≤ [F : ℚ(j)]`, `g = fieldGenus`.

Why true (STANDARD): Riemann–Hurwitz (Stichtenoth, *Algebraic function fields and codes*, Thm
3.4.13, with Dedekind's different theorem Thm 3.5.1 in characteristic 0; Hartshorne IV.2.4
geometrically; numbers UNVERIFIED) gives `2g − 2 = −2d + Σ_P (e_P − 1) deg P`, the sum over the
places above `t = 0, 1, ∞` only; at each of these three degree-one places the fundamental
identity `Σ_{P|Q} e_P f_P = d` (Stichtenoth Thm 3.1.11) gives `Σ_{P|Q} (e_P − 1) f_P ≤ d − 1`; so
`2g − 2 ≤ d − 3`. Also needed: the places of `F/ℚ` are discrete valuation rings (Stichtenoth Thm
1.1.6) to read `IsBelyiFunction` as `e_P = 1`, and `fieldGenus` (holomorphic differentials) is the
Riemann–Roch genus (Stichtenoth Thm 1.5.15 / Chevalley; UNVERIFIED). A Lean proof needs Lean
statements of these four textbook results over Mathlib's `ValuationSubring` (places, `e_P` as the
index of `Uₚ·ℚ(t)ˣ` in `Fˣ`, `deg P` as the `ℚ`-dimension of the residue field) and about 400
lines of valuation-theoretic glue. -/
def BelyiGenusBound : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      2 * fieldGenus F + 1 ≤ Module.finrank Qj F

/-- **The genus bound that the proof uses** (weaker than `GenusX1Field`): `g(K_N) ≤ N²`. -/
def GenusX1Le : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    fieldGenus (fieldX1 P) ≤ N ^ 2

/-- **The conclusion of `LeafModCurves.dim_J1_le`** (`dim J₁(N) ≤ N²`), the only use of T34. -/
def DimJ1Le : Prop :=
  ∀ (N : ℕ) (J : PkgI3.AbVar ℚ), 0 < N → IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2

/-- `GenusX1Field → GenusX1Le` (proved, from `genus_Gamma1_le`). -/
theorem genusX1Le_of_genusX1Field (h : GenusX1Field) : GenusX1Le := by
  intro N P hN hP
  have : NeZero N := ⟨hN.ne'⟩
  have h1 := h N P hN hP
  have h2 := genus_Gamma1_le N
  rw [← h1] at h2
  exact_mod_cast h2

/-- **`DimJ1Le` from the first half of T34 and the genus bound** (proved). -/
theorem dimJ1Le_of (h1 : DimJacobianEqGenus) (h2 : GenusX1Le) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, h2 N P hN hP⟩

/-- `K_N` is finite over `ℚ(j)`. -/
instance fieldX1_finiteDimensional (P : EjBar.toAffine.Point) :
    FiniteDimensional Qj (fieldX1 P) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (xCoord P))

/-- **`GenusX1Le` from the Riemann–Hurwitz bound for Belyi functions and `X₀(N)`-transitivity**
(proved; `BelyiX1` and the constant field are kernel theorems). -/
theorem genusX1Le_of_belyi (hB : BelyiGenusBound) (h0 : ZInQ.RLeaf.X0Transitive) :
    GenusX1Le := by
  intro N P hN hP
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hK := ZInQ.RLeaf.x1ConstantField_of_x0Transitive h0 N P hN hP
  have := hB (fieldX1 P) hK hBel
  omega

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, `BelyiGenusBound` and
`X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_belyi (h1 : DimJacobianEqGenus) (hB : BelyiGenusBound)
    (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of h1 (genusX1Le_of_belyi hB h0)

/-! ## `BelyiGenusBound` from three textbook theorems

Places of a function field `F/ℚ` are Mathlib `ValuationSubring`s; the ramification index over
`ℚ(j)` is the index of `U_P · ℚ(j)ˣ` in `Fˣ` (`Fˣ/U_P` is the value group), the degree of a place
is the `ℚ`-dimension of its residue field. -/

section RH

variable (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- A place of `F/ℚ`: a proper valuation subring containing `ℚ`. -/
structure Place where
  w : ValuationSubring F
  ne_top : w ≠ ⊤
  rat_mem : ∀ c : ℚ, algebraMap ℚ F c ∈ w

variable {F}

theorem Place.ext' {P Q : Place F} (h : P.w = Q.w) : P = Q := by
  cases P; cases Q; cases h; rfl

/-- `ℚ → κ(P)`. -/
def Place.ratHom (P : Place F) : ℚ →+* IsLocalRing.ResidueField P.w :=
  (IsLocalRing.residue P.w).comp ((algebraMap ℚ F).codRestrict P.w.toSubring P.rat_mem)

/-- The degree `[κ(P) : ℚ]` of a place. -/
def Place.deg (P : Place F) : ℕ :=
  @Module.finrank ℚ (IsLocalRing.ResidueField P.w) _ _ P.ratHom.toModule

/-- The ramification index `e(P | P ∩ ℚ(j))`: the index of `U_P · ℚ(j)ˣ` in `Fˣ`. -/
def Place.ramIdx (P : Place F) : ℕ :=
  (P.w.unitGroup ⊔ (Units.map (algebraMap Qj F : Qj →* F)).range).index

/-- The Belyi coordinate `t = j/1728` in `F`. -/
abbrev tF : F := algebraMap Qj F (RatFunc.X / 1728)

variable (F)

/-- **Leaf: Riemann–Hurwitz for `F/ℚ(j)`** (published). For `F` finite over `ℚ(j)` with
constant field `ℚ`: only finitely many places ramify, and
`2 g(F) − 2 = [F : ℚ(j)] · (2·0 − 2) + Σ_P (e_P − 1) deg P`.
Source: Stichtenoth, *Algebraic Function Fields and Codes* (2nd ed.), Thm 3.4.13 (Hurwitz genus
formula, `g(ℚ(j)) = 0`) with Thm 3.5.1 (Dedekind's different theorem: `d(P) = e_P − 1` in
characteristic 0); Hartshorne IV.2.4 geometrically (numbers UNVERIFIED). The genus is
`fieldGenus` (the dimension of the holomorphic differentials, which equals the Riemann–Roch genus:
Stichtenoth Thm 1.5.15 / Hartshorne II.8, UNVERIFIED): a composite of these printed statements. -/
def RiemannHurwitzQj : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
      ∃ h : (Function.support fun P : Place F => ((P.ramIdx : ℤ) - 1) * P.deg).Finite,
        2 * (fieldGenus F : ℤ) - 2 =
          -2 * (Module.finrank Qj F : ℤ) + ∑ P ∈ h.toFinset, ((P.ramIdx : ℤ) - 1) * P.deg

/-- **Leaf: the fundamental identity at the places `j = 0`, `j = 1728`, `j = ∞` of `ℚ(j)`**
(published). For `F` finite over `ℚ(j)` and `Q` one of these three places of degree one, finitely
many places `P` of `F` lie over `Q` and `Σ_{P|Q} e_P deg P = [F : ℚ(j)]`.
Source: Stichtenoth Thm 3.1.11 (`Σ e(P|Q) f(P|Q) = [F : ℚ(j)]`) with `deg P = f(P|Q) deg Q` and
`deg Q = 1` (Stichtenoth §3.1; numbers UNVERIFIED). `P` lies over `j = 0` iff `t ∈ 𝔪_P`, over
`j = 1728` iff `t − 1 ∈ 𝔪_P`, over `j = ∞` iff `t ∉ 𝒪_P` (`t = j/1728`). -/
def FundamentalIdentityQj : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ∀ Z ∈ ({{P : Place F | tF ∈ P.w ∧ tF ∈ P.w.nonunits},
        {P : Place F | tF ∈ P.w ∧ tF - 1 ∈ P.w.nonunits},
        {P : Place F | tF ∉ P.w}} : Set (Set (Place F))),
      ∃ h : Z.Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F

/-- **Leaf: places of a function field are discrete valuation rings** (published). Every place
`P` of `F/ℚ` has a uniformizer `π`: `π ∈ 𝒪_P` is not a unit, and every `x ∈ Fˣ` is `π^n` times a
unit of `𝒪_P`. Source: Stichtenoth Thm 1.1.6 with Def. 1.1.4 / Thm 1.1.5 (numbers UNVERIFIED). -/
def PlacesAreDVR : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ∀ P : Place F, ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup

end RH

section Glue

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- Valuation of a `ℤ`-power of a unit. -/
theorem val_zpow (A : ValuationSubring F) (x : Fˣ) (n : ℤ) :
    A.valuation ((x ^ n : Fˣ) : F) = A.valuation (x : F) ^ n := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀]

/-- **`e_P = 1` when a uniformizer comes from `ℚ(j)`** (proved). If `P` has a uniformizer `π` and
`s = r ∈ ℚ(j)ˣ` is a non-unit of `𝒪_P` dividing every element of `𝔪_P`, then `e_P = 1`. -/
theorem ramIdx_eq_one (P : Place F) (π : Fˣ) (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) (r : Qj) (hr0 : r ≠ 0)
    (hs : algebraMap Qj F r ∈ P.w.nonunits)
    (hgen : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = algebraMap Qj F r * y) : P.ramIdx = 1 := by
  set v := P.w.valuation
  set s : Fˣ := Units.map (algebraMap Qj F : Qj →* F) (Units.mk0 r hr0) with hsdef
  have hsval : (s : F) = algebraMap Qj F r := rfl
  have hsrange : s ∈ (Units.map (algebraMap Qj F : Qj →* F)).range := ⟨_, rfl⟩
  -- `v π < 1`
  have hvπ1 : v π ≤ 1 := (P.w.valuation_le_one_iff _).mpr hπ
  have hvπne : v π ≠ 1 := fun h => hπu ((P.w.mem_unitGroup_iff π).mpr h)
  have hvπ : v π < 1 := lt_of_le_of_ne hvπ1 hvπne
  have hvπ0 : 0 < v π := (Valuation.pos_iff v).mpr π.ne_zero
  have hanti := zpow_right_strictAnti₀ hvπ0 hvπ
  -- `v(x) = v(π)^n` from the uniformizer
  have hval : ∀ x : Fˣ, ∃ n : ℤ, v x = v π ^ n := by
    intro x
    obtain ⟨n, hn⟩ := hdvr x
    refine ⟨n, ?_⟩
    have h1 : v ((x * π ^ (-n) : Fˣ) : F) = 1 := (P.w.mem_unitGroup_iff _).mp hn
    rw [Units.val_mul, map_mul, val_zpow, zpow_neg] at h1
    have hne : v π ^ n ≠ 0 := (zpow_pos hvπ0 n).ne'
    calc v x = v x * ((v π ^ n)⁻¹ * v π ^ n) := by rw [inv_mul_cancel₀ hne, mul_one]
      _ = v π ^ n := by rw [← mul_assoc, h1, one_mul]
  -- `v(s) = v(π)`
  obtain ⟨m, hm⟩ := hval s
  have hvs : v s < 1 := (P.w.mem_nonunits_iff).mp (hsval ▸ hs)
  have hπn : (π : F) ∈ P.w.nonunits := (P.w.mem_nonunits_iff).mpr hvπ
  obtain ⟨y, hy, hπy⟩ := hgen _ hπn
  have hvy : v y ≤ 1 := (P.w.valuation_le_one_iff _).mpr hy
  have hle : v π ≤ v s := by
    rw [hπy, map_mul, ← hsval]
    exact mul_le_of_le_one_right zero_le hvy
  have hm1 : m = 1 := by
    have h1 : v π ^ (1 : ℤ) ≤ v π ^ m := by rw [zpow_one, ← hm]; exact hle
    have h2 : v π ^ m < v π ^ (0 : ℤ) := by rw [zpow_zero, ← hm]; exact hvs
    have h3 : m ≤ 1 := hanti.le_iff_ge.mp h1
    have h4 : 0 < m := hanti.lt_iff_gt.mp h2
    omega
  rw [hm1, zpow_one] at hm
  -- every unit lies in `U_P · ℚ(j)ˣ`
  rw [Place.ramIdx, Subgroup.index_eq_one, eq_top_iff]
  intro x _
  obtain ⟨n, hn⟩ := hval x
  have hu : x * s ^ (-n) ∈ P.w.unitGroup := by
    rw [P.w.mem_unitGroup_iff, Units.val_mul, map_mul, val_zpow, hm, hn, zpow_neg,
      mul_inv_cancel₀ (zpow_pos hvπ0 n).ne']
  have : x = (x * s ^ (-n)) * s ^ n := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ hsrange n))

end Glue

section Glue2

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem algebraMap_rat_comp : (algebraMap Qj F).comp (algebraMap ℚ Qj) = algebraMap ℚ F :=
  RingHom.ext_rat _ _

theorem mul_mem_nonunits (A : ValuationSubring F) {a b : F} (ha : a ∈ A) (hb : b ∈ A.nonunits) :
    a * b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hb ⊢
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le ((A.valuation_le_one_iff a).mpr ha)) hb

/-- Polynomials over `ℚ` at an element of `𝒪_P` stay in `𝒪_P`. -/
theorem aeval_mem (P : Place F) {z : F} (hz : z ∈ P.w) (p : Polynomial ℚ) :
    Polynomial.aeval z p ∈ P.w := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (P.rat_mem _) (Subring.pow_mem _ hz _)

/-- `ℚ(j)`-polynomials at an element of `𝒪_P`, when `ℚ(j) ⊆ 𝒪_P`. -/
theorem aeval_mem_Qj (P : Place F) (himg : ∀ r : Qj, algebraMap Qj F r ∈ P.w) {z : F}
    (hz : z ∈ P.w) (p : Polynomial Qj) : Polynomial.aeval z p ∈ P.w := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  exact Subring.mul_mem _ (himg _) (Subring.pow_mem _ hz _)

/-- The polynomials over `ℚ` vanishing at the place `P` (when `t ∈ 𝒪_P`). -/
def polyIdeal (P : Place F) (ht : (tF : F) ∈ P.w) : Ideal (Polynomial ℚ) where
  carrier := {p | Polynomial.aeval (tF : F) p ∈ P.w.nonunits}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    exact P.w.nonunits.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact P.w.nonunits.zero_mem
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at *
    exact mul_mem_nonunits P.w (aeval_mem P ht c) hx

theorem polyIdeal_isPrime (P : Place F) (ht : (tF : F) ∈ P.w) : (polyIdeal P ht).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    show Polynomial.aeval (tF : F) 1 ∉ P.w.nonunits
    rw [map_one, ValuationSubring.mem_nonunits_iff, map_one]
    exact lt_irrefl _
  · intro a b hab
    have ha := (P.w.valuation_le_one_iff _).mpr (aeval_mem P ht a)
    have hb := (P.w.valuation_le_one_iff _).mpr (aeval_mem P ht b)
    change Polynomial.aeval (tF : F) (a * b) ∈ P.w.nonunits at hab
    change Polynomial.aeval (tF : F) a ∈ P.w.nonunits ∨ Polynomial.aeval (tF : F) b ∈ P.w.nonunits
    rw [map_mul, ValuationSubring.mem_nonunits_iff, map_mul] at hab
    rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff]
    by_contra h
    push_neg at h
    have h1 := le_antisymm ha h.1
    have h2 := le_antisymm hb h.2
    rw [h1, h2, one_mul] at hab
    exact lt_irrefl _ hab

/-- `ℚ[j] → F`, through `ℚ(j)`, is evaluation at `1728 t`. -/
theorem algebraMap_poly (p : Polynomial ℚ) :
    algebraMap Qj F (algebraMap (Polynomial ℚ) Qj p) =
      Polynomial.aeval (tF : F) (p.comp (Polynomial.C 1728 * Polynomial.X)) := by
  have h1728 : Polynomial.aeval (tF : F) (Polynomial.C (1728 : ℚ) * Polynomial.X) =
      algebraMap Qj F RatFunc.X := by
    rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp only [map_ofNat]
    rw [tF, ← map_ofNat (algebraMap Qj F) 1728, ← map_mul]
    congr 1
    field_simp
  have h2 : algebraMap Qj F (algebraMap (Polynomial ℚ) Qj p) =
      Polynomial.aeval (algebraMap Qj F RatFunc.X) p := by
    have : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
        (Polynomial.aeval (algebraMap Qj F RatFunc.X)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      simp [RatFunc.algebraMap_X]
    exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) this
  rw [h2, Polynomial.aeval_comp]
  exact (congrArg (fun z => Polynomial.aeval z p) h1728).symm

theorem comp_ne_zero {p : Polynomial ℚ} (hp : p ≠ 0) :
    p.comp (Polynomial.C 1728 * Polynomial.X) ≠ 0 := by
  intro h
  have h2 := congrArg Polynomial.natDegree h
  rw [Polynomial.natDegree_comp, Polynomial.natDegree_C_mul_X _ (by norm_num), mul_one,
    Polynomial.natDegree_zero] at h2
  have h3 := congrArg Polynomial.leadingCoeff h
  rw [Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ (by norm_num)]; norm_num),
    Polynomial.leadingCoeff_zero] at h3
  simp only [Polynomial.leadingCoeff_C_mul_X, mul_eq_zero, pow_eq_zero_iff', Polynomial.leadingCoeff_eq_zero] at h3
  tauto

/-- **The ideal of a place is nonzero** (proved): otherwise `ℚ(j) ⊆ 𝒪_P`, and then `𝒪_P = F`
since `F` is algebraic over `ℚ(j)` (an element outside `𝒪_P` has an inverse in `𝔪_P` whose minimal
polynomial has a nonzero constant term in `𝔪_P ∩ ℚ(j) = 0`). -/
theorem polyIdeal_ne_bot [FiniteDimensional Qj F] (P : Place F) (ht : (tF : F) ∈ P.w)
    (htr : Transcendental ℚ (tF : F)) : polyIdeal P ht ≠ ⊥ := by
  intro hbot
  have hunit : ∀ p : Polynomial ℚ, p ≠ 0 → (Polynomial.aeval (tF : F) p)⁻¹ ∈ P.w := by
    intro p hp
    have h2 : Polynomial.aeval (tF : F) p ∉ P.w.nonunits := fun h => by
      have : p ∈ polyIdeal P ht := h
      rw [hbot, Ideal.mem_bot] at this
      exact hp this
    have h0 : Polynomial.aeval (tF : F) p ≠ 0 := fun h0 => htr ⟨p, hp, h0⟩
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    push_neg at h2
    exact h2.2
  have himg : ∀ r : Qj, algebraMap Qj F r ∈ P.w := by
    intro r
    rw [← RatFunc.num_div_denom r, map_div₀, algebraMap_poly, algebraMap_poly, div_eq_mul_inv]
    exact Subring.mul_mem _ (aeval_mem P ht _) (hunit _ (comp_ne_zero (RatFunc.denom_ne_zero r)))
  obtain ⟨x, hx⟩ : ∃ x, x ∉ P.w := by
    by_contra h
    push_neg at h
    exact P.ne_top (eq_top_iff.mpr fun x _ => h x)
  have hx0 : x ≠ 0 := fun h => hx (h ▸ P.w.zero_mem)
  have hy : x⁻¹ ∈ P.w.nonunits := (P.w.inv_mem_nonunits_iff).mpr (Or.inr hx)
  have hyw : x⁻¹ ∈ P.w := P.w.nonunits_subset hy
  have hy0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hint : IsIntegral Qj x⁻¹ := IsIntegral.of_finite Qj _
  set p := minpoly Qj x⁻¹
  have hc0 := minpoly.coeff_zero_ne_zero hint hy0
  have hev : Polynomial.aeval x⁻¹ p = 0 := minpoly.aeval Qj _
  have hsplit := Polynomial.X_mul_divX_add p
  rw [← hsplit, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at hev
  have hc : algebraMap Qj F (p.coeff 0) = -(x⁻¹ * Polynomial.aeval x⁻¹ p.divX) := by
    linear_combination hev
  have hcn : algebraMap Qj F (p.coeff 0) ∈ P.w.nonunits := by
    rw [hc, mul_comm]
    exact P.w.nonunits.neg_mem (mul_mem_nonunits P.w (aeval_mem_Qj P himg hyw _) hy)
  have hcinv : (algebraMap Qj F (p.coeff 0))⁻¹ ∈ P.w := by
    rw [← map_inv₀]; exact himg _
  rw [ValuationSubring.mem_nonunits_iff_or] at hcn
  rcases hcn with h | h
  · exact hc0 ((map_eq_zero_iff _ (algebraMap Qj F).injective).mp h)
  · exact h hcinv

/-- A nonzero prime ideal of `ℚ[X]` contains a monic irreducible polynomial. -/
theorem exists_monic_irreducible_mem (I : Ideal (Polynomial ℚ)) [hI : I.IsPrime] (h0 : I ≠ ⊥) :
    ∃ q : Polynomial ℚ, q.Monic ∧ Irreducible q ∧ q ∈ I := by
  set g := Submodule.IsPrincipal.generator I
  have hg0 : g ≠ 0 := by
    intro h
    apply h0
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    simp [g, h]
  have hgp : Prime g := Submodule.IsPrincipal.prime_generator_of_isPrime I h0
  refine ⟨g * Polynomial.C g.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hg0, ?_, ?_⟩
  · refine (irreducible_mul_isUnit ?_).mpr hgp.irreducible
    exact Polynomial.isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg0)))
  · exact I.mul_mem_right _ (Submodule.IsPrincipal.generator_mem I)

end Glue2

section Glue3

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- `ℚ(j) → F` commutes with evaluating `ℚ`-polynomials. -/
theorem algebraMap_aeval (z : Qj) (q : Polynomial ℚ) :
    algebraMap Qj F (Polynomial.aeval z q) = Polynomial.aeval (algebraMap Qj F z) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, algebraMap_rat_comp]

/-- **Every place lies over `j = 0`, `j = 1728`, `j = ∞`, or is unramified** (proved from the
Belyi property and the uniformizer leaf). -/
theorem place_cases [FiniteDimensional Qj F] (hB : IsBelyiFunction ℚ F (tF : F))
    (hD : PlacesAreDVR) (P : Place F) :
    ((tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits) ∨ ((tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits) ∨
      (tF : F) ∉ P.w ∨ P.ramIdx = 1 := by
  by_cases ht : (tF : F) ∈ P.w
  · have hpr := polyIdeal_isPrime P ht
    obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
      (polyIdeal_ne_bot P ht hB.1)
    have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
    by_cases hX : q = Polynomial.X
    · left
      rw [hX, Polynomial.aeval_X] at hqI'
      exact ⟨ht, hqI'⟩
    by_cases hX1 : q = Polynomial.X - 1
    · right; left
      rw [hX1, map_sub, Polynomial.aeval_X, map_one] at hqI'
      exact ⟨ht, hqI'⟩
    right; right; right
    have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
    obtain ⟨π, hπ, hπu, hdvr⟩ := hD F P
    set r : Qj := Polynomial.aeval (RatFunc.X / 1728 : Qj) q with hr
    have hrq : algebraMap Qj F r = Polynomial.aeval (tF : F) q := by
      rw [hr, algebraMap_aeval]
    have hr0 : r ≠ 0 := by
      intro h0
      have : Polynomial.aeval (tF : F) q = 0 := by rw [← hrq, h0, map_zero]
      exact hB.1 ⟨q, hqm.ne_zero, this⟩
    refine ramIdx_eq_one P π hπ hπu hdvr r hr0 (hrq ▸ hqI') ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgen x hx
    exact ⟨y, hy, hrq ▸ hxy⟩
  · right; right; left
    exact ht

/-- Variant of `place_cases` with uniformizers only at places containing `t`. -/
theorem place_cases' [FiniteDimensional Qj F] (hB : IsBelyiFunction ℚ F (tF : F))
    (hD : ∀ P : Place F, (tF : F) ∈ P.w → ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) (P : Place F) :
    ((tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits) ∨ ((tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits) ∨
      (tF : F) ∉ P.w ∨ P.ramIdx = 1 := by
  by_cases ht : (tF : F) ∈ P.w
  · have hpr := polyIdeal_isPrime P ht
    obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
      (polyIdeal_ne_bot P ht hB.1)
    have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
    by_cases hX : q = Polynomial.X
    · left
      rw [hX, Polynomial.aeval_X] at hqI'
      exact ⟨ht, hqI'⟩
    by_cases hX1 : q = Polynomial.X - 1
    · right; left
      rw [hX1, map_sub, Polynomial.aeval_X, map_one] at hqI'
      exact ⟨ht, hqI'⟩
    right; right; right
    have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
    obtain ⟨π, hπ, hπu, hdvr⟩ := hD P ht
    set r : Qj := Polynomial.aeval (RatFunc.X / 1728 : Qj) q with hr
    have hrq : algebraMap Qj F r = Polynomial.aeval (tF : F) q := by
      rw [hr, algebraMap_aeval]
    have hr0 : r ≠ 0 := by
      intro h0
      have : Polynomial.aeval (tF : F) q = 0 := by rw [← hrq, h0, map_zero]
      exact hB.1 ⟨q, hqm.ne_zero, this⟩
    refine ramIdx_eq_one P π hπ hπu hdvr r hr0 (hrq ▸ hqI') ?_
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hgen x hx
    exact ⟨y, hy, hrq ▸ hxy⟩
  · right; right; left
    exact ht

/-- **`BelyiGenusBound` from Riemann–Hurwitz, the fundamental identity and the uniformizer leaf**
(proved). -/
theorem belyiGenusBound_of_leaves (hRH : RiemannHurwitzQj) (hFI : FundamentalIdentityQj)
    (hD : PlacesAreDVR) : BelyiGenusBound := by
  classical
  intro F _ _ _ _ hK hB
  obtain ⟨hsupp, hRHeq⟩ := hRH F hK
  set Z0 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} with hZ0
  set Z1 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} with hZ1
  set Zi : Set (Place F) := {P | (tF : F) ∉ P.w} with hZi
  obtain ⟨h0, hs0⟩ := hFI F Z0 (by simp [hZ0])
  obtain ⟨h1, hs1⟩ := hFI F Z1 (by simp [hZ1])
  obtain ⟨hi, hsi⟩ := hFI F Zi (by simp [hZi])
  set f : Place F → ℤ := fun P => ((P.ramIdx : ℤ) - 1) * P.deg with hf
  set A := h0.toFinset ∪ h1.toFinset ∪ hi.toFinset with hA
  have hsub : hsupp.toFinset ⊆ A := by
    intro P hP
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hP
    rcases place_cases hB hD P with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
    · exfalso
      apply hP
      show ((P.ramIdx : ℤ) - 1) * P.deg = 0
      rw [h]
      simp
  have hsum : ∑ P ∈ hsupp.toFinset, f P = ∑ P ∈ A, f P :=
    Finset.sum_subset hsub fun P _ hP => by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hP
  have hd01 : Disjoint h0.toFinset h1.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Set.Finite.mem_toFinset] at hP0 hP1
    have h1n : (1 : F) ∈ P.w.nonunits := by
      have := P.w.nonunits.sub_mem hP0.2 hP1.2
      rwa [sub_sub_cancel] at this
    rw [ValuationSubring.mem_nonunits_iff, map_one] at h1n
    exact lt_irrefl _ h1n
  have hd : Disjoint (h0.toFinset ∪ h1.toFinset) hi.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP hPi
    rw [Set.Finite.mem_toFinset] at hPi
    rcases Finset.mem_union.mp hP with hP | hP <;> rw [Set.Finite.mem_toFinset] at hP
    · exact hPi hP.1
    · exact hPi hP.1
  rw [hA, Finset.sum_union hd, Finset.sum_union hd01] at hsum
  have hdpos : 0 < Module.finrank Qj F := Module.finrank_pos
  have part : ∀ (Z : Set (Place F)) (hZ : Z.Finite),
      ∑ P ∈ hZ.toFinset, P.ramIdx * P.deg = Module.finrank Qj F →
        ∑ P ∈ hZ.toFinset, f P ≤ (Module.finrank Qj F : ℤ) - 1 := by
    intro Z hZ hs
    have e1 : ∑ P ∈ hZ.toFinset, f P =
        ((∑ P ∈ hZ.toFinset, P.ramIdx * P.deg : ℕ) : ℤ) - ∑ P ∈ hZ.toFinset, (P.deg : ℤ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [hf]
      ring
    rw [e1, hs]
    obtain ⟨P, hP, hne⟩ : ∃ P ∈ hZ.toFinset, P.ramIdx * P.deg ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    have hdeg : 1 ≤ P.deg := Nat.pos_of_ne_zero fun h => hne (by rw [h, mul_zero])
    have : (1 : ℤ) ≤ ∑ P ∈ hZ.toFinset, (P.deg : ℤ) :=
      le_trans (by exact_mod_cast hdeg)
        (Finset.single_le_sum (f := fun P : Place F => (P.deg : ℤ)) (fun P _ => by positivity) hP)
    linarith
  have p0 := part Z0 h0 hs0
  have p1 := part Z1 h1 hs1
  have pi := part Zi hi hsi
  have key : 2 * (fieldGenus F : ℤ) + 1 ≤ Module.finrank Qj F := by
    have := hRHeq
    rw [hsum] at this
    linarith
  exact_mod_cast key

/-- **`DimJ1Le` (the use of T34) from textbook leaves and `X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_textbook (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (hFI : FundamentalIdentityQj) (hD : PlacesAreDVR) (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_leaves hRH hFI hD) h0

end Glue3

section Glue4

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- **Places containing `j` are discrete valuation rings** (proved; replaces `PlacesAreDVR` where it
is used). With `R` the integral closure of `ℚ[j]` in `F` (a Dedekind domain with fraction field
`F`), `R ⊆ 𝒪_P`, `𝔭 = R ∩ 𝔪_P` is a nonzero prime, and a uniformizer of the DVR `R_𝔭 ⊆ 𝒪_P` is a
uniformizer of `𝒪_P`. -/
theorem exists_uniformizer [FiniteDimensional Qj F] (P : Place F) (ht : (tF : F) ∈ P.w) :
    ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup := by
  classical
  set v := P.w.valuation
  -- `j ∈ 𝒪_P`
  have hs : algebraMap Qj F RatFunc.X ∈ P.w := by
    have : algebraMap Qj F RatFunc.X = algebraMap ℚ F 1728 * (tF : F) := by
      rw [tF, ← algebraMap_rat_comp, RingHom.comp_apply, ← map_mul]
      congr 1
      rw [map_ofNat]
      field_simp
    rw [this]
    exact Subring.mul_mem _ (P.rat_mem _) ht
  letI : Algebra (Polynomial ℚ) F := ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  have : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  set R := integralClosure (Polynomial ℚ) F
  have : IsDedekindDomain R := integralClosure.isDedekindDomain (Polynomial ℚ) Qj F
  have : IsFractionRing R F :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) Qj F R
  -- `ℚ[j] ⊆ 𝒪_P`
  have hpoly : ∀ p : Polynomial ℚ, algebraMap (Polynomial ℚ) F p ∈ P.w := by
    intro p
    have : algebraMap (Polynomial ℚ) F p = Polynomial.aeval (algebraMap Qj F RatFunc.X) p := by
      change (algebraMap Qj F) (algebraMap (Polynomial ℚ) Qj p) = _
      have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
          (Polynomial.aeval (algebraMap Qj F RatFunc.X)).toRingHom := by
        refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
        simp [RatFunc.algebraMap_X]
      exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) h2
    rw [this]
    exact aeval_mem P hs p
  -- `R ⊆ 𝒪_P` (valuation rings are integrally closed)
  let φ : Polynomial ℚ →+* P.w := (algebraMap (Polynomial ℚ) F).codRestrict P.w.toSubring hpoly
  have hRw : ∀ r : R, (r : F) ∈ P.w := by
    rintro ⟨x, hx⟩
    obtain ⟨p, hpm, hp⟩ := hx
    have hint : IsIntegral P.w x := ⟨p.map φ, hpm.map φ, by
      rw [Polynomial.eval₂_map]; exact hp⟩
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    show x ∈ P.w
    rw [← hy]; exact y.2
  -- the prime `𝔭 = R ∩ 𝔪_P`
  let ψ : R →+* P.w := (R.val.toRingHom).codRestrict P.w.toSubring hRw
  set 𝔭 : Ideal R := (IsLocalRing.maximalIdeal P.w).comap ψ with h𝔭def
  have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hmem𝔭 : ∀ r : R, r ∈ 𝔭 ↔ (r : F) ∈ P.w.nonunits := by
    intro r
    rw [h𝔭def, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    rfl
  have hunit : ∀ r : R, r ∉ 𝔭 → ((r : F))⁻¹ ∈ P.w := by
    intro r hr
    rw [hmem𝔭, ValuationSubring.mem_nonunits_iff_or] at hr
    push_neg at hr
    exact hr.2
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro hbot
    apply P.ne_top
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : b ∉ 𝔭 := by
      rw [hbot, Ideal.mem_bot]
      intro h; exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ h
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (hRw a) (hunit b hb0)
  -- the DVR `R_𝔭 ⊆ F`
  have hle : 𝔭.primeCompl ≤ nonZeroDivisors R := Ideal.primeCompl_le_nonZeroDivisors 𝔭
  set Rp := Localization.subalgebra.ofField F 𝔭.primeCompl hle with hRpdef
  have : IsLocalRing Rp := IsLocalization.AtPrime.isLocalRing Rp 𝔭
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h𝔭ne Rp
  have hRpw : ∀ y : Rp, (y : F) ∈ P.w := by
    rintro ⟨y, hy⟩
    obtain ⟨a, b, hb, rfl⟩ := hy
    exact Subring.mul_mem _ (hRw a) (hunit b hb)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Rp
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  -- units of `R_𝔭` are units of `𝒪_P`
  have hU : ∀ u : Rpˣ, v ((u : Rp) : F) = 1 := by
    intro u
    have h1 : v ((u : Rp) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRpw u)
    have h2 : v (((u⁻¹ : Rpˣ) : Rp) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRpw _)
    have h3 : ((u : Rp) : F) * (((u⁻¹ : Rpˣ) : Rp) : F) = 1 := by
      rw [← Subalgebra.coe_mul, Units.mul_inv, Subalgebra.coe_one]
    have h4 : v ((u : Rp) : F) * v (((u⁻¹ : Rpˣ) : Rp) : F) = 1 := by rw [← map_mul, h3, map_one]
    by_contra hne
    have hlt : v ((u : Rp) : F) < 1 := lt_of_le_of_ne h1 hne
    have : v ((u : Rp) : F) * v (((u⁻¹ : Rpˣ) : Rp) : F) < 1 :=
      lt_of_lt_of_le (mul_lt_one_of_lt_of_le hlt h2) le_rfl
    rw [h4] at this
    exact lt_irrefl _ this
  refine ⟨Units.mk0 (ϖ : F) hϖ0, hRpw ϖ, ?_, ?_⟩
  · -- `ϖ ∈ 𝔪_P`
    rw [ValuationSubring.mem_unitGroup_iff]
    obtain ⟨⟨a, s'⟩, hϖeq⟩ := IsLocalization.mk'_surjective (S := Rp) 𝔭.primeCompl ϖ
    have hϖmax : ϖ ∈ IsLocalRing.maximalIdeal Rp :=
      (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
    rw [← hϖeq, IsLocalization.AtPrime.mk'_mem_maximal_iff Rp 𝔭] at hϖmax
    have hϖeq' : IsLocalization.mk' Rp a s' = ϖ := hϖeq
    have hspec := IsLocalization.mk'_spec Rp a s'
    rw [hϖeq'] at hspec
    have hF : (ϖ : F) * ((s' : R) : F) = ((a : R) : F) := congrArg Subtype.val hspec
    have ha : v ((a : R) : F) < 1 := (P.w.mem_nonunits_iff).mp ((hmem𝔭 a).mp hϖmax)
    have hs1 : v ((s' : R) : F) = 1 := by
      have h1 : v ((s' : R) : F) ≤ 1 := (P.w.valuation_le_one_iff _).mpr (hRw s')
      have h2 : ((s' : R) : F) ∉ P.w.nonunits := (hmem𝔭 s').not.mp s'.2
      rw [ValuationSubring.mem_nonunits_iff, not_lt] at h2
      exact le_antisymm h1 h2
    intro hv
    have : v ((a : R) : F) = 1 := by
      rw [← hF, map_mul, hs1, mul_one]
      exact hv
    rw [this] at ha
    exact lt_irrefl _ ha
  · intro x
    obtain ⟨a, b, hb, hab0⟩ := IsFractionRing.div_surjective (A := Rp) (x : F)
    have hab : ((a : Rp) : F) / ((b : Rp) : F) = x := hab0
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Subalgebra.coe_zero, zero_div] at hab
      exact x.ne_zero hab.symm
    obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
    obtain ⟨n, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨(m : ℤ) - n, ?_⟩
    rw [ValuationSubring.mem_unitGroup_iff]
    have hxe : ((x * Units.mk0 (ϖ : F) hϖ0 ^ (-((m : ℤ) - n)) : Fˣ) : F) =
        ((u : Rp) : F) * (((u' : Rp) : F))⁻¹ := by
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, ← hab, hu, hu']
      push_cast
      have hu0 : ((u' : Rp) : F) ≠ 0 := fun h => u'.ne_zero (Subtype.ext h)
      rw [neg_sub, zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast]
      field_simp
    rw [hxe, map_mul, map_inv₀, hU, hU, inv_one, mul_one]

/-- **`BelyiGenusBound` from Riemann–Hurwitz and the fundamental identity** (proved; the uniformizers
at the places containing `t` are `exists_uniformizer`). -/
theorem belyiGenusBound_of_rh_fi (hRH : RiemannHurwitzQj) (hFI : FundamentalIdentityQj) :
    BelyiGenusBound := by
  classical
  intro F _ _ _ _ hK hB
  obtain ⟨hsupp, hRHeq⟩ := hRH F hK
  set Z0 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} with hZ0
  set Z1 : Set (Place F) := {P | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} with hZ1
  set Zi : Set (Place F) := {P | (tF : F) ∉ P.w} with hZi
  obtain ⟨h0, hs0⟩ := hFI F Z0 (by simp [hZ0])
  obtain ⟨h1, hs1⟩ := hFI F Z1 (by simp [hZ1])
  obtain ⟨hi, hsi⟩ := hFI F Zi (by simp [hZi])
  set f : Place F → ℤ := fun P => ((P.ramIdx : ℤ) - 1) * P.deg with hf
  set A := h0.toFinset ∪ h1.toFinset ∪ hi.toFinset with hA
  have hsub : hsupp.toFinset ⊆ A := by
    intro P hP
    rw [Set.Finite.mem_toFinset, Function.mem_support] at hP
    rcases place_cases' hB (fun P ht => exists_uniformizer P ht) P with h | h | h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h))
    · exact Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).mpr h)
    · exfalso
      apply hP
      show ((P.ramIdx : ℤ) - 1) * P.deg = 0
      rw [h]
      simp
  have hsum : ∑ P ∈ hsupp.toFinset, f P = ∑ P ∈ A, f P :=
    Finset.sum_subset hsub fun P _ hP => by
      rwa [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hP
  have hd01 : Disjoint h0.toFinset h1.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Set.Finite.mem_toFinset] at hP0 hP1
    have h1n : (1 : F) ∈ P.w.nonunits := by
      have := P.w.nonunits.sub_mem hP0.2 hP1.2
      rwa [sub_sub_cancel] at this
    rw [ValuationSubring.mem_nonunits_iff, map_one] at h1n
    exact lt_irrefl _ h1n
  have hd : Disjoint (h0.toFinset ∪ h1.toFinset) hi.toFinset := by
    rw [Finset.disjoint_left]
    intro P hP hPi
    rw [Set.Finite.mem_toFinset] at hPi
    rcases Finset.mem_union.mp hP with hP | hP <;> rw [Set.Finite.mem_toFinset] at hP
    · exact hPi hP.1
    · exact hPi hP.1
  rw [hA, Finset.sum_union hd, Finset.sum_union hd01] at hsum
  have hdpos : 0 < Module.finrank Qj F := Module.finrank_pos
  have part : ∀ (Z : Set (Place F)) (hZ : Z.Finite),
      ∑ P ∈ hZ.toFinset, P.ramIdx * P.deg = Module.finrank Qj F →
        ∑ P ∈ hZ.toFinset, f P ≤ (Module.finrank Qj F : ℤ) - 1 := by
    intro Z hZ hs
    have e1 : ∑ P ∈ hZ.toFinset, f P =
        ((∑ P ∈ hZ.toFinset, P.ramIdx * P.deg : ℕ) : ℤ) - ∑ P ∈ hZ.toFinset, (P.deg : ℤ) := by
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun P _ => ?_
      simp only [hf]
      ring
    rw [e1, hs]
    obtain ⟨P, hP, hne⟩ : ∃ P ∈ hZ.toFinset, P.ramIdx * P.deg ≠ 0 := by
      by_contra hc
      push_neg at hc
      rw [Finset.sum_eq_zero hc] at hs
      omega
    have hdeg : 1 ≤ P.deg := Nat.pos_of_ne_zero fun h => hne (by rw [h, mul_zero])
    have : (1 : ℤ) ≤ ∑ P ∈ hZ.toFinset, (P.deg : ℤ) :=
      le_trans (by exact_mod_cast hdeg)
        (Finset.single_le_sum (f := fun P : Place F => (P.deg : ℤ)) (fun P _ => by positivity) hP)
    linarith
  have p0 := part Z0 h0 hs0
  have p1 := part Z1 h1 hs1
  have pi := part Zi hi hsi
  have key : 2 * (fieldGenus F : ℤ) + 1 ≤ Module.finrank Qj F := by
    have := hRHeq
    rw [hsum] at this
    linarith
  exact_mod_cast key

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, Riemann–Hurwitz, the fundamental
identity and `X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_rh_fi (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (hFI : FundamentalIdentityQj) (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_rh_fi hRH hFI) h0

end Glue4

/-! ## `FundamentalIdentityQj` from Mathlib's fundamental identity for Dedekind domains -/

section Glue5

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F]

/-- The coordinate `j` in `F`. -/
abbrev sF : F := algebraMap Qj F RatFunc.X

theorem algebraMap_poly_eq (p : Polynomial ℚ) :
    algebraMap (Polynomial ℚ) F p = Polynomial.aeval (sF : F) p := by
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) Qj F]
  have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
      (Polynomial.aeval (sF : F)).toRingHom := by
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    simp [RatFunc.algebraMap_X]
  exact congrArg (fun φ : Polynomial ℚ →+* F => φ p) h2

/-- The integral closure of `ℚ[j]` lies in every place containing `j`. -/
theorem intCl_mem (P : Place F) (hs : (sF : F) ∈ P.w) (r : integralClosure (Polynomial ℚ) F) :
    (r : F) ∈ P.w := by
  have hpoly : ∀ p : Polynomial ℚ, algebraMap (Polynomial ℚ) F p ∈ P.w := fun p => by
    rw [algebraMap_poly_eq]; exact aeval_mem P hs p
  let φ : Polynomial ℚ →+* P.w := (algebraMap (Polynomial ℚ) F).codRestrict P.w.toSubring hpoly
  obtain ⟨x, hx⟩ := r
  obtain ⟨p, hpm, hp⟩ := hx
  have hint : IsIntegral P.w x := ⟨p.map φ, hpm.map φ, by
    rw [Polynomial.eval₂_map]; exact hp⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  show x ∈ P.w
  rw [← hy]; exact y.2

theorem isSeparable_Qj [FiniteDimensional Qj F] : Algebra.IsSeparable Qj F :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem isDedekind_intCl [FiniteDimensional Qj F] :
    IsDedekindDomain (integralClosure (Polynomial ℚ) F) :=
  haveI := isSeparable_Qj (F := F)
  integralClosure.isDedekindDomain (Polynomial ℚ) Qj F

theorem isFractionRing_intCl [FiniteDimensional Qj F] :
    IsFractionRing (integralClosure (Polynomial ℚ) F) F :=
  haveI := isSeparable_Qj (F := F)
  IsIntegralClosure.isFractionRing_of_finite_extension (Polynomial ℚ) Qj F _

attribute [local instance] isDedekind_intCl isFractionRing_intCl

variable [FiniteDimensional Qj F]

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- The center on `OF` of a place containing `j`, a height-one prime. -/
noncomputable def centerHS (P : Place F) (hs : (sF : F) ∈ P.w) : HeightOneSpectrum OF where
  asIdeal := (IsLocalRing.maximalIdeal P.w).comap
    ((OF).val.toRingHom.codRestrict P.w.toSubring (intCl_mem P hs))
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hbot
    apply P.ne_top
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OF) x
    have hb0 : (b : F) ∉ P.w.nonunits := by
      intro h
      have : b ∈ (IsLocalRing.maximalIdeal P.w).comap
          ((OF).val.toRingHom.codRestrict P.w.toSubring (intCl_mem P hs)) := by
        rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; exact h
      rw [hbot, Ideal.mem_bot] at this
      exact nonZeroDivisors.coe_ne_zero ⟨b, hb⟩ this
    rw [ValuationSubring.mem_nonunits_iff_or] at hb0
    push_neg at hb0
    rw [div_eq_mul_inv]
    exact Subring.mul_mem _ (intCl_mem P hs a) hb0.2

theorem mem_centerHS (P : Place F) (hs : (sF : F) ∈ P.w) (r : OF) :
    r ∈ (centerHS P hs).asIdeal ↔ (r : F) ∈ P.w.nonunits := by
  change r ∈ Ideal.comap _ _ ↔ _
  rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

/-- A place containing `j` is the valuation ring of its center. -/
theorem w_eq_valuationSubring (P : Place F) (hs : (sF : F) ∈ P.w) :
    P.w = ((centerHS P hs).valuation F).valuationSubring := by
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  symm
  refine ValuationSubring.eq_of_le_of_ne_top _ ?_ P.ne_top
  rintro x hx
  obtain ⟨a, b, hb, rfl⟩ := hx
  have hb0 : (b : F) ∉ P.w.nonunits := (mem_centerHS P hs b).not.mp hb
  rw [ValuationSubring.mem_nonunits_iff_or] at hb0
  push_neg at hb0
  exact Subring.mul_mem _ (intCl_mem P hs a) hb0.2

/-- The place of a height-one prime of `OF`. -/
noncomputable def placeOf (w : HeightOneSpectrum OF) : Place F where
  w := (w.valuation F).valuationSubring
  ne_top := by
    simp only [ne_eq, Valuation.valuationSubring_eq_top_iff, not_not]; infer_instance
  rat_mem c := by
    have hr : ((Polynomial.C c : Polynomial ℚ) : Polynomial ℚ) ∈ (⊤ : Subalgebra (Polynomial ℚ) (Polynomial ℚ)) :=
      trivial
    let r : OF := algebraMap (Polynomial ℚ) OF (Polynomial.C c)
    have : algebraMap ℚ F c = algebraMap OF F r := by
      change _ = algebraMap (Polynomial ℚ) F (Polynomial.C c)
      rw [algebraMap_poly_eq, Polynomial.aeval_C]
    rw [this]
    exact (Valuation.mem_valuationSubring_iff _ _).mpr (HeightOneSpectrum.valuation_le_one _ _)

theorem sF_mem_placeOf (w : HeightOneSpectrum OF) : (sF : F) ∈ (placeOf w).w := by
  have : (sF : F) = algebraMap OF F (algebraMap (Polynomial ℚ) OF Polynomial.X) := by
    change _ = algebraMap (Polynomial ℚ) F Polynomial.X
    rw [algebraMap_poly_eq, Polynomial.aeval_X]
  rw [this]
  exact (Valuation.mem_valuationSubring_iff _ _).mpr (HeightOneSpectrum.valuation_le_one _ _)

theorem placeOf_centerHS (P : Place F) (hs : (sF : F) ∈ P.w) : placeOf (centerHS P hs) = P :=
  Place.ext' (w_eq_valuationSubring P hs).symm

theorem centerHS_placeOf (w : HeightOneSpectrum OF) :
    centerHS (placeOf w) (sF_mem_placeOf w) = w := by
  ext r
  rw [mem_centerHS, ValuationSubring.mem_nonunits_iff_or,
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)]
  change (r : F) = 0 ∨ ((r : F))⁻¹ ∉ (w.valuation F).valuationSubring ↔ _
  rw [Valuation.mem_valuationSubring_iff, map_inv₀, not_le]
  by_cases hr : (r : F) = 0
  · have : algebraMap OF F r = 0 := hr
    simp [hr, this]
  · have h0 : w.valuation F (algebraMap OF F r) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hr
    change _ ↔ w.valuation F (r : F) < 1
    rw [one_lt_inv_iff₀]
    simp only [hr, false_or]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨zero_lt_iff.mpr h0, h⟩

/-- The prime `(j − a)` of `ℚ[j]`. -/
noncomputable abbrev pa (a : ℚ) : Ideal (Polynomial ℚ) := Ideal.span {Polynomial.X - Polynomial.C a}

theorem pa_isMaximal (a : ℚ) : (pa a).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (Polynomial.irreducible_X_sub_C a)

theorem pa_ne_bot (a : ℚ) : pa a ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]; exact Polynomial.X_sub_C_ne_zero a

/-- The places over `j = a`. -/
def Zfin (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] (a : ℚ) : Set (Place F) :=
  {P | (sF : F) ∈ P.w ∧ (sF : F) - algebraMap ℚ F a ∈ P.w.nonunits}

theorem algebraMap_X_sub_C (a : ℚ) :
    ((algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) : OF) : F) =
      (sF : F) - algebraMap ℚ F a := by
  have : ((algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) : OF) : F) =
      algebraMap (Polynomial ℚ) F (Polynomial.X - Polynomial.C a) := rfl
  rw [this, algebraMap_poly_eq, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]

theorem placeOf_mem_Zfin_iff (a : ℚ) (w : HeightOneSpectrum OF) :
    placeOf w ∈ Zfin F a ↔ w.asIdeal ∈ (pa a).primesOver OF := by
  have hpm := pa_isMaximal a
  have key : (sF : F) - algebraMap ℚ F a ∈ (placeOf w).w.nonunits ↔
      algebraMap (Polynomial ℚ) OF (Polynomial.X - Polynomial.C a) ∈ w.asIdeal := by
    conv_rhs => rw [← centerHS_placeOf w]
    rw [mem_centerHS, algebraMap_X_sub_C]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨w.isPrime, ⟨?_⟩⟩
    have hle : pa a ≤ w.asIdeal.under (Polynomial ℚ) := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact key.mp h
    exact hpm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  · rintro ⟨-, hlo⟩
    refine ⟨sF_mem_placeOf w, key.mpr ?_⟩
    have : Polynomial.X - Polynomial.C a ∈ w.asIdeal.under (Polynomial ℚ) := by
      rw [← hlo.over]; exact Ideal.subset_span rfl
    exact this

theorem faithful_intCl : FaithfulSMul (Polynomial ℚ) OF := by
  have hinjF : Function.Injective (algebraMap (Polynomial ℚ) F) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) Qj F]
    exact (algebraMap Qj F).injective.comp (IsFractionRing.injective (Polynomial ℚ) Qj)
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y hxy
  apply hinjF
  exact congrArg (fun z : OF => (z : F)) hxy

/-- `ℤᵐ⁰ˣ` is generated by `exp (-1)`, of infinite order. -/
theorem zpowers_exp_neg_one :
    Subgroup.zpowers (Units.mk0 (WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  refine ⟨-WithZero.log (u : WithZero (Multiplicative ℤ)), ?_⟩
  ext
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0]
  rw [← WithZero.exp_zsmul, show (-WithZero.log (u : WithZero (Multiplicative ℤ))) • (-1 : ℤ) =
    WithZero.log (u : WithZero (Multiplicative ℤ)) by simp, WithZero.exp_log u.ne_zero]

theorem orderOf_exp_neg_one :
    orderOf (Units.mk0 (WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero) = 0 := by
  rw [orderOf_eq_zero_iff']
  intro n hn h
  have h2 := congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ))) h
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one] at h2
  rw [← WithZero.exp_nsmul, ← WithZero.exp_zero] at h2
  have h3 := WithZero.exp_injective h2
  simp at h3
  omega

/-- `e_P` is Mathlib's ramification index. -/
theorem ramIdx_placeOf (a : ℚ) (w : HeightOneSpectrum OF) (hw : w.asIdeal ∈ (pa a).primesOver OF) :
    (placeOf w).ramIdx = Ideal.ramificationIdx' (pa a) w.asIdeal := by
  have hlo : w.asIdeal.LiesOver (pa a) := hw.2
  have := faithful_intCl (F := F)
  have : Module.IsTorsionFree (Polynomial ℚ) OF := inferInstance
  rw [Ideal.ramificationIdx'_eq_ramificationIdx (pa a) w.asIdeal (pa_ne_bot a)]
  set e := w.asIdeal.ramificationIdx (Polynomial ℚ) with he
  let vp : HeightOneSpectrum (Polynomial ℚ) := ⟨pa a, (pa_isMaximal a).isPrime, pa_ne_bot a⟩
  have : w.asIdeal.LiesOver vp.asIdeal := hlo
  have hlies : ∀ x : Qj, vp.valuation Qj x ^ e = w.valuation F (algebraMap Qj F x) :=
    fun x => HeightOneSpectrum.valuation_liesOver F vp w x
  let v := w.valuation F
  let φ : Fˣ →* (WithZero (Multiplicative ℤ))ˣ := Units.map (v : F →*₀ WithZero (Multiplicative ℤ))
  have hφ : ∀ x : Fˣ, (φ x : WithZero (Multiplicative ℤ)) = v x := fun x => rfl
  have hker : φ.ker = (placeOf w).w.unitGroup := by
    ext x
    rw [MonoidHom.mem_ker, Units.ext_iff, hφ, Units.val_one]
    exact (Valuation.mem_unitGroup_iff (v := v) (x := x)).symm
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := HeightOneSpectrum.valuation_surjective (K := F) w (u : WithZero (Multiplicative ℤ))
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact u.ne_zero hx.symm
    exact ⟨Units.mk0 x hx0, Units.ext (by rw [hφ]; exact hx)⟩
  set Rg := (Units.map (algebraMap Qj F : Qj →* F)).range with hRg
  have hH : (placeOf w).w.unitGroup ⊔ Rg = (Subgroup.map φ Rg).comap φ := by
    rw [Subgroup.comap_map_eq, hker, sup_comm]
  set g : (WithZero (Multiplicative ℤ))ˣ := Units.mk0 (WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero
  have hmap : Subgroup.map φ Rg = Subgroup.zpowers (g ^ (e : ℤ)) := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      have hy0 : vp.valuation Qj (y : Qj) ≠ 0 := by
        rw [Valuation.ne_zero_iff]; exact y.ne_zero
      obtain ⟨n, hn⟩ : (Units.mk0 _ hy0) ∈ Subgroup.zpowers g := by
        rw [zpowers_exp_neg_one]; trivial
      refine ⟨n, Units.ext ?_⟩
      simp only [Units.val_zpow_eq_zpow_val] at hn ⊢
      rw [hφ]
      change _ = v (algebraMap Qj F (y : Qj))
      rw [← hlies, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      have hn' := congrArg (fun u : (WithZero (Multiplicative ℤ))ˣ => (u : WithZero (Multiplicative ℤ))) hn
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hn'
      rw [hn']
    · rw [Subgroup.zpowers_le]
      obtain ⟨π, hπ⟩ := vp.valuation_exists_uniformizer Qj
      have hπ0 : π ≠ 0 := by
        rintro rfl; rw [map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
      refine ⟨Units.map (algebraMap Qj F : Qj →* F) (Units.mk0 π hπ0), ⟨_, rfl⟩, Units.ext ?_⟩
      rw [hφ]
      change v (algebraMap Qj F π) = _
      rw [← hlies, hπ, Units.val_zpow_eq_zpow_val, Units.val_mk0, zpow_natCast]
  rw [Place.ramIdx, hH, Subgroup.index_comap_of_surjective _ hsurj, hmap,
    Subgroup.index_zpowers_zpow zpowers_exp_neg_one, orderOf_exp_neg_one]
  simp

/-- `deg P` is Mathlib's inertia degree. -/
theorem deg_placeOf (a : ℚ) (w : HeightOneSpectrum OF) (hw : w.asIdeal ∈ (pa a).primesOver OF) :
    (placeOf w).deg = Ideal.inertiaDeg' (pa a) w.asIdeal := by
  have hlo : w.asIdeal.LiesOver (pa a) := hw.2
  have hmax : w.asIdeal.IsMaximal := w.isMaximal
  have hpm := pa_isMaximal a
  have hc : Ideal.comap (algebraMap (Polynomial ℚ) OF) w.asIdeal = pa a := hlo.over.symm
  rw [Ideal.inertiaDeg', dif_pos hc]
  let A := HeightOneSpectrum.valuationSubringAtPrime F w
  have hAB : A = (w.valuation F).valuationSubring :=
    HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring w
  let e1 : A ≃+* (placeOf w).w := RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hAB)
  let e2 : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField (placeOf w).w :=
    IsLocalRing.ResidueField.mapEquiv e1
  let e3 : (OF ⧸ w.asIdeal) ≃+* IsLocalRing.ResidueField A :=
    (IsLocalization.AtPrime.equivQuotMaximalIdeal w.asIdeal A).toRingEquiv
  let j : IsLocalRing.ResidueField (placeOf w).w ≃+* OF ⧸ w.asIdeal := (e3.trans e2).symm
  let i : ℚ ≃+* Polynomial ℚ ⧸ pa a := (Polynomial.quotientSpanXSubCAlgEquiv a).symm.toRingEquiv
  letI := (placeOf w).ratHom.toAlgebra
  exact Algebra.finrank_eq_of_equiv_equiv i j (RingHom.ext_rat _ _)

theorem centerHS_congr {P Q : Place F} (h : P = Q) (hP : (sF : F) ∈ P.w) (hQ : (sF : F) ∈ Q.w) :
    centerHS P hP = centerHS Q hQ := by
  subst h; rfl

/-- **The fundamental identity at `j = a`** (proved from Mathlib's for Dedekind domains). -/
theorem fundamentalIdentity_fin (a : ℚ) :
    ∃ h : (Zfin F a).Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  classical
  have hpm := pa_isMaximal a
  have hp0 := pa_ne_bot a
  have hinjF : Function.Injective (algebraMap (Polynomial ℚ) F) := by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℚ) Qj F]
    exact (algebraMap Qj F).injective.comp (IsFractionRing.injective (Polynomial ℚ) Qj)
  have : FaithfulSMul (Polynomial ℚ) OF := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro x y hxy
    apply hinjF
    have h1 := congrArg (fun z : OF => (z : F)) hxy
    exact h1
  have : Module.IsTorsionFree (Polynomial ℚ) OF := inferInstance
  have : Module.Finite (Polynomial ℚ) OF := by
    have := isSeparable_Qj (F := F)
    exact IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  set S := IsDedekindDomain.primesOverFinset (pa a) OF with hS
  have hmemS : ∀ 𝔓, 𝔓 ∈ S ↔ 𝔓 ∈ (pa a).primesOver OF := fun 𝔓 =>
    IsDedekindDomain.mem_primesOverFinset_iff hp0 OF
  let G : ∀ 𝔓 ∈ S, Place F := fun 𝔓 h𝔓 =>
    placeOf ⟨𝔓, ((hmemS 𝔓).mp h𝔓).1, by
      have := ((hmemS 𝔓).mp h𝔓).2
      exact Ideal.ne_bot_of_liesOver_of_ne_bot hp0 𝔓⟩
  have hG : ∀ 𝔓 h𝔓, G 𝔓 h𝔓 ∈ Zfin F a := fun 𝔓 h𝔓 =>
    (placeOf_mem_Zfin_iff a _).mpr ((hmemS 𝔓).mp h𝔓)
  have hZ : Zfin F a = Set.range (fun x : S => G x.1 x.2) := by
    ext P
    constructor
    · intro hP
      have hs := hP.1
      set w := centerHS P hs
      have hPw : placeOf w = P := placeOf_centerHS P hs
      have hw : w.asIdeal ∈ S := (hmemS _).mpr ((placeOf_mem_Zfin_iff a w).mp (hPw ▸ hP))
      refine ⟨⟨w.asIdeal, hw⟩, ?_⟩
      show placeOf _ = P
      convert hPw
    · rintro ⟨x, rfl⟩
      exact hG x.1 x.2
  have hfin : (Zfin F a).Finite := hZ ▸ Set.finite_range _
  refine ⟨hfin, ?_⟩
  rw [← Ideal.sum_ramification_inertia (S := OF) (p := pa a) Qj F hp0]
  symm
  refine Finset.sum_bij G (fun 𝔓 h𝔓 => (Set.Finite.mem_toFinset _).mpr (hG 𝔓 h𝔓)) ?_ ?_ ?_
  · intro 𝔓₁ h₁ 𝔓₂ h₂ he
    have := centerHS_congr he (sF_mem_placeOf _) (sF_mem_placeOf _)
    rw [centerHS_placeOf, centerHS_placeOf] at this
    exact congrArg HeightOneSpectrum.asIdeal this
  · intro P hP
    rw [Set.Finite.mem_toFinset, hZ] at hP
    obtain ⟨⟨𝔓, h𝔓⟩, rfl⟩ := hP
    exact ⟨𝔓, h𝔓, rfl⟩
  · intro 𝔓 h𝔓
    rw [ramIdx_placeOf a _ ((hmemS 𝔓).mp h𝔓), deg_placeOf a _ ((hmemS 𝔓).mp h𝔓)]

end Glue5

section Twist

theorem invX_hφ : (nonZeroDivisors (Polynomial ℚ)) ≤
    (nonZeroDivisors Qj).comap (Polynomial.aeval (RatFunc.X⁻¹ : Qj) : Polynomial ℚ →ₐ[ℚ] Qj).toRingHom := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h0
  have h : IsAlgebraic ℚ (RatFunc.X⁻¹ : Qj) := ⟨p, nonZeroDivisors.ne_zero hp, h0⟩
  apply RatFunc.transcendental_X (K := ℚ)
  convert IsAlgebraic.inv_iff.mp h
  exact Subsingleton.elim _ _

/-- `j ↦ 1/j` on `ℚ(j)`. -/
noncomputable def invXHom : Qj →+* Qj :=
  RatFunc.liftRingHom (Polynomial.aeval (RatFunc.X⁻¹ : Qj) : Polynomial ℚ →ₐ[ℚ] Qj).toRingHom invX_hφ

theorem invXHom_algebraMap (p : Polynomial ℚ) :
    invXHom (algebraMap (Polynomial ℚ) Qj p) = Polynomial.aeval (RatFunc.X⁻¹ : Qj) p := by
  have := RatFunc.liftRingHom_apply_div'
    (φ := (Polynomial.aeval (RatFunc.X⁻¹ : Qj) : Polynomial ℚ →ₐ[ℚ] Qj).toRingHom)
    (hφ := invX_hφ) p 1
  simpa [invXHom] using this

theorem invXHom_X : invXHom (RatFunc.X : Qj) = RatFunc.X⁻¹ := by
  have := invXHom_algebraMap Polynomial.X
  rwa [RatFunc.algebraMap_X, Polynomial.aeval_X] at this

theorem invXHom_invXHom (x : Qj) : invXHom (invXHom x) = x := by
  have h : (invXHom.comp invXHom).comp (algebraMap (Polynomial ℚ) Qj) =
      (RingHom.id Qj).comp (algebraMap (Polynomial ℚ) Qj) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, RatFunc.algebraMap_X,
      invXHom_X, map_inv₀, inv_inv]
  exact congrArg (fun φ : Qj →+* Qj => φ x)
    (IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℚ)) h)

/-- `j ↦ 1/j` as a ring automorphism. -/
noncomputable def invXEquiv : Qj ≃+* Qj :=
  RingEquiv.ofRingHom invXHom invXHom
    (RingHom.ext fun x => invXHom_invXHom x) (RingHom.ext fun x => invXHom_invXHom x)

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F]

/-- The twisted `ℚ(j)`-algebra structure `c · x = (1/j ↦ ...)`: `j` acts as `1/j`. -/
@[reducible] noncomputable def twistAlg : Algebra Qj F :=
  ((algebraMap Qj F).comp invXEquiv.toRingHom).toAlgebra

theorem twist_finrank :
    @Module.finrank Qj F _ _ (twistAlg (F := F)).toModule = Module.finrank Qj F :=
  @Algebra.finrank_eq_of_equiv_equiv Qj F _ _ (twistAlg (F := F)) Qj F _ _ _ invXEquiv
    (RingEquiv.refl F) rfl

theorem twist_finiteDimensional : @FiniteDimensional Qj F _ _ (twistAlg (F := F)).toModule := by
  have h0 : 0 < @Module.finrank Qj F _ _ (twistAlg (F := F)).toModule := by
    rw [twist_finrank]; exact Module.finrank_pos
  exact @FiniteDimensional.of_finrank_pos Qj F _ _ (twistAlg (F := F)).toModule h0

theorem twist_ramIdx (P : Place F) : @Place.ramIdx F _ (twistAlg (F := F)) _ P = P.ramIdx := by
  unfold Place.ramIdx
  congr 2
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Units.map invXEquiv.toRingHom.toMonoidHom y, Units.ext rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map invXEquiv.toRingHom.toMonoidHom y, Units.ext ?_⟩
    change (algebraMap Qj F) (invXEquiv (invXEquiv (y : Qj))) = _
    rw [show invXEquiv (invXEquiv (y : Qj)) = (y : Qj) from invXHom_invXHom _]
    rfl

end Twist

section FI

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem mul_rat_mem_iff (P : Place F) {c : ℚ} (hc : c ≠ 0) (x : F) :
    (algebraMap ℚ F c * x ∈ P.w ↔ x ∈ P.w) ∧
      (algebraMap ℚ F c * x ∈ P.w.nonunits ↔ x ∈ P.w.nonunits) := by
  have hv : P.w.valuation (algebraMap ℚ F c) = 1 := by
    have h1 := (P.w.valuation_le_one_iff _).mpr (P.rat_mem c)
    have h2 := (P.w.valuation_le_one_iff _).mpr (P.rat_mem c⁻¹)
    rw [map_inv₀, map_inv₀] at h2
    have h0 : P.w.valuation (algebraMap ℚ F c) ≠ 0 := by
      rw [Valuation.ne_zero_iff, map_ne_zero_iff _ (algebraMap ℚ F).injective]; exact hc
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)
  refine ⟨?_, ?_⟩
  · rw [← P.w.valuation_le_one_iff, ← P.w.valuation_le_one_iff, map_mul, hv, one_mul]
  · rw [ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff, map_mul, hv, one_mul]

end FI

section FIfinal

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

theorem tF_eq_mul : (tF : F) = algebraMap ℚ F (1 / 1728) * (sF : F) := by
  rw [tF, sF, ← algebraMap_rat_comp, RingHom.comp_apply, ← map_mul]
  congr 1
  rw [map_div₀, map_one, map_ofNat]
  ring

theorem tF_sub_one_eq_mul :
    (tF : F) - 1 = algebraMap ℚ F (1 / 1728) * ((sF : F) - algebraMap ℚ F 1728) := by
  rw [tF_eq_mul, mul_sub, ← map_mul]
  norm_num

/-- The fundamental identity at a finite place, with the `ℚ[j]`-structure built in. -/
theorem fundamentalIdentity_fin' [FiniteDimensional Qj F] (a : ℚ) :
    ∃ h : (Zfin F a).Finite, ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  letI : Algebra (Polynomial ℚ) F :=
    ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  have : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  exact fundamentalIdentity_fin a

theorem sF_twist : @sF F _ (twistAlg (F := F)) = (sF : F)⁻¹ := by
  show (algebraMap Qj F) (invXEquiv RatFunc.X) = (sF : F)⁻¹
  rw [show invXEquiv (RatFunc.X : Qj) = RatFunc.X⁻¹ from invXHom_X, map_inv₀]

theorem zfin_twist : @Zfin F _ (twistAlg (F := F)) _ 0 = {P : Place F | (tF : F) ∉ P.w} := by
  have hsF0 : (sF : F) ≠ 0 := by
    rw [sF, map_ne_zero_iff _ (algebraMap Qj F).injective]; exact RatFunc.X_ne_zero
  ext P
  show (@sF F _ (twistAlg (F := F)) ∈ P.w ∧ @sF F _ (twistAlg (F := F)) - algebraMap ℚ F 0 ∈
    P.w.nonunits) ↔ (tF : F) ∉ P.w
  rw [sF_twist, map_zero, sub_zero, tF_eq_mul, (mul_rat_mem_iff P (by norm_num) _).1]
  constructor
  · rintro ⟨-, h2⟩
    rw [ValuationSubring.inv_mem_nonunits_iff] at h2
    exact h2.resolve_left hsF0
  · intro h2
    have h3 : (sF : F)⁻¹ ∈ P.w.nonunits := (P.w.inv_mem_nonunits_iff).mpr (Or.inr h2)
    exact ⟨P.w.nonunits_subset h3, h3⟩

/-- **The fundamental identity at `j = ∞`** (proved: the fundamental identity at `j = 0` for the
twisted structure `j ↦ 1/j`). -/
theorem fundamentalIdentity_inf [FiniteDimensional Qj F] :
    ∃ h : {P : Place F | (tF : F) ∉ P.w}.Finite,
      ∑ P ∈ h.toFinset, P.ramIdx * P.deg = Module.finrank Qj F := by
  obtain ⟨h, hs⟩ := @fundamentalIdentity_fin' F _ (twistAlg (F := F)) _ twist_finiteDimensional 0
  have h' : {P : Place F | (tF : F) ∉ P.w}.Finite := zfin_twist (F := F) ▸ h
  refine ⟨h', ?_⟩
  have hfs : h'.toFinset = h.toFinset := by
    ext P
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, zfin_twist]
  rw [hfs, ← twist_finrank, ← hs]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [twist_ramIdx]

/-- **`FundamentalIdentityQj`, proved** (from Mathlib's fundamental identity for Dedekind domains). -/
theorem fundamentalIdentityQj : FundamentalIdentityQj := by
  intro F _ _ _ _ Z hZ
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hZ
  rcases hZ with rfl | rfl | rfl
  · have hZ0 : {P : Place F | (tF : F) ∈ P.w ∧ (tF : F) ∈ P.w.nonunits} = Zfin F 0 := by
      ext P
      simp only [Zfin, Set.mem_setOf_eq, map_zero, sub_zero]
      rw [tF_eq_mul, (mul_rat_mem_iff P (by norm_num) _).1, (mul_rat_mem_iff P (by norm_num) _).2]
    rw [hZ0]
    exact fundamentalIdentity_fin' 0
  · have hZ1 : {P : Place F | (tF : F) ∈ P.w ∧ (tF : F) - 1 ∈ P.w.nonunits} = Zfin F 1728 := by
      ext P
      simp only [Zfin, Set.mem_setOf_eq]
      rw [tF_sub_one_eq_mul, tF_eq_mul, (mul_rat_mem_iff P (by norm_num) _).1,
        (mul_rat_mem_iff P (by norm_num) _).2]
    rw [hZ1]
    exact fundamentalIdentity_fin' 1728
  · exact fundamentalIdentity_inf

/-- **`BelyiGenusBound` from Riemann–Hurwitz alone** (proved). -/
theorem belyiGenusBound_of_rh (hRH : RiemannHurwitzQj) : BelyiGenusBound :=
  belyiGenusBound_of_rh_fi hRH fundamentalIdentityQj

/-- **`DimJ1Le` (the use of T34) from `DimJacobianEqGenus`, Riemann–Hurwitz and
`X₀(N)`-transitivity** (proved). -/
theorem dimJ1Le_of_rh (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj)
    (h0 : ZInQ.RLeaf.X0Transitive) : DimJ1Le :=
  dimJ1Le_of_belyi h1 (belyiGenusBound_of_rh hRH) h0

end FIfinal

end GenusRoute



namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

/-- **`DimJ1Le` (the only use of T34) from `DimJacobianEqGenus` and Riemann–Hurwitz alone**
(proved). No `GenusX1Field`, no `X0Transitive`: the constant field of `K_N` comes from the model of
`X₁(N)` carried by `IsJ1` (`constantFieldIsQ_of_curve`), the Belyi function and the degree bound
`[K_N : ℚ(j)] ≤ N²` from the kernel theorem `ZInQ.RLeaf.belyiX1`, and `2g + 1 ≤ [K_N : ℚ(j)]` from
`belyiGenusBound_of_rh`. -/
theorem dimJ1Le_of_rh_curve (h1 : DimJacobianEqGenus) (hRH : RiemannHurwitzQj) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  have hK : ConstantFieldIsQ (fieldX1 P) := constantFieldIsQ_of_curve X hC (fieldX1 P) he.some
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hB := belyiGenusBound_of_rh hRH (fieldX1 P) hK hBel
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, by omega⟩

/-- **The genus bound for every model (proved)**: for a model `X` of `X₁(N)` (`IsX1Model`), the genus
of `K_N` is at most `(N² − 1)/2`, from Riemann–Hurwitz alone. -/
theorem genus_le_of_model (hRH : RiemannHurwitzQj) (N : ℕ) (hN : 0 < N) (X : Over SpecQ)
    (hX : IsX1Model N X) : ∃ P : EjBar.toAffine.Point, addOrderOf P = N ∧
      2 * fieldGenus (fieldX1 P) + 1 ≤ N ^ 2 := by
  obtain ⟨hC, hI, P, hP, he⟩ := hX
  have hK : ConstantFieldIsQ (fieldX1 P) := constantFieldIsQ_of_curve X hC (fieldX1 P) he.some
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hB := belyiGenusBound_of_rh hRH (fieldX1 P) hK hBel
  exact ⟨P, hP, by omega⟩

end GenusRoute

/-! ## An elementary genus bound: `g(F) ≤ [F : ℚ(j)]` for a Belyi function, without Riemann–Hurwitz

`fieldGenus F` is bounded by an explicit injection, using only the leaf `LocalDerivation` (the
derivative with respect to a local parameter preserves the valuation ring). No Riemann–Roch, no
Riemann–Hurwitz, no identification of `fieldGenus` with another genus. -/

namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section ElemLeaf

/-- **Leaf: the derivative with respect to a local parameter preserves the valuation ring.**
For `F` finite over `ℚ(j)` with `ℚ` algebraically closed in `F` (Stichtenoth's standing
assumption that `ℚ` is the full constant field), a place `P` of `F/ℚ` and a local parameter `π` of
`P` (`π ≠ 0`,
`π ∈ 𝔪_P`, every element of `𝔪_P` is `π · y` with `y ∈ 𝒪_P`), there is a derivation
`δ = d/dπ : F → F` over `ℚ` with `δ π = 1` and `δ 𝒪_P ⊆ 𝒪_P`.
Published: Stichtenoth, *Algebraic Function Fields and Codes*, §4.1 (the `t`-derivative `δ_t` for a
separating element `t`; a prime element of a place is separating, and `δ_t(𝒪_P) ⊆ 𝒪_P` for a
`P`-prime element `t`), Prop. 4.1.8 (number UNVERIFIED); equivalently, `Ω_{𝒪_P/ℚ}` is free with basis
`dπ` (`𝒪_P` is the local ring of a smooth curve over `ℚ` at a closed point: Hartshorne II.8.8 with
II.8.7 and II.6.7, numbers UNVERIFIED), and `δ` is `dπ ↦ 1` extended to `F`. -/
def LocalDerivation : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → ∀ (P : Place F) (π : F), π ≠ 0 → π ∈ P.w.nonunits → (∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) →
      ∃ δ : Derivation ℚ F F, δ π = 1 ∧ ∀ x ∈ P.w, δ x ∈ P.w

/-- **The genus bound for Belyi functions in the weak form the proof needs**:
`g(F) ≤ [F : ℚ(j)]` (proved below from `LocalDerivation`). -/
def GenusLeDegree : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F → IsBelyiFunction ℚ F (algebraMap Qj F (RatFunc.X / 1728)) →
      fieldGenus F ≤ Module.finrank Qj F

end ElemLeaf

section ElemVal

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- Nonzero rationals are units at every place. -/
theorem val_rat (P : Place F) {c : ℚ} (hc : c ≠ 0) : P.w.valuation (algebraMap ℚ F c) = 1 := by
  have h1 : P.w.valuation (algebraMap ℚ F c) ≤ 1 := (P.w.valuation_le_one_iff _).2 (P.rat_mem c)
  have h2 : P.w.valuation (algebraMap ℚ F c⁻¹) ≤ 1 := (P.w.valuation_le_one_iff _).2 (P.rat_mem _)
  have h3 : P.w.valuation (algebraMap ℚ F c) * P.w.valuation (algebraMap ℚ F c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : P.w.ValueGroup) = _ := h3.symm
    _ ≤ P.w.valuation (algebraMap ℚ F c) * 1 := mul_le_mul_right h2 _
    _ = _ := mul_one _

/-- **Derivative of `u π^(m+1)` (proved).** For a derivation `δ` preserving `𝒪_P` with `δ π = 1`,
`π ∈ 𝔪_P`, and a unit `u` of `𝒪_P`: `δ(u π^(m+1)) = π^m c` with `c` a unit of `𝒪_P` (in
characteristic `0`, `c = π δu + (m+1) u`). -/
theorem deriv_unit_pow (P : Place F) (δ : Derivation ℚ F F) (hδ : ∀ x ∈ P.w, δ x ∈ P.w) {π : F}
    (hπ : π ∈ P.w.nonunits) (hδπ : δ π = 1) {u : F} (hu : P.w.valuation u = 1) (m : ℕ) :
    ∃ c : F, c ≠ 0 ∧ c ∈ P.w ∧ c⁻¹ ∈ P.w ∧ δ (u * π ^ (m + 1)) = π ^ m * c := by
  have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
  set c : F := π * δ u + (algebraMap ℚ F ((m : ℚ) + 1)) * u with hc
  have hval : P.w.valuation c = 1 := by
    have hlt : P.w.valuation (π * δ u) < P.w.valuation (algebraMap ℚ F ((m : ℚ) + 1) * u) := by
      rw [map_mul, map_mul, val_rat P (by positivity), hu, one_mul]
      calc P.w.valuation π * P.w.valuation (δ u) ≤ P.w.valuation π * 1 :=
            mul_le_mul_right ((P.w.valuation_le_one_iff _).2 (hδ u huw)) _
        _ = P.w.valuation π := mul_one _
        _ < 1 := P.w.mem_nonunits_iff.mp hπ
    rw [hc, Valuation.map_add_eq_of_lt_right _ hlt, map_mul, val_rat P (by positivity), hu, one_mul]
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hval; exact zero_ne_one hval
  refine ⟨c, hc0, (P.w.valuation_le_one_iff c).1 hval.le, (P.w.valuation_le_one_iff _).1 ?_, ?_⟩
  · rw [map_inv₀, hval, inv_one]
  · rw [Derivation.leibniz, Derivation.leibniz_pow, hδπ, hc]
    simp only [smul_eq_mul, nsmul_eq_mul, mul_one, Nat.add_sub_cancel, map_add, map_natCast,
      map_one, Nat.cast_add, Nat.cast_one]
    ring

/-- **Decomposition at a uniformizer (proved).** A nonzero `z ∈ 𝔪_P` is `u π^(m+1)` with `u` a unit,
for a uniformizer `π` in the form of `exists_uniformizer`. -/
theorem decomp_nonunit (P : Place F) {π : Fˣ} (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) {z : F} (hz0 : z ≠ 0)
    (hz : z ∈ P.w.nonunits) :
    ∃ (u : F) (m : ℕ), P.w.valuation u = 1 ∧ z = u * (π : F) ^ (m + 1) := by
  have hvπ1 : P.w.valuation (π : F) ≤ 1 := (P.w.valuation_le_one_iff _).2 hπ
  have hvπ : P.w.valuation (π : F) < 1 :=
    lt_of_le_of_ne hvπ1 (fun h => hπu ((P.w.mem_unitGroup_iff π).2 h))
  obtain ⟨n, hn⟩ := hdvr (Units.mk0 z hz0)
  rw [ValuationSubring.mem_unitGroup_iff] at hn
  have hπ0 : (π : F) ≠ 0 := π.ne_zero
  have hvz : P.w.valuation z < 1 := P.w.mem_nonunits_iff.mp hz
  -- `n ≥ 1`
  have hn1 : 1 ≤ n := by
    by_contra hlt
    push Not at hlt
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -n = k := ⟨(-n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    have hval : P.w.valuation z * P.w.valuation (π : F) ^ k = 1 := by
      have := hn
      simp only [Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, hk, zpow_natCast,
        Units.val_pow_eq_pow_val, map_mul, map_pow] at this
      exact this
    have : P.w.valuation z * P.w.valuation (π : F) ^ k < 1 := by
      calc P.w.valuation z * P.w.valuation (π : F) ^ k ≤ P.w.valuation z * 1 :=
            mul_le_mul_right (pow_le_one' hvπ1 k) _
        _ = P.w.valuation z := mul_one _
        _ < 1 := hvz
    rw [hval] at this
    exact lt_irrefl _ this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨z * ((π : F) ^ (m + 1))⁻¹, m, ?_, ?_⟩
  · have := hn
    simp only [Units.val_mul, Units.val_mk0, Units.val_zpow_eq_zpow_val, hm] at this
    rwa [neg_add, zpow_add₀ hπ0, zpow_neg, zpow_neg, zpow_natCast, zpow_one, ← mul_inv,
      ← pow_succ] at this
  · field_simp

/-- The leaf's local-parameter conditions for a uniformizer in the form of `exists_uniformizer`. -/
theorem localParam_of (P : Place F) {π : Fˣ} (hπ : (π : F) ∈ P.w) (hπu : π ∉ P.w.unitGroup)
    (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup) :
    (π : F) ∈ P.w.nonunits ∧ ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = (π : F) * y := by
  have hvπ1 : P.w.valuation (π : F) ≤ 1 := (P.w.valuation_le_one_iff _).2 hπ
  have hvπ : P.w.valuation (π : F) < 1 :=
    lt_of_le_of_ne hvπ1 (fun h => hπu ((P.w.mem_unitGroup_iff π).2 h))
  refine ⟨P.w.mem_nonunits_iff.mpr hvπ, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · exact ⟨0, P.w.zero_mem, by rw [hx0, mul_zero]⟩
  obtain ⟨u, m, hu, rfl⟩ := decomp_nonunit P hπ hπu hdvr hx0 hx
  refine ⟨u * (π : F) ^ m, Subring.mul_mem _ ((P.w.valuation_le_one_iff u).1 hu.le)
    (Subring.pow_mem _ hπ m), by ring⟩

end ElemVal

section ElemMain

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- **Every place has a uniformizer (proved)**: `exists_uniformizer` at places containing `t`, and for
the twisted structure `j ↦ 1/j` at the others. -/
theorem exists_uniformizer_all (P : Place F) :
    ∃ π : Fˣ, (π : F) ∈ P.w ∧ π ∉ P.w.unitGroup ∧
      ∀ x : Fˣ, ∃ n : ℤ, x * π ^ (-n) ∈ P.w.unitGroup := by
  by_cases ht : (tF : F) ∈ P.w
  · exact exists_uniformizer P ht
  · haveI := twist_finiteDimensional (F := F)
    refine @exists_uniformizer F _ (twistAlg (F := F)) _ twist_finiteDimensional P ?_
    have hs : (sF : F) ∉ P.w := by
      intro hs; apply ht; rw [tF_eq_mul]; exact Subring.mul_mem _ (P.rat_mem _) hs
    have hinv : (sF : F)⁻¹ ∈ P.w := (P.w.mem_or_inv_mem _).resolve_left hs
    have : @tF F _ (twistAlg (F := F)) = algebraMap ℚ F (1 / 1728) * (sF : F)⁻¹ := by
      rw [@tF_eq_mul F _ (twistAlg (F := F)), sF_twist]
    rw [this]
    exact Subring.mul_mem _ (P.rat_mem _) hinv

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F] in
/-- `D_P`: a derivation preserving `𝒪_P` maps the differentials regular at `P` into `𝒪_P`. -/
theorem lift_mem_of_regularAt (P : Place F) (δ : Derivation ℚ F F) (hδ : ∀ x ∈ P.w, δ x ∈ P.w)
    {ω : Ω[F⁄ℚ]} (hω : ω ∈ regularAt F P.w) : δ.liftKaehlerDifferential ω ∈ P.w := by
  induction hω using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hx
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul]
    exact Subring.mul_mem _ ha (hδ b hb)
  | zero => rw [map_zero]; exact P.w.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  | neg x _ hx => rw [map_neg]; exact Subring.neg_mem _ hx

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F] in
theorem sF_eq_mul : (sF : F) = algebraMap ℚ F 1728 * (tF : F) := by
  rw [tF_eq_mul, ← mul_assoc, ← map_mul]; norm_num

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] in
/-- `s − 1728 ≠ 0` in `F`. -/
theorem sF_sub_ne_zero : (sF : F) - algebraMap ℚ F 1728 ≠ 0 := by
  intro h
  have h' : algebraMap Qj F (RatFunc.X - algebraMap ℚ Qj 1728) = 0 := by
    rw [map_sub, ← RingHom.comp_apply, algebraMap_rat_comp]; exact h
  rw [map_eq_zero_iff _ (algebraMap Qj F).injective, sub_eq_zero, map_ofNat] at h'
  apply RatFunc.transcendental_X (K := ℚ)
  refine ⟨Polynomial.X - Polynomial.C 1728, Polynomial.X_sub_C_ne_zero _, ?_⟩
  simp [h']

omit [Algebra (Polynomial ℚ) F] [IsScalarTower (Polynomial ℚ) Qj F] in
theorem sF_ne_zero : (sF : F) ≠ 0 := by
  intro h
  rw [sF, map_eq_zero_iff _ (algebraMap Qj F).injective] at h
  exact RatFunc.X_ne_zero h

/-- **The local conditions (proved).** If `h • ds` is regular at every place, then
`h s (s − 1728)` lies in every place containing `s`, and `h (s − 1728) ∈ 𝔪_P` at every place not
containing `s`. -/
theorem local_conditions (hL : LocalDerivation) (hK : ConstantFieldIsQ F) (hB : IsBelyiFunction ℚ F (tF : F)) (h : F)
    (hω : ∀ P : Place F, h • KaehlerDifferential.D ℚ F (sF : F) ∈ regularAt F P.w) :
    (∀ P : Place F, (sF : F) ∈ P.w →
        h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) ∈ P.w) ∧
      (∀ P : Place F, (sF : F) ∉ P.w → h * ((sF : F) - algebraMap ℚ F 1728) ∈ P.w.nonunits) := by
  have key : ∀ (P : Place F) (π : F) (δ : Derivation ℚ F F), δ π = 1 → (∀ x ∈ P.w, δ x ∈ P.w) →
      h * δ (sF : F) ∈ P.w := by
    intro P π δ _ hδ
    have := lift_mem_of_regularAt P δ hδ (hω P)
    rwa [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul] at this
  have h1728 : ∀ (δ : Derivation ℚ F F), δ ((sF : F) - algebraMap ℚ F 1728) = δ (sF : F) := by
    intro δ; rw [map_sub, Derivation.map_algebraMap, sub_zero]
  constructor
  · intro P hs
    have hs1728 : (sF : F) - algebraMap ℚ F 1728 ∈ P.w := Subring.sub_mem _ hs (P.rat_mem _)
    -- the three cases at a finite place
    by_cases h0 : (sF : F) ∈ P.w.nonunits
    · -- over `j = 0`
      obtain ⟨π, hπ, hπu, hdvr⟩ := exists_uniformizer_all P
      obtain ⟨hπn, hπd⟩ := localParam_of P hπ hπu hdvr
      obtain ⟨δ, hδπ, hδ⟩ := hL F hK P π π.ne_zero hπn hπd
      obtain ⟨u, m, hu, hsu⟩ := decomp_nonunit P hπ hπu hdvr sF_ne_zero h0
      obtain ⟨c, hc0, hcw, hciw, hδs⟩ := deriv_unit_pow P δ hδ hπn hδπ hu m
      have hk := key P π δ hδπ hδ
      rw [hsu, hδs] at hk
      have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
      have heq : h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) =
          (h * ((π : F) ^ m * c)) * ((π : F) * u * c⁻¹) * ((sF : F) - algebraMap ℚ F 1728) := by
        rw [hsu]; field_simp; ring
      rw [heq]
      exact Subring.mul_mem _ (Subring.mul_mem _ hk
        (Subring.mul_mem _ (Subring.mul_mem _ hπ huw) hciw)) hs1728
    by_cases h1 : (sF : F) - algebraMap ℚ F 1728 ∈ P.w.nonunits
    · -- over `j = 1728`
      obtain ⟨π, hπ, hπu, hdvr⟩ := exists_uniformizer_all P
      obtain ⟨hπn, hπd⟩ := localParam_of P hπ hπu hdvr
      obtain ⟨δ, hδπ, hδ⟩ := hL F hK P π π.ne_zero hπn hπd
      obtain ⟨u, m, hu, hsu⟩ := decomp_nonunit P hπ hπu hdvr sF_sub_ne_zero h1
      obtain ⟨c, hc0, hcw, hciw, hδs⟩ := deriv_unit_pow P δ hδ hπn hδπ hu m
      have hk := key P π δ hδπ hδ
      rw [← h1728 δ, hsu, hδs] at hk
      have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
      have heq : h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) =
          (h * ((π : F) ^ m * c)) * ((π : F) * u * c⁻¹) * (sF : F) := by
        rw [hsu]; field_simp; ring
      rw [heq]
      exact Subring.mul_mem _ (Subring.mul_mem _ hk
        (Subring.mul_mem _ (Subring.mul_mem _ hπ huw) hciw)) hs
    · -- unramified: the Belyi property gives a uniformizer `q(t)`
      have ht : (tF : F) ∈ P.w := by
        rw [tF_eq_mul]; exact Subring.mul_mem _ (P.rat_mem _) hs
      have hpr := polyIdeal_isPrime P ht
      obtain ⟨q, hqm, hqi, hqI⟩ := exists_monic_irreducible_mem (polyIdeal P ht)
        (polyIdeal_ne_bot P ht hB.1)
      have hqI' : Polynomial.aeval (tF : F) q ∈ P.w.nonunits := hqI
      have hX : q ≠ Polynomial.X := by
        rintro rfl
        rw [Polynomial.aeval_X] at hqI'
        apply h0
        rw [sF_eq_mul]
        exact mul_mem_nonunits P.w (P.rat_mem _) hqI'
      have hX1 : q ≠ Polynomial.X - 1 := by
        rintro rfl
        rw [map_sub, Polynomial.aeval_X, map_one] at hqI'
        apply h1
        rw [sF_eq_mul, show algebraMap ℚ F 1728 * (tF : F) - algebraMap ℚ F 1728 =
          algebraMap ℚ F 1728 * ((tF : F) - 1) by ring]
        exact mul_mem_nonunits P.w (P.rat_mem _) hqI'
      have hgen := hB.2 P.w P.rat_mem ht q hqm hqi hX hX1 hqI'
      have hq0 : Polynomial.aeval (tF : F) q ≠ 0 := fun h0' => hB.1 ⟨q, hqm.ne_zero, h0'⟩
      obtain ⟨δ, hδπ, hδ⟩ := hL F hK P _ hq0 hqI' hgen
      have hk := key P _ δ hδπ hδ
      -- `δ(q(t)) = q'(t) δ t = 1`
      have hdq : Polynomial.aeval (tF : F) (Polynomial.derivative q) * δ (tF : F) = 1 := by
        rw [← hδπ, Derivation.map_aeval, smul_eq_mul]
      have hds : δ (sF : F) = algebraMap ℚ F 1728 * δ (tF : F) := by
        rw [sF_eq_mul, Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero,
          smul_eq_mul]
      have hq'w : Polynomial.aeval (tF : F) (Polynomial.derivative q) ∈ P.w := aeval_mem P ht _
      have hh : h ∈ P.w := by
        have heq : h = (h * δ (sF : F)) * (Polynomial.aeval (tF : F) (Polynomial.derivative q) *
            algebraMap ℚ F (1 / 1728)) := by
          rw [hds]
          have h1728ne : algebraMap ℚ F 1728 * algebraMap ℚ F (1 / 1728) = 1 := by
            rw [← map_mul]; norm_num
          calc h = h * (Polynomial.aeval (tF : F) (Polynomial.derivative q) * δ (tF : F)) *
                (algebraMap ℚ F 1728 * algebraMap ℚ F (1 / 1728)) := by rw [hdq, h1728ne]; ring
            _ = _ := by ring
        rw [heq]
        exact Subring.mul_mem _ hk (Subring.mul_mem _ hq'w (P.rat_mem _))
      exact Subring.mul_mem _ hh (Subring.mul_mem _ hs hs1728)
  · -- at infinity: `z = 1/(sF : F) ∈ 𝔪_P`
    intro P hs
    have hz : (sF : F)⁻¹ ∈ P.w.nonunits :=
      P.w.inv_mem_nonunits_iff.mpr (Or.inr hs)
    have hzw : (sF : F)⁻¹ ∈ P.w := (P.w.mem_or_inv_mem _).resolve_left hs
    obtain ⟨π, hπ, hπu, hdvr⟩ := exists_uniformizer_all P
    obtain ⟨hπn, hπd⟩ := localParam_of P hπ hπu hdvr
    obtain ⟨δ, hδπ, hδ⟩ := hL F hK P π π.ne_zero hπn hπd
    obtain ⟨u, m, hu, hzu⟩ := decomp_nonunit P hπ hπu hdvr (inv_ne_zero sF_ne_zero) hz
    obtain ⟨c, hc0, hcw, hciw, hδz⟩ := deriv_unit_pow P δ hδ hπn hδπ hu m
    have hk := key P π δ hδπ hδ
    have hs0 : (sF : F) ≠ 0 := sF_ne_zero
    have hδs : δ (sF : F) = -((sF : F) ^ 2) * δ (sF : F)⁻¹ := by
      rw [Derivation.leibniz_inv, smul_eq_mul]; field_simp
    have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
    have hπ0 : (π : F) ≠ 0 := π.ne_zero
    have huw : u ∈ P.w := (P.w.valuation_le_one_iff u).1 hu.le
    have heq : h * ((sF : F) - algebraMap ℚ F 1728) =
        (h * δ (sF : F)) * (-(π : F) * u * (1 - algebraMap ℚ F 1728 * (sF : F)⁻¹) * c⁻¹) := by
      have hs' : (sF : F) = (u * (π : F) ^ (m + 1))⁻¹ := by rw [← hzu, inv_inv]
      rw [hδs, hzu, hδz, hs']
      field_simp
      ring
    rw [heq]
    refine mul_mem_nonunits P.w hk ?_
    have h' : -(π : F) * u * (1 - algebraMap ℚ F 1728 * (sF : F)⁻¹) * c⁻¹ =
        (-(u * (1 - algebraMap ℚ F 1728 * (sF : F)⁻¹) * c⁻¹)) * (π : F) := by ring
    rw [h']
    refine mul_mem_nonunits P.w ?_ hπn
    refine Subring.neg_mem _ (Subring.mul_mem _ (Subring.mul_mem _ huw ?_) hciw)
    exact Subring.sub_mem _ P.w.one_mem (Subring.mul_mem _ (P.rat_mem _) hzw)

end ElemMain

end GenusRoute

namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section ElemDiff

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F]

omit [FiniteDimensional Qj F] in
/-- `d(a) ∈ F · ds` for `a ∈ ℚ(j)` (quotient rule). -/
theorem D_algebraMap_mem_span (a : Qj) :
    KaehlerDifferential.D ℚ F (algebraMap Qj F a) ∈
      Submodule.span F {KaehlerDifferential.D ℚ F (sF : F)} := by
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial ℚ) a
  have hp : ∀ r : Polynomial ℚ,
      algebraMap Qj F (algebraMap (Polynomial ℚ) Qj r) = Polynomial.aeval (sF : F) r := by
    intro r
    have h2 : (algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj) =
        (Polynomial.aeval (sF : F)).toRingHom := by
      refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
      simp [RatFunc.algebraMap_X]
    exact congrArg (fun φ : Polynomial ℚ →+* F => φ r) h2
  rw [map_div₀, hp p, hp q, Derivation.leibniz_div, Derivation.map_aeval, Derivation.map_aeval]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_) <;>
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

/-- **`Ω_{F/ℚ} = F · ds` (proved)**: `F/ℚ(j)` is finite separable, so `Ω_{F/ℚ(j)} = 0` and
`F ⊗ Ω_{ℚ(j)/ℚ} → Ω_{F/ℚ}` is onto; `Ω_{ℚ(j)/ℚ}` is generated by the `d a`. -/
theorem mem_span_D_sF (ω : Ω[F⁄ℚ]) :
    ω ∈ Submodule.span F {KaehlerDifferential.D ℚ F (sF : F)} := by
  haveI : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified Qj F := Algebra.FormallyUnramified.of_isSeparable Qj F
  have hC : ∀ c : ℚ, algebraMap Qj F (RatFunc.C c) = algebraMap ℚ F c := fun c =>
    congrArg (fun φ : ℚ →+* F => φ c) (RingHom.ext_rat ((algebraMap Qj F).comp RatFunc.C) _)
  haveI : IsScalarTower ℚ Qj F := ⟨fun c a x => by
    rw [RatFunc.smul_eq_C_mul]; simp only [Algebra.smul_def, map_mul, hC, mul_assoc]⟩
  have hker : ω ∈ LinearMap.ker (KaehlerDifferential.map ℚ Qj F F) := by
    rw [LinearMap.mem_ker]; exact Subsingleton.elim _ _
  rw [← KaehlerDifferential.range_mapBaseChange] at hker
  obtain ⟨t, rfl⟩ := hker
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul f η =>
    rw [KaehlerDifferential.mapBaseChange_tmul]
    refine Submodule.smul_mem _ f ?_
    have hη : η ∈ Submodule.span Qj (Set.range (KaehlerDifferential.D ℚ Qj)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hη using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [KaehlerDifferential.map_D]; exact D_algebraMap_mem_span a
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [map_smul, ← algebraMap_smul F c]
      exact Submodule.smul_mem _ _ hx
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

end ElemDiff

section ElemSpace

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- **The space `V`**: `h` with `h s (s − 1728)` in every place containing `s` and
`h (s − 1728) ∈ 𝔪_P` at every place not containing `s` (`s = j` in `F`). -/
def Vspace (F : Type) [Field F] [Algebra Qj F] [Algebra ℚ F] : Submodule ℚ F where
  carrier := {h | (∀ P : Place F, (sF : F) ∈ P.w →
      h * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)) ∈ P.w) ∧
    (∀ P : Place F, (sF : F) ∉ P.w → h * ((sF : F) - algebraMap ℚ F 1728) ∈ P.w.nonunits)}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun P hP => by rw [add_mul]; exact Subring.add_mem _ (ha1 P hP) (hb1 P hP),
      fun P hP => ?_⟩
    rw [add_mul, P.w.mem_nonunits_iff]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _)
      (max_lt (P.w.mem_nonunits_iff.mp (ha2 P hP)) (P.w.mem_nonunits_iff.mp (hb2 P hP)))
  zero_mem' := ⟨fun P _ => by rw [zero_mul]; exact P.w.zero_mem,
    fun P _ => by rw [zero_mul, P.w.mem_nonunits_iff, map_zero]; exact zero_lt_one⟩
  smul_mem' := by
    rintro c h ⟨h1, h2⟩
    refine ⟨fun P hP => ?_, fun P hP => ?_⟩
    · rw [Algebra.smul_def, mul_assoc]; exact Subring.mul_mem _ (P.rat_mem c) (h1 P hP)
    · rw [Algebra.smul_def, mul_assoc]; exact mul_mem_nonunits P.w (P.rat_mem c) (h2 P hP)

/-- **Elements in every place are rational (proved)**, when `ℚ` is algebraically closed in `F`:
`ℚ` is then integrally closed in `F`, and an element outside an integrally closed subring is
outside some valuation subring containing it (Mathlib, Stacks 090P). -/
theorem mem_rat_of_all_places (hK : ConstantFieldIsQ F) {k : F} (hk : ∀ P : Place F, k ∈ P.w) :
    k ∈ Set.range (algebraMap ℚ F) := by
  by_contra hnot
  let R : Subring F := (algebraMap ℚ F).range
  have hkR : k ∉ R := fun h => hnot (by obtain ⟨c, hc⟩ := RingHom.mem_range.mp h; exact ⟨c, hc⟩)
  have hratHom : ratHom F = algebraMap ℚ F := RingHom.ext_rat _ _
  haveI : IsIntegrallyClosedIn R F := by
    rw [Subring.isIntegrallyClosedIn_iff]
    intro x hx
    obtain ⟨p, hpm, hp⟩ := hx
    let e : ℚ ≃+* R := RingEquiv.ofBijective (algebraMap ℚ F).rangeRestrict
      ⟨(algebraMap ℚ F).injective.codRestrict _, RingHom.rangeRestrict_surjective _⟩
    have hcomp : (algebraMap R F).comp e.toRingHom = algebraMap ℚ F := RingHom.ext_rat _ _
    have hf : p.map e.symm.toRingHom ≠ 0 :=
      (Polynomial.map_ne_zero_iff e.symm.injective).mpr hpm.ne_zero
    have hev : (p.map e.symm.toRingHom).eval₂ (ratHom F) x = 0 := by
      rw [hratHom, Polynomial.eval₂_map, ← hcomp, RingHom.comp_assoc]
      have : e.toRingHom.comp e.symm.toRingHom = RingHom.id R := by
        ext r; simp
      rw [this, RingHom.comp_id]; exact hp
    obtain ⟨c, hc⟩ := hK x ⟨_, hf, hev⟩
    rw [← hc, hratHom]; exact RingHom.mem_range_self _ _
  obtain ⟨V, hRV, hkV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hkR
  have hV : V ≠ ⊤ := fun h => hkV (h ▸ ValuationSubring.mem_top _)
  exact hkV (hk ⟨V, hV, fun c => hRV (RingHom.mem_range_self _ c)⟩)

/-- There is a place over `j = ∞` (from the fundamental identity at `∞`). -/
theorem exists_place_inf [FiniteDimensional Qj F] : ∃ P : Place F, (sF : F) ∉ P.w := by
  obtain ⟨hfin, hsum⟩ := fundamentalIdentityQj F {P : Place F | (tF : F) ∉ P.w} (by simp)
  by_contra hne
  push Not at hne
  have hempty : hfin.toFinset = ∅ := by
    ext P
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.notMem_empty, iff_false, not_not]
    rw [tF_eq_mul]; exact Subring.mul_mem _ (P.rat_mem _) (hne P)
  rw [hempty, Finset.sum_empty] at hsum
  exact (Module.finrank_pos (R := Qj) (M := F)).ne hsum

end ElemSpace

section ElemCount

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- **Elements in every place containing `s` are integral over `ℚ[s]` (proved)**: `OF` is a Dedekind
domain, its height-one primes are the places containing `s`. -/
theorem mem_OF_of_places {x : F} (hx : ∀ P : Place F, (sF : F) ∈ P.w → x ∈ P.w) : x ∈ OF := by
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := OF) F x (fun v => by
    have h := hx (placeOf v) (sF_mem_placeOf v)
    change x ∈ (v.valuation F).valuationSubring at h
    exact (Valuation.mem_valuationSubring_iff _ _).mp h)
  rw [← hr]; exact r.2

theorem algebraMap_poly_C (c : ℚ) : algebraMap (Polynomial ℚ) F (Polynomial.C c) = algebraMap ℚ F c := by
  have : (algebraMap (Polynomial ℚ) F).comp Polynomial.C = algebraMap ℚ F := RingHom.ext_rat _ _
  exact congrArg (fun φ : ℚ →+* F => φ c) this

theorem algebraMap_poly_X : algebraMap (Polynomial ℚ) F Polynomial.X = (sF : F) := by
  rw [IsScalarTower.algebraMap_apply (Polynomial ℚ) Qj F, RatFunc.algebraMap_X]

/-- **`dim_ℚ V ≤ [F : ℚ(j)]` (proved).** `h ↦ h s (s − 1728) mod s·OF` injects `V` into
`OF / s·OF ≅ ℚ^d` (`OF` is free of rank `d` over `ℚ[s]`): if `h s (s − 1728) = s k` with `k ∈ OF`, then
`k = h (s − 1728)` lies in every place and in `𝔪_P` over `∞`, so `k ∈ ℚ` and `k = 0`. -/
theorem finrank_Vspace_le (hK : ConstantFieldIsQ F) :
    FiniteDimensional ℚ (Vspace F) ∧ Module.finrank ℚ (Vspace F) ≤ Module.finrank Qj F := by
  haveI := isSeparable_Qj (F := F)
  haveI : Module.IsTorsionFree (Polynomial ℚ) F := .trans_faithfulSMul (Polynomial ℚ) Qj F
  haveI : Module.Free (Polynomial ℚ) OF := IsIntegralClosure.module_free (Polynomial ℚ) Qj F OF
  haveI : Module.Finite (Polynomial ℚ) OF := IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  have hrank : Module.finrank (Polynomial ℚ) OF = Module.finrank Qj F :=
    IsIntegralClosure.rank (Polynomial ℚ) Qj F OF
  let ι := Module.Free.ChooseBasisIndex (Polynomial ℚ) OF
  let b := Module.Free.chooseBasis (Polynomial ℚ) OF
  have hcard : Fintype.card ι = Module.finrank Qj F := by
    rw [← hrank, Module.finrank_eq_card_chooseBasisIndex]
  let x : Vspace F → OF := fun h =>
    ⟨h.1 * ((sF : F) * ((sF : F) - algebraMap ℚ F 1728)), mem_OF_of_places h.2.1⟩
  have hxadd : ∀ h1 h2, x (h1 + h2) = x h1 + x h2 := fun h1 h2 => Subtype.ext (by
    simp only [x, Submodule.coe_add, Subalgebra.coe_add]; ring)
  have hxsmul : ∀ (c : ℚ) h, x (c • h) = Polynomial.C c • x h := fun c h => Subtype.ext (by
    rw [SetLike.val_smul]
    simp only [x, Submodule.coe_smul, Algebra.smul_def, algebraMap_poly_C]
    ring)
  let Ψ : Vspace F →ₗ[ℚ] (ι → ℚ) :=
    { toFun := fun h i => (b.repr (x h) i).eval 0
      map_add' := fun h1 h2 => by
        ext i; simp only [hxadd, map_add, Finsupp.add_apply, Polynomial.eval_add, Pi.add_apply]
      map_smul' := fun c h => by
        ext i
        simp only [hxsmul, map_smul, Finsupp.smul_apply, smul_eq_mul, Polynomial.eval_mul,
          Polynomial.eval_C, RingHom.id_apply, Pi.smul_apply] }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hΨ
    have hdvd : ∀ i, (Polynomial.X : Polynomial ℚ) ∣ b.repr (x h) i := fun i => by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
      exact congrFun hΨ i
    choose q hq using hdvd
    let k : OF := ∑ i, q i • b i
    have hxk : x h = (Polynomial.X : Polynomial ℚ) • k := by
      conv_lhs => rw [← b.sum_repr (x h)]
      simp only [k, Finset.smul_sum, smul_smul, hq]
    have hkF : (k : F) = h.1 * ((sF : F) - algebraMap ℚ F 1728) := by
      have h1 := congrArg (fun y : OF => (y : F)) hxk
      simp only [SetLike.val_smul] at h1
      simp only [x, Algebra.smul_def, algebraMap_poly_X] at h1
      have hs0 : (sF : F) ≠ 0 := sF_ne_zero
      refine mul_left_cancel₀ hs0 ?_
      rw [← h1]; ring
    have hkall : ∀ P : Place F, (k : F) ∈ P.w := by
      intro P
      by_cases hs : (sF : F) ∈ P.w
      · exact intCl_mem P hs k
      · rw [hkF]
        exact (P.w.valuation_le_one_iff _).mp (P.w.mem_nonunits_iff.mp (h.2.2 P hs)).le
    obtain ⟨c, hc⟩ := mem_rat_of_all_places hK hkall
    obtain ⟨P, hP⟩ := exists_place_inf (F := F)
    have hkP := h.2.2 P hP
    rw [← hkF, ← hc] at hkP
    have hc0 : c = 0 := by
      by_contra hc0
      rw [P.w.mem_nonunits_iff, val_rat P hc0] at hkP
      exact lt_irrefl _ hkP
    rw [hc0, map_zero] at hc
    rw [← hc] at hkF
    have : h.1 = 0 := by
      rcases mul_eq_zero.mp hkF.symm with h0 | h0
      · exact h0
      · exact absurd h0 sF_sub_ne_zero
    exact Subtype.ext this
  haveI : FiniteDimensional ℚ (Vspace F) := Module.Finite.of_injective Ψ hinj
  refine ⟨this, ?_⟩
  calc Module.finrank ℚ (Vspace F) ≤ Module.finrank ℚ (ι → ℚ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℚ
    _ = _ := hcard

/-- **`g(F) ≤ [F : ℚ(j)]` (proved from `LocalDerivation`).** Every holomorphic differential is
`h · ds` (`mem_span_D_sF`) with `h ∈ V` (`local_conditions`), and `dim V ≤ [F : ℚ(j)]`. -/
theorem genus_le_finrank (hL : LocalDerivation) (hK : ConstantFieldIsQ F)
    (hB : IsBelyiFunction ℚ F (tF : F)) : fieldGenus F ≤ Module.finrank Qj F := by
  obtain ⟨hfd, hle⟩ := finrank_Vspace_le hK
  let φ : F →ₗ[ℚ] Ω[F⁄ℚ] :=
    (LinearMap.toSpanSingleton F Ω[F⁄ℚ] (KaehlerDifferential.D ℚ F (sF : F))).restrictScalars ℚ
  have hsub : holoDiff F ≤ (Vspace F).map φ := by
    refine Submodule.span_le.mpr fun ω hω => ?_
    obtain ⟨h, rfl⟩ := Submodule.mem_span_singleton.mp (mem_span_D_sF ω)
    exact ⟨h, local_conditions hL hK hB h (fun P => hω P.w P.rat_mem), rfl⟩
  haveI : Module.Finite ℚ ((Vspace F).map φ) := Module.Finite.map _ _
  calc fieldGenus F = Module.finrank ℚ (holoDiff F) := rfl
    _ ≤ Module.finrank ℚ ((Vspace F).map φ) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank ℚ (Vspace F) := Submodule.finrank_map_le φ (Vspace F)
    _ ≤ _ := hle

end ElemCount

/-- **`GenusLeDegree` from `LocalDerivation` (proved).** -/
theorem genusLeDegree_of_localDerivation (hL : LocalDerivation) : GenusLeDegree := by
  intro F _ _ _ _ hK hB
  letI : Algebra (Polynomial ℚ) F :=
    ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
  haveI : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
  exact genus_le_finrank hL hK hB

/-- **`DimJ1Le` (the only use of T34) from `DimJacobianEqGenus` and `LocalDerivation` (proved).**
No Riemann–Hurwitz, no `GenusX1Field`, no `X0Transitive`. -/
theorem dimJ1Le_of_localDerivation (h1 : DimJacobianEqGenus) (hL : LocalDerivation) : DimJ1Le := by
  rintro N J hN ⟨X, P₀, aj, ⟨hC, hI, P, hP, he⟩, hJ⟩
  have hK : ConstantFieldIsQ (fieldX1 P) := constantFieldIsQ_of_curve X hC (fieldX1 P) he.some
  obtain ⟨hBel, hdeg⟩ := ZInQ.RLeaf.belyiX1 N P hN hP
  have hg := genusLeDegree_of_localDerivation hL (fieldX1 P) hK hBel
  exact ⟨fieldGenus (fieldX1 P), h1 X hC P₀ J aj hJ hI (fieldX1 P) he, hg.trans hdeg⟩

end GenusRoute


/-! ## `LocalDerivation`, proved -/

namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDBasic

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [FiniteDimensional Qj F]

omit [FiniteDimensional Qj F] in
theorem isScalarTower_Q_Qj : IsScalarTower ℚ Qj F := by
  have hC : ∀ c : ℚ, algebraMap Qj F (RatFunc.C c) = algebraMap ℚ F c := fun c =>
    congrArg (fun φ : ℚ →+* F => φ c) (RingHom.ext_rat ((algebraMap Qj F).comp RatFunc.C) _)
  exact ⟨fun c a x => by
    rw [RatFunc.smul_eq_C_mul]; simp only [Algebra.smul_def, map_mul, hC, mul_assoc]⟩

/-- `F` is essentially of finite type over `ℚ`. -/
theorem essFiniteType_QF : Algebra.EssFiniteType ℚ F := by
  haveI := isScalarTower_Q_Qj (F := F)
  haveI : Algebra.EssFiniteType (Polynomial ℚ) Qj :=
    Algebra.EssFiniteType.of_isLocalization Qj (nonZeroDivisors (Polynomial ℚ))
  haveI : Algebra.EssFiniteType ℚ Qj := Algebra.EssFiniteType.comp ℚ (Polynomial ℚ) Qj
  exact Algebra.EssFiniteType.comp ℚ Qj F

omit [FiniteDimensional Qj F] in
/-- `s = j` is transcendental over `ℚ` in `F`. -/
theorem sF_transcendental : Transcendental ℚ (sF : F) := by
  rintro ⟨p, hp0, hp⟩
  have key : ∀ φ : ℚ →+* Qj, Polynomial.eval₂ φ RatFunc.X p = 0 := by
    intro φ
    apply (algebraMap Qj F).injective
    rw [map_zero, Polynomial.hom_eval₂,
      show (algebraMap Qj F).comp φ = algebraMap ℚ F from RingHom.ext_rat _ _, ← Polynomial.aeval_def]
    exact hp
  exact RatFunc.transcendental_X (K := ℚ) ⟨p, hp0, key _⟩

/-- `Ω_{F/ℚ} ≠ 0`: otherwise `F/ℚ` is formally unramified, hence separable algebraic. -/
theorem nontrivial_kaehler : Nontrivial Ω[F⁄ℚ] := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  haveI : Algebra.FormallyUnramified ℚ F := ⟨h⟩
  haveI := essFiniteType_QF (F := F)
  haveI : Algebra.IsSeparable ℚ F := (Algebra.FormallyUnramified.iff_isSeparable ℚ F).mp inferInstance
  exact sF_transcendental (Algebra.IsAlgebraic.isAlgebraic (sF : F))

theorem D_sF_ne_zero : KaehlerDifferential.D ℚ F (sF : F) ≠ 0 := by
  intro h0
  haveI := nontrivial_kaehler (F := F)
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[F⁄ℚ])
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (mem_span_D_sF ω)
  rw [h0, smul_zero] at hω; exact hω rfl

/-- **`d/ds` (proved).** -/
theorem exists_deriv_s : ∃ δ : Derivation ℚ F F, δ (sF : F) = 1 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one F (D_sF_ne_zero (F := F))
  exact ⟨f.compDer (KaehlerDifferential.D ℚ F), by simpa using hf⟩

/-- Every derivation is determined by its value at `s`: `δ x = δ_s(x) · δ(s)`. -/
theorem deriv_eq_mul (δs δ : Derivation ℚ F F) (hδs : δs (sF : F) = 1) (x : F) :
    δ x = δs x * δ (sF : F) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (mem_span_D_sF (KaehlerDifferential.D ℚ F x))
  have h1 := congrArg δ.liftKaehlerDifferential hc
  have h2 := congrArg δs.liftKaehlerDifferential hc
  simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, hδs, mul_one] at h1 h2
  rw [← h1, h2]

end LDBasic

section LDPlace

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F]

/-- For a uniformizer `π` (leaf form) and `π₀` (exponent form), some power of `π` brings any element
into `𝒪_P`. -/
theorem exists_pow_mul_mem (P : Place F) {π : F} (hπn : π ∈ P.w.nonunits)
    (hπd : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) {π₀ : Fˣ} (hπ₀ : (π₀ : F) ∈ P.w)
    (hπ₀u : π₀ ∉ P.w.unitGroup) (hdvr : ∀ x : Fˣ, ∃ n : ℤ, x * π₀ ^ (-n) ∈ P.w.unitGroup) (y : F) :
    ∃ N : ℕ, π ^ N * y ∈ P.w := by
  by_cases hy : y ∈ P.w
  · exact ⟨0, by rw [pow_zero, one_mul]; exact hy⟩
  have hy0 : y ≠ 0 := fun h => hy (h ▸ P.w.zero_mem)
  have hyi : y⁻¹ ∈ P.w.nonunits := P.w.inv_mem_nonunits_iff.mpr (Or.inr hy)
  obtain ⟨u, m, hu, hyu⟩ := decomp_nonunit P hπ₀ hπ₀u hdvr (inv_ne_zero hy0) hyi
  -- `π₀ = π c`, `c ∈ 𝒪_P`
  have hπ₀n : (π₀ : F) ∈ P.w.nonunits := (localParam_of P hπ₀ hπ₀u hdvr).1
  obtain ⟨c, hc, hπ₀c⟩ := hπd _ hπ₀n
  have hu0 : u ≠ 0 := by intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  refine ⟨m + 1, ?_⟩
  have hyeq : y = (u * (π₀ : F) ^ (m + 1))⁻¹ := by rw [← hyu, inv_inv]
  -- `π^(m+1) y = π^(m+1) / (u (π c)^(m+1))`; we need `c` to be a unit: `π = π₀ c'`
  obtain ⟨c', hc', hπc'⟩ := (localParam_of P hπ₀ hπ₀u hdvr).2 π hπn
  have hπ0 : π ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hπ₀c; exact π₀.ne_zero hπ₀c
  have hcc' : c * c' = 1 := by
    have : π = π * (c * c') := by rw [← mul_assoc, ← hπ₀c, ← hπc']
    exact (mul_eq_left₀ hπ0).mp this.symm
  have hc0 : c ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hci : c⁻¹ = c' := (eq_inv_of_mul_eq_one_right hcc').symm
  have huinv : u⁻¹ ∈ P.w := (P.w.valuation_le_one_iff _).1 (by rw [map_inv₀, hu, inv_one])
  have : π ^ (m + 1) * y = u⁻¹ * c' ^ (m + 1) := by
    have hc1 : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
    have hcm : c ^ m * c⁻¹ ^ m = 1 := by rw [← mul_pow, hc1, one_pow]
    rw [hyeq, hπ₀c, ← hci]; field_simp
    linear_combination (-(π * π ^ m * (c ^ m * c⁻¹ ^ m))) * hc1 + (-(π * π ^ m)) * hcm
  rw [this]
  exact Subring.mul_mem _ huinv (Subring.pow_mem _ hc' _)

end LDPlace

end GenusRoute

namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDFin

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- Elements of `𝒪_P` are fractions `a / b` with `a, b ∈ OF`, `b` outside the center of `P`. -/
theorem frac_rep (P : Place F) (hs : (sF : F) ∈ P.w) {x : F} (hx : x ∈ P.w) :
    ∃ a b : OF, b ∉ (centerHS P hs).asIdeal ∧ x = (a : F) * (b : F)⁻¹ := by
  have hw : P.w = HeightOneSpectrum.valuationSubringAtPrime F (centerHS P hs) := by
    rw [w_eq_valuationSubring P hs, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  rw [hw] at hx
  obtain ⟨a, b, hb, rfl⟩ := hx
  exact ⟨a, b, hb, rfl⟩

/-- An element of `OF` outside the center is a unit of `𝒪_P`. -/
theorem inv_mem_of_not_mem_center (P : Place F) (hs : (sF : F) ∈ P.w) {b : OF}
    (hb : b ∉ (centerHS P hs).asIdeal) : ((b : F))⁻¹ ∈ P.w ∧ (b : F) ≠ 0 := by
  have hbw : (b : F) ∈ P.w := intCl_mem P hs b
  have hbn : (b : F) ∉ P.w.nonunits := fun h => hb ((mem_centerHS P hs b).mpr h)
  have hv1 : P.w.valuation (b : F) = 1 := by
    refine le_antisymm ((P.w.valuation_le_one_iff _).2 hbw) ?_
    by_contra hlt; push Not at hlt
    exact hbn (P.w.mem_nonunits_iff.mpr hlt)
  refine ⟨(P.w.valuation_le_one_iff _).1 (by rw [map_inv₀, hv1, inv_one]), ?_⟩
  intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1

/-- `δ(p(s)) = p'(s) δ(s)`. -/
theorem deriv_algebraMap_poly (δ : Derivation ℚ F F) (c : Polynomial ℚ) :
    δ (algebraMap (Polynomial ℚ) F c) =
      algebraMap (Polynomial ℚ) F (Polynomial.derivative c) * δ (sF : F) := by
  rw [algebraMap_poly_eq, algebraMap_poly_eq, Derivation.map_aeval, smul_eq_mul]

/-- **The derivative `d/ds` is bounded on `𝒪_P` (proved).** -/
theorem deriv_bound (P : Place F) (hs : (sF : F) ∈ P.w) (δs : Derivation ℚ F F)
    (hδs : δs (sF : F) = 1) {π : F} (hπn : π ∈ P.w.nonunits)
    (hπd : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) :
    ∃ N : ℕ, ∀ x ∈ P.w, π ^ N * δs x ∈ P.w := by
  classical
  haveI : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.IsTorsionFree (Polynomial ℚ) F := .trans_faithfulSMul (Polynomial ℚ) Qj F
  haveI : Module.Free (Polynomial ℚ) OF := IsIntegralClosure.module_free (Polynomial ℚ) Qj F OF
  haveI : Module.Finite (Polynomial ℚ) OF := IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  obtain ⟨π₀, hπ₀, hπ₀u, hdvr⟩ := exists_uniformizer_all P
  have hπw : π ∈ P.w := (P.w.valuation_le_one_iff _).1 (P.w.mem_nonunits_iff.mp hπn).le
  let ι := Module.Free.ChooseBasisIndex (Polynomial ℚ) OF
  let b := Module.Free.chooseBasis (Polynomial ℚ) OF
  have hNi : ∀ i : ι, ∃ N : ℕ, π ^ N * δs (b i : F) ∈ P.w := fun i =>
    exists_pow_mul_mem P hπn hπd hπ₀ hπ₀u hdvr _
  choose Nf hNf using hNi
  let N₀ := Finset.univ.sup Nf
  have hb : ∀ i, π ^ N₀ * δs (b i : F) ∈ P.w := by
    intro i
    have hle : Nf i ≤ N₀ := Finset.le_sup (Finset.mem_univ i)
    have : π ^ N₀ * δs (b i : F) = π ^ (N₀ - Nf i) * (π ^ Nf i * δs (b i : F)) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]; exact Subring.mul_mem _ (Subring.pow_mem _ hπw _) (hNf i)
  have hOF : ∀ a : OF, π ^ N₀ * δs (a : F) ∈ P.w := by
    intro a
    have ha : (a : F) = ∑ i, algebraMap (Polynomial ℚ) F (b.repr a i) * (b i : F) := by
      conv_lhs => rw [← b.sum_repr a]
      simp only [AddSubmonoidClass.coe_finset_sum, Algebra.smul_def, Subalgebra.coe_mul,
        Subalgebra.coe_algebraMap]
    rw [ha, map_sum, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Derivation.leibniz, deriv_algebraMap_poly, hδs, smul_eq_mul, smul_eq_mul, mul_one]
    have h1 : algebraMap (Polynomial ℚ) F (b.repr a i) ∈ P.w := by
      rw [algebraMap_poly_eq]; exact aeval_mem P hs _
    have h2 : algebraMap (Polynomial ℚ) F (Polynomial.derivative (b.repr a i)) ∈ P.w := by
      rw [algebraMap_poly_eq]; exact aeval_mem P hs _
    have h3 : (b i : F) ∈ P.w := intCl_mem P hs _
    have : π ^ N₀ * (algebraMap (Polynomial ℚ) F (b.repr a i) * δs (b i : F) +
        (b i : F) * algebraMap (Polynomial ℚ) F (Polynomial.derivative (b.repr a i))) =
        algebraMap (Polynomial ℚ) F (b.repr a i) * (π ^ N₀ * δs (b i : F)) +
          π ^ N₀ * ((b i : F) * algebraMap (Polynomial ℚ) F (Polynomial.derivative (b.repr a i))) := by
      ring
    rw [this]
    exact Subring.add_mem _ (Subring.mul_mem _ h1 (hb i))
      (Subring.mul_mem _ (Subring.pow_mem _ hπw _) (Subring.mul_mem _ h3 h2))
  refine ⟨N₀, fun x hx => ?_⟩
  obtain ⟨a, c, hc, rfl⟩ := frac_rep P hs hx
  obtain ⟨hci, hc0⟩ := inv_mem_of_not_mem_center P hs hc
  have haw : (a : F) ∈ P.w := intCl_mem P hs a
  rw [Derivation.leibniz, Derivation.leibniz_inv, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have : π ^ N₀ * ((a : F) * (-(c : F)⁻¹ ^ 2 * δs (c : F)) + (c : F)⁻¹ * δs (a : F)) =
      (c : F)⁻¹ * (π ^ N₀ * δs (a : F)) - (a : F) * (c : F)⁻¹ * (c : F)⁻¹ * (π ^ N₀ * δs (c : F)) := by
    ring
  rw [this]
  exact Subring.sub_mem _ (Subring.mul_mem _ hci (hOF a))
    (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ haw hci) hci) (hOF c))

end LDFin

end GenusRoute

namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDRes

open IsDedekindDomain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

attribute [local instance] isDedekind_intCl isFractionRing_intCl

local notation "OF" => integralClosure (Polynomial ℚ) F

/-- **Residue structure (proved).** At a place containing `s` there is `θ ∈ 𝒪_P` and `g ∈ ℚ[T]` with
`g(θ) ∈ 𝔪_P`, `g'(θ)` a unit, and every `x ∈ 𝒪_P` congruent to some `p(θ)` modulo `𝔪_P`. (The residue
field `OF/𝔭` is a finitely generated `ℚ`-algebra and a field, hence finite over `ℚ` (Zariski); take a
primitive element and its minimal polynomial.) -/
theorem residue_structure (P : Place F) (hs : (sF : F) ∈ P.w) :
    ∃ θ : F, θ ∈ P.w ∧ ∃ g : Polynomial ℚ, Polynomial.aeval θ g ∈ P.w.nonunits ∧
      (Polynomial.aeval θ (Polynomial.derivative g))⁻¹ ∈ P.w ∧
      Polynomial.aeval θ (Polynomial.derivative g) ≠ 0 ∧
      ∀ x ∈ P.w, ∃ p : Polynomial ℚ, x - Polynomial.aeval θ p ∈ P.w.nonunits := by
  classical
  haveI : Algebra.IsSeparable Qj F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Module.Finite (Polynomial ℚ) OF := IsIntegralClosure.finite (Polynomial ℚ) Qj F OF
  letI : Algebra ℚ OF := ((algebraMap (Polynomial ℚ) OF).comp (algebraMap ℚ (Polynomial ℚ))).toAlgebra
  haveI : IsScalarTower ℚ (Polynomial ℚ) OF := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℚ OF :=
    Algebra.FiniteType.trans (S := Polynomial ℚ) inferInstance inferInstance
  set 𝔭 := centerHS P hs with h𝔭
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isPrime.isMaximal 𝔭.ne_bot
  letI : Field (OF ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  haveI : Module.Finite ℚ (OF ⧸ 𝔭.asIdeal) := finite_of_finite_type_of_isJacobsonRing ℚ _
  haveI : Algebra.IsSeparable ℚ (OF ⧸ 𝔭.asIdeal) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ (OF ⧸ 𝔭.asIdeal)
  have hint : IsIntegral ℚ α := IsIntegral.of_finite ℚ α
  have hpoly : ∀ y : OF ⧸ 𝔭.asIdeal, ∃ p : Polynomial ℚ, Polynomial.aeval α p = y := by
    intro y
    have hy : y ∈ (IntermediateField.adjoin ℚ {α}).toSubalgebra := by rw [hα]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, hp⟩
  obtain ⟨θ, hθ⟩ := Ideal.Quotient.mk_surjective α
  have hmk : ∀ p : Polynomial ℚ, Ideal.Quotient.mk 𝔭.asIdeal (Polynomial.aeval θ p) =
      Polynomial.aeval α p := by
    intro p
    rw [← hθ]
    exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℚ 𝔭.asIdeal) θ p).symm
  have hcoe : ∀ p : Polynomial ℚ, ((Polynomial.aeval θ p : OF) : F) = Polynomial.aeval (θ : F) p := by
    intro p
    rw [Polynomial.aeval_def, Polynomial.aeval_def]
    have h := Polynomial.hom_eval₂ p (algebraMap ℚ OF) (OF).val.toRingHom θ
    rw [show (OF).val.toRingHom.comp (algebraMap ℚ OF) = algebraMap ℚ F from RingHom.ext_rat _ _] at h
    exact h
  set g := minpoly ℚ α with hg
  have hg0 : Polynomial.aeval α g = 0 := minpoly.aeval ℚ α
  have hg'0 : Polynomial.aeval α (Polynomial.derivative g) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable ℚ α).aeval_derivative_ne_zero hg0
  refine ⟨(θ : F), intCl_mem P hs θ, g, ?_, ?_⟩
  · rw [← hcoe, ← mem_centerHS P hs, ← Ideal.Quotient.eq_zero_iff_mem, hmk, hg0]
  have hnot : Polynomial.aeval θ (Polynomial.derivative g) ∉ 𝔭.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hmk]; exact hg'0
  obtain ⟨hinv, hne⟩ := inv_mem_of_not_mem_center P hs hnot
  rw [hcoe] at hinv hne
  refine ⟨hinv, hne, fun x hx => ?_⟩
  obtain ⟨a, c, hc, rfl⟩ := frac_rep P hs hx
  obtain ⟨hci, hc0⟩ := inv_mem_of_not_mem_center P hs hc
  have hc' : Ideal.Quotient.mk 𝔭.asIdeal c ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hc
  obtain ⟨p, hp⟩ := hpoly (Ideal.Quotient.mk 𝔭.asIdeal a * (Ideal.Quotient.mk 𝔭.asIdeal c)⁻¹)
  refine ⟨p, ?_⟩
  have hmem : a - Polynomial.aeval θ p * c ∈ 𝔭.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hmk, hp]
    field_simp
    ring
  have hmemF := (mem_centerHS P hs _).mp hmem
  have heq : (a : F) * (c : F)⁻¹ - Polynomial.aeval (θ : F) p =
      (c : F)⁻¹ * ((a - Polynomial.aeval θ p * c : OF) : F) := by
    rw [Subalgebra.coe_sub, Subalgebra.coe_mul, hcoe]
    field_simp
  rw [heq]
  exact mul_mem_nonunits P.w hci hmemF

end LDRes

end GenusRoute

namespace GenusRoute

open AlgebraicGeometry CategoryTheory LeafModCurves X1Belyi ZInQ.Contrib.CurvesG

section LDMain

variable {F : Type} [Field F] [Algebra Qj F] [Algebra ℚ F] [Algebra (Polynomial ℚ) F]
  [IsScalarTower (Polynomial ℚ) Qj F] [FiniteDimensional Qj F]

/-- **`LocalDerivation` at a place containing `s` (proved).** With `δ_s = d/ds`: (i) `δ_s` is bounded
on `𝒪_P` (`deriv_bound`); (ii) writing `x = p(θ) + π y` and `g(θ) = π z` (`residue_structure`),
`δ_s x ∈ 𝒪_P δ_s(π) + π (𝒪_P δ_s z + δ_s y)`; iterating, `π^N (δ_s x − a δ_s π) ∈ π^k 𝒪_P` for all `k`.
For `x = s` this forces `δ_s π ≠ 0`, and then `δ = δ_s / δ_s(π)` maps `𝒪_P` into `𝒪_P`. -/
theorem localDer_fin (P : Place F) (hs : (sF : F) ∈ P.w) (π : F) (hπ0 : π ≠ 0)
    (hπn : π ∈ P.w.nonunits) (hπd : ∀ x ∈ P.w.nonunits, ∃ y ∈ P.w, x = π * y) :
    ∃ δ : Derivation ℚ F F, δ π = 1 ∧ ∀ x ∈ P.w, δ x ∈ P.w := by
  obtain ⟨δs, hδs⟩ := exists_deriv_s (F := F)
  obtain ⟨N, hN⟩ := deriv_bound P hs δs hδs hπn hπd
  obtain ⟨θ, hθ, g, hg, hg'i, hg'0, hres⟩ := residue_structure P hs
  have hπw : π ∈ P.w := (P.w.valuation_le_one_iff _).1 (P.w.mem_nonunits_iff.mp hπn).le
  have hdec : ∀ x ∈ P.w, ∃ A ∈ P.w, ∃ B ∈ P.w, ∃ z ∈ P.w, ∃ y ∈ P.w,
      δs x = A * δs π + π * (B * δs z + δs y) := by
    intro x hx
    obtain ⟨p, hp⟩ := hres x hx
    obtain ⟨y, hy, hxy⟩ := hπd _ hp
    obtain ⟨z, hz, hgz⟩ := hπd _ hg
    have hθd : Polynomial.aeval θ (Polynomial.derivative g) * δs θ = π * δs z + z * δs π := by
      rw [← smul_eq_mul, ← Derivation.map_aeval, hgz, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    have hθd' : δs θ = (Polynomial.aeval θ (Polynomial.derivative g))⁻¹ * (π * δs z + z * δs π) := by
      rw [← hθd]; field_simp
    have hx' : x = Polynomial.aeval θ p + π * y := by rw [← hxy]; ring
    have hp'w : Polynomial.aeval θ (Polynomial.derivative p) ∈ P.w := aeval_mem P hθ _
    refine ⟨Polynomial.aeval θ (Polynomial.derivative p) *
        (Polynomial.aeval θ (Polynomial.derivative g))⁻¹ * z + y,
      Subring.add_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hp'w hg'i) hz) hy,
      Polynomial.aeval θ (Polynomial.derivative p) * (Polynomial.aeval θ (Polynomial.derivative g))⁻¹,
      Subring.mul_mem _ hp'w hg'i, z, hz, y, hy, ?_⟩
    rw [hx', map_add, Derivation.map_aeval, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, hθd']
    ring
  have hQ : ∀ k : ℕ, ∀ x ∈ P.w, ∃ a ∈ P.w, ∃ r ∈ P.w, π ^ N * (δs x - a * δs π) = π ^ k * r := by
    intro k
    induction k with
    | zero => intro x hx; exact ⟨0, P.w.zero_mem, π ^ N * δs x, hN x hx, by ring⟩
    | succ k ih =>
      intro x hx
      obtain ⟨A, hA, B, hB, z, hz, y, hy, hxe⟩ := hdec x hx
      obtain ⟨az, haz, rz, hrz, hz'⟩ := ih z hz
      obtain ⟨ay, hay, ry, hry, hy'⟩ := ih y hy
      refine ⟨A + π * (B * az + ay),
        Subring.add_mem _ hA (Subring.mul_mem _ hπw (Subring.add_mem _ (Subring.mul_mem _ hB haz) hay)),
        B * rz + ry, Subring.add_mem _ (Subring.mul_mem _ hB hrz) hry, ?_⟩
      rw [hxe]
      linear_combination π * B * hz' + π * hy'
  have hδπ : δs π ≠ 0 := by
    intro h0
    obtain ⟨a, ha, r, hr, he⟩ := hQ (N + 1) (sF : F) hs
    rw [h0, mul_zero, sub_zero, hδs, mul_one] at he
    have h1 : π * r = 1 := by
      have hπN : π ^ N ≠ 0 := pow_ne_zero _ hπ0
      apply mul_left_cancel₀ hπN
      calc π ^ N * (π * r) = π ^ (N + 1) * r := by ring
        _ = π ^ N := he.symm
        _ = π ^ N * 1 := (mul_one _).symm
    have h2 := mul_mem_nonunits P.w hr hπn
    rw [mul_comm, h1, P.w.mem_nonunits_iff, map_one] at h2
    exact lt_irrefl _ h2
  obtain ⟨π₀, hπ₀, hπ₀u, hdvr⟩ := exists_uniformizer_all P
  obtain ⟨k, hk⟩ := exists_pow_mul_mem P hπn hπd hπ₀ hπ₀u hdvr (π ^ N * δs π)⁻¹
  refine ⟨(δs π)⁻¹ • δs, ?_, fun x hx => ?_⟩
  · rw [Derivation.smul_apply, smul_eq_mul, inv_mul_cancel₀ hδπ]
  obtain ⟨a, ha, r, hr, he⟩ := hQ k x hx
  have hπN : π ^ N ≠ 0 := pow_ne_zero _ hπ0
  have : ((δs π)⁻¹ • δs) x = a + (π ^ k * (π ^ N * δs π)⁻¹) * r := by
    rw [Derivation.smul_apply, smul_eq_mul]
    have hx' : δs x = a * δs π + π ^ k * r / π ^ N := by
      rw [← he]; field_simp; ring
    rw [hx']
    field_simp
  rw [this]
  exact Subring.add_mem _ ha (Subring.mul_mem _ hk hr)

end LDMain

/-- **`LocalDerivation`, proved.** At places containing `s = j` by `localDer_fin`; at the places over
`j = ∞` by `localDer_fin` for the twisted structure `j ↦ 1/j`. -/
theorem localDerivation : LocalDerivation := by
  intro F _ _ _ _ _ P π hπ0 hπn hπd
  by_cases hs : (sF : F) ∈ P.w
  · letI : Algebra (Polynomial ℚ) F :=
      ((algebraMap Qj F).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
    haveI : IsScalarTower (Polynomial ℚ) Qj F := IsScalarTower.of_algebraMap_eq' rfl
    exact localDer_fin P hs π hπ0 hπn hπd
  · letI : Algebra (Polynomial ℚ) F :=
      ((@algebraMap Qj F _ _ (twistAlg (F := F))).comp (algebraMap (Polynomial ℚ) Qj)).toAlgebra
    have htw : @IsScalarTower (Polynomial ℚ) Qj F _ (twistAlg (F := F)).toSMul _ := by
      letI := twistAlg (F := F)
      exact IsScalarTower.of_algebraMap_eq' rfl
    have hs' : @sF F _ (twistAlg (F := F)) ∈ P.w := by
      rw [sF_twist]; exact (P.w.mem_or_inv_mem _).resolve_left hs
    exact @localDer_fin F _ (twistAlg (F := F)) _ _ htw twist_finiteDimensional P hs' π hπ0 hπn hπd

/-- **The genus bound with no leaf (proved).** -/
theorem genusLeDegree : GenusLeDegree := genusLeDegree_of_localDerivation localDerivation

/-- **`DimJ1Le` (the only use of T34) from `DimJacobianEqGenus` alone (proved).** -/
theorem dimJ1Le_of_dimJacobianEqGenus (h1 : DimJacobianEqGenus) : DimJ1Le :=
  dimJ1Le_of_localDerivation h1 localDerivation

end GenusRoute

end



namespace GenusRoute

/-- **`DimJ1Le` (the only use of T34) with no hypothesis (proved)**: dimjac-glue's
`ModularSplit.DimJac.dimJacobianEqGenus` (copied verbatim above) and `dimJ1Le_of_dimJacobianEqGenus`. -/
theorem dimJ1Le : DimJ1Le := dimJ1Le_of_dimJacobianEqGenus ModularSplit.DimJac.dimJacobianEqGenus

end GenusRoute


#print axioms ModularSplit.DimJac.dimJacobianEqGenus
#print axioms GenusRoute.localDerivation
#print axioms GenusRoute.dimJ1Le

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`DimJ1Le` on the OneProof copies** (`PkgI3.AbVar`, `LeafModCurves.IsJ1` of `HDec`): the conclusion
of `LeafModCurves.dim_J1_le`, the only use of `t34`. -/
def DimJ1Le5 : Prop :=
  ∀ (N : ℕ) (J : PkgI3.AbVar ℚ), 0 < N → LeafModCurves.IsJ1 N J →
    ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2

/-- Transport of the kernel-level `GenusRoute.DimJ1Le` to the OneProof copies (as `t34_of_split5`). -/
theorem dimJ1Le5_of_kernel (h : GenusRoute.DimJ1Le) : DimJ1Le5 := by
  rintro N J hN ⟨X, P₀, aj, hX, hJ⟩
  exact h N (toAbVarK4 J) hN
    ⟨X, P₀, aj, ⟨⟨hX.1.proper, hX.1.smooth, hX.1.geomConnected⟩, hX.2⟩, isJacobianK_of5 hJ⟩

/-- **The replacement for `t34` (proved)**: `dim J₁(N) ≤ N²` from `DimJacobianEqGenus` (proved by
dimjac-glue) and the leaf `RiemannHurwitzQj`. No `GenusX1Field`, no `X0Transitive`. -/
theorem t34Le_of_rh (h1 : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus)
    (hRH : GenusRoute.RiemannHurwitzQj) : DimJ1Le5 :=
  dimJ1Le5_of_kernel (GenusRoute.dimJ1Le_of_rh_curve h1 hRH)

/-- **The replacement for `t34`, with no hypothesis (proved)**: `dim J₁(N) ≤ N²` on the OneProof copies,
from `GenusRoute.dimJ1Le` (dimjac-glue's `dimJacobianEqGenus` and the proved `LocalDerivation`). -/
theorem t34Le : DimJ1Le5 := dimJ1Le5_of_kernel GenusRoute.dimJ1Le

/-- **The replacement for `t34` from the local leaf (proved)**: `dim J₁(N) ≤ N²` from
`DimJacobianEqGenus` (proved by dimjac-glue) and `GenusRoute.LocalDerivation`. No Riemann–Hurwitz,
no `GenusX1Field`, no `X0Transitive`. -/
theorem t34Le_of_localDerivation (h1 : _root_.ZInQ.Contrib.CurvesG.DimJacobianEqGenus)
    (hL : GenusRoute.LocalDerivation) : DimJ1Le5 :=
  dimJ1Le5_of_kernel (GenusRoute.dimJ1Le_of_localDerivation h1 hL)

/-- `t34` implies `DimJ1Le5` (so the new field is weaker than the old one). -/
theorem dimJ1Le5_of_t34 (h : LeafModCurves.DimJ1Genus) : DimJ1Le5 :=
  fun N J hN hJ => LeafModCurves.dim_J1_le h N hN J hJ

/-- **Drop-in for `TailD.lean:236`** (`LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1`). -/
theorem dim_J1_le_of5 (h : DimJ1Le5) (N : ℕ) (hN : 0 < N) (J : PkgI3.AbVar ℚ)
    (hJ : LeafModCurves.IsJ1 N J) : ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2 :=
  h N J hN hJ

/-- The type of `dim_J1_le_of5 h` is the type of `LeafModCurves.dim_J1_le t34` (checked by `example`). -/
example (h : DimJ1Le5) (t34 : LeafModCurves.DimJ1Genus) (N : ℕ) (hN : 0 < N) (J : PkgI3.AbVar ℚ)
    (hJ : LeafModCurves.IsJ1 N J) :
    (∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2) ∧ (∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2) :=
  ⟨dim_J1_le_of5 h N hN J hJ, LeafModCurves.dim_J1_le t34 N hN J hJ⟩

namespace G0Split

/-- **Drop-in for `TailD.lean:250`**: `javanpeykarJ1` (LPrefix) with `t34` replaced by `DimJ1Le5`; the
proof is `javanpeykarJ1`'s with `LeafModCurves.dim_J1_le hT34 N hN J hJ` replaced by `h N J hN hJ`. -/
theorem javanpeykarJ1_of_le (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel)
    (h : DimJ1Le5) : JavanpeykarJ1 := by
  intro N hN J hJ g hg hg1 x hx
  obtain ⟨X, _, _, P₀, aj, hJac, t, ht, d, hd, hd0, hdN⟩ := hB N hN J hJ
  have h' := hR18 ℚ X P₀ J aj hJac g hg hg1 t ht d hd hd0
  rw [hx] at h'
  have hxb : x ≤ ZInQ.LeafPush2.javanpeykarBound g d := EReal.coe_le_coe_iff.mp h'
  obtain ⟨g', hg', hgN⟩ := h N J hN hJ
  have hgg : g = g' := by
    have : (g : WithBot ℕ∞) = (g' : WithBot ℕ∞) := hg.symm.trans hg'
    exact_mod_cast this
  subst hgg
  have hgR : (g : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  have hdR : (d : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hdN
  calc x ≤ ZInQ.LeafPush2.javanpeykarBound g d := hxb
    _ = 13 * 10 ^ 6 * (g : ℝ) * (d : ℝ) ^ 5 := rfl
    _ ≤ 13 * 10 ^ 6 * ((N : ℝ) ^ 2) * ((N : ℝ) ^ 2) ^ 5 := by gcongr
    _ = 13000000 * (N : ℝ) ^ 12 := by ring

/-- `javanpeykarJ1_of_le` agrees with the original on `t34`. -/
example (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel) (t34 : LeafModCurves.DimJ1Genus) :
    javanpeykarJ1_of_le hR18 hB (dimJ1Le5_of_t34 t34) = javanpeykarJ1 hR18 hB t34 := rfl

end G0Split

end HSyn

end HDec

#print axioms HDec.HSyn.t34Le
#print axioms HDec.HSyn.t34Le_of_rh
#print axioms HDec.HSyn.t34Le_of_localDerivation
#print axioms HDec.HSyn.G0Split.javanpeykarJ1_of_le

/-! ### The consumer, refolded: TailD's `glueOutputs_of_leaves3` with `t.t34` replaced by `t34Le`

Copied from `ZInQKernel/OneProof/H/TailD.lean` (lines 204-257, with that file's `maxHeartbeats` and
`-instance` settings); the only changes are the name and the two lines at TailD.lean:236 and :250. The
copy no longer mentions `t.t34`. -/

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

open G0Split in
theorem glueOutputs_of_leaves3_t34Le (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  obtain ⟨hDimF, hDim, hSimp, hPMH, hBC, hProdE, hRev, hThetaPt, hMod, hCopies⟩ := gp
  have hBelyi : X1BelyiOnModel := x1BelyiOnModel_of_belyiX1 t.belyiX1
  have hAdd : HeightAdditivity := heightAdditivity_of_h5neron t.t41 r.h5.2 hPMH
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2)
  intro u hu
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)))
  -- G2-G16 (missing piece 10, `ModularConstituent`): the field `L'`, the model `A`, the level `N`, `J₁(N)`
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  -- H5: the stable height of `A` is real
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  -- G19: the theta point (missing piece 9, `ThetaPointOfFibre`) and Pazuki (R22)
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, Or.inl ?_⟩
  -- E1: a nonzero homomorphism `A → J₁(N)_{L'}`
  obtain ⟨f, hf⟩ := hom_of_common3 r t _ _ hCC
  -- G5-G6 (missing piece 4, `FibreSimple`): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- G17 after Poincaré (`isogenousProduct`, from missing pieces 1, 7, 8): `A × Z`, the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := dim_J1_le_of5 t34Le N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  -- heights (H5; missing pieces 5, 6; R18 with missing pieces 2, 3)
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1_of_le hR18 hBelyi t34Le N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  -- E3-E4 (proved from R19-R21)
  exact transfer_core r.r19 r.r20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

end HSyn

end

end HDec

#print axioms HDec.HSyn.glueOutputs_of_leaves3_t34Le
