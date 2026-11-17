import ZInQKernel.HDecomp.ModCurves.X1Belyi
import ZInQKernel.Contrib.CurvesG.GenusSplit
import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.SmoothStalk
import ZInQKernel.Contrib.SmoothFibre.Basic

/-! # genus-route: the constant field of a smooth proper geometrically connected curve over `ℚ`

`constantFieldIsQ_of_curve` (proved): if `X/ℚ` is a smooth proper geometrically connected integral
curve (`LeafModCurves.IsCurve`) and `F ≃+* K(X)`, then `ℚ` is algebraically closed in `F`
(`X1Belyi.ConstantFieldIsQ F`). Applied to a model of `X₁(N)` this replaces `X0Transitive` in
curve-split's route to `dim J₁(N) ≤ N²`.

Proof: (1) an integral smooth curve is normal (copied from curve-split, `CurveBij.lean`); (2) an
element `y ∈ K(X)` algebraic over `ℚ` is integral over every `Γ(X, U)`, `U` affine, which is
integrally closed with fraction field `K(X)`, so `y ∈ Γ(X, U)`; the local sections glue to
`s ∈ Γ(X, ⊤)` (sheaf axiom; `X` irreducible, so all overlaps are nonempty); (3) with
`A = ℚ[T]/(minpoly y)` (a number field), `s` gives `φ : X → Spec A` over `Spec ℚ`; base change to
`ℚ̄` and geometric connectedness make `Spec (ℚ̄ ⊗ A)` connected (`φ` is surjective, so is its base
change); `ℚ̄ ⊗ A` is Artinian, so its spectrum is discrete, hence a single point; but two distinct
roots `α ≠ β` of `minpoly y` in `ℚ̄` give two distinct primes. So `deg minpoly y = 1`.

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

#print axioms GenusRoute.constantFieldIsQ_of_curve
