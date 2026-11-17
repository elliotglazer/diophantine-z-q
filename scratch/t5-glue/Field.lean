import Mathlib

/-!
# t5-glue, part 2: extension of automorphisms to an algebraically closed field (Mathlib only)

Task t5-glue (2026-11-14). Proves, for `ι : k →+* K` with `k`, `K` algebraically closed:

* `exists_ringEquiv_extend`: every automorphism `ρ` of `k` extends to an automorphism `σ` of `K`
  with `σ ∘ ι = ι ∘ ρ`;
* `mem_range_of_fixed`: an element of `K` fixed by every automorphism of `K` fixing `ι(k)` lies in
  `ι(k)`.

Both by Steinitz: `K` is an algebraic closure of `k[T]` for a transcendence basis `T`; an
automorphism of the polynomial ring `k[T]` (coefficients by `ρ`; or `X_z ↦ X_z + 1`) extends to `K`
(Mathlib's `IsAlgClosure.equivOfEquiv`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace T5Glue

open MvPolynomial

/-- An automorphism of the polynomial ring on a transcendence basis extends to `K`. -/
theorem exists_aut_extend {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {ιT : Type*} {v : ιT → K} (hv : IsTranscendenceBasis k v)
    (ψ : MvPolynomial ιT k ≃+* MvPolynomial ιT k) :
    ∃ σ : K ≃+* K, ∀ p : MvPolynomial ιT k, σ (aeval v p) = aeval v (ψ p) := by
  let e := hv.1.aevalEquiv
  let φ : Algebra.adjoin k (Set.range v) ≃+* Algebra.adjoin k (Set.range v) :=
    e.symm.toRingEquiv.trans (ψ.trans e.toRingEquiv)
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range v)) K := hv.isAlgebraic
  have : IsAlgClosure (Algebra.adjoin k (Set.range v)) K := ⟨inferInstance, inferInstance⟩
  refine ⟨IsAlgClosure.equivOfEquiv K K φ, fun p => ?_⟩
  rw [← hv.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap,
    ← hv.1.algebraMap_aevalEquiv]
  congr 1
  simp [φ, e]

/-- **Extension of automorphisms.** -/
theorem exists_ringEquiv_extend {k K : Type*} [Field k] [Field K] [IsAlgClosed K]
    (ι : k →+* K) (ρ : k ≃+* k) : ∃ σ : K ≃+* K, ∀ a : k, σ (ι a) = ι (ρ a) := by
  let _ : Algebra k K := ι.toAlgebra
  have : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 ι.injective
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis k K
  obtain ⟨σ, hσ⟩ := exists_aut_extend hT (MvPolynomial.mapEquiv T ρ)
  refine ⟨σ, fun a => ?_⟩
  have h := hσ (C a)
  simp only [aeval_C, mapEquiv_apply, map_C] at h
  exact h

/-- An element algebraic over an algebraically closed subfield lies in it. -/
theorem mem_range_of_isAlgebraic {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    {z : K} (hz : IsAlgebraic k z) : z ∈ Set.range (algebraMap k K) := by
  have hi : IsIntegral k z := hz.isIntegral
  exact minpoly.mem_range_of_degree_eq_one k z
    (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hi))

/-- **Fixed points.** An element of `K` fixed by every automorphism fixing `ι(k)` is in `ι(k)`. -/
theorem mem_range_of_fixed {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [IsAlgClosed K]
    (ι : k →+* K) (z : K) (hz : ∀ σ : K ≃+* K, (∀ a : k, σ (ι a) = ι a) → σ z = z) :
    ∃ a : k, ι a = z := by
  classical
  let _ : Algebra k K := ι.toAlgebra
  by_contra hne
  have htr : Transcendental k z := fun halg => hne (mem_range_of_isAlgebraic halg)
  have hind : AlgebraicIndepOn k id ({z} : Set K) := by
    rw [AlgebraicIndepOn, algebraicIndependent_singleton_iff (⟨z, rfl⟩ : ({z} : Set K))]
    exact htr
  obtain ⟨t, hzt, hT⟩ := exists_isTranscendenceBasis_superset hind
  have hzt' : z ∈ t := hzt rfl
  let z' : t := ⟨z, hzt'⟩
  let f : t → MvPolynomial t k := fun i => if i = z' then X i + 1 else X i
  let g : t → MvPolynomial t k := fun i => if i = z' then X i - 1 else X i
  have hgf : (aeval g).comp (aeval f) = AlgHom.id k (MvPolynomial t k) := by
    apply MvPolynomial.algHom_ext; intro i
    simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply, f, g]
    split_ifs with h <;> simp [h]
  have hfg : (aeval f).comp (aeval g) = AlgHom.id k (MvPolynomial t k) := by
    apply MvPolynomial.algHom_ext; intro i
    simp only [AlgHom.comp_apply, aeval_X, AlgHom.id_apply, f, g]
    split_ifs with h <;> simp [h]
  let ψ : MvPolynomial t k ≃ₐ[k] MvPolynomial t k := AlgEquiv.ofAlgHom (aeval f) (aeval g) hfg hgf
  obtain ⟨σ, hσ⟩ := exists_aut_extend hT ψ.toRingEquiv
  have hfix : ∀ a : k, σ (ι a) = ι a := by
    intro a
    have h := hσ (C a)
    rw [aeval_C, AlgEquiv.coe_toRingEquiv, ← algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes] at h
    exact h
  have h2 : σ z = z + 1 := by
    have h := hσ (X z')
    rw [aeval_X, AlgEquiv.coe_toRingEquiv] at h
    have hψ : ψ (X z') = X z' + 1 := by simp [ψ, f]
    rw [hψ, map_add, aeval_X, map_one] at h
    exact h
  rw [hz σ hfix] at h2
  simp at h2

end T5Glue
