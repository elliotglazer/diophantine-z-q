import Mathlib

open IsLocalRing Polynomial
open scoped Pointwise
set_option linter.style.haveILetI false

namespace GTSHPair

attribute [local instance] Ideal.Quotient.field in
/-- **A separable residue polynomial.** `φ : R → M` lands in a valuation ring `W` with
`φ⁻¹(𝔪_W) = 𝔮`; if `R/𝔮` is separable over `A/p` then every `x = φ(a)/φ(s)` with `s ∉ 𝔮` is a
root modulo `𝔪_W` of a polynomial over `A` whose reduction is separable. -/
theorem exists_sep_poly {A R M : Type*} [CommRing A] [CommRing R] [Algebra A R] [Field M]
    (φ : R →+* M) (p : Ideal A) [p.IsMaximal] (𝔮 : Ideal R) [𝔮.IsMaximal] [𝔮.LiesOver p]
    [Algebra.IsSeparable (A ⧸ p) (R ⧸ 𝔮)] (W : ValuationSubring M)
    (h𝔮 : ∀ r, r ∈ 𝔮 ↔ φ r ∈ W.nonunits) (hφW : ∀ r, φ r ∈ W) (x : M) (a s : R) (hs : s ∉ 𝔮)
    (hxs : x * φ s = φ a) :
    ∃ f : A[X], (f.map (Ideal.Quotient.mk p)).Separable ∧
      (f.map (φ.comp (algebraMap A R))).eval x ∈ W.nonunits := by
  set y : R ⧸ 𝔮 := Ideal.Quotient.mk 𝔮 a * (Ideal.Quotient.mk 𝔮 s)⁻¹
  have hsy : Ideal.Quotient.mk 𝔮 s ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hint : IsIntegral (A ⧸ p) y := Algebra.IsIntegral.isIntegral y
  set g := minpoly (A ⧸ p) y
  have hg : g.Separable := Algebra.IsSeparable.isSeparable (A ⧸ p) y
  obtain ⟨f, hfg, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective g)
    (minpoly.monic hint)
  refine ⟨f, by rw [hfg]; exact hg, ?_⟩
  set fR := f.map (algebraMap A R)
  have hfR : fR.Monic := hfm.map _
  set F := (scaleRoots fR s).eval a
  -- `F ∈ 𝔮`
  have hF : F ∈ 𝔮 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e1 : Ideal.Quotient.mk 𝔮 F =
        (scaleRoots (fR.map (Ideal.Quotient.mk 𝔮)) (Ideal.Quotient.mk 𝔮 s)).eval
          (Ideal.Quotient.mk 𝔮 a) := by
      rw [← map_scaleRoots _ _ _ (by rw [hfR.leadingCoeff, map_one]; exact one_ne_zero),
        Polynomial.eval_map, ← Polynomial.eval₂_hom]
    have e2 : fR.map (Ideal.Quotient.mk 𝔮) = g.map (algebraMap (A ⧸ p) (R ⧸ 𝔮)) := by
      rw [← hfg, Polynomial.map_map, Polynomial.map_map]
      congr 1
    have e3 : Ideal.Quotient.mk 𝔮 a = Ideal.Quotient.mk 𝔮 s * y := by
      rw [mul_comm, mul_assoc, inv_mul_cancel₀ hsy, mul_one]
    rw [e1, e2, e3, scaleRoots_eval_mul, Polynomial.eval_map, ← Polynomial.aeval_def,
      minpoly.aeval, mul_zero]
  -- transport to `M`
  have e4 : φ F = φ s ^ fR.natDegree * (f.map (φ.comp (algebraMap A R))).eval x := by
    have : φ F = eval₂ φ (φ s * x) (scaleRoots fR s) := by
      rw [mul_comm, hxs, ← Polynomial.eval₂_hom]
    rw [this, scaleRoots_eval₂_mul, ← Polynomial.map_map, Polynomial.eval_map]
  have hφF := (h𝔮 F).mp hF
  have hsu : φ s ∉ W.nonunits := fun h => hs ((h𝔮 s).mpr h)
  rw [ValuationSubring.mem_nonunits_iff] at hφF hsu ⊢
  have hv1 : W.valuation (φ s) = 1 :=
    le_antisymm ((W.valuation_le_one_iff _).mpr (hφW s)) (not_lt.mp hsu)
  rw [e4, map_mul, map_pow, hv1, one_pow, one_mul] at hφF
  exact hφF

end GTSHPair
