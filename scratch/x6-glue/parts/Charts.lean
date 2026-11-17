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
