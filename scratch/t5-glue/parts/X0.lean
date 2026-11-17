
noncomputable section

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura

/-! ## §3. Verbatim copies of tyz-split's two Props (`scratch/tyz-split/T5.lean` §2)

The kernel's `Shimura.IsRatModFn`, `HeegnerForm`, `ιC`, `GalQ`, `idealLat`, `discOf`, … are
imported; `modCoord` is the verbatim copy of §0. -/

/-- **GLUE CM-MODULI** (tyz-split, verbatim). -/
def CMModuli : Prop :=
  ∀ (N : ℕ), 0 < N →
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
    ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
      ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt m : ℂ) →
    ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) (ρ : GalQ),
      (∀ x : ringClassField (conductorOrder (QNeg m) f),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
          ((conductorOrder (QNeg m) f).picClass J) x)) →
    ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
      idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
      idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
      ∃ x : ℕ → Qbar, (∀ i < N, ιC (x i) = modCoord N Q.tauH i) ∧
        ∀ i < N, ιC (ρ (x i)) = modCoord N Q'.tauH i

/-- **GLUE X0-RAT** (tyz-split, verbatim). -/
def X0RatStructure : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (τ τ' : UpperHalfPlane) (ρ : GalQ) (x : ℕ → Qbar),
      (∀ i < N, ιC (x i) = modCoord N τ i) → (∀ i < N, ιC (ρ (x i)) = modCoord N τ' i) →
      ∃ b b' : Qbar, ιC b = g τ ∧ ιC b' = g τ' ∧ ρ b = b'

/-! ## §4. The modular-curve part `X0RatStructure` -/

/-- **LEAF X0-MODULI (the canonical model of `X₀(N)` over `ℚ`: `Aut(ℂ)` acts on the values of
`ℚ(X₀(N))` through the moduli interpretation).** Let `N ≥ 1`, `g ∈ ℚ(X₀(N))` regular on `ℍ`
(`IsRatModFn N g`), `σ ∈ Aut(ℂ)` and `τ, τ' ∈ ℍ`, where the point `(E_τ, ⟨1/N⟩)` of `Y₀(N)` is
algebraic (its moduli coordinates `modCoord N τ i`, `i < N`, i.e. `j(τ)` and the symmetric functions
of the Weber values of `⟨1/N⟩ \ 0`, are algebraic numbers: `(E_τ, ⟨1/N⟩)` has a model over `ℚ̄`), such
that `σ` carries `(E_τ, ⟨1/N⟩)` to `(E_{τ'}, ⟨k/N⟩)`, in Weierstrass coordinates: for some `μ ∈ ℂˣ`,
`(x, y) ↦ (μ⁻²x, μ⁻³y)` is an isomorphism `E_τ^σ ≅ E_{τ'}`
(`σ(g₂(τ)) = μ⁴g₂(τ')`, `σ(g₃(τ)) = μ⁶g₃(τ')`) sending `σ(P)`, `P = (℘_τ(1/N), ℘'_τ(1/N))`, to the
point `k/N` of `E_{τ'}` for some `1 ≤ k < N` (no condition for `N = 1`). Then `σ(g(τ)) = g(τ')`.

Content: `X₀(N)_ℚ`, the model of `Γ₀(N)\ℍ*` whose function field is the field of functions with
rational `q`-expansion at `∞`, is the coarse moduli space of pairs `(E, C)` (`C` cyclic of order
`N`), compatibly with `Aut(ℂ)`: `g(x)^σ = g(x^σ)` for `g ∈ ℚ(X₀(N))` regular at `x`, where
`x^σ = (E^σ, C^σ)`. Sources (theorem numbers UNVERIFIED, from memory; no network): Shimura 1971,
*Introduction to the arithmetic theory of automorphic functions*, §6.7 (canonical models of
`Γ₀(N)\ℍ*`) with Thm. 6.6 (`F_N = ℚ(ζ_N)(j, f_a)`, Fricke functions = Weber values `h(E, a)`) and
Prop. 6.9; Deligne–Rapoport, *Les schémas de modules de courbes elliptiques* (LNM 349), VI.6 and
VII (q-expansion principle); Diamond–Shurman, *A first course in modular forms*, §7.5–7.7.
On `ℚ̄`-points this is the printed Galois equivariance `g(x)^ρ = g(x^ρ)`, `ρ = σ|_ℚ̄` (Diamond–Shurman
§7.7; Deligne–Rapoport VI (coarse moduli scheme over `ℚ`) and VII (q-expansion principle)).
Relation to the print: `k/N` has exact order `N` whenever the hypothesis holds (`σ` and the
isomorphism preserve the order of `σ(P)`), so `C^σ` is sent to `⟨k/N⟩ = C_{τ'}` and the
hypothesis says `(E_τ, C_τ)^σ ≅ (E_{τ'}, C_{τ'})`; the conclusion is the printed equivariance.
No complex multiplication is involved. -/
def X0ModuliGalois : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (g : UpperHalfPlane → ℂ), IsRatModFn N g →
    ∀ (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      (∀ i < N, ∃ a : Qbar, ιC a = modCoord N τ i) →
      IsConjModel (σ : ℂ →+* ℂ) (pp τ) (pp τ') μ →
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) →
      σ (g τ) = g τ'

/-- **GLUE AUT-EXT (field theory).** Every `ρ ∈ Gal(ℚ̄/ℚ)` extends, through `ιC : ℚ̄ → ℂ`, to an
automorphism of `ℂ`. (Steinitz: `ℂ` is an algebraic closure of `ιC(ℚ̄)(T)` for a transcendence basis
`T`; extend `ρ` by `T ↦ T`. Mathlib: `IsAlgClosed.equivOfTranscendenceBasis`.) -/
def AutExtends : Prop := ∀ ρ : GalQ, ∃ σ : ℂ ≃+* ℂ, ∀ a : Qbar, σ (ιC a) = ιC (ρ a)

/-- **GLUE FIX-ALG (field theory).** A complex number fixed by every automorphism of `ℂ` fixing
`ιC(ℚ̄)` pointwise is algebraic (in the image of `ιC`). (If `z` is transcendental over `ιC(ℚ̄)`,
extend `z ↦ z + 1` from `ιC(ℚ̄)(z)` to `ℂ`.) -/
def FixedAlgebraic : Prop :=
  ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ a : Qbar, σ (ιC a) = ιC a) → σ z = z) → ∃ a : Qbar, ιC a = z

/-- **TEXTBOOK DISC-NE-ZERO.** `Δ(ℂ/⟨1, τ⟩) = g₂³ − 27g₃² ≠ 0`: the roots `℘(1/2)`, `℘(τ/2)`,
`℘((1 + τ)/2)` of `4x³ − g₂x − g₃` are distinct (Silverman, *The arithmetic of elliptic curves*,
GTM 106, Prop. VI.3.6(b); Serre, *A course in arithmetic*, VII.3; UNVERIFIED numbers). -/
def DiscNeZero : Prop := ∀ τ : UpperHalfPlane, discL (pp τ) ≠ 0

/-! ### Lemmas -/

theorem pp_lattice_coe (τ : UpperHalfPlane) :
    (pp τ).lattice = Submodule.span ℤ {(1 : ℂ), (τ : ℂ)} := rfl

/-- `a/N ∉ ⟨1, τ⟩` for `0 < a < N`. -/
theorem div_nat_not_mem (τ : UpperHalfPlane) {a N : ℕ} (h1 : 0 < a) (h2 : a < N) :
    ((a : ℂ) / N) ∉ (pp τ).lattice := by
  rw [PeriodPair.mem_lattice]
  rintro ⟨p, q, hpq⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have him := congrArg Complex.im hpq
  simp only [pp, add_im, mul_im, intCast_re, intCast_im, one_im, one_re, mul_zero, zero_mul,
    add_zero, zero_add] at him
  have hq : (q : ℝ) = 0 := by
    have hdiv : ((a : ℂ) / N).im = 0 := by
      rw [show ((a : ℂ) / N) = ((a / N : ℝ) : ℂ) by push_cast; rfl, ofReal_im]
    rw [hdiv] at him
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · exact absurd h (ne_of_gt τ.im_pos)
  have hq' : q = 0 := by exact_mod_cast hq
  subst hq'
  simp only [pp, Int.cast_zero, zero_mul, add_zero, mul_one] at hpq
  have : (p : ℂ) * N = a := by rw [hpq]; field_simp
  have h3 : (p : ℤ) * N = a := by exact_mod_cast this
  have : (0 : ℤ) < p := by
    by_contra hp; rw [not_lt] at hp
    have : (p : ℤ) * N ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg hp (by positivity)
    omega
  have : (N : ℤ) ≤ p * N := by nlinarith
  omega

/-- `σ` commutes with `esymm`. -/
theorem map_esymm (σ : ℂ →+* ℂ) (s : Multiset ℂ) (i : ℕ) : σ (s.esymm i) = (s.map σ).esymm i := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, map_multiset_sum]
  congr 1
  apply Multiset.map_congr rfl
  intro t _
  simp [map_multiset_prod]

/-- Two multisets of the same cardinality with the same elementary symmetric functions are equal. -/
theorem multiset_eq_of_esymm (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ i, 1 ≤ i → i ≤ Multiset.card s → s.esymm i = t.esymm i) : s = t := by
  have hP : (s.map fun r => Polynomial.X + Polynomial.C r).prod =
      (t.map fun r => Polynomial.X + Polynomial.C r).prod := by
    rw [Multiset.prod_X_add_C_eq_sum_esymm, Multiset.prod_X_add_C_eq_sum_esymm, ← hc]
    refine Finset.sum_congr rfl fun i hi => ?_
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0; simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · rw [h i h0 (by simpa [Nat.lt_succ_iff] using hi)]
  have key : ∀ u : Multiset ℂ, (u.map fun r => Polynomial.X + Polynomial.C r).prod =
      ((u.map Neg.neg).map fun a => Polynomial.X - Polynomial.C a).prod := by
    intro u; rw [Multiset.map_map]; congr 1; apply Multiset.map_congr rfl; intro r _
    simp [sub_eq_add_neg]
  have hr := congrArg Polynomial.roots hP
  rw [key, key, Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

/-- The multiset of Weber values on `⟨1/N⟩ \ 0`. -/
def weberSet (N : ℕ) (τ : UpperHalfPlane) : Multiset ℂ :=
  (Multiset.range (N - 1)).map fun k : ℕ => weber (pp τ) (((k : ℂ) + 1) / N)

theorem modCoord_succ (N : ℕ) (τ : UpperHalfPlane) {i : ℕ} (hi : i ≠ 0) :
    modCoord N τ i = (weberSet N τ).esymm i := by
  simp [modCoord, hi, weberSet]

theorem modCoord_zero (N : ℕ) (τ : UpperHalfPlane) : modCoord N τ 0 = jL (pp τ) := by
  simp [modCoord]

theorem weberSet_card (N : ℕ) (τ : UpperHalfPlane) : Multiset.card (weberSet N τ) = N - 1 := by
  simp [weberSet]

/-- **Moduli transport.** If `σ` maps the moduli coordinates of `τ` to those of `τ'`, then `σ`
carries `(E_τ, ⟨1/N⟩)` to `(E_{τ'}, ⟨k/N⟩)` in the sense of `X0ModuliGalois`. -/
theorem moduli_transport (hD : DiscNeZero) (σ : ℂ →+* ℂ) {N : ℕ} (hN : 0 < N)
    {τ τ' : UpperHalfPlane} (h : ∀ i < N, σ (modCoord N τ i) = modCoord N τ' i) :
    ∃ μ, IsConjModel σ (pp τ) (pp τ') μ ∧
      (2 ≤ N → ∃ k : ℕ, 1 ≤ k ∧ k < N ∧
        σ ((pp τ).weierstrassP (1 / N)) = μ ^ 2 * (pp τ').weierstrassP (k / N) ∧
        σ ((pp τ).derivWeierstrassP (1 / N)) = μ ^ 3 * (pp τ').derivWeierstrassP (k / N)) := by
  have h0 := h 0 hN
  rw [modCoord_zero, modCoord_zero] at h0
  obtain ⟨μ, hμ⟩ := exists_conjModel_of_jL (hD τ) (hD τ') h0
  by_cases hN2 : 2 ≤ N
  swap
  · exact ⟨μ, hμ, fun h2 => absurd h2 hN2⟩
  have hW : (weberSet N τ).map σ = weberSet N τ' := by
    apply multiset_eq_of_esymm
    · simp [weberSet_card]
    · intro i hi1 hi2
      rw [Multiset.card_map, weberSet_card] at hi2
      rw [← map_esymm, ← modCoord_succ N τ (by omega), ← modCoord_succ N τ' (by omega)]
      exact h i (by omega)
  have hmem : σ (weber (pp τ) (1 / N)) ∈ weberSet N τ' := by
    rw [← hW]
    refine Multiset.mem_map_of_mem σ (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), ?_⟩)
    simp
  obtain ⟨k₀, hk₀, hk⟩ := Multiset.mem_map.1 hmem
  rw [Multiset.mem_range] at hk₀
  obtain ⟨μ', hμ', hp⟩ := hμ.adjust (hD τ') hk.symm
  have hz : ((1 : ℕ) : ℂ) / N ∉ (pp τ).lattice := div_nat_not_mem τ (by norm_num) (by omega)
  have hw : ((k₀ + 1 : ℕ) : ℂ) / N ∉ (pp τ').lattice := div_nat_not_mem τ' (by omega) (by omega)
  push_cast at hz hw
  rcases hμ'.deriv_sign hz hw hp with e | e
  · refine ⟨μ', hμ', fun _ => ⟨k₀ + 1, by omega, by omega, ?_, ?_⟩⟩
    · push_cast; exact hp
    · push_cast; exact e
  · refine ⟨μ', hμ', fun _ => ⟨N - (k₀ + 1), by omega, by omega, ?_, ?_⟩⟩
    · have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have e1 : (((N - (k₀ + 1) : ℕ) : ℂ) / N) = -(((k₀ : ℂ) + 1) / N - (pp τ').ω₁) := by
        rw [Nat.cast_sub (by omega)]; push_cast; simp only [pp]; field_simp; ring
      rw [hp, e1, PeriodPair.weierstrassP_neg,
        PeriodPair.weierstrassP_sub_coe (pp τ') _ ⟨_, (pp τ').ω₁_mem_lattice⟩]
    · have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      have e1 : (((N - (k₀ + 1) : ℕ) : ℂ) / N) = -(((k₀ : ℂ) + 1) / N - (pp τ').ω₁) := by
        rw [Nat.cast_sub (by omega)]; push_cast; simp only [pp]; field_simp; ring
      rw [e, e1, PeriodPair.derivWeierstrassP_neg,
        PeriodPair.derivWeierstrassP_sub_coe (pp τ') _ ⟨_, (pp τ').ω₁_mem_lattice⟩]
      ring

/-- **`X0RatStructure` from the canonical-model leaf `X0ModuliGalois`**, the field-theory glue
`AutExtends`, `FixedAlgebraic` and the textbook fact `DiscNeZero`. -/
theorem x0RatStructure_of (hL : X0ModuliGalois) (hA : AutExtends) (hF : FixedAlgebraic)
    (hD : DiscNeZero) : X0RatStructure := by
  intro N hN g hg τ τ' ρ x hx hx'
  -- algebraicity of `g(τ)`
  obtain ⟨b, hb⟩ := hF (g τ) fun σ₀ hσ₀ => by
    have h : ∀ i < N, (σ₀ : ℂ →+* ℂ) (modCoord N τ i) = modCoord N τ i := fun i hi => by
      rw [← hx i hi]; exact hσ₀ (x i)
    obtain ⟨μ, hμ, hk⟩ := moduli_transport hD (σ₀ : ℂ →+* ℂ) hN h
    exact hL N hN g hg σ₀ τ τ μ (fun i hi => ⟨x i, hx i hi⟩) hμ hk
  obtain ⟨σ, hσ⟩ := hA ρ
  have h : ∀ i < N, (σ : ℂ →+* ℂ) (modCoord N τ i) = modCoord N τ' i := fun i hi => by
    rw [← hx i hi, ← hx' i hi]; exact hσ (x i)
  obtain ⟨μ, hμ, hk⟩ := moduli_transport hD (σ : ℂ →+* ℂ) hN h
  refine ⟨b, ρ b, hb, ?_, rfl⟩
  rw [← hσ, hb]
  exact hL N hN g hg σ τ τ' μ (fun i hi => ⟨x i, hx i hi⟩) hμ hk

end T5Glue
