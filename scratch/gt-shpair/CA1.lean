import Mathlib

open IsLocalRing Polynomial
open scoped Pointwise

set_option linter.style.haveILetI false

namespace GTSHPair


section Count

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

attribute [local instance] Ideal.Quotient.field in
/-- `|D_P| = |I_P| · |Aut(κ(P)/κ(p))|` with no separability hypothesis. -/
theorem card_stabilizer_eq_card_inertia_mul_card_gal (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) := by
  have : Subgroup.index _ = _ := Nat.card_congr
    (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← this, ← ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

theorem card_stabilizer_eq_ram_mul_inertiaDeg [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have h2 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [Nat.card_prod, Nat.card_coe_set_eq, Algebra.IsInvariant.orbit_eq_primesOver R S G p P] at h2
  have h0 : (p.primesOver S).ncard ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact (Nat.card_pos (α := G)).ne' h1.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) (h2.trans h1.symm)


attribute [local instance] Ideal.Quotient.field in
/-- `|I_P| · |Aut(κ(P)/κ(p))| = e · f` with no separability hypothesis. -/
theorem card_inertia_mul_card_gal [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) =
      p.ramificationIdxIn S * p.inertiaDegIn S := by
  rw [← card_stabilizer_eq_card_inertia_mul_card_gal p P, card_stabilizer_eq_ram_mul_inertiaDeg p P]

end Count

/-- For a normal extension, the number of automorphisms is the separable degree. -/
theorem card_aut_eq_finSepDegree (F E : Type*) [Field F] [Field E] [Algebra F E] [Normal F E] :
    Nat.card (E ≃ₐ[F] E) = Field.finSepDegree F E :=
  (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

/-- **Separable-degree count.** `F ⊆ E ⊆ L`, `L/F` finite and normal, `L/E` normal. If
`e · [E : F] · |Aut(L/E)| = |Aut(L/F)|` then `e = 1` and `E/F` is separable. -/
theorem eq_one_and_isSeparable_of_card {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E]
    [Algebra E L] [Algebra F L] [IsScalarTower F E L] [FiniteDimensional F L] [Normal F L]
    [Normal E L] (e : ℕ)
    (h : e * Module.finrank F E * Nat.card (L ≃ₐ[E] L) = Nat.card (L ≃ₐ[F] L)) :
    e = 1 ∧ Algebra.IsSeparable F E := by
  haveI : FiniteDimensional F E := FiniteDimensional.left F E L
  haveI : FiniteDimensional E L := FiniteDimensional.right F E L
  rw [card_aut_eq_finSepDegree, card_aut_eq_finSepDegree,
    ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F E L] at h
  have hs2 : 0 < Field.finSepDegree E L := Nat.pos_of_ne_zero (NeZero.ne _)
  have h' : e * Module.finrank F E = Field.finSepDegree F E := Nat.eq_of_mul_eq_mul_right hs2 h
  have hle := Field.finSepDegree_le_finrank F E
  have hpos : 0 < Module.finrank F E := Module.finrank_pos
  have hspos : 0 < Field.finSepDegree F E := Nat.pos_of_ne_zero (NeZero.ne _)
  have he : e = 1 := by
    rcases Nat.lt_or_ge e 1 with he | he
    · interval_cases e; omega
    · by_contra hne
      have : 2 * Module.finrank F E ≤ e * Module.finrank F E := Nat.mul_le_mul_right _ (by omega)
      omega
  refine ⟨he, ?_⟩
  rw [he, one_mul] at h'
  exact (Field.finSepDegree_eq_finrank_iff F E).mp h'.symm

attribute [local instance] Ideal.Quotient.field in
/-- **The inertia ring is unramified with separable residue extension** (no separability
hypothesis on residue fields). `A ⊆ R ⊆ S`, `S/A` Galois with group `G`, `S/R` Galois with group the
inertia group `H` of a maximal `P ⊆ S` over `p`. Then `𝔮 = P ∩ R` has ramification index `1` over
`p` and `R/𝔮` is separable over `A/p`. -/
theorem inertia_unram {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [IsDomain A]
    [IsDomain R] [IsDomain S] [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G A S]
    [Module.Finite A S] [Module.Finite R S] [Module.Flat A S] [Module.Flat R S]
    (p : Ideal A) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [IsGaloisGroup (P.inertia G) R S] [(P.under R).IsMaximal] [(P.under R).LiesOver p] :
    (P.under R).ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ p) (R ⧸ P.under R) := by
  set 𝔮 := P.under R
  set H := P.inertia G
  haveI : IsScalarTower (A ⧸ p) (R ⧸ 𝔮) (S ⧸ P) := IsScalarTower.of_algebraMap_eq (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply])
  have hc1 := card_inertia_mul_card_gal (G := G) p P
  have hc3 := card_inertia_mul_card_gal (G := H) 𝔮 P
  have e4 : Nat.card (P.inertia H) = Nat.card H :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun h => fun s => h.2 s))
  rw [e4] at hc3
  have hHpos : 0 < Nat.card H := Nat.card_pos
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G, Ideal.inertiaDegIn_eq_inertiaDeg p P G,
    Ideal.ramificationIdx_tower (R := A) 𝔮 P, Ideal.inertiaDeg_tower (R := A) 𝔮 P] at hc1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 P H, Ideal.inertiaDegIn_eq_inertiaDeg 𝔮 P H]
    at hc3
  haveI : Normal (A ⧸ p) (S ⧸ P) := Ideal.Quotient.normal G p P
  haveI : Normal (R ⧸ 𝔮) (S ⧸ P) := Ideal.Quotient.normal H 𝔮 P
  haveI : FiniteDimensional (A ⧸ p) (S ⧸ P) := inferInstance
  refine eq_one_and_isSeparable_of_card (L := S ⧸ P) _ ?_
  rw [← Ideal.inertiaDeg_eq_of_isMaximal p 𝔮]
  have h5 : Nat.card H * Nat.card ((S ⧸ P) ≃ₐ[A ⧸ p] (S ⧸ P)) =
      Nat.card H * (𝔮.ramificationIdx A * 𝔮.inertiaDeg A *
        Nat.card ((S ⧸ P) ≃ₐ[R ⧸ 𝔮] (S ⧸ P))) := by
    rw [hc1]
    calc _ = 𝔮.ramificationIdx A * 𝔮.inertiaDeg A * (P.ramificationIdx R * P.inertiaDeg R) := by ring
      _ = _ := by rw [← hc3]; ring
  exact (Nat.eq_of_mul_eq_mul_left hHpos h5).symm



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



/-! ## A. Valuation rings over a Dedekind domain are localizations -/

section Loc

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
  [IsFractionRing R F]

/-- `R → W` for a valuation subring `W` of `Frac R` containing `R`. -/
def toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : R →+* W :=
  (algebraMap R F).codRestrict W.toSubring hW

/-- The center `R ∩ 𝔪_W`. -/
def ctr (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) : Ideal R :=
  (maximalIdeal W).comap (toW W hW)

theorem mem_ctr_iff (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) (r : R) :
    r ∈ ctr W hW ↔ algebraMap R F r ∈ W.nonunits := by
  change toW W hW r ∈ maximalIdeal W ↔ _
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.mem_nonunits_iff]
  rfl

instance ctr_isPrime (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) :
    (ctr W hW).IsPrime := Ideal.comap_isPrime _ _

theorem isUnit_toW (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {s : R}
    (hs : s ∉ ctr W hW) : IsUnit (toW W hW s) := by
  by_contra h
  exact hs ((mem_maximalIdeal _).mpr h)

theorem mem_of_mul_eq' (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W) {x : F}
    {a s : R} (hs : s ∉ ctr W hW) (h : x * algebraMap R F s = algebraMap R F a) : x ∈ W := by
  obtain ⟨u, hu⟩ := isUnit_toW W hW hs
  have h1 : ((u : W) : F) = algebraMap R F s := by rw [hu]; rfl
  have h2 : (((u⁻¹ : Wˣ) : W) : F) * ((u : W) : F) = 1 :=
    congrArg (fun z : W => (z : F)) (Units.inv_mul u)
  have : x = algebraMap R F a * (((u⁻¹ : Wˣ) : W) : F) := by
    rw [← h, h1.symm, _root_.mul_assoc, mul_comm ((u : W) : F), h2, _root_.mul_one]
  rw [this]
  exact mul_mem (hW a) (u⁻¹ : Wˣ).1.2

/-- **A valuation subring `W ⊇ R` of `Frac R` with nonzero center is the localization of `R` at
its center**: every `x ∈ W` is `a/s` with `a, s ∈ R`, `s ∉ 𝔭`. (Generalizes reduct-glue's
`mem_iff_exists` from `𝓞_L` to any Dedekind domain; same proof.) -/
theorem exists_of_mem (W : ValuationSubring F) (hW : ∀ r : R, algebraMap R F r ∈ W)
    (h0 : ctr W hW ≠ ⊥) {x : F} (hx : x ∈ W) :
    ∃ a s : R, s ∉ ctr W hW ∧ x * algebraMap R F s = algebraMap R F a := by
  let 𝔭 := ctr W hW
  let B := Localization.AtPrime 𝔭
  haveI : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R h0 B
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : (algebraMap R F b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr (nonZeroDivisors.ne_zero hb)
  obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R B a) (algebraMap R B b)
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl c
  have hinj := IsLocalization.injective B 𝔭.primeCompl_le_nonZeroDivisors
  have hspec := IsLocalization.mk'_spec B r s
  have hs : (s : R) ∉ ctr W hW := s.2
  rcases hc with h | h
  · have h' : a * r = b * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    have hL : (algebraMap R F a) * (algebraMap R F r) =
        (algebraMap R F b) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    by_cases hr : r ∈ 𝔭
    · exfalso
      apply hs
      have hX : (⟨_, hx⟩ : W) * toW W hW r = toW W hW s := by
        apply Subtype.ext
        change (algebraMap R F a / algebraMap R F b) * (algebraMap R F r) = algebraMap R F s
        rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
      change toW W hW s ∈ maximalIdeal W
      rw [← hX]
      exact Ideal.mul_mem_left _ _ hr
    · refine ⟨s, r, hr, ?_⟩
      rw [div_mul_eq_mul_div, hL, mul_div_cancel_left₀ _ hb0]
  · have h' : b * r = a * s := by
      apply hinj
      rw [map_mul, map_mul, ← h, ← hspec]
      ring
    refine ⟨r, s, hs, ?_⟩
    have hL : (algebraMap R F b) * (algebraMap R F r) =
        (algebraMap R F a) * (algebraMap R F s) := by
      rw [← map_mul, ← map_mul, h']
    rw [div_mul_eq_mul_div, ← hL, mul_div_cancel_left₀ _ hb0]

end Loc

/-! ## B. The inertia field of a finite Galois extension is unramified -/

section Key

theorem nonunits_comap {E M : Type*} [Field E] [Field M] (f : E →+* M) (W : ValuationSubring M)
    (x : E) : x ∈ (W.comap f).nonunits ↔ f x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  simp only [ValuationSubring.mem_comap, map_inv₀, map_eq_zero]

theorem div_mem_nonunits {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W.nonunits) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at hn hd' ⊢
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

theorem div_mem {M : Type*} [Field M] (W : ValuationSubring M) {n d : M}
    (hn : n ∈ W) (hd : d ∈ W) (hd' : d ∉ W.nonunits) : n / d ∈ W := by
  rw [← W.valuation_le_one_iff] at hn ⊢
  rw [ValuationSubring.mem_nonunits_iff] at hd'
  have h1 : W.valuation d = 1 :=
    le_antisymm ((W.valuation_le_one_iff d).mpr hd) (not_lt.mp hd')
  rw [map_div₀, h1, div_one]
  exact hn

/-- An element of `M` integral over a subring contained in `W` lies in `W`. -/
theorem mem_of_isIntegral {A M : Type*} [CommRing A] [Field M] [Algebra A M]
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W) {x : M}
    (hx : IsIntegral A x) : x ∈ W := by
  letI : Algebra A W := ((algebraMap A M).codRestrict W.toSubring hAW).toAlgebra
  haveI : IsScalarTower A W M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h2 : IsIntegral W x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2


/-- **Uniformizer from `𝔮 · J ⊆ ϖR` with `J ⊄ 𝔮`.** `R` Dedekind, `W` a valuation subring of
`F = Frac R` over `R` with center `𝔮 ≠ 0`, `ϖ ∈ 𝔮` and `j ∉ 𝔮` with `𝔮 · j ⊆ ϖ R`. Then every nonzero
`y ∈ F` with `y = a/s`, `s ∉ 𝔮`, is `ϖⁿ` times a unit of `W`. -/
theorem unit_mul_pow_of_div {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] (W : ValuationSubring F)
    (hW : ∀ r : R, algebraMap R F r ∈ W) (ϖ j : R) (hj : j ∉ ctr W hW)
    (hdiv : ∀ n ∈ ctr W hW, ∃ r : R, n * j = ϖ * r) (hϖ : ϖ ∈ ctr W hW) (hϖ0 : ϖ ≠ 0) :
    ∀ (m : ℕ) (y : F) (a s : R), y ≠ 0 → s ∉ ctr W hW →
      y * algebraMap R F s = algebraMap R F a → a ∉ (ctr W hW) ^ (m + 1) →
      ∃ n : ℕ, y / algebraMap R F ϖ ^ n ∈ W ∧ (y / algebraMap R F ϖ ^ n)⁻¹ ∈ W := by
  set 𝔮 := ctr W hW
  have hϖF : algebraMap R F ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hϖ0
  have unit_case : ∀ (y : F) (a s : R), y ≠ 0 → s ∉ 𝔮 →
      y * algebraMap R F s = algebraMap R F a → a ∉ 𝔮 →
      ∃ n : ℕ, y / algebraMap R F ϖ ^ n ∈ W ∧ (y / algebraMap R F ϖ ^ n)⁻¹ ∈ W := by
    intro y a s hy hs hys ha
    refine ⟨0, ?_, ?_⟩
    · rw [pow_zero, div_one]; exact mem_of_mul_eq' W hW hs hys
    · rw [pow_zero, div_one]
      refine mem_of_mul_eq' W hW (a := s) ha ?_
      rw [← hys]; field_simp
  intro m
  induction m with
  | zero =>
    intro y a s hy hs hys ha
    exact unit_case y a s hy hs hys (by rwa [zero_add, pow_one] at ha)
  | succ m ih =>
    intro y a s hy hs hys ha
    by_cases ha𝔮 : a ∉ 𝔮
    · exact unit_case y a s hy hs hys ha𝔮
    push Not at ha𝔮
    obtain ⟨r, hr⟩ := hdiv a ha𝔮
    have hsj : s * j ∉ 𝔮 := fun h =>
      ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hs hj)
    have hr' : r ∉ 𝔮 ^ (m + 1) := by
      intro hrm
      have h1 : j * a ∈ 𝔮 ^ (m + 1 + 1) := by
        rw [mul_comm, hr, pow_succ']
        exact Ideal.mul_mem_mul hϖ hrm
      rcases Ideal.IsPrime.mul_mem_pow 𝔮 h1 with h | h
      · exact hj h
      · exact ha h
    have hy' : y / algebraMap R F ϖ ≠ 0 := div_ne_zero hy hϖF
    have hys' : y / algebraMap R F ϖ * algebraMap R F (s * j) = algebraMap R F r := by
      have h2 : algebraMap R F a * algebraMap R F j = algebraMap R F ϖ * algebraMap R F r := by
        rw [← map_mul, ← map_mul, hr]
      rw [← hys] at h2
      rw [map_mul]
      field_simp
      linear_combination h2
    obtain ⟨n, h1, h2⟩ := ih (y / algebraMap R F ϖ) r (s * j) hy' hsj hys' hr'
    refine ⟨n + 1, ?_, ?_⟩
    · rwa [pow_succ', ← div_div]
    · rwa [pow_succ', ← div_div]

variable {K M : Type*} [Field K] [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K]
  [IsFractionRing A K] [Algebra A M] [IsScalarTower A K M]

instance instSMulCommClassGal : SMulCommClass (M ≃ₐ[K] M) A M where
  smul_comm σ a x := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A K M, AlgEquiv.commutes]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **Key lemma (finite level, any characteristic, any residue field).** `M/K` finite Galois, `A ⊆ K`
a DVR, `W` a valuation ring of `M` over `A`. If `x ∈ W` is fixed by every `σ ∈ Gal(M/K)` acting
trivially modulo `𝔪_W`, then (a) if `x ≠ 0`, `x = ϖⁿ · (unit of W)` for a uniformizer `ϖ` of `A`;
(b) `x` is a root modulo `𝔪_W` of a polynomial over `A` with separable reduction. -/
theorem key_finite
    (W : ValuationSubring M) (hAW : ∀ a : A, algebraMap A M a ∈ W)
    (hctr : ∀ a : A, algebraMap A M a ∈ W.nonunits ↔ a ∈ maximalIdeal A)
    (ϖ : A) (hϖ : Irreducible ϖ) (x : M)
    (hfix : ∀ σ : M ≃ₐ[K] M, (∀ y ∈ W, σ y - y ∈ W.nonunits) → σ x = x)
    (hxW : x ∈ W) :
    (x ≠ 0 → ∃ n : ℕ, x / algebraMap A M ϖ ^ n ∈ W ∧ (x / algebraMap A M ϖ ^ n)⁻¹ ∈ W) ∧
    ∃ f : A[X], (f.map (residue A)).Separable ∧ (f.map (algebraMap A M)).eval x ∈ W.nonunits := by
  classical
  -- the ring of integers `S` of `M` over `A`
  let S := integralClosure A M
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain A K M
  haveI : Module.Finite A S := IsIntegralClosure.finite A K M S
  haveI : IsFractionRing S M := IsIntegralClosure.isFractionRing_of_finite_extension A K M S
  haveI : IsGaloisGroup (M ≃ₐ[K] M) A S := IsGaloisGroup.of_isFractionRing _ A S K M
  have hSW : ∀ s : S, algebraMap S M s ∈ W := fun s =>
    mem_of_isIntegral W hAW s.2
  let p := maximalIdeal A
  let P : Ideal S := ctr W hSW
  have hP : ∀ s : S, s ∈ P ↔ (s : M) ∈ W.nonunits := fun s => mem_ctr_iff W hSW s
  haveI : P.LiesOver p := by
    constructor
    ext a
    rw [Ideal.under_def, Ideal.mem_comap, hP]
    exact (hctr a).symm
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖp : ϖ ∈ p := (mem_maximalIdeal _).mpr hϖ.not_isUnit
  have hAinj : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hP0 : P ≠ ⊥ := by
    intro h
    have : algebraMap A S ϖ ∈ P := by rw [hP]; exact (hctr ϖ).mpr hϖp
    rw [h, Ideal.mem_bot] at this
    apply hϖ0
    apply hAinj
    rw [map_zero]
    exact congrArg (fun z : S => (z : M)) this
  haveI : FaithfulSMul A S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hAinj (congrArg (fun z : S => (z : M)) h)
  haveI : Module.IsTorsionFree A S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  -- the inertia field `E` and its ring of integers `R`
  let H := P.inertia (M ≃ₐ[K] M)
  let E : IntermediateField K M := FixedPoints.intermediateField H
  haveI : IsScalarTower A E M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let R := integralClosure A E
  haveI : IsDedekindDomain R := integralClosure.isDedekindDomain A K E
  haveI : Module.Finite A R := IsIntegralClosure.finite A K E R
  haveI : IsFractionRing R E := IsIntegralClosure.isFractionRing_of_finite_extension A K E R
  have hRS : ∀ r : R, IsIntegral A (algebraMap E M (r : E)) := fun r =>
    r.2.map (IsScalarTower.toAlgHom A E M)
  let φ : R →+* S := ((algebraMap E M).comp (algebraMap R E)).codRestrict S (fun r => hRS r)
  letI : Algebra R S := φ.toAlgebra
  haveI : IsScalarTower A R S := IsScalarTower.of_algebraMap_eq (fun a => by
    apply Subtype.ext
    change algebraMap A M a = algebraMap E M (algebraMap A E a)
    rw [← IsScalarTower.algebraMap_apply])
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.tower_top A
  haveI : IsGaloisGroup H E M := IsGaloisGroup.subgroup (M ≃ₐ[K] M) K M H
  haveI : IsGaloisGroup H R S := IsGaloisGroup.of_isFractionRing H R S E M
  haveI : Module.Finite R S := Module.Finite.of_restrictScalars_finite A R S
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    apply Subtype.ext
    apply (algebraMap E M).injective
    exact congrArg (fun z : S => (z : M)) h
  haveI : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_faithfulSMul]; infer_instance
  let 𝔮 : Ideal R := P.under R
  haveI : 𝔮.LiesOver p := Ideal.LiesOver.tower_bot P 𝔮 p
  have hRinj0 : Function.Injective (algebraMap A R) := by
    intro a b h
    exact hAinj (congrArg (fun r : R => algebraMap E M (r : E)) h)
  haveI : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  have hϖ𝔮0 : algebraMap A R ϖ ∈ 𝔮 := by
    change algebraMap R S (algebraMap A R ϖ) ∈ P
    rw [← IsScalarTower.algebraMap_apply, hP]
    exact (hctr ϖ).mpr hϖp
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hϖ𝔮0
    exact hϖ0 (hRinj0 (by rw [hϖ𝔮0, map_zero]))
  haveI : 𝔮.IsMaximal := Ideal.IsPrime.isMaximal inferInstance h𝔮0
  obtain ⟨he𝔮, hsep⟩ := inertia_unram (M ≃ₐ[K] M) p P (R := R)
  -- `p𝓞_E = 𝔮 · J` with `J ⊄ 𝔮`
  have hpspan : p = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hRinj : Function.Injective (algebraMap A R) := by
    intro a b h
    exact hAinj (congrArg (fun r : R => algebraMap E M (r : E)) h)
  have hpR0 : p.map (algebraMap A R) ≠ ⊥ := by
    rw [hpspan, Ideal.map_span, Set.image_singleton, Ne, Ideal.span_singleton_eq_bot]
    exact fun h => hϖ0 (hRinj (by rw [h, map_zero]))
  have hmult := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity p 𝔮 hpR0
  rw [he𝔮] at hmult
  have h𝔮top : 𝔮 ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  have hfin : FiniteMultiplicity 𝔮 (p.map (algebraMap A R)) :=
    FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff]) hpR0
  obtain ⟨J, hJ⟩ : 𝔮 ∣ p.map (algebraMap A R) := by
    have := pow_multiplicity_dvd 𝔮 (p.map (algebraMap A R))
    rwa [← hmult, pow_one] at this
  have hJ𝔮 : ¬ J ≤ 𝔮 := by
    intro hle
    apply hfin.not_pow_dvd_of_multiplicity_lt (m := 2) (by rw [← hmult]; norm_num)
    rw [hJ, pow_two]
    exact mul_dvd_mul_left 𝔮 (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨j, hjJ, hj𝔮⟩ := IsConcreteLE.not_le_iff_exists.mp hJ𝔮
  let ϖR := algebraMap A R ϖ
  have hϖR : p.map (algebraMap A R) = Ideal.span {ϖR} := by
    rw [hpspan, Ideal.map_span, Set.image_singleton]
  have hdivide : ∀ n ∈ 𝔮, ∃ r : R, n * j = ϖR * r := by
    intro n hn
    have : n * j ∈ p.map (algebraMap A R) := by
      rw [hJ]; exact Ideal.mul_mem_mul hn hjJ
    rw [hϖR, Ideal.mem_span_singleton'] at this
    obtain ⟨r, hr⟩ := this
    exact ⟨r, by rw [← hr, mul_comm]⟩
  have hϖ𝔮 : ϖR ∈ 𝔮 := by
    have : ϖR ∈ p.map (algebraMap A R) := Ideal.mem_map_of_mem _ hϖp
    rw [hJ] at this
    exact (Ideal.mul_le_right (I := J) (J := 𝔮)) (by rwa [mul_comm] at this)
  -- every element of the inertia group acts trivially modulo `𝔪_W` on all of `W`
  have hcond : ∀ σ ∈ H, ∀ y ∈ W, σ y - y ∈ W.nonunits := by
    intro σ hσ y hy
    obtain ⟨a, s, hs, hys⟩ := exists_of_mem W hSW hP0 hy
    have ha : σ (a : M) - a ∈ W.nonunits := by
      have := (hP _).mp (hσ a)
      have e1 : ((σ • a : S) : M) = σ (a : M) := rfl
      rwa [Subalgebra.coe_sub, e1] at this
    have hs' : σ (s : M) - s ∈ W.nonunits := by
      have := (hP _).mp (hσ s)
      have e1 : ((σ • s : S) : M) = σ (s : M) := rfl
      rwa [Subalgebra.coe_sub, e1] at this
    rw [hP] at hs
    have hsW : (s : M) ∈ W := hSW s
    rw [ValuationSubring.mem_nonunits_iff] at ha hs' hs ⊢
    have vs : W.valuation (s : M) = 1 :=
      le_antisymm ((W.valuation_le_one_iff _).mpr hsW) (not_lt.mp hs)
    have vσs : W.valuation (σ (s : M)) = 1 := by
      have : σ (s : M) = (s : M) + (σ (s : M) - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [vs]; exact hs'), vs]
    have hs0 : (s : M) ≠ 0 := fun h => by rw [h, map_zero] at vs; exact zero_ne_one vs
    have hσs0 : σ (s : M) ≠ 0 := fun h => by rw [h, map_zero] at vσs; exact zero_ne_one vσs
    have hy' : y = (a : M) / s := by rw [eq_div_iff hs0]; exact hys
    have key : σ y - y = ((σ (a : M) - a) * s - a * (σ (s : M) - s)) / (σ (s : M) * s) := by
      rw [hy', map_div₀]
      field_simp
      ring
    rw [key, map_div₀, map_mul, vσs, vs, _root_.mul_one, div_one]
    have haW : W.valuation (a : M) ≤ 1 := (W.valuation_le_one_iff _).mpr (hSW a)
    rw [sub_eq_add_neg]
    apply Valuation.map_add_lt _
    · rw [map_mul, vs, _root_.mul_one]; exact ha
    · rw [Valuation.map_neg, map_mul]
      calc W.valuation (a : M) * W.valuation (σ (s : M) - s)
          ≤ 1 * W.valuation (σ (s : M) - s) := by gcongr
        _ < 1 := by rw [_root_.one_mul]; exact hs'
  have hxE : x ∈ E := by
    intro h
    exact hfix h (hcond h h.2)
  -- the valuation ring of `E`
  let WE := W.comap (algebraMap E M)
  have hRW : ∀ r : R, algebraMap R E r ∈ WE := fun r => hSW (φ r)
  have hctrE : ctr WE hRW = 𝔮 := by
    ext r
    rw [mem_ctr_iff, nonunits_comap]
    exact (hP (φ r)).symm
  have hϖR0 : algebraMap A R ϖ ≠ 0 := fun h => hϖ0 (hRinj (by rw [h, map_zero]))
  have hctrE0 : ctr WE hRW ≠ ⊥ := by
    rw [hctrE]
    intro h
    rw [h] at hϖ𝔮
    exact hϖR0 hϖ𝔮
  obtain ⟨a, s, hs, hxs⟩ := exists_of_mem WE hRW hctrE0 (x := ⟨x, hxE⟩) hxW
  have hφ𝔮 : ∀ r : R, r ∈ 𝔮 ↔ (φ r : M) ∈ W.nonunits := fun r => hP (φ r)
  refine ⟨fun hx0 => ?_, ?_⟩
  swap
  · haveI : 𝔮.LiesOver p := inferInstance
    obtain ⟨f, hf, hfx⟩ := exists_sep_poly ((algebraMap E M).comp (algebraMap R E)) p 𝔮 W
      hφ𝔮 (fun r => hSW (φ r)) x a s (by rwa [← hctrE]) (by
        have := congrArg (algebraMap E M) hxs
        rwa [map_mul] at this)
    refine ⟨f, hf, ?_⟩
    have e : ((algebraMap E M).comp (algebraMap R E)).comp (algebraMap A R) = algebraMap A M := by
      ext c
      change algebraMap E M (algebraMap R E (algebraMap A R c)) = algebraMap A M c
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    rwa [e] at hfx
  have hxE0 : (⟨x, hxE⟩ : E) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at hxs
    rcases mul_eq_zero.mp hxs with h' | h'
    · exact hxE0 h'
    · apply hs
      rw [(map_eq_zero_iff _ (IsFractionRing.injective R E)).mp h']
      exact Ideal.zero_mem _
  have hfa : FiniteMultiplicity 𝔮 (Ideal.span {a}) :=
    FiniteMultiplicity.of_not_isUnit (by rwa [Ideal.isUnit_iff])
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha0)
  have ham : a ∉ 𝔮 ^ (multiplicity 𝔮 (Ideal.span {a}) + 1) := by
    intro h
    apply hfa.not_pow_dvd_of_multiplicity_lt (lt_add_one _)
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  rw [← hctrE] at hdivide hϖ𝔮 hj𝔮 ham
  obtain ⟨n, h1, h2⟩ := unit_mul_pow_of_div WE hRW (algebraMap A R ϖ) j hj𝔮 hdivide hϖ𝔮 hϖR0
    _ _ a s hxE0 hs hxs ham
  have e : ((algebraMap A E ϖ : E) : M) = algebraMap A M ϖ := rfl
  refine ⟨n, ?_, ?_⟩
  · have := h1; simpa [WE, ValuationSubring.mem_comap, e] using this
  · have := h2; simpa [WE, ValuationSubring.mem_comap, e] using this

end Key

end GTSHPair
