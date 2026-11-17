
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §5. The CM part `CMModuli`

### Adelic objects (Mathlib's finite adeles and ideles of `K = ℚ(√−m)`) -/

/-- The finite adeles `𝔸_{K,f}` of `K = ℚ(√−m)`. -/
abbrev AfK (m : ℕ) [NeZero m] := FiniteAdeleRing (𝓞 (QNeg m)) (QNeg m)

/-- `𝔞̂ ⊂ 𝔸_{K,f}`: the closure of (the image of) a subset `𝔞 ⊂ K`; for a lattice `𝔞`,
`𝔞̂ = 𝔞 ⊗ ℤ̂`. -/
def latHat (m : ℕ) [NeZero m] (𝔞 : Set (QNeg m)) : Set (AfK m) :=
  closure (algebraMap (QNeg m) (AfK m) '' 𝔞)

/-- The finite component `s_f ∈ 𝔸_{K,f}` of an idele `s` of `K`. -/
def finPart {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : AfK m :=
  (s : AdeleRing (𝓞 (QNeg m)) (QNeg m)).2

/-- The idele class of an idele. -/
def icl {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    IdeleClassGroup (𝓞 (QNeg m)) (QNeg m) :=
  QuotientGroup.mk s

/-- `s⁻¹𝔞 = K ∩ s_f⁻¹𝔞̂ = {x ∈ K : s_f x ∈ 𝔞̂}` (Shimura 1971, §5.2). -/
def sInvLat (m : ℕ) [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (𝔞 : Set (QNeg m)) :
    Set (QNeg m) :=
  {x | finPart s * algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞}

/-- **`σ = [s, K]` on `K^ab`** (through the embedding `ιC ∘ e : Kˢ → ℂ`): for every finite abelian
extension `F/K` inside `Kˢ`, `σ` acts on `ιC(e(F))` as Tau Ceti's global Artin symbol of the idele
class of `s` (which sends a uniformizer at `𝔭` to the arithmetic Frobenius,
`rayClassQuotient_ofAdicCompletion_of_isUniformizer`). -/
def ArtinCond (m : ℕ) [NeZero m] (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar) (σ : ℂ ≃+* ℂ)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : Prop :=
  ∀ (F : IntermediateField (QNeg m) (SeparableClosure (QNeg m))) [FiniteDimensional (QNeg m) F]
    [NumberField F] [IsAbelianGalois (QNeg m) F] (x : F),
    σ (ιC (e x)) = ιC (e (ideleClassArtinMap (QNeg m) F (icl s) x))

/-- **LEAF SHIMURA-5.4 (the main theorem of complex multiplication, with torsion; printed form in
Weierstrass coordinates).** Let `K = ℚ(√−m) ⊂ ℂ` (through `κ`, `√−m ↦ i√m`), `e : Kˢ → ℚ̄`
normalized (`ιC ∘ e = κ` on `K`), `σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` with `σ = [s, K]` on `K^ab`
(`ArtinCond`). Let `𝔞 ⊂ K` be a lattice, `P` a period pair with lattice `κ(𝔞)` and `P'` one with
lattice `κ(s⁻¹𝔞)`. Then there is `μ ∈ ℂˣ` such that `(x, y) ↦ (μ⁻²x, μ⁻³y)` is an isomorphism
`E_P^σ ≅ E_{P'}` (`σ(g₂(P)) = μ⁴g₂(P')`, `σ(g₃(P)) = μ⁶g₃(P')`) and, for `u ∈ K \ 𝔞` and any
`v ∈ K` representing `s⁻¹u ∈ K/s⁻¹𝔞` (`s_f v − u ∈ 𝔞̂`),
`σ(℘_P(u)) = μ²℘_{P'}(v)` and `σ(℘'_P(u)) = μ³℘'_{P'}(v)`.

Source: Shimura 1971, *Introduction to the arithmetic theory of automorphic functions*, Thm. 5.4:
for an analytic isomorphism `ξ : ℂ/𝔞 → E(ℂ)` there is a unique `ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` with
`ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`; Lang, *Elliptic functions*, Ch. 10, Thm. 3; Silverman,
*Advanced topics*, GTM 151, Thm. II.8.2 (for `𝒪_K`) (theorem numbers UNVERIFIED, from memory).
Here `E = E_P : y² = 4x³ − g₂(P)x − g₃(P)` with `ξ = (℘_P, ℘'_P)`; every analytic isomorphism
`ℂ/s⁻¹𝔞 → E^σ(ℂ)` is `z ↦ (μ²℘_{P'}(z), μ³℘'_{P'}(z))` for some `μ ∈ ℂˣ` (`ξ'(0) = ξ(0)^σ = O`,
a holomorphic map of complex tori fixing `0` is `z ↦ αz`, and isomorphisms of short Weierstrass
models are `(x, y) ↦ (μ²x, μ³y)`), so this is the printed statement, restricted to `u ∉ 𝔞` (then
`v ∉ s⁻¹𝔞`, since `K ∩ 𝔞̂ = 𝔞`, so `℘_{P'}(v)` is a value, not the junk value at a pole); the
conclusion holds for every representative `v` because two of them differ by an element of `s⁻¹𝔞`. Normalization:
Shimura's `[s, K]` sends a uniformizer at `𝔭` to the arithmetic Frobenius, as Tau Ceti's Artin map
does; then `E^{Frob_𝔭} ≅ ℂ/𝔭⁻¹𝔞`, consistent with `j(𝔞)^{Art 𝔭} = j(𝔭⁻¹𝔞)` used by the kernel's
`MainTheoremCMj`. -/
def ShimuraMainCM : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)) (P P' : PeriodPair),
    (P.lattice : Set ℂ) = kappa m '' 𝔞 → (P'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞 →
    ∃ μ : ℂ, IsConjModel (σ : ℂ →+* ℂ) P P' μ ∧
      ∀ u v : QNeg m, kappa m u ∉ P.lattice →
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        σ (P.weierstrassP (kappa m u)) = μ ^ 2 * P'.weierstrassP (kappa m v) ∧
        σ (P.derivWeierstrassP (kappa m u)) = μ ^ 3 * P'.derivWeierstrassP (kappa m v)

/-- **GLUE ARTIN-LIFT (class field theory).** Every `σ ∈ Aut(ℂ)` fixing `κ(K)` is `[s, K]` on
`K^ab` for some idele `s`: the global Artin map `C_K → Gal(K^ab/K)` is surjective (its image is
dense and `C_K` modulo its connected component is compact; e.g. Neukirch, *Algebraic number
theory*, Ch. VI §5; Cassels–Fröhlich, Ch. VII §5; UNVERIFIED numbers), applied through
`ιC ∘ e` (which maps `Kˢ` onto the algebraic numbers, stable under `σ`). -/
def ArtinLift : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ σ : ℂ ≃+* ℂ, (∀ k : QNeg m, σ (kappa m k) = kappa m k) →
    ∃ s : IdeleGroup (𝓞 (QNeg m)) (QNeg m), ArtinCond m e σ s

/-- **LAT-HAT (adelic topology; proved in §5c, `latHatInter`).** The lattice `𝔞 = κ⁻¹⟨1, τ_Q⟩ ⊂ K`
of a Heegner form is the set of elements of `K` lying in its closure `𝔞̂ ⊂ 𝔸_{K,f}`: `K ∩ 𝔞̂ = 𝔞`. -/
def LatHatInter : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → ∀ (f : ℕ) [NeZero f] (D : ℤ), D = discOf m f →
    ∀ (N : ℕ) (Q : HeegnerForm N D),
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m (kappa m ⁻¹' (Q.lat : Set ℂ))} =
      kappa m ⁻¹' (Q.lat : Set ℂ)

/-- **GLUE IDELE-LATTICE (the lattice computation, shimura-modfn §1).** Let `O = ℤ + f𝓞_K`, `J` an
ideal of `𝓞_K` prime to `f`, `s` an idele whose ring class is the class of `J ∩ O`
(`ringClassIdeleQuotient`), and `Q, Q'` Heegner forms of level `N` and discriminant `D = disc O`
with `κ(J ∩ O)·(⟨1, τ_{Q'}⟩, ⟨1/N, τ_{Q'}⟩) = c·(⟨1, τ_Q⟩, ⟨1/N, τ_Q⟩)`; write
`𝔞 = κ⁻¹⟨1, τ_Q⟩`. Then for some `c' ≠ 0`: `κ(s⁻¹𝔞) = c'·⟨1, τ_{Q'}⟩`, and the map `u ↦ s⁻¹u`
sends the nonzero points `(k + 1)/N` (`0 ≤ k < N − 1`) of `⟨1/N, τ_Q⟩/⟨1, τ_Q⟩` bijectively onto
the nonzero points `c'·(π(k) + 1)/N` of `c'·⟨1/N, τ_{Q'}⟩/c'·⟨1, τ_{Q'}⟩` (`π` a permutation).

Content: `s = k·s_J·w` with `k ∈ Kˣ`, `s_J` an idele of `J` and `w ∈ Ô^× × ℂˣ` (the kernel of the
ring-class quotient, `mem_ker_ringClassIdeleQuotient_iff`); `⟨1, τ_Q⟩` and `⟨1/N, τ_Q⟩` are
`κ(O)`-stable (`kappa_mul_mem_lat`, `kappa_mul_mem_latN_gen`), so `w` fixes their closures and
`s⁻¹(L, L_N) = k⁻¹(J ∩ O)⁻¹(L, L_N) = (k⁻¹c⁻¹)·(L', L'_N)`; multiplication by `s_f⁻¹` is an
isomorphism `K/𝔞 ≅ 𝔸_{K,f}/𝔞̂ → 𝔸_{K,f}/s⁻¹𝔞̂ ≅ K/s⁻¹𝔞` mapping `L_N/L` onto `s⁻¹L_N/s⁻¹L`.
A computation with Mathlib's adeles and Tau Ceti's ring-class quotient (no CM theory). -/
def IdeleLatticeHeegner : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J →
  ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
    idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
    idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
    ∃ c' : ℂ, c' ≠ 0 ∧ kappa m '' sInvLat m s (kappa m ⁻¹' (Q.lat : Set ℂ)) = c' • (Q'.lat : Set ℂ) ∧
      ∃ π : Equiv.Perm (Fin (N - 1)), ∀ k : Fin (N - 1), ∃ v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v -
            algebraMap (QNeg m) (AfK m) (algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N)) ∈
          latHat m (kappa m ⁻¹' (Q.lat : Set ℂ)) ∧
        kappa m v - c' * ((((π k : ℕ) : ℂ) + 1) / N) ∈ c' • (Q'.lat : Set ℂ)

/-! ### Lemmas -/

section Lemmas

variable {m : ℕ} [NeZero m]

theorem kappa_omega (m : ℕ) : kappa m QuadraticAlgebra.omega = I * (Real.sqrt m : ℂ) := by
  simp [kappa, QuadraticAlgebra.omega]

/-- `ιC ∘ e = κ` on `K` for a normalized `e`. -/
theorem kappa_eq_of_normalized (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar)
    (he : ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ)) (k : QNeg m) :
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) k)) = kappa m k := by
  let φ : QNeg m →ₐ[ℚ] ℂ :=
    ιCA.comp (e.comp ((Algebra.ofId (QNeg m) (SeparableClosure (QNeg m))).restrictScalars ℚ))
  have : φ = kappaAlg m := by
    apply QuadraticAlgebra.algHom_ext
    rw [kappaAlg_apply, kappa_omega]
    exact he
  have h : φ k = kappaAlg m k := by rw [this]
  rw [kappaAlg_apply] at h
  exact h

theorem kappa_rat (q : ℚ) : kappa m (algebraMap ℚ (QNeg m) q) = (q : ℂ) := by
  rw [← kappaAlg_apply, AlgHom.commutes]; simp

theorem kappa_injective : Function.Injective (kappa m) := by
  intro a b h
  rw [← kappaAlg_apply, ← kappaAlg_apply] at h
  exact (kappaAlg m).toRingHom.injective h

theorem kappa_add (a b : QNeg m) : kappa m (a + b) = kappa m a + kappa m b := by
  simp only [← kappaAlg_apply, map_add]

theorem kappa_intCast_mul (n : ℤ) (a : QNeg m) : kappa m (n * a) = n * kappa m a := by
  simp only [← kappaAlg_apply, map_mul, map_intCast]

/-- `τ_Q ∈ κ(K)`. -/
theorem exists_kappa_tau {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D) :
    ∃ t : QNeg m, kappa m t = Q.tau := by
  have hA : (Q.A : ℂ) ≠ 0 := heegner_A_ne_zero Q
  set c₀ : ℝ := if m % 4 = 3 then (f : ℝ) else 2 * f with hc₀
  have hc : ∃ q : ℚ, (q : ℝ) = c₀ := by
    by_cases h : m % 4 = 3
    · exact ⟨f, by simp [hc₀, h]⟩
    · exact ⟨2 * f, by simp [hc₀, h]⟩
  obtain ⟨q, hq⟩ := hc
  refine ⟨⟨-(Q.B : ℚ) / (2 * Q.A), q / (2 * Q.A)⟩, ?_⟩
  have hs : Real.sqrt (-(D : ℝ)) = c₀ * Real.sqrt m := by rw [hD]; exact sqrt_neg_discOf m f
  simp only [kappa, HeegnerForm.tau, cmPoint, hs]
  push_cast
  rw [← hq]
  field_simp
  push_cast
  ring

theorem lat_subset_range {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D) :
    (Q.lat : Set ℂ) ⊆ Set.range (kappa m) := by
  obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q
  intro z hz
  rw [SetLike.mem_coe, HeegnerForm.lat, Submodule.mem_span_pair] at hz
  obtain ⟨a, b, rfl⟩ := hz
  refine ⟨(a : QNeg m) * 1 + (b : QNeg m) * t, ?_⟩
  rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht]
  simp [kappa, zsmul_eq_mul, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem preimage_lat_eq_span {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D)
    {t : QNeg m} (ht : kappa m t = Q.tau) :
    kappa m ⁻¹' (Q.lat : Set ℂ) = (Submodule.span ℤ {(1 : QNeg m), t} : Set (QNeg m)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, HeegnerForm.lat, Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, kappa_injective ?_⟩
    simp only [zsmul_eq_mul] at hab ⊢
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht, ← hab]
    simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · rintro ⟨a, b, rfl⟩
    refine ⟨a, b, ?_⟩
    simp only [zsmul_eq_mul]
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ht]
    simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

theorem weber_add_mem (P : PeriodPair) (z l : ℂ) (hl : l ∈ P.lattice) :
    weber P (z + l) = weber P z := by
  unfold weber
  rw [P.weierstrassP_add_coe z ⟨l, hl⟩]

/-- The period pair `(c, cτ)`. -/
def ppScale (c : ℂ) (hc : c ≠ 0) (τ : UpperHalfPlane) : PeriodPair :=
  ⟨c, c * τ, by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 : c * ((s : ℂ) * 1 + (t : ℂ) * τ) = 0 := by
      simp only [Complex.real_smul] at h; linear_combination h
    have h2 : s • (1 : ℂ) + t • (τ : ℂ) = 0 := by
      rcases mul_eq_zero.1 h1 with h' | h'
      · exact absurd h' hc
      · simpa [Complex.real_smul] using h'
    exact (LinearIndependent.pair_iff.1 (linIndep_one_tau τ)) s t h2⟩

theorem ppScale_isScale (c : ℂ) (hc : c ≠ 0) (τ : UpperHalfPlane) :
    IsScale (ppScale c hc τ) (pp τ) c := by
  refine ⟨hc, ?_⟩
  ext x
  simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_smul_set, smul_eq_mul, ppScale, pp]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a * 1 + b * τ, ⟨a, b, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨a, b, rfl⟩, rfl⟩
    exact ⟨a, b, by ring⟩

theorem range_map_fin {α : Type*} (n : ℕ) (g : ℕ → α) :
    (Multiset.range n).map g = (Finset.univ : Finset (Fin n)).val.map (fun k : Fin n => g (k : ℕ)) := by
  have h1 : (Finset.univ : Finset (Fin n)).val.map (fun k : Fin n => (k : ℕ)) = Multiset.range n := by
    have := congrArg Finset.val (Fin.map_valEmbedding_univ (n := n))
    rw [Finset.map_val] at this
    rw [show (fun k : Fin n => (k : ℕ)) = Fin.valEmbedding from rfl, this, Nat.Iio_eq_range]
    rfl
  rw [← h1, Multiset.map_map]
  rfl

end Lemmas

/-- **Ring-class reciprocity pins the idele class** (proved from Tau Ceti's
`ringClassArtinEquiv_ringClassIdeleQuotient`): if `σ = [s, K]` on `K^ab`, `σ` extends `ρ`, and `ρ`
acts on `e(H_O)` as `Art(J ∩ O)`, then the ring class of `s` is the class of `J ∩ O`. -/
theorem ringClass_of_artin {m f : ℕ} [NeZero m] [NeZero f]
    (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar) (σ : ℂ ≃+* ℂ)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (hs : ArtinCond m e σ s) (ρ : GalQ)
    (hσ : ∀ a : Qbar, σ (ιC a) = ιC (ρ a))
    (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (hρ : ∀ x : ringClassField (conductorOrder (QNeg m) f),
      ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg m) f)
        ((conductorOrder (QNeg m) f).picClass J) x)) :
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J := by
  apply (ringClassArtinEquiv (conductorOrder (QNeg m) f)).injective
  rw [ringClassArtinEquiv_ringClassIdeleQuotient]
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  have h1 := hs (ringClassField (conductorOrder (QNeg m) f)) x
  rw [hσ, hρ] at h1
  have h2 := ιC.injective h1
  have h3 := e.toRingHom.injective h2
  exact h3.symm

/-- **`CMModuli` from the printed main theorem of CM** (`ShimuraMainCM`, Shimura 1971 Thm. 5.4),
the field-theory glue `AutExtends`, `FixedAlgebraic`, the class-field glue `ArtinLift` and the
adelic glue `LatHatInter`, `IdeleLatticeHeegner`. -/
theorem cmModuli_of (hL : ShimuraMainCM) (hA : AutExtends) (hF : FixedAlgebraic)
    (hAL : ArtinLift) (hI : LatHatInter) (hH : IdeleLatticeHeegner) : CMModuli := by
  intro N hN m f _ _ hsq e he J ρ hρ D hD Q Q' c hLc hLN
  obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q
  set 𝔞 : Set (QNeg m) := kappa m ⁻¹' (Q.lat : Set ℂ) with h𝔞def
  have h𝔞 : ((pp Q.tauH).lattice : Set ℂ) = kappa m '' 𝔞 :=
    (Set.image_preimage_eq_of_subset (lat_subset_range hD Q)).symm
  have hNN : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  -- the points `u_k = (k + 1)/N ∈ K`
  have hu : ∀ k : ℕ, k < N - 1 →
      kappa m (algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N)) = ((k : ℂ) + 1) / N ∧
      kappa m (algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N)) ∉ (pp Q.tauH).lattice := by
    intro k hk
    have e1 : kappa m (algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N)) = ((k : ℂ) + 1) / N := by
      rw [kappa_rat]; push_cast; rfl
    refine ⟨e1, ?_⟩
    rw [e1]
    have := div_nat_not_mem Q.tauH (a := k + 1) (N := N) (by omega) (by omega)
    push_cast at this
    exact this
  -- Step A: the moduli coordinates of `τ_Q` are algebraic
  have halg : ∀ i < N, ∃ a : Qbar, ιC a = modCoord N Q.tauH i := by
    intro i hi
    apply hF
    intro σ₀ hσ₀
    have hs1 : ArtinCond m e σ₀ 1 := by
      intro F _ _ _ x
      rw [show icl (1 : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) = 1 from QuotientGroup.mk_one _, map_one,
        AlgEquiv.one_apply]
      exact hσ₀ _
    have hfin1 : finPart (1 : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) = 1 := by
      simp only [finPart, Units.val_one, Prod.snd_one]
    have hsInv : sInvLat m 1 𝔞 = 𝔞 := by
      have := hI m hsq f D hD N Q
      simp only [sInvLat, hfin1, one_mul]
      exact this
    obtain ⟨μ, hμ, hpts⟩ := hL m hsq e he σ₀ 1 hs1 𝔞 (pp Q.tauH) (pp Q.tauH) h𝔞
      (by rw [hsInv]; exact h𝔞)
    have hW : (weberSet N Q.tauH).map (σ₀ : ℂ →+* ℂ) = weberSet N Q.tauH := by
      rw [weberSet, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro k hk
      rw [Multiset.mem_range] at hk
      obtain ⟨e1, e2⟩ := hu k hk
      have h0 : finPart (1 : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) *
          algebraMap (QNeg m) (AfK m) (algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N)) -
          algebraMap (QNeg m) (AfK m) (algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N)) ∈
          latHat m 𝔞 := by
        rw [hfin1, one_mul, sub_self]
        refine subset_closure ⟨0, ?_, map_zero _⟩
        show kappa m 0 ∈ Q.lat
        rw [show kappa m 0 = 0 by simp [kappa]]; exact Submodule.zero_mem _
      have hp := (hpts _ _ e2 h0).1
      rw [e1] at hp
      exact hμ.weber hp
    by_cases h0 : i = 0
    · subst h0; rw [modCoord_zero]; exact hμ.jL
    · rw [modCoord_succ N _ h0]
      show (σ₀ : ℂ →+* ℂ) _ = _
      rw [map_esymm, hW]
  classical
  let x : ℕ → Qbar := fun i => if h : i < N then (halg i h).choose else 0
  have hx : ∀ i < N, ιC (x i) = modCoord N Q.tauH i := by
    intro i hi; simp only [x, hi, ↓reduceDIte]; exact (halg i hi).choose_spec
  refine ⟨x, hx, ?_⟩
  -- Step B: Galois conjugation
  obtain ⟨σ, hσ⟩ := hA ρ
  have hσK : ∀ k : QNeg m, σ (kappa m k) = kappa m k := by
    intro k
    rw [← kappa_eq_of_normalized e he k, hσ]
    have h1 := hρ (algebraMap (QNeg m) (ringClassField (conductorOrder (QNeg m) f)) k)
    rw [AlgEquiv.commutes] at h1
    exact congrArg ιC h1
  obtain ⟨s, hs⟩ := hAL m hsq e he σ hσK
  have hcl := ringClass_of_artin (m := m) (f := f) e σ s hs ρ hσ J hρ
  have hH1 := hH N hN m f hsq J s
  have hH2 := hH1 hcl
  have hH3 := hH2 D hD Q Q' c hLc hLN
  obtain ⟨c', hc', hlat, π, hπ⟩ := hH3
  have hsc := ppScale_isScale c' hc' Q'.tauH
  obtain ⟨μ, hμ, hpts⟩ := hL m hsq e he σ s hs 𝔞 (pp Q.tauH) (ppScale c' hc' Q'.tauH) h𝔞
    (by rw [hsc.2]; exact hlat.symm)
  have hk : ∀ k : Fin (N - 1), (σ : ℂ →+* ℂ) (weber (pp Q.tauH) ((((k : ℕ) : ℂ) + 1) / N)) =
      weber (pp Q'.tauH) ((((π k : ℕ) : ℂ) + 1) / N) := by
    intro k
    obtain ⟨v, hv1, hv2⟩ := hπ k
    obtain ⟨e1, e2⟩ := hu k k.2
    have hp := (hpts _ v e2 hv1).1
    rw [e1] at hp
    rw [hμ.weber hp]
    have hl : kappa m v - c' * ((((π k : ℕ) : ℂ) + 1) / N) ∈ (ppScale c' hc' Q'.tauH).lattice := by
      rw [← SetLike.mem_coe, hsc.2]; exact hv2
    rw [show kappa m v = c' * ((((π k : ℕ) : ℂ) + 1) / N) +
        (kappa m v - c' * ((((π k : ℕ) : ℂ) + 1) / N)) by ring, weber_add_mem _ _ _ hl, hsc.weber]
  have hW : (weberSet N Q.tauH).map (σ : ℂ →+* ℂ) = weberSet N Q'.tauH := by
    rw [weberSet, weberSet, range_map_fin, range_map_fin, Multiset.map_map]
    calc (Finset.univ : Finset (Fin (N - 1))).val.map
          ((σ : ℂ →+* ℂ) ∘ fun k : Fin (N - 1) => weber (pp Q.tauH) ((((k : ℕ) : ℂ) + 1) / N))
        = (Finset.univ : Finset (Fin (N - 1))).val.map
          (fun k : Fin (N - 1) => weber (pp Q'.tauH) ((((π k : ℕ) : ℂ) + 1) / N)) :=
          Multiset.map_congr rfl fun k _ => hk k
      _ = ((Finset.univ : Finset (Fin (N - 1))).val.map π).map
          (fun k : Fin (N - 1) => weber (pp Q'.tauH) ((((k : ℕ) : ℂ) + 1) / N)) := by
          rw [Multiset.map_map]; rfl
      _ = _ := by rw [Multiset.map_univ_val_equiv π]
  intro i hi
  rw [← hσ, hx i hi]
  by_cases h0 : i = 0
  · subst h0; rw [modCoord_zero, modCoord_zero]
    show (σ : ℂ →+* ℂ) _ = _
    rw [hμ.jL, hsc.jL]
  · rw [modCoord_succ N _ h0, modCoord_succ N _ h0]
    show (σ : ℂ →+* ℂ) _ = _
    rw [map_esymm, hW]

end T5Glue
