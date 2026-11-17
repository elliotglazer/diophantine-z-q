
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §5h. `IdeleLatticeScale` from two smaller glue Props -/

/-- **GLUE RING-CLASS-LATTICE (the idelic and the congruence descriptions of `Pic O` agree).** If
the ring class of the idele `s` (Tau Ceti's `ringClassIdeleQuotient`, defined through ray classes
modulo the conductor) is the class of `J ∩ O`, then the `O`-lattice `𝔍_s = K ∩ s_f·Ô_O` of `s` is
`k·(J ∩ O)` for some `k ∈ Kˣ`. (Standard: `Pic O ≅ 𝔸_K^×/Kˣ Ô_O^× K_∞^×`, `s ↦ [K ∩ s_f Ô_O]`;
Neukirch I §12 and VI §1, Cox §7 and §9; UNVERIFIED numbers. Proof: move `s` by a principal idele
into the congruence subgroup of the conductor `𝔣` (Tau Ceti
`exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`); then `rayClassQuotient` is the ray class of
the ideal `I` of `s_f` (`rayClassQuotient_mk_of_mem`), `I = J·(βγ)` with `β ∈ O`, `γ ≡ 1 mod* 𝔣`
(`mem_ker_rayClassToPic`), and locally `s_f Ô_O = I_p` at `p ∤ f`, `= O_p` at `p ∣ f`, so
`𝔍_s = I ∩ O = βγ·(J ∩ O)`.) -/
def RingClassLattice : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J →
    ∃ k : QNeg m, k ≠ 0 ∧ idealOf m f s = (fun x => k * x) '' idealMeetOrder m f J

/-- **GLUE INVERTIBLE-COLON (`J ∩ O` is invertible).** Under `κ(J ∩ O)·L' = c·L` and
`κ(J ∩ O)·L'_N = c·L_N` (Heegner forms of discriminant `disc O`, `J` prime to `f`):
`c ≠ 0`, `κ(𝔞 : J ∩ O) = c⁻¹·L'` and `κ(𝔞_N : J ∩ O) = c⁻¹·L'_N`, where `𝔞 = κ⁻¹L`, `𝔞_N = κ⁻¹L_N`.
(`⊇` is immediate; `⊆` cancels `J ∩ O` using its inverse: ideals of `O` prime to the conductor are
invertible, Tau Ceti `isUnit_coeIdeal_of_mem_integralIdealsAwayConductor`; `L'`, `L'_N` are
`O`-stable.) -/
def InvertibleColon : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
    idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
    idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
    c ≠ 0 ∧
      kappa m '' colon (kappa m ⁻¹' (Q.lat : Set ℂ)) (idealMeetOrder m f J) =
        c⁻¹ • (Q'.lat : Set ℂ) ∧
      kappa m '' colon (kappa m ⁻¹' (Q.latN : Set ℂ)) (idealMeetOrder m f J) =
        c⁻¹ • (Q'.latN : Set ℂ)

section ScaleAux

variable {m : ℕ} [NeZero m]

theorem colon_smul (𝔞 𝔍 : Set (QNeg m)) {k : QNeg m} (hk : k ≠ 0) :
    colon 𝔞 ((fun x => k * x) '' 𝔍) = (fun x => k⁻¹ * x) '' colon 𝔞 𝔍 := by
  ext y
  constructor
  · intro hy
    refine ⟨k * y, fun j hj => ?_, by field_simp⟩
    have := hy (k * j) ⟨j, hj, rfl⟩
    rwa [show j * (k * y) = k * j * y by ring]
  · rintro ⟨z, hz, rfl⟩ _ ⟨j, hj, rfl⟩
    have := hz j hj
    rwa [show k * j * (k⁻¹ * z) = j * z by field_simp]

theorem kappa_image_smul (X : Set (QNeg m)) (k : QNeg m) :
    kappa m '' ((fun x => k * x) '' X) = kappa m k • kappa m '' X := by
  ext z
  simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨kappa m x, ⟨x, hx, rfl⟩, by rw [← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply,
      map_mul]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨k * x, ⟨x, hx, rfl⟩, by rw [← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply,
      map_mul]⟩

theorem smul_smul_set (a b : ℂ) (S : Set ℂ) : a • b • S = (a * b) • S := by
  rw [smul_smul]

theorem kappa_inv (k : QNeg m) : kappa m k⁻¹ = (kappa m k)⁻¹ := by
  rw [← kappaAlg_apply, ← kappaAlg_apply, map_inv₀]

/-- `κ⁻¹⟨κa, κb⟩ = ⟨a, b⟩`. -/
theorem preimage_span_pair (a b : QNeg m) :
    kappa m ⁻¹' (Submodule.span ℤ {kappa m a, kappa m b} : Set ℂ) =
      (Submodule.span ℤ {a, b} : Set (QNeg m)) := by
  ext x
  simp only [Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_pair]
  constructor
  · rintro ⟨p, q, hpq⟩
    refine ⟨p, q, kappa_injective ?_⟩
    simp only [zsmul_eq_mul] at hpq ⊢
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ← hpq]
  · rintro ⟨p, q, rfl⟩
    refine ⟨p, q, ?_⟩
    simp only [zsmul_eq_mul]
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul]

/-- **`K ∩ 𝔞̂_N = 𝔞_N` for `𝔞_N = κ⁻¹⟨1/N, τ_Q⟩`** (`n = 2c₀`, `d = 2AN`). -/
theorem latHat_inter_heegnerN (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ}
    (hD : D = discOf m f) {N : ℕ} (hN : 0 < N) (Q : HeegnerForm N D) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m (kappa m ⁻¹' (Q.latN : Set ℂ))} =
      kappa m ⁻¹' (Q.latN : Set ℂ) := by
  have ht := kappa_tK (m := m) hD Q
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  set a : QNeg m := algebraMap ℚ (QNeg m) (1 / N) with ha
  have hka : kappa m a = 1 / (N : ℂ) := by rw [ha, kappa_rat]; push_cast; rfl
  have hlatN : Q.latN = Submodule.span ℤ {kappa m a, kappa m (tK m Q (cz m f))} := by
    rw [HeegnerForm.latN, hka, ht]
  rw [hlatN, preimage_span_pair]
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hAt : ((Q.A.toNat : ℕ) : ℚ) = Q.A := by
    have : ((Q.A.toNat : ℕ) : ℤ) = Q.A := Int.toNat_of_nonneg hA.le
    exact_mod_cast this
  have hNa : (N : QNeg m) * a = 1 := by
    rw [ha, ← map_natCast (algebraMap ℚ (QNeg m)), ← map_mul]; field_simp; simp
  refine latHat_inter_of_sandwich a (tK m Q (cz m f)) (2 * cz m f) (2 * Q.A.toNat * N)
    (by have := cz_pos (m := m) (f := f); omega)
    (by have h1 : 0 < Q.A.toNat := by omega
        positivity) ?_ ?_ ?_
  · intro y
    have h1 := two_cz_mul_mem hsq hD Q y
    rw [Submodule.mem_span_pair] at h1 ⊢
    obtain ⟨p, q, hpq⟩ := h1
    refine ⟨p * N, q, ?_⟩
    rw [← hpq]
    simp only [zsmul_eq_mul]
    push_cast
    rw [show (p : QNeg m) * (N : QNeg m) * a = (p : QNeg m) * ((N : QNeg m) * a) by ring, hNa, mul_one]
  · refine ⟨((2 * Q.A.toNat : ℕ) : 𝓞 (QNeg m)), ?_⟩
    rw [map_natCast]
    push_cast
    rw [mul_assoc, hNa, mul_one]
  · refine ⟨((N : ℕ) : 𝓞 (QNeg m)) * ((-Q.B : 𝓞 (QNeg m)) + (cz m f : 𝓞 (QNeg m)) * sqrtNeg m), ?_⟩
    have hsq' : algebraMap (𝓞 (QNeg m)) (QNeg m) (sqrtNeg m) = QuadraticAlgebra.omega := coe_sqrtNeg
    rw [map_mul, map_natCast, map_add, map_mul, map_neg, map_intCast, map_natCast, hsq',
      natCast_mul_mk N, natCast_mul_mk (2 * Q.A.toNat * N)]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK, QuadraticAlgebra.im_add,
        QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast]
      push_cast [hAt]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK, QuadraticAlgebra.re_add,
        QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast]
      push_cast [hAt]
      field_simp
      ring

end ScaleAux

/-- **`IdeleLatticeScale` from `RingClassLattice` and `InvertibleColon`** (with `sInvLat_eq_colon`,
`latHatInter`, `latHat_inter_heegnerN` and the kernel's `κ(O)`-stability lemmas). -/
theorem ideleLatticeScale_of (hA : RingClassLattice) (hB : InvertibleColon) :
    IdeleLatticeScale := by
  intro N hN m f _ _ hsq J s hcl D hD Q Q' c hLc hLN
  obtain ⟨k, hk, hks⟩ := hA m f hsq J s hcl
  obtain ⟨hc, h1, h2⟩ := hB N hN m f hsq J D hD Q Q' c hLc hLN
  have hκk : kappa m k ≠ 0 := by
    intro h0; apply hk; apply kappa_injective; rw [h0]; simp [kappa]
  refine ⟨(kappa m k)⁻¹ * c⁻¹, mul_ne_zero (inv_ne_zero hκk) (inv_ne_zero hc), ?_, ?_⟩
  · have hO : ∀ o ∈ Osub m f, ∀ y ∈ kappaComap (m := m) Q.lat, o * y ∈ kappaComap (m := m) Q.lat := by
      intro o ho y hy
      show kappaLin m (o * y) ∈ Q.lat
      rw [kappaLin_apply, ← kappaAlg_apply, map_mul, kappaAlg_apply, kappaAlg_apply]
      exact kappa_mul_mem_lat hsq hD Q ho _ (by simpa [kappaComap, kappaLin_apply] using hy)
    have hInt : ∀ x : QNeg m, algebraMap (QNeg m) (AfK m) x ∈
        latHat m ((kappaComap (m := m) Q.lat : Submodule ℤ (QNeg m)) : Set (QNeg m)) →
        x ∈ kappaComap (m := m) Q.lat := by
      intro x hx
      rw [coe_kappaComap] at hx
      have := latHatInter m hsq f D hD N Q
      have hx' := (Set.ext_iff.1 this x).1 hx
      show x ∈ ((kappaComap (m := m) Q.lat : Submodule ℤ (QNeg m)) : Set (QNeg m))
      rw [coe_kappaComap]; exact hx'
    have e := sInvLat_eq_colon (kappaComap (m := m) Q.lat) hO hInt s
    rw [coe_kappaComap] at e
    rw [e, hks, colon_smul _ _ hk, kappa_image_smul, h1, kappa_inv, smul_smul_set]
  · have hO : ∀ o ∈ Osub m f, ∀ y ∈ kappaComap (m := m) Q.latN,
        o * y ∈ kappaComap (m := m) Q.latN := by
      intro o ho y hy
      show kappaLin m (o * y) ∈ Q.latN
      rw [kappaLin_apply, ← kappaAlg_apply, map_mul, kappaAlg_apply, kappaAlg_apply]
      exact kappa_mul_mem_latN_gen hsq hD Q ho _ (by simpa [kappaComap, kappaLin_apply] using hy)
    have hInt : ∀ x : QNeg m, algebraMap (QNeg m) (AfK m) x ∈
        latHat m ((kappaComap (m := m) Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m)) →
        x ∈ kappaComap (m := m) Q.latN := by
      intro x hx
      rw [coe_kappaComap] at hx
      have := latHat_inter_heegnerN hsq hD hN Q
      have hx' := (Set.ext_iff.1 this x).1 hx
      show x ∈ ((kappaComap (m := m) Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m))
      rw [coe_kappaComap]; exact hx'
    have e := sInvLat_eq_colon (kappaComap (m := m) Q.latN) hO hInt s
    rw [coe_kappaComap] at e
    rw [e, hks, colon_smul _ _ hk, kappa_image_smul, h2, kappa_inv, smul_smul_set]

end T5Glue
