
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §5c. `K ∩ 𝔞̂ = 𝔞`, proved for lattices `n𝓞_K ⊆ ℤa + ℤb ⊆ d⁻¹𝓞_K` -/

section LatHatProof

variable {m : ℕ} [NeZero m]

/-- Adeles `y` with `n⁻¹y` integral at every finite place (`n·𝒪̂`). -/
def intAd (m : ℕ) [NeZero m] (n : ℕ) : Set (AfK m) :=
  {y | ∀ v : HeightOneSpectrum (𝓞 (QNeg m)),
    (algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y) v ∈ v.adicCompletionIntegers (QNeg m)}

theorem isClosed_intAd (n : ℕ) : IsClosed (intAd m n) := by
  unfold intAd
  rw [Set.ofPred_forall]
  refine isClosed_iInter fun v => ?_
  have hmul : Continuous fun y : AfK m => algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y :=
    continuous_const.mul continuous_id
  have hc : Continuous fun y : AfK m =>
      (algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y) v :=
    (RestrictedProduct.continuous_eval v).comp hmul
  have hcl : IsClosed ((v.adicCompletionIntegers (QNeg m) : Set (v.adicCompletion (QNeg m)))) :=
    Valued.isClosed_integer _
  exact hcl.preimage hc

theorem algebraMap_mem_intAd_iff (n : ℕ) (z : QNeg m) :
    algebraMap (QNeg m) (AfK m) z ∈ intAd m n ↔
      (n : QNeg m)⁻¹ * z ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)) := by
  unfold intAd
  simp only [Set.mem_setOf_eq, ← map_mul]
  constructor
  · intro h
    have := HeightOneSpectrum.mem_integers_of_valuation_le_one (QNeg m) ((n : QNeg m)⁻¹ * z)
      (fun v => by
        have h1 := h v
        rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
        exact h1)
    exact this
  · rintro ⟨r, hr⟩ v
    rw [FiniteAdeleRing.algebraMap_apply, ← hr]
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

/-- **`K ∩ 𝔞̂ = 𝔞`** for `𝔞 = ℤa + ℤb` with `n𝓞_K ⊆ 𝔞` and `d·a, d·b ∈ 𝓞_K`. -/
theorem latHat_inter_of_sandwich (a b : QNeg m) (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (hn𝔞 : ∀ y : 𝓞 (QNeg m), (n : QNeg m) * y ∈ Submodule.span ℤ {a, b})
    (hda : (d : QNeg m) * a ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)))
    (hdb : (d : QNeg m) * b ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m))) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈
        latHat m (Submodule.span ℤ {a, b} : Set (QNeg m))} = Submodule.span ℤ {a, b} := by
  set 𝔞 := Submodule.span ℤ {a, b} with h𝔞
  have hn0 : (n : QNeg m) ≠ 0 := by exact_mod_cast hn.ne'
  set M : ℕ := n * d with hM
  have hM0 : 0 < M := Nat.mul_pos hn hd
  -- finitely many coset representatives `i a + j b`
  let S : Finset (QNeg m) :=
    ((Finset.range M) ×ˢ (Finset.range M)).image fun p => (p.1 : QNeg m) * a + (p.2 : QNeg m) * b
  let U : Set (AfK m) := ⋃ s ∈ S, (fun y => y - algebraMap (QNeg m) (AfK m) s) ⁻¹' intAd m n
  have hUc : IsClosed U := by
    refine (S.finite_toSet).isClosed_biUnion fun s _ => ?_
    exact (isClosed_intAd n).preimage (continuous_id.sub continuous_const)
  -- integrality of `d·(p'a + q'b)`
  have hdint : ∀ p q : ℤ, (d : QNeg m) * ((p : QNeg m) * a + (q : QNeg m) * b) ∈
      Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)) := by
    intro p q
    obtain ⟨ra, hra⟩ := hda
    obtain ⟨rb, hrb⟩ := hdb
    refine ⟨(p : 𝓞 (QNeg m)) * ra + (q : 𝓞 (QNeg m)) * rb, ?_⟩
    rw [map_add, map_mul, map_mul, hra, hrb, map_intCast, map_intCast]; ring
  have hsub : algebraMap (QNeg m) (AfK m) '' (𝔞 : Set (QNeg m)) ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, h𝔞, Submodule.mem_span_pair] at hx
    obtain ⟨p, q, rfl⟩ := hx
    have hMi : (0 : ℤ) < M := by exact_mod_cast hM0
    set i := p % (M : ℤ)
    set j := q % (M : ℤ)
    have hp : p = i + M * (p / M) := by have := Int.emod_add_ediv_mul p M; linarith
    have hq : q = j + M * (q / M) := by have := Int.emod_add_ediv_mul q M; linarith
    have hi0 : 0 ≤ i := Int.emod_nonneg p (by omega)
    have hiM : i < M := Int.emod_lt_of_pos p hMi
    have hj0 : 0 ≤ j := Int.emod_nonneg q (by omega)
    have hjM : j < M := Int.emod_lt_of_pos q hMi
    refine Set.mem_iUnion₂.2 ⟨(i.toNat : QNeg m) * a + (j.toNat : QNeg m) * b, ?_, ?_⟩
    · exact Finset.mem_image.2 ⟨(i.toNat, j.toNat), Finset.mem_product.2
        ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩, rfl⟩
    · show algebraMap (QNeg m) (AfK m) (p • a + q • b) -
        algebraMap (QNeg m) (AfK m) ((i.toNat : QNeg m) * a + (j.toNat : QNeg m) * b) ∈ intAd m n
      rw [← map_sub, algebraMap_mem_intAd_iff]
      have hit : ((i.toNat : ℕ) : QNeg m) = (i : QNeg m) := by
        have : ((i.toNat : ℕ) : ℤ) = i := Int.toNat_of_nonneg hi0
        exact_mod_cast this
      have hjt : ((j.toNat : ℕ) : QNeg m) = (j : QNeg m) := by
        have : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
        exact_mod_cast this
      have e : (n : QNeg m)⁻¹ * (p • a + q • b - ((i.toNat : QNeg m) * a + (j.toNat : QNeg m) * b)) =
          (d : QNeg m) * (((p / M : ℤ) : QNeg m) * a + ((q / M : ℤ) : QNeg m) * b) := by
        rw [hit, hjt, zsmul_eq_mul, zsmul_eq_mul]
        conv_lhs => rw [hp, hq]
        push_cast [hM]
        field_simp
        ring
      rw [e]
      exact hdint _ _
  have hcl : latHat m (𝔞 : Set (QNeg m)) ⊆ U := closure_minimal hsub hUc
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (hcl hx)
    simp only [Set.mem_preimage] at hxs
    rw [← map_sub, algebraMap_mem_intAd_iff] at hxs
    obtain ⟨r, hr⟩ := hxs
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.1 hs
    have hr' : (r : QNeg m) = (n : QNeg m)⁻¹ * (x - ((i : QNeg m) * a + (j : QNeg m) * b)) := hr
    have hxe : x = ((i : QNeg m) * a + (j : QNeg m) * b) + (n : QNeg m) * r := by
      rw [hr']; field_simp; ring
    rw [SetLike.mem_coe, hxe]
    refine 𝔞.add_mem ?_ (hn𝔞 r)
    have h1 : (i : QNeg m) * a = (i : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    have h2 : (j : QNeg m) * b = (j : ℤ) • b := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [h1, h2]
    exact 𝔞.add_mem (𝔞.smul_mem _ (Submodule.subset_span (by simp)))
      (𝔞.smul_mem _ (Submodule.subset_span (by simp)))
  · intro hx
    exact mem_latHat_of_mem hx

end LatHatProof

end T5Glue

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

section Heegner

variable {m : ℕ} [NeZero m]

/-- `c₀ = f` (`m ≡ 3 mod 4`) or `2f`: `√(−disc O) = c₀√m`. -/
def cz (m f : ℕ) : ℕ := if m % 4 = 3 then f else 2 * f

/-- `τ_Q = (−B + c₀√−m)/(2A) ∈ K`. -/
def tK {N : ℕ} {D : ℤ} (m : ℕ) (Q : HeegnerForm N D) (c : ℕ) : QNeg m :=
  ⟨-(Q.B : ℚ) / (2 * Q.A), (c : ℚ) / (2 * Q.A)⟩

theorem kappa_tK {f : ℕ} {D : ℤ} (hD : D = discOf m f) {N : ℕ} (Q : HeegnerForm N D) :
    kappa m (tK m Q (cz m f)) = Q.tau := by
  have hA : (Q.A : ℂ) ≠ 0 := heegner_A_ne_zero Q
  have hs : Real.sqrt (-(D : ℝ)) = (cz m f : ℝ) * Real.sqrt m := by
    rw [hD, sqrt_neg_discOf m f]; unfold cz; split_ifs <;> push_cast <;> ring
  simp only [kappa, tK, HeegnerForm.tau, cmPoint, hs]
  push_cast
  field_simp

theorem cz_pos {f : ℕ} [NeZero f] : 0 < cz m f := by
  have := Nat.pos_of_ne_zero (NeZero.ne f)
  unfold cz; split_ifs <;> omega

theorem natCast_mul_mk (d : ℕ) (z : QNeg m) : (d : QNeg m) * z = ⟨d * z.re, d * z.im⟩ := by
  ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_natCast,
    QuadraticAlgebra.im_natCast]

theorem zsmul_mk (X : ℤ) (z : QNeg m) : X • z = ⟨X * z.re, X * z.im⟩ := by
  ext <;> simp [zsmul_eq_mul]

/-- `2c₀·𝓞_K ⊆ ℤ + ℤτ_Q` (kernel `two_coords`). -/
theorem two_cz_mul_mem (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ} (hD : D = discOf m f)
    {N : ℕ} (Q : HeegnerForm N D) (y : 𝓞 (QNeg m)) :
    ((2 * cz m f : ℕ) : QNeg m) * y ∈ Submodule.span ℤ {(1 : QNeg m), tK m Q (cz m f)} := by
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  obtain ⟨α, β, Nn, hα, hβ, -⟩ := two_coords hsq y
  rw [Submodule.mem_span_pair]
  refine ⟨cz m f * α + β * Q.B, 2 * Q.A * β, ?_⟩
  have hre : (y : QNeg m).re = α / 2 := by linarith
  have him : (y : QNeg m).im = β / 2 := by linarith
  rw [natCast_mul_mk, zsmul_mk, zsmul_mk]
  ext
  · simp only [QuadraticAlgebra.re_add, tK, QuadraticAlgebra.re_one, hre]
    push_cast
    field_simp
    ring
  · simp only [QuadraticAlgebra.im_add, tK, QuadraticAlgebra.im_one, him]
    push_cast
    field_simp
    ring

/-- **`K ∩ 𝔞̂ = 𝔞` for `𝔞 = κ⁻¹⟨1, τ_Q⟩`** (`n = 2c₀`, `d = 2A`). -/
theorem latHat_inter_heegner (hsq : Squarefree m) {f : ℕ} [NeZero f] {D : ℤ} (hD : D = discOf m f)
    {N : ℕ} (Q : HeegnerForm N D) :
    {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈ latHat m (kappa m ⁻¹' (Q.lat : Set ℂ))} =
      kappa m ⁻¹' (Q.lat : Set ℂ) := by
  have ht := kappa_tK (m := m) hD Q
  rw [preimage_lat_eq_span hD Q ht]
  have hA : (0 : ℤ) < Q.A := Q.A_pos
  have hAq : (Q.A : ℚ) ≠ 0 := by exact_mod_cast hA.ne'
  have hAt : ((Q.A.toNat : ℕ) : ℚ) = Q.A := by
    have : ((Q.A.toNat : ℕ) : ℤ) = Q.A := Int.toNat_of_nonneg hA.le
    exact_mod_cast this
  refine latHat_inter_of_sandwich 1 (tK m Q (cz m f)) (2 * cz m f) (2 * Q.A.toNat)
    (by have := cz_pos (m := m) (f := f); omega) (by omega) ?_ ?_ ?_
  · exact two_cz_mul_mem hsq hD Q
  · refine ⟨((2 * Q.A.toNat : ℕ) : 𝓞 (QNeg m)), ?_⟩
    rw [map_natCast, mul_one]
  · refine ⟨(-Q.B : 𝓞 (QNeg m)) + (cz m f : 𝓞 (QNeg m)) * sqrtNeg m, ?_⟩
    have hsq' : algebraMap (𝓞 (QNeg m)) (QNeg m) (sqrtNeg m) = QuadraticAlgebra.omega := coe_sqrtNeg
    rw [map_add, map_mul, map_neg, map_intCast, map_natCast, hsq', natCast_mul_mk (2 * Q.A.toNat)]
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_neg, QuadraticAlgebra.re_mul,
        QuadraticAlgebra.re_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK]
      push_cast [hAt]
      field_simp
      ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_neg, QuadraticAlgebra.im_mul,
        QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast,
        QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega, tK]
      push_cast [hAt]
      field_simp
      ring

end Heegner

/-- **`LatHatInter`, proved.** -/
theorem latHatInter : LatHatInter :=
  fun _ _ hsq _ _ _ hD _ Q => latHat_inter_heegner hsq hD Q

end T5Glue
