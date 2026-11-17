
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise
  TauCeti.GlobalNumberFields.NumberFieldOrder

/-! ## §5i. `InvertibleColon`, proved from Tau Ceti's invertibility of `J ∩ O` -/

section Invert

variable {m f : ℕ} [NeZero m] [NeZero f]

theorem kappa_mul_eq (a b : QNeg m) : kappa m (a * b) = kappa m a * kappa m b := by
  simp only [← kappaAlg_apply, map_mul]

/-- The invertible fractional ideal `J ∩ O` of `O` (Tau Ceti). -/
abbrev jUnit (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) :
    (FractionalIdeal (nonZeroDivisors (conductorOrder (QNeg m) f).toSubalgebra) (QNeg m))ˣ :=
  (conductorOrder (QNeg m) f).integralIdealsAwayConductorToInvertible
    ((conductorOrder (QNeg m) f).integralIdealsAwayConductorEquiv.symm J)

/-- Its elements are those of `J ∩ O`. -/
theorem mem_jUnit_iff (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (x : QNeg m) :
    x ∈ ((jUnit J).val : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m)) ↔
      x ∈ idealMeetOrder m f J := by
  rw [FractionalIdeal.mem_coe, coe_integralIdealsAwayConductorToInvertible_apply,
    FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨x', hx', rfl⟩
    rw [Ideal.mem_map_of_equiv] at hx'
    obtain ⟨y, hy, rfl⟩ := hx'
    rw [coe_integralIdealsAwayConductorEquiv_symm_apply, Ideal.mem_comap] at hy
    refine ⟨(conductorOrder (QNeg m) f).toRingOfIntegersEquiv y |>.2, (y : 𝓞 (QNeg m)), hy, rfl⟩
  · rintro ⟨hxO, z, hz, rfl⟩
    refine ⟨⟨(z : QNeg m), hxO⟩, ?_, rfl⟩
    rw [Ideal.mem_map_of_equiv]
    refine ⟨⟨z, by rw [mem_toRingOfIntegers]; exact hxO⟩, ?_, rfl⟩
    rw [coe_integralIdealsAwayConductorEquiv_symm_apply, Ideal.mem_comap]
    exact hz

theorem inv_mul_jUnit (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus) :
    (((jUnit J)⁻¹).val : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m)) *
      ((jUnit J).val : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m)) = 1 := by
  rw [← FractionalIdeal.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    FractionalIdeal.coe_one]

end Invert

/-- **`InvertibleColon`, proved.** -/
theorem invertibleColon : InvertibleColon := by
  intro N hN m f _ _ hsq J D hD Q Q' c hLc hLN
  set Jf : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m) := ((jUnit J).val : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m))
  set Jinv : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m) :=
    (((jUnit J)⁻¹).val : Submodule (conductorOrder (QNeg m) f).toSubalgebra (QNeg m))
  have hmul : Jinv * Jf = 1 := inv_mul_jUnit J
  -- κ(o)·L' ⊆ L' for o ∈ O
  have hOL : ∀ {L : Submodule ℤ ℂ}, (∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L, kappa m o * x ∈ L) →
      ∀ w ∈ Jinv * Jf, ∀ x ∈ L, kappa m w * x ∈ L := by
    intro L hL w hw x hx
    rw [hmul, Submodule.mem_one] at hw
    obtain ⟨o, rfl⟩ := hw
    exact hL o o.2 x hx
  -- elements of `idealLat J` are κ-images of elements of `J ∩ O`
  have hspan : ∀ i ∈ idealLat m f J, ∃ j ∈ idealMeetOrder m f J, kappa m j = i := by
    intro i hi
    induction hi using Submodule.span_induction with
    | mem z hz => obtain ⟨j, hj, rfl⟩ := hz; exact ⟨j, hj, rfl⟩
    | zero => exact ⟨0, (mem_jUnit_iff J 0).1 (Submodule.zero_mem _), by simp [kappa]⟩
    | add a b _ _ ha hb =>
      obtain ⟨j₁, hj₁, rfl⟩ := ha
      obtain ⟨j₂, hj₂, rfl⟩ := hb
      exact ⟨j₁ + j₂, (mem_jUnit_iff J _).1 (Submodule.add_mem _ ((mem_jUnit_iff J _).2 hj₁)
        ((mem_jUnit_iff J _).2 hj₂)), kappa_add _ _⟩
    | smul r a _ ha =>
      obtain ⟨j, hj, rfl⟩ := ha
      refine ⟨(r : QNeg m) * j, (mem_jUnit_iff J _).1 ?_, ?_⟩
      · have : (r : QNeg m) * j = (r : (conductorOrder (QNeg m) f).toSubalgebra) • j := by
          rw [Algebra.smul_def]; rfl
        rw [this]; exact Submodule.smul_mem _ _ ((mem_jUnit_iff J _).2 hj)
      · rw [kappa_intCast_mul, zsmul_eq_mul]
  -- the cancellation: `κ(J ∩ O)·z ⊆ c·L` ⇒ `z ∈ L'` (for `L = κ(J∩O)·L'`-type data)
  have cancel : ∀ (L L' : Submodule ℤ ℂ),
      (∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L', kappa m o * x ∈ L') →
      idealLat m f J * L' = L.map (LinearMap.mulLeft ℤ c) →
      ∀ z : ℂ, (∀ j ∈ idealMeetOrder m f J, kappa m j * z ∈ L) → c * z ∈ L' := by
    intro L L' hL' hJL z hz
    -- every `w ∈ Jinv * Jf` satisfies `κ(w)·(c z) ∈ L'`
    have key : ∀ w ∈ Jinv * Jf, kappa m w * (c * z) ∈ L' := by
      intro w hw
      refine Submodule.mul_induction_on hw ?_ ?_
      · intro a ha b hb
        have hb' : b ∈ idealMeetOrder m f J := (mem_jUnit_iff J b).1 hb
        have h1 : c * (kappa m b * z) ∈ idealLat m f J * L' := by
          rw [hJL]
          exact ⟨kappa m b * z, hz b hb', rfl⟩
        have h2 : ∀ y ∈ idealLat m f J * L', kappa m a * y ∈ L' := by
          intro y hy
          refine Submodule.mul_induction_on hy ?_ ?_
          · intro i hi x hx
            obtain ⟨j, hj, rfl⟩ := hspan i hi
            rw [← mul_assoc, ← kappa_mul_eq]
            exact hOL hL' (a * j) (Submodule.mul_mem_mul ha ((mem_jUnit_iff J j).2 hj)) x hx
          · intro y₁ y₂ h₁ h₂
            rw [mul_add]; exact L'.add_mem h₁ h₂
        have := h2 _ h1
        rwa [kappa_mul_eq, show kappa m a * kappa m b * (c * z) = kappa m a * (c * (kappa m b * z))
          by ring]
      · intro x y hx hy
        rw [kappa_add, add_mul]; exact L'.add_mem hx hy
    have h1 : (1 : QNeg m) ∈ Jinv * Jf := by rw [hmul]; exact Submodule.one_le.1 le_rfl
    have := key 1 h1
    rwa [show kappa m 1 = 1 by simp [kappa, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one],
      one_mul] at this
  -- elements of `idealLat J * L'` are κ-images when `L' ⊆ κ(K)`
  have hrange : ∀ (L' : Submodule ℤ ℂ), (L' : Set ℂ) ⊆ Set.range (kappa m) →
      ∀ w ∈ idealLat m f J * L', w ∈ Set.range (kappa m) := by
    intro L' hL' w hw
    refine Submodule.mul_induction_on hw ?_ ?_
    · intro i hi y hy
      obtain ⟨j, -, rfl⟩ := hspan i hi
      obtain ⟨y₀, rfl⟩ := hL' hy
      exact ⟨j * y₀, kappa_mul_eq _ _⟩
    · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, kappa_add _ _⟩
  -- `c ≠ 0`
  have hJne : (J : Ideal (𝓞 (QNeg m))) ≠ ⊥ :=
    ((conductorOrder (QNeg m) f).mem_integralIdealsPrimeTo_conductorModulus_iff.1 J.2).1
  have hc : c ≠ 0 := by
    intro hc0
    set n : ℕ := Ideal.absNorm (J : Ideal (𝓞 (QNeg m)))
    have hn0 : n ≠ 0 := fun h => hJne (Ideal.absNorm_eq_zero_iff.1 h)
    have hnJ : (n : 𝓞 (QNeg m)) ∈ (J : Ideal (𝓞 (QNeg m))) := Ideal.absNorm_mem _
    have hnO : (n : QNeg m) ∈ idealMeetOrder m f J :=
      ⟨Subalgebra.natCast_mem _ n, (n : 𝓞 (QNeg m)), hnJ, by simp⟩
    have hj : (n : ℂ) ∈ idealLat m f J := by
      refine Submodule.subset_span ⟨(n : QNeg m), hnO, ?_⟩
      rw [← kappaAlg_apply, map_natCast]
    have h1 : (n : ℂ) * 1 ∈ idealLat m f J * Q'.lat :=
      Submodule.mul_mem_mul hj (Submodule.subset_span (by simp))
    rw [hLc, hc0] at h1
    obtain ⟨y, -, hy⟩ := h1
    simp only [LinearMap.mulLeft_apply, zero_mul, mul_one] at hy
    exact hn0 (by exact_mod_cast hy.symm)
  -- the two image equalities
  have img : ∀ (L L' : Submodule ℤ ℂ), (1 : ℂ) ∈ L →
      (∀ o ∈ (conductorOrder (QNeg m) f).toSubalgebra, ∀ x ∈ L', kappa m o * x ∈ L') →
      (L' : Set ℂ) ⊆ Set.range (kappa m) →
      idealLat m f J * L' = L.map (LinearMap.mulLeft ℤ c) →
      kappa m '' colon (kappa m ⁻¹' (L : Set ℂ)) (idealMeetOrder m f J) = c⁻¹ • (L' : Set ℂ) := by
    intro L L' hL1 hL'O hL'r hJL
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hcz := cancel L L' hL'O hJL (kappa m x) (fun j hj => by
        have := hx j hj
        rwa [Set.mem_preimage, kappa_mul_eq] at this)
      exact Set.mem_smul_set.2 ⟨c * kappa m x, hcz, by rw [smul_eq_mul, inv_mul_cancel_left₀ hc]⟩
    · intro hw
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hw
      obtain ⟨y₀, rfl⟩ := hL'r hy
      have hcL : c ∈ Set.range (kappa m) := by
        apply hrange L' hL'r
        rw [hJL]
        exact ⟨1, hL1, by simp⟩
      obtain ⟨c₀, hc₀⟩ := hcL
      have hc₀0 : c₀ ≠ 0 := by rintro rfl; apply hc; rw [← hc₀]; simp [kappa]
      refine ⟨c₀⁻¹ * y₀, fun j hj => ?_, ?_⟩
      · have h1 : kappa m j * kappa m y₀ ∈ idealLat m f J * L' :=
          Submodule.mul_mem_mul (Submodule.subset_span ⟨j, hj, rfl⟩) hy
        rw [hJL] at h1
        obtain ⟨q, hq, hqe⟩ := h1
        simp only [LinearMap.mulLeft_apply] at hqe
        show kappa m (j * (c₀⁻¹ * y₀)) ∈ L
        rw [kappa_mul_eq, kappa_mul_eq, kappa_inv, hc₀,
          show kappa m j * (c⁻¹ * kappa m y₀) = c⁻¹ * (kappa m j * kappa m y₀) by ring, ← hqe,
          inv_mul_cancel_left₀ hc]
        exact hq
      · rw [kappa_mul_eq, kappa_inv, hc₀, smul_eq_mul]
  -- `⟨1/N, τ_{Q'}⟩ ⊆ κ(K)`
  have hrN : (Q'.latN : Set ℂ) ⊆ Set.range (kappa m) := by
    obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q'
    intro z hz
    rw [SetLike.mem_coe, HeegnerForm.latN, Submodule.mem_span_pair] at hz
    obtain ⟨a, b, rfl⟩ := hz
    refine ⟨(a : QNeg m) * algebraMap ℚ (QNeg m) (1 / N) + (b : QNeg m) * t, ?_⟩
    rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, kappa_rat, ht, zsmul_eq_mul, zsmul_eq_mul]
    push_cast; rfl
  refine ⟨hc, img Q.lat Q'.lat (Submodule.subset_span (by simp))
    (fun o ho => kappa_mul_mem_lat hsq hD Q' ho) (lat_subset_range hD Q') hLc,
    img Q.latN Q'.latN (lat_le_latN Q hN (Submodule.subset_span (by simp)))
    (fun o ho => kappa_mul_mem_latN_gen hsq hD Q' ho) hrN hLN⟩

end T5Glue
