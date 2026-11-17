
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §5d. `StrongApprox`, proved from Tau Ceti's strong approximation
(`IsDedekindDomain.FiniteAdeleRing.denseRange_algebraMap`, `closure_range_algebraMap`,
`isOpen_integralAdeles`) -/

theorem strongApprox : StrongApprox := by
  intro m _ hsq f _ D hD N Q s u
  set n : ℕ := 2 * cz m f with hn
  have hn0 : (n : QNeg m) ≠ 0 := by
    have := cz_pos (m := m) (f := f); exact_mod_cast (show n ≠ 0 by omega)
  set 𝔞 : Set (QNeg m) := kappa m ⁻¹' (Q.lat : Set ℂ) with h𝔞
  have h𝔞span : 𝔞 = (Submodule.span ℤ {(1 : QNeg m), tK m Q (cz m f)} : Set (QNeg m)) :=
    preimage_lat_eq_span hD Q (kappa_tK hD Q)
  -- the open set `V = n·𝒪̂ ⊆ 𝔞̂`
  set V : Set (AfK m) := (fun y => algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y) ⁻¹'
    (FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) : Set (AfK m)) with hV
  have hVo : IsOpen V :=
    (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
      (continuous_const.mul continuous_id)
  have hVsub : V ⊆ latHat m 𝔞 := by
    intro y hy
    have hcl := FiniteAdeleRing.closure_range_algebraMap (𝓞 (QNeg m)) (QNeg m)
    have hy' := (Set.ext_iff.1 hcl (algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y)).2 hy
    have hcont : Continuous fun z : AfK m => algebraMap (QNeg m) (AfK m) (n : QNeg m) * z :=
      continuous_const.mul continuous_id
    have h1 := image_closure_subset_closure_image hcont ⟨_, hy', rfl⟩
    have hyeq : algebraMap (QNeg m) (AfK m) (n : QNeg m) *
        (algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) * y) = y := by
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hn0, map_one, one_mul]
    beta_reduce at h1
    rw [hyeq] at h1
    refine closure_mono ?_ h1
    rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
    refine ⟨(n : QNeg m) * (r : QNeg m), ?_, ?_⟩
    · rw [h𝔞span]; exact two_cz_mul_mem hsq hD Q r
    · rw [map_mul] <;> rfl
  -- the open set `W = s_f⁻¹(u + V)`, nonempty
  set W : Set (AfK m) := (fun y => finPart s * y - algebraMap (QNeg m) (AfK m) u) ⁻¹' V with hW
  have hWo : IsOpen W := hVo.preimage ((continuous_const.mul continuous_id).sub continuous_const)
  have hWne : W.Nonempty := by
    refine ⟨finPart s⁻¹ * algebraMap (QNeg m) (AfK m) u, ?_⟩
    have hinv : finPart s * finPart s⁻¹ = 1 := by
      simp only [finPart]
      rw [← Prod.snd_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Prod.snd_one]
    show algebraMap (QNeg m) (AfK m) ((n : QNeg m)⁻¹) *
      (finPart s * (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) u) - algebraMap (QNeg m) (AfK m) u) ∈
        FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)
    rw [← mul_assoc, hinv, one_mul, sub_self, mul_zero]
    exact Subalgebra.zero_mem _
  obtain ⟨v, hv⟩ := (FiniteAdeleRing.denseRange_algebraMap (𝓞 (QNeg m)) (QNeg m)).exists_mem_open
    hWo hWne
  exact ⟨v, hVsub hv⟩

end T5Glue
