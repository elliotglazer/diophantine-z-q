import VC.B2

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem range_coe' : Set.range ((↑) : UpperHalfPlane → ℂ) = {w : ℂ | 0 < w.im} :=
  UpperHalfPlane.range_coe

theorem density_eq (z : UpperHalfPlane) :
    (((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) : ℝ) = 1 / (z : ℂ).im ^ 2 := by
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_mk]
  rw [div_pow, one_pow]; rfl

theorem measurable_density :
    Measurable fun z : UpperHalfPlane => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) := by
  refine Measurable.pow_const (Measurable.div measurable_const ?_) 2
  apply Measurable.subtype_mk
  exact Complex.measurable_im.comp UpperHalfPlane.measurable_coe

/-- `∫_ℍ f(z) y² dμ = ∫_ℂ f` for `f` vanishing off `ℍ`. -/
theorem integral_H (f : ℂ → ℝ) (hf : ∀ w : ℂ, w.im ≤ 0 → f w = 0) :
    ∫ z : UpperHalfPlane, f z * (z : ℂ).im ^ 2 = ∫ w, f w := by
  rw [UpperHalfPlane.volume_def, integral_withDensity_eq_integral_smul measurable_density]
  have e : ∀ z : UpperHalfPlane, ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) •
      (f z * (z : ℂ).im ^ 2) = f z := by
    intro z
    rw [NNReal.smul_def, smul_eq_mul, density_eq]
    have h : (z : ℂ).im ≠ 0 := ne_of_gt z.im_pos
    field_simp
  simp_rw [e]
  rw [← UpperHalfPlane.measurableEmbedding_coe.integral_map (fun w => f w),
    UpperHalfPlane.measurableEmbedding_coe.map_comap, range_coe']
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro w hw
  exact hf w (not_lt.1 hw)

theorem integrable_H {f : ℂ → ℝ} (hf : ∀ w : ℂ, w.im ≤ 0 → f w = 0) (hfi : Integrable f) :
    Integrable (fun z : UpperHalfPlane => f z * (z : ℂ).im ^ 2) := by
  rw [UpperHalfPlane.volume_def, integrable_withDensity_iff_integrable_smul measurable_density]
  have e : (fun z : UpperHalfPlane => ((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2 : ℝ≥0) •
      (f z * (z : ℂ).im ^ 2)) = fun z : UpperHalfPlane => f z := by
    funext z
    rw [NNReal.smul_def, smul_eq_mul, density_eq]
    have h : (z : ℂ).im ≠ 0 := ne_of_gt z.im_pos
    field_simp
  rw [e]
  change Integrable (f ∘ UpperHalfPlane.coe) _
  rw [← UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff,
    UpperHalfPlane.measurableEmbedding_coe.map_comap]
  exact hfi.restrict

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- **Unfolding**: for the partition function `χ`, `∫_ℍ χ dμ = vol(s)`. -/
theorem lintegral_chi {s : Set UpperHalfPlane} (hs : IsFundDomain Γ s) {χ : ℂ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hχ0 : ∀ w, 0 ≤ χ w)
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1) :
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (χ z) = volume s := by
  have := countable_G hΓ
  have hF := isFundamentalDomain hΓ hs
  rw [hF.lintegral_eq_tsum']
  have hmeas : ∀ g : permG (subG hΓ), Measurable fun z : UpperHalfPlane =>
      ENNReal.ofReal (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ)) := fun g =>
    ENNReal.measurable_ofReal.comp (hχ.measurable.comp (UpperHalfPlane.measurable_coe.comp
      (measurable_const_smul g⁻¹)))
  rw [← lintegral_tsum (fun g => (hmeas g).aemeasurable)]
  have h1 : ∀ z : UpperHalfPlane, ∑' g : permG (subG hΓ),
      ENNReal.ofReal (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ)) = 1 := by
    intro z
    have hinv : ∑ᶠ g : permG (subG hΓ), χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) = 1 := by
      rw [← hsum z]
      exact finsum_comp_equiv (Equiv.inv _) (f := fun g => χ ((g • z : UpperHalfPlane) : ℂ))
    have hfin : (Function.support fun g : permG (subG hΓ) =>
        χ ((g⁻¹ • z : UpperHalfPlane) : ℂ)).Finite := by
      exact (support_finite hΓ hχc hχU z).preimage (f := fun g : permG (subG hΓ) => g⁻¹)
        (inv_injective.injOn)
    rw [tsum_eq_sum (s := hfin.toFinset), ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hχ0 _),
      ← finsum_eq_sum_of_support_subset _ (by simp), hinv, ENNReal.ofReal_one]
    intro g hg
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hg
    simp [hg]
  simp_rw [h1]
  simp

end ValenceCocompact
