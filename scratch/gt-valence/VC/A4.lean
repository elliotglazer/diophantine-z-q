import VC.A3

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem laplacian_continuous {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) : Continuous (Δ χ) := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  have h := hχ.continuous_iteratedFDeriv' (m := 2)
  exact ((continuous_eval_const _).comp h).add ((continuous_eval_const _).comp h)

theorem tsupport_laplacian_subset (χ : ℂ → ℝ) : tsupport (Δ χ) ⊆ tsupport χ := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  refine closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra h
  apply hx
  have := image_eq_zero_of_notMem_tsupport
    (fun hx' => h (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := χ) 2 hx'))
  simp [this]

theorem laplacian_hasCompactSupport {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) :
    HasCompactSupport (Δ χ) :=
  hχc.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacian_subset χ)

theorem integral_scale {χ : ℂ → ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∫ x, 2 * ε ^ 2 / (‖x‖ ^ 2 + ε ^ 2) ^ 2 * χ x =
      ∫ z, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z) := by
  have h1 := Measure.integral_comp_smul_of_nonneg (volume : Measure ℂ)
    (fun x => 2 * ε ^ 2 / (‖x‖ ^ 2 + ε ^ 2) ^ 2 * χ x) ε (hR := hε.le)
  have h2 : (fun z : ℂ => 2 * ε ^ 2 / (‖ε • z‖ ^ 2 + ε ^ 2) ^ 2 * χ (ε • z)) =
      fun z => (ε ^ 2)⁻¹ * (2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z)) := by
    funext z
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    field_simp
  rw [h2, integral_const_mul, Complex.finrank_real_complex, smul_eq_mul] at h1
  exact (mul_left_cancel₀ (by positivity) h1).symm

theorem abs_ureg_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {x : ℂ} (hx : x ≠ 0) :
    |ureg ε x| ≤ |Real.log ‖x‖| + Real.log (‖x‖ ^ 2 + 1) / 2 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have ha : Real.log ‖x‖ ≤ ureg ε x := by
    unfold ureg
    have : Real.log (‖x‖ ^ 2) ≤ Real.log (‖x‖ ^ 2 + ε ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hb : ureg ε x ≤ Real.log (‖x‖ ^ 2 + 1) / 2 := by
    unfold ureg
    have : Real.log (‖x‖ ^ 2 + ε ^ 2) ≤ Real.log (‖x‖ ^ 2 + 1) :=
      Real.log_le_log (by positivity) (by nlinarith)
    linarith
  have hb0 : 0 ≤ Real.log (‖x‖ ^ 2 + 1) / 2 := by
    have := Real.log_nonneg (show (1:ℝ) ≤ ‖x‖ ^ 2 + 1 by nlinarith); linarith
  rcases le_or_gt 0 (ureg ε x) with h | h
  · rw [abs_of_nonneg h]; linarith [abs_nonneg (Real.log ‖x‖)]
  · rw [abs_of_neg h]; linarith [neg_abs_le (Real.log ‖x‖)]

/-- **The fundamental solution**: `∫ log|x| Δχ = 2π χ(0)` for a `C²` test function. -/
theorem integral_log_norm_laplacian_zero {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) : ∫ x, Real.log ‖x‖ * Δ χ x = 2 * Real.pi * χ 0 := by
  set l : Filter ℝ := 𝓝[>] 0
  have hΔ := laplacian_continuous hχ
  have hΔc := laplacian_hasCompactSupport hχc
  -- equality for ε > 0
  have heq : ∀ᶠ ε in l, ∫ x, ureg ε x * Δ χ x = ∫ z, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε : 0 < ε := hε
    rw [integral_mul_laplacian isOpen_univ (ureg_contDiff hε).contDiffOn hχ hχc (subset_univ _)]
    simp_rw [laplacian_ureg hε]
    exact integral_scale hε
  -- right side limit
  have hint : Integrable (fun z : ℂ => 2 / (‖z‖ ^ 2 + 1) ^ 2) :=
    .of_integral_ne_zero (by rw [integral_radial]; positivity)
  obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  have T1 : Tendsto (fun ε : ℝ => ∫ z : ℂ, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z)) l
      (𝓝 (∫ z : ℂ, 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ 0)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun z : ℂ => 2 / (‖z‖ ^ 2 + 1) ^ 2 * C)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_) (hint.mul_const C) ?_
    · exact (Continuous.mul (show Continuous (fun z : ℂ => 2 / (‖z‖ ^ 2 + 1) ^ 2) by
          fun_prop (disch := (intro; positivity)))
        (hχ.continuous.comp (show Continuous (fun z : ℂ => ε • z) by fun_prop))).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
    · refine Eventually.of_forall fun z => ?_
      have hc : Continuous (fun ε : ℝ => 2 / (‖z‖ ^ 2 + 1) ^ 2 * χ (ε • z)) :=
        continuous_const.mul (hχ.continuous.comp (continuous_id.smul continuous_const))
      have := hc.tendsto 0
      simp only [zero_smul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
  rw [integral_mul_const, integral_radial] at T1
  -- left side limit
  have hbint : Integrable (fun x => |Real.log ‖x‖ * Δ χ x| + Real.log (‖x‖ ^ 2 + 1) / 2 * |Δ χ x|) := by
    refine (integrable_log_norm_mul hΔ hΔc).abs.add ?_
    exact (Continuous.mul (show Continuous (fun x : ℂ => Real.log (‖x‖ ^ 2 + 1) / 2) by
      fun_prop (disch := (intro; positivity))) hΔ.abs).integrable_of_hasCompactSupport
      hΔc.abs.mul_left
  have hae : ∀ᵐ x : ℂ, x ≠ 0 := by
    rw [ae_iff]; simp
  have T2 : Tendsto (fun ε : ℝ => ∫ x, ureg ε x * Δ χ x) l (𝓝 (∫ x, Real.log ‖x‖ * Δ χ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ hbint ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((ureg_contDiff hε).continuous.mul hΔ).aestronglyMeasurable
    · filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
      filter_upwards [hae] with x hx
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
      have := abs_ureg_le hε.1 hε.2 hx
      nlinarith [abs_nonneg (Δ χ x)]
    · filter_upwards [hae] with x hx
      have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have hc : ContinuousAt (fun ε : ℝ => ureg ε x * Δ χ x) 0 := by
        unfold ureg
        refine ContinuousAt.mul (ContinuousAt.div_const ?_ _) continuousAt_const
        exact (continuous_const.add (continuous_pow 2)).continuousAt.log (by simp; positivity)
      have := hc.tendsto
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      convert this using 2
      simp only [ureg]
      rw [show (0:ℝ) ^ 2 = 0 by norm_num, add_zero, Real.log_pow]; push_cast; ring
  have T1' := T1.congr' (EventuallyEq.symm heq)
  have := tendsto_nhds_unique T2 T1'
  rw [this]

/-- **The fundamental solution**: `∫ log|x - u| Δχ = 2π χ(u)`. -/
theorem integral_log_norm_sub_laplacian {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (u : ℂ) : ∫ x, Real.log ‖x - u‖ * Δ χ x = 2 * Real.pi * χ u := by
  set χu : ℂ → ℝ := fun x => χ (x + u)
  have h1 : ContDiff ℝ 2 χu := hχ.comp (contDiff_id.add contDiff_const)
  have h2 : HasCompactSupport χu := hχc.comp_homeomorph (Homeomorph.addRight u)
  have h3 : ∀ y, Δ χu y = Δ χ (y + u) := by
    intro y
    rw [laplacian_eq_iteratedFDeriv_complexPlane, laplacian_eq_iteratedFDeriv_complexPlane]
    simp only [χu, iteratedFDeriv_comp_add_right]
  have := integral_log_norm_laplacian_zero h1 h2
  simp only [h3, χu, zero_add] at this
  rw [← this, ← integral_add_right_eq_self (μ := volume) (fun x => Real.log ‖x - u‖ * Δ χ x) u]
  simp

end ValenceCocompact
