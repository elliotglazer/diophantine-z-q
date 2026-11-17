import VC.A2

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem abs_log_le (R r : ℝ) (hr0 : 0 < r) (hr : r < R) : |Real.log r| ≤ (1 + R ^ 2) * r⁻¹ := by
  rw [le_mul_inv_iff₀ hr0]
  rcases le_or_gt r 1 with h1 | h1
  · have := Real.abs_log_mul_self_lt r hr0 h1
    rw [abs_mul, abs_of_pos hr0] at this
    nlinarith
  · have hl : Real.log r ≤ r := (Real.log_le_sub_one_of_pos hr0).trans (by linarith)
    have hl0 : 0 ≤ Real.log r := Real.log_nonneg h1.le
    rw [abs_of_nonneg hl0]
    nlinarith

theorem integrableOn_log_norm_ball (R : ℝ) :
    IntegrableOn (fun x : ℂ => Real.log ‖x‖) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1 + R ^ 2) (α := 1) (by simp) (by simp) ?_ ?_
  · rw [ae_restrict_iff' measurableSet_ball]
    refine Eventually.of_forall fun x hx => ?_
    rw [mem_ball_zero_iff] at hx
    rw [Real.rpow_neg_one, Real.norm_eq_abs]
    rcases eq_or_lt_of_le (norm_nonneg x) with h | h
    · rw [← h]; simp
    · exact abs_log_le R ‖x‖ h hx
  · exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable

theorem locallyIntegrable_log_norm : LocallyIntegrable (fun x : ℂ => Real.log ‖x‖) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball 0
  exact (integrableOn_log_norm_ball R).mono_set hR

theorem integrable_log_norm_mul {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => Real.log ‖x‖ * g x) := by
  simpa [smul_eq_mul] using
    locallyIntegrable_log_norm.integrable_smul_right_of_hasCompactSupport hg hgc

theorem integral_radial : ∫ z : ℂ, 2 / (‖z‖ ^ 2 + 1) ^ 2 = 2 * Real.pi := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ) (fun y : ℝ => 2 / (y ^ 2 + 1) ^ 2)
  rw [h]
  have hball : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have key : ∫ y in Ioi (0:ℝ), y * (2 / (y ^ 2 + 1) ^ 2) = 1 := by
    have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (l := 0)
      (g := fun y : ℝ => -(y ^ 2 + 1)⁻¹) (g' := fun y : ℝ => y * (2 / (y ^ 2 + 1) ^ 2))
      (fun x _ => by
        have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
          simpa using (hasDerivAt_pow 2 x).add_const 1
        have := (h1.inv (by positivity)).neg
        convert this using 1
        field_simp)
      (fun x hx => by have : (0:ℝ) < x := hx; positivity)
      (by
        have : Tendsto (fun y : ℝ => y ^ 2 + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop (by norm_num))
        exact this.inv_tendsto_atTop.neg.congr (fun _ => rfl) |>.trans (by simp))
    rw [this]; norm_num
  have hI : ∫ y in Ioi (0:ℝ), y ^ (Module.finrank ℝ ℂ - 1) • (2 / (y ^ 2 + 1) ^ 2) = 1 := by
    simp only [Complex.finrank_real_complex, smul_eq_mul]
    simpa using key
  rw [hI, hball, Complex.finrank_real_complex]; simp

end ValenceCocompact
