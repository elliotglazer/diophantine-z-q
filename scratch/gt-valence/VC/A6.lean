import VC.A5

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem bilin_rot' (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (α β : ℝ) :
    B (α • (1:ℂ) + β • I) (α • (1:ℂ) + β • I) + B ((-β) • (1:ℂ) + α • I) ((-β) • (1:ℂ) + α • I) =
      (α ^ 2 + β ^ 2) * (B 1 1 + B I I) := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

theorem bilin_rot (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    B a a + B (a * I) (a * I) = ‖a‖ ^ 2 * (B 1 1 + B I I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • I := by apply Complex.ext <;> simp
  have haI : a * I = (-a.im) • (1 : ℂ) + a.re • I := by apply Complex.ext <;> simp
  have hn : ‖a‖ ^ 2 = a.re ^ 2 + a.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [haI, hn]
  have := bilin_rot' B a.re a.im
  rw [← ha] at this
  exact this

theorem fderiv_real_of_complex {φ : ℂ → ℂ} {y : ℂ} (h : DifferentiableAt ℂ φ y) (v : ℂ) :
    HasFDerivAt φ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv φ y)).restrictScalars ℝ) y
    ∧ ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv φ y)).restrictScalars ℝ) v =
      deriv φ y * v := by
  refine ⟨h.hasDerivAt.hasFDerivAt.restrictScalars ℝ, ?_⟩
  simp [mul_comm]

/-- `d2 (χ ∘ φ) v z` for `φ` holomorphic. -/
theorem d2_comp {χ : ℂ → ℝ} {φ : ℂ → ℂ} {z : ℂ} (hφ : AnalyticAt ℂ φ z)
    (hχ : ContDiffAt ℝ 2 χ (φ z)) (v : ℂ) :
    d2 (χ ∘ φ) v z = fderiv ℝ χ (φ z) (deriv (deriv φ) z * v * v) +
      fderiv ℝ (fderiv ℝ χ) (φ z) (deriv φ z * v) (deriv φ z * v) := by
  have hφev : ∀ᶠ y in 𝓝 z, AnalyticAt ℂ φ y := hφ.eventually_analyticAt
  have hχev : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 χ (φ y) :=
    hφ.continuousAt.eventually (hχ.eventually (by simp))
  have hev : (fun y => fderiv ℝ (χ ∘ φ) y v) =ᶠ[𝓝 z]
      fun y => fderiv ℝ χ (φ y) (deriv φ y * v) := by
    filter_upwards [hφev, hχev] with y hy1 hy2
    obtain ⟨hL, hLv⟩ := fderiv_real_of_complex hy1.differentiableAt v
    have hχy : HasFDerivAt χ (fderiv ℝ χ (φ y)) (φ y) :=
      (hy2.differentiableAt (by norm_num)).hasFDerivAt
    rw [(hχy.comp y hL).fderiv]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hLv]
  unfold d2
  rw [hev.fderiv_eq]
  -- derivative of y ↦ fderiv χ (φ y)
  obtain ⟨hLz, hLzv⟩ := fderiv_real_of_complex hφ.differentiableAt v
  have hd2 : DifferentiableAt ℝ (fderiv ℝ χ) (φ z) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hG : HasFDerivAt (fun y => fderiv ℝ χ (φ y)) _ z := hd2.hasFDerivAt.comp z hLz
  -- derivative of y ↦ deriv φ y * v
  have hφ' : AnalyticAt ℂ (deriv φ) z := hφ.deriv
  have hH : HasDerivAt (fun y => deriv φ y * v) (deriv (deriv φ) z * v) z :=
    hφ'.differentiableAt.hasDerivAt.mul_const v
  obtain ⟨hHf, hHv⟩ := fderiv_real_of_complex (φ := fun y => deriv φ y * v)
    hH.differentiableAt v
  rw [hH.deriv] at hHf hHv
  have := (hG.clm_apply hHf).fderiv
  rw [this]
  simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.flip_apply]
  rw [hHv, hLzv]

/-- **Conformal invariance of the Laplacian**: `Δ(χ ∘ φ)(z) = |φ'(z)|² (Δχ)(φ z)` for `φ` holomorphic. -/
theorem laplacian_comp_holomorphic {χ : ℂ → ℝ} {φ : ℂ → ℂ} {z : ℂ} (hφ : AnalyticAt ℂ φ z)
    (hχ : ContDiffAt ℝ 2 χ (φ z)) :
    Δ (χ ∘ φ) z = ‖deriv φ z‖ ^ 2 * Δ χ (φ z) := by
  have hc : ContDiffAt ℝ 2 (χ ∘ φ) z :=
    hχ.comp z (hφ.contDiffAt.restrict_scalars ℝ)
  rw [laplacian_eq_d2 hc, d2_comp hφ hχ, d2_comp hφ hχ, laplacian_eq_d2 hχ]
  rw [d2, d2]
  have hd2 : DifferentiableAt ℝ (fderiv ℝ χ) (φ z) :=
    (hχ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd2 (differentiableAt_const 1), fderiv_clm_apply hd2 (differentiableAt_const I)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, add_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply]
  have hrot := bilin_rot (fderiv ℝ (fderiv ℝ χ) (φ z)) (deriv φ z)
  have h1 : deriv (deriv φ) z * 1 * 1 = - (deriv (deriv φ) z * I * I) := by
    rw [mul_assoc, mul_assoc, I_mul_I]; ring
  rw [h1, map_neg, mul_one]
  linear_combination hrot

end ValenceCocompact
