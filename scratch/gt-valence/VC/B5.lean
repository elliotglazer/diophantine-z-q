import VC.B4

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

/-- The invariant `log (|F| y^m)`. -/
def PhiF (m : ℕ) (F : ℂ → ℂ) (w : ℂ) : ℝ := Real.log (‖F w‖ * w.im ^ m)

theorem phiF_invariant {m : ℕ} {F : ℂ → ℂ} {γ : GL (Fin 2) ℝ}
    (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) (z : UpperHalfPlane)
    (haut : ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) :
    PhiF m F ((γ • z : UpperHalfPlane) : ℂ) = PhiF m F z := by
  unfold PhiF
  congr 1
  have him : ((γ • z : UpperHalfPlane) : ℂ).im = (γ : Matrix (Fin 2) (Fin 2) ℝ).det * (z : ℂ).im /
      ‖UpperHalfPlane.denom γ z‖ ^ 2 := by
    rw [UpperHalfPlane.coe_im, UpperHalfPlane.im_smul_eq_div_normSq, det_val_eq, abs_of_pos hγ,
      Complex.sq_norm]
    rfl
  have hd : 0 < ‖UpperHalfPlane.denom γ z‖ := norm_pos_iff.2 (UpperHalfPlane.denom_ne_zero γ z)
  rw [him, div_pow, mul_pow, ← pow_mul]
  have hd2 : 0 < ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) := pow_pos hd _
  field_simp
  linear_combination haut

theorem codiscrete_ne_zero {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0) :
    {w | F w ≠ 0} ∈ codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  filter_upwards [zeros_isolated hU hF hne hx] with w hw
  intro h
  exact h.2 hw

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- **The valence identity** `2π Σ ord_ρ χ(ρ) = m vol(s)` for the partition function `χ`. -/
theorem main_identity {s : Set UpperHalfPlane} (hs : IsFundDomain Γ s) {m : ℕ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {w | 0 < w.im}) (hne : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0)
    (haut : ∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ {w | 0 < w.im}) (hχ0 : ∀ w, 0 ≤ χ w)
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1) :
    volume s ≠ ⊤ ∧
      2 * Real.pi * ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w = m * (volume s).toReal := by
  have hUo : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨hint1, hR⟩ := integral_log_norm_analytic hUo hUc hF hne hχ hχc hχU
  have hΔ := laplacian_continuous hχ
  have hΔc := laplacian_hasCompactSupport hχc
  have hΔU : tsupport (Δ χ) ⊆ {w | 0 < w.im} := (tsupport_laplacian_subset χ).trans hχU
  have hlogim : ContDiffOn ℝ 2 (fun w : ℂ => Real.log w.im) {w | 0 < w.im} := fun w hw =>
    ((Complex.imCLM.contDiff.contDiffAt).log (ne_of_gt hw)).contDiffWithinAt
  have hint2 : Integrable fun w : ℂ => Real.log w.im * Δ χ w :=
    integrable_mul_of hUo hlogim.continuousOn hΔ hΔc hΔU
  -- a.e. decomposition of the invariant
  have hae0 : ∀ᵐ w : ℂ, w ∈ {w : ℂ | 0 < w.im} → F w ≠ 0 := by
    have : ∀ᵐ w ∂(volume.restrict {w : ℂ | 0 < w.im}), F w ≠ 0 :=
      ae_restrict_le_codiscreteWithin (μ := (volume : Measure ℂ)) hUo.measurableSet
        (codiscrete_ne_zero hUc hF hne)
    rwa [ae_restrict_iff' hUo.measurableSet] at this
  have hdec : (fun w => PhiF m F w * Δ χ w) =ᵐ[volume]
      fun w => Real.log ‖F w‖ * Δ χ w + m * (Real.log w.im * Δ χ w) := by
    filter_upwards [hae0] with w hw
    by_cases hwU : 0 < w.im
    · have h1 := hw hwU
      unfold PhiF
      rw [Real.log_mul (norm_ne_zero_iff.2 h1) (pow_ne_zero _ hwU.ne'), Real.log_pow]
      ring
    · rw [tsupport_laplacian_subset_U hχU w (not_lt.1 hwU)]; ring
  have hint : Integrable fun w => PhiF m F w * Δ χ w :=
    (hint1.add (hint2.const_mul _)).congr hdec.symm
  -- invariance
  have hΦ : ∀ (g : permG (subG hΓ)) (z : UpperHalfPlane),
      PhiF m F ((g • z : UpperHalfPlane) : ℂ) = PhiF m F z := by
    intro g z
    rw [rep_smul]
    exact phiF_invariant (rep_det hΓ g) z (haut _ (rep_memΓ hΓ g) z)
  have h0 := integral_invariant_laplacian hΓ hΦ hχ hχc hχU hsum hint
  rw [integral_congr_ae hdec, integral_add hint1 (hint2.const_mul _), integral_const_mul, hR] at h0
  -- the log Im term
  have hlog : ∫ w, Real.log w.im * Δ χ w = - ∫ w, χ w / w.im ^ 2 := by
    rw [integral_mul_laplacian hUo hlogim hχ hχc hχU, ← integral_neg]
    congr 1; funext w
    by_cases hw : χ w = 0
    · simp [hw]
    · have hwU : 0 < w.im := hχU (subset_tsupport _ hw)
      rw [laplacian_log_im hwU]; ring
  -- the volume
  have hvan : ∀ w : ℂ, w.im ≤ 0 → χ w / w.im ^ 2 = 0 := fun w hw => by
    rw [image_eq_zero_of_notMem_tsupport (fun h => (not_lt.2 hw) (hχU h)), zero_div]
  have hcH := integral_H (fun w => χ w / w.im ^ 2) hvan
  have he : ∀ z : UpperHalfPlane, χ z / (z : ℂ).im ^ 2 * (z : ℂ).im ^ 2 = χ z := fun z => by
    have : (z : ℂ).im ≠ 0 := ne_of_gt z.im_pos
    field_simp
  simp_rw [he] at hcH
  have hcont : ContinuousOn (fun w : ℂ => 1 / w.im ^ 2) {w | 0 < w.im} := fun w hw =>
    (continuousAt_const.div (Complex.continuous_im.continuousAt.pow 2)
      (pow_ne_zero _ (ne_of_gt hw))).continuousWithinAt
  have hχint : Integrable fun w : ℂ => χ w / w.im ^ 2 := by
    have := integrable_mul_of hUo hcont hχ.continuous hχc hχU
    refine this.congr (Eventually.of_forall fun w => ?_)
    simp only; ring
  have hχH : Integrable fun z : UpperHalfPlane => χ z := by
    have := integrable_H hvan hχint
    exact this.congr (Eventually.of_forall he)
  have hL := lintegral_chi hΓ hs hχ.continuous hχc hχU hχ0 hsum
  have hfin : volume s ≠ ⊤ := by
    rw [← hL]; exact (hχH.lintegral_lt_top).ne
  have hvol : ∫ z : UpperHalfPlane, χ z = (volume s).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => hχ0 _)
      (hχ.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable, hL]
  refine ⟨hfin, ?_⟩
  rw [hlog, ← hcH, hvol] at h0
  linarith

end ValenceCocompact
