import VC.A4

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric

namespace ValenceCocompact

theorem integrable_log_norm_sub_mul {g : ℂ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : ℂ) : Integrable (fun x => Real.log ‖x - u‖ * g x) := by
  have h := integrable_log_norm_mul (g := fun y => g (y + u)) (hg.comp (continuous_id.add continuous_const))
    (hgc.comp_homeomorph (Homeomorph.addRight u))
  have := h.comp_sub_right u
  simpa using this

/-- Harmonic functions integrate to zero against `Δχ`. -/
theorem integral_log_norm_nonvanishing {g : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hg : AnalyticOnNhd ℂ g V) (hg0 : ∀ u ∈ V, g u ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) :
    ∫ x, Real.log ‖g x‖ * Δ χ x = 0 := by
  have hH : ∀ x ∈ V, InnerProductSpace.HarmonicAt (fun z => Real.log ‖g z‖) x :=
    fun x hx => (hg x hx).harmonicAt_log_norm (hg0 x hx)
  have hC : ContDiffOn ℝ 2 (fun z => Real.log ‖g z‖) V :=
    fun x hx => (hH x hx).1.contDiffWithinAt
  rw [integral_mul_laplacian hV hC hχ hχc hχV]
  have : ∀ x, Δ (fun z => Real.log ‖g z‖) x * χ x = 0 := by
    intro x
    by_cases hx : χ x = 0
    · simp [hx]
    · have hxV : x ∈ V := hχV (subset_tsupport _ hx)
      rw [(hH x hxV).2.eq_of_nhds]; simp
  simp [this]

/-- Zeros of a nonzero analytic function on a preconnected open set are isolated. -/
theorem zeros_isolated {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (hne : ∃ z ∈ U, F z ≠ 0) {z : ℂ} (hz : z ∈ U) : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 := by
  rcases (hF z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    obtain ⟨w, hw, hFw⟩ := hne
    exact hFw (hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz h hw)
  · exact h

theorem order_ne_top {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (hne : ∃ z ∈ U, F z ≠ 0) {z : ℂ} (hz : z ∈ U) : analyticOrderAt F z ≠ ⊤ := by
  obtain ⟨w, hw, hFw⟩ := hne
  exact hF.analyticOrderAt_ne_top_of_isPreconnected hU hw hz
    (by rw [analyticOrderAt_eq_zero.2 (Or.inr hFw)]; simp)

/-- **Riesz decomposition of `log |F|`** (the distributional Laplacian of `log|F|` is `2π Σ ord_ρ δ_ρ`):
for `F` analytic and not identically zero on a preconnected open `U` and a `C²` test function `χ`
supported in `U`, `∫ log|F| Δχ = 2π Σ_ρ ord_ρ(F) χ(ρ)`; also the integrand is integrable. -/
theorem integral_log_norm_analytic {F : ℂ → ℂ} {U : Set ℂ} (hUo : IsOpen U) (hU : IsPreconnected U)
    (hF : AnalyticOnNhd ℂ F U) (hne : ∃ z ∈ U, F z ≠ 0) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    Integrable (fun x => Real.log ‖F x‖ * Δ χ x) ∧
    ∫ x, Real.log ‖F x‖ * Δ χ x =
      2 * Real.pi * ∑ᶠ z, ((analyticOrderAt F z).toNat : ℝ) * χ z := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hχc hUo hχU
  have hFV : MeromorphicOn F V := fun x hx => (hF x (hVU (subset_closure hx))).meromorphicAt
  have hFcl : MeromorphicOn F (closure V) := fun x hx => (hF x (hVU hx)).meromorphicAt
  have hfin : (MeromorphicOn.divisor F V).support.Finite :=
    hFcl.divisor_support_finite_of_subset hVc subset_closure
  have hord : ∀ u : V, meromorphicOrderAt F u ≠ ⊤ := by
    intro u
    rw [(hF u (hVU (subset_closure u.2))).meromorphicOrderAt_eq]
    have := order_ne_top hU hF hne (hVU (subset_closure u.2))
    revert this
    cases analyticOrderAt F u <;> simp
  obtain ⟨g, hg, hg0, hfg⟩ := hFV.extract_zeros_poles hord hfin
  have hlog := MeromorphicOn.extract_zeros_poles_log hg0 hfg
  set D := MeromorphicOn.divisor F V
  set S := hfin.toFinset
  -- evaluate the finsum of functions
  have hsum : ∀ x, (∑ᶠ u, (fun z => (D u : ℝ) * Real.log ‖z - u‖)) x =
      ∑ u ∈ S, (D u : ℝ) * Real.log ‖x - u‖ := by
    intro x
    rw [finsum_eq_sum_of_support_subset _ (s := S)]
    · rw [Finset.sum_apply]
    · intro u hu
      simp only [S, Set.Finite.coe_toFinset, Function.mem_support]
      intro h; apply hu; simp [h]; rfl
  -- a.e. equality on V
  have hae : ∀ᵐ x, x ∈ V → Real.log ‖F x‖ = ∑ u ∈ S, (D u : ℝ) * Real.log ‖x - u‖ +
      Real.log ‖g x‖ := by
    have h1 : ∀ᵐ x ∂(volume.restrict V), Real.log ‖F x‖ =
        ((∑ᶠ u, fun z => (D u : ℝ) * Real.log ‖z - u‖) + fun z => Real.log ‖g z‖) x :=
      ae_restrict_le_codiscreteWithin hVo.measurableSet hlog
    rw [ae_restrict_iff' hVo.measurableSet] at h1
    filter_upwards [h1] with x hx hxV
    have := hx hxV
    simp only [Pi.add_apply] at this
    rw [this, hsum]
  have hΔ := laplacian_continuous hχ
  have hΔc := laplacian_hasCompactSupport hχc
  have hΔV : tsupport (Δ χ) ⊆ V := (tsupport_laplacian_subset χ).trans hKV
  have heq : (fun x => Real.log ‖F x‖ * Δ χ x) =ᵐ[volume]
      fun x => ∑ u ∈ S, (D u : ℝ) * (Real.log ‖x - u‖ * Δ χ x) + Real.log ‖g x‖ * Δ χ x := by
    filter_upwards [hae] with x hx
    by_cases hxV : x ∈ V
    · rw [hx hxV, add_mul, Finset.sum_mul]
      simp only [mul_assoc]
    · have : Δ χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxV (hΔV h))
      simp [this]
  have hgint : Integrable (fun x => Real.log ‖g x‖ * Δ χ x) := by
    have hc : ContinuousOn (fun x => Real.log ‖g x‖) V :=
      fun x hx => ((hg x hx).continuousAt.norm.log (by simpa using hg0 ⟨x, hx⟩)).continuousWithinAt
    exact integrable_mul_of hVo hc hΔ hΔc hΔV
  have hsint : ∀ u ∈ S, Integrable (fun x => (D u : ℝ) * (Real.log ‖x - u‖ * Δ χ x)) :=
    fun u _ => (integrable_log_norm_sub_mul hΔ hΔc u).const_mul _
  refine ⟨(Integrable.add (integrable_finsetSum _ hsint) hgint).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add (integrable_finsetSum _ hsint) hgint,
    integral_finsetSum _ hsint,
    integral_log_norm_nonvanishing hVo hg (fun u hu => hg0 ⟨u, hu⟩) hχ hχc hKV, add_zero]
  simp_rw [integral_const_mul, integral_log_norm_sub_laplacian hχ hχc]
  rw [finsum_eq_sum_of_support_subset _ (s := S), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun u hu => ?_
    have huV : u ∈ V := D.supportWithinDomain (by simpa [S] using hu)
    have hD : (D u : ℝ) = ((analyticOrderAt F u).toNat : ℝ) := by
      simp only [D]
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hF.mono (subset_closure.trans hVU)) huV]
      have := order_ne_top hU hF hne (hVU (subset_closure huV))
      revert this
      cases analyticOrderAt F u <;> simp
    rw [hD]; ring
  · intro u hu
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hu
    have huV : u ∈ V := hKV (subset_tsupport _ hu.2)
    simp only [Set.Finite.coe_toFinset, Function.mem_support, S, D]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hF.mono (subset_closure.trans hVU)) huV]
    have := order_ne_top hU hF hne (hVU (subset_closure huV))
    have h1 := hu.1
    revert this h1
    cases analyticOrderAt F u <;> simp

end ValenceCocompact
