import VC.B5

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem no_lower_order {p q : ℂ → ℝ} {t : ℂ} (hp : ContinuousAt p t) (hpt : p t ≠ 0)
    (hq : ContinuousAt q t) {k : ℕ} (hk : 0 < k)
    (h : ∀ᶠ w in 𝓝[≠] t, p w = ‖w - t‖ ^ k * q w) : False := by
  have h1 : Tendsto p (𝓝[≠] t) (𝓝 (p t)) := hp.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun w => ‖w - t‖ ^ k * q w) (𝓝[≠] t) (𝓝 (‖t - t‖ ^ k * q t)) :=
    (((continuous_id.sub continuous_const).norm.pow k).continuousAt.mul hq).tendsto.mono_left
      nhdsWithin_le_nhds
  simp only [sub_self, norm_zero, zero_pow hk.ne', zero_mul] at h2
  exact hpt (tendsto_nhds_unique h1 (h2.congr' (EventuallyEq.symm h)))

/-- Two analytic functions whose norms agree up to a continuous nonvanishing factor have the same
order. -/
theorem ord_eq_of_norm {f g : ℂ → ℂ} {t : ℂ} (hf : AnalyticAt ℂ f t) (hg : AnalyticAt ℂ g t)
    {c : ℂ → ℝ} (hc : ContinuousAt c t) (hct : c t ≠ 0)
    (h : ∀ᶠ w in 𝓝 t, ‖f w‖ = c w * ‖g w‖) : analyticOrderAt f t = analyticOrderAt g t := by
  have hcev : ∀ᶠ w in 𝓝 t, c w ≠ 0 := hc.eventually_ne hct
  by_cases hgt : analyticOrderAt g t = ⊤
  · rw [hgt, analyticOrderAt_eq_top]
    filter_upwards [analyticOrderAt_eq_top.1 hgt, h] with w hw hw'
    rw [hw, norm_zero, mul_zero] at hw'
    exact norm_eq_zero.1 hw'
  by_cases hft : analyticOrderAt f t = ⊤
  · rw [hft, eq_comm, analyticOrderAt_eq_top]
    filter_upwards [analyticOrderAt_eq_top.1 hft, h, hcev] with w hw hw' hc'
    rw [hw, norm_zero] at hw'
    exact norm_eq_zero.1 ((mul_eq_zero.1 hw'.symm).resolve_left hc')
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.1 hft
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.1 hgt
  rw [← ha, ← hb]
  obtain ⟨f1, hf1, hf1t, hff⟩ := (hf.analyticOrderAt_eq_natCast).1 ha.symm
  obtain ⟨g1, hg1, hg1t, hgg⟩ := (hg.analyticOrderAt_eq_natCast).1 hb.symm
  have hrel : ∀ᶠ w in 𝓝 t, ‖w - t‖ ^ a * ‖f1 w‖ = c w * (‖w - t‖ ^ b * ‖g1 w‖) := by
    filter_upwards [h, hff, hgg] with w hw hfw hgw
    rw [hfw, hgw, norm_smul, norm_smul, norm_pow, norm_pow] at hw
    exact hw
  have hne : ∀ᶠ w in 𝓝[≠] t, ‖w - t‖ ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 hw)
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    refine no_lower_order (p := fun w => ‖f1 w‖) (q := fun w => c w * ‖g1 w‖)
      hf1.continuousAt.norm (norm_ne_zero_iff.2 hf1t) (hc.mul hg1.continuousAt.norm)
      (k := b - a) (Nat.sub_pos_of_lt hab) ?_
    filter_upwards [nhdsWithin_le_nhds hrel, hne] with w hw hw0
    have : ‖w - t‖ ^ b = ‖w - t‖ ^ a * ‖w - t‖ ^ (b - a) := by
      rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this] at hw
    have hpa : ‖w - t‖ ^ a ≠ 0 := pow_ne_zero _ hw0
    apply mul_left_cancel₀ hpa
    rw [hw]; ring
  · rw [hab]
  · exfalso
    refine no_lower_order (p := fun w => c w * ‖g1 w‖) (q := fun w => ‖f1 w‖)
      (hc.mul hg1.continuousAt.norm) (mul_ne_zero hct (norm_ne_zero_iff.2 hg1t))
      hf1.continuousAt.norm (k := a - b) (Nat.sub_pos_of_lt hab) ?_
    filter_upwards [nhdsWithin_le_nhds hrel, hne] with w hw hw0
    have : ‖w - t‖ ^ a = ‖w - t‖ ^ b * ‖w - t‖ ^ (a - b) := by
      rw [← pow_add, Nat.add_sub_cancel' hab.le]
    rw [this] at hw
    have hpa : ‖w - t‖ ^ b ≠ 0 := pow_ne_zero _ hw0
    apply mul_left_cancel₀ hpa
    rw [← mul_assoc, mul_comm (‖w - t‖ ^ b), mul_assoc, ← hw]; ring

/-- Orders are constant along `Γ`-orbits (norm automorphy suffices). -/
theorem ord_smul_eq {m : ℕ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F {w | 0 < w.im})
    {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (haut : ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) (t : UpperHalfPlane) :
    analyticOrderAt F ((γ • t : UpperHalfPlane) : ℂ) = analyticOrderAt F t := by
  have ht := t.im_pos
  have hd : deriv (mob γ) t ≠ 0 := by
    rw [(hasDerivAt_mob γ ht).deriv]
    exact div_ne_zero (by exact_mod_cast hγ.ne') (pow_ne_zero _ (denom_ne ht))
  rw [coe_smul_eq_mob hγ, ← analyticOrderAt_comp_of_deriv_ne_zero (analyticAt_mob γ ht) hd]
  have hmobt : 0 < (mob γ t).im := mob_im_pos hγ ht
  refine ord_eq_of_norm ((hF _ hmobt).comp (analyticAt_mob γ ht)) (hF _ ht)
    (c := fun w => ‖UpperHalfPlane.denom γ w‖ ^ (2 * m) / (γ : Matrix (Fin 2) (Fin 2) ℝ).det ^ m)
    ?_ ?_ ?_
  · refine ContinuousAt.div_const ?_ _
    unfold UpperHalfPlane.denom
    fun_prop
  · exact div_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.2 (denom_ne ht))) (pow_ne_zero _ hγ.ne')
  · have hU : {w : ℂ | 0 < w.im} ∈ 𝓝 (t : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds ht
    filter_upwards [hU] with w hw
    have := haut ⟨w, hw⟩
    rw [coe_smul_eq_mob hγ] at this
    simp only [Function.comp_apply]
    have hdp : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det ^ m := pow_pos hγ m
    field_simp
    exact this

end ValenceCocompact
