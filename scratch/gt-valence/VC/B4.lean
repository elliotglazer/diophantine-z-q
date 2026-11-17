import VC.B3

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem laplacian_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℝ) (x : ℂ)
    (hf : ∀ i ∈ S, ContDiffAt ℝ 2 (f i) x) :
    Δ (fun w => ∑ i ∈ S, f i w) x = ∑ i ∈ S, Δ (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [show (fun _ : ℂ => (0:ℝ)) = fun _ => (0:ℝ) from rfl, laplacian_const]; rfl
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : ContDiffAt ℝ 2 (f a) x := hf a (Finset.mem_insert_self a S)
    have h2 : ContDiffAt ℝ 2 (fun w => ∑ i ∈ S, f i w) x :=
      ContDiffAt.sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have := h1.laplacian_add h2
    rw [show (fun w => f a w + ∑ i ∈ S, f i w) = f a + fun w => ∑ i ∈ S, f i w from rfl, this,
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

theorem tsupport_laplacian_subset_U {χ : ℂ → ℝ} (hχU : tsupport χ ⊆ {w | 0 < w.im}) (w : ℂ)
    (hw : w.im ≤ 0) : Δ χ w = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    (not_lt.2 hw) (hχU (tsupport_laplacian_subset χ h))

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- **The key cancellation**: for a `Γ`-invariant `Φ` with `ΦΔχ` integrable, `∫ Φ Δχ = 0`. -/
theorem integral_invariant_laplacian {Φ : ℂ → ℝ}
    (hΦ : ∀ (g : permG (subG hΓ)) (z : UpperHalfPlane), Φ ((g • z : UpperHalfPlane) : ℂ) = Φ z)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1)
    (hint : Integrable fun w => Φ w * Δ χ w) :
    ∫ w, Φ w * Δ χ w = 0 := by
  have hvan : ∀ w : ℂ, w.im ≤ 0 → Φ w * Δ χ w = 0 := fun w hw => by
    rw [tsupport_laplacian_subset_U hχU w hw, mul_zero]
  have hconv := (integral_H (fun w => Φ w * Δ χ w) hvan).symm
  have ha := integrable_H hvan hint
  rw [hconv]
  set a : UpperHalfPlane → ℝ := fun z => Φ z * Δ χ z * (z : ℂ).im ^ 2 with ha_def
  -- a compact neighbourhood of the support
  have hUo : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hχc hUo hχU
  set K' : Set UpperHalfPlane := (↑) ⁻¹' closure V
  have hK' : IsCompact K' := isCompact_preimage_coe hVc hVU
  obtain ⟨S, hS⟩ := locally_finite hΓ hχc hχU hK'
  have hS1 : ∀ z ∈ K', ∑ g ∈ S, χ ((g • z : UpperHalfPlane) : ℂ) = 1 := fun z hz => by
    rw [← finsum_eq_sum hΓ hχc hχU hS hz, hsum]
  have hS2 : ∀ z ∈ K', ∑ g ∈ S, χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) = 1 := fun z hz => by
    have h1 : ∑ᶠ g : permG (subG hΓ), χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) = 1 := by
      rw [← hsum z]
      exact finsum_comp_equiv (Equiv.inv _) (f := fun g => χ ((g • z : UpperHalfPlane) : ℂ))
    rw [← h1]
    exact (finsum_eq_sum_of_support_subset _ fun g hg => (hS z hz g).2 hg).symm
  have hχb : ∃ C, ∀ w, ‖χ w‖ ≤ C := hχ.continuous.bounded_above_of_compact_support hχc
  obtain ⟨C, hC⟩ := hχb
  have hmeasg : ∀ g : permG (subG hΓ), AEStronglyMeasurable
      (fun z : UpperHalfPlane => χ ((g • z : UpperHalfPlane) : ℂ)) volume := fun g =>
    (hχ.continuous.measurable.comp (UpperHalfPlane.measurable_coe.comp
      (measurable_const_smul g))).aestronglyMeasurable
  -- step (i)-(ii)
  have e1 : ∀ z, a z = ∑ g ∈ S, a z * χ ((g • z : UpperHalfPlane) : ℂ) := by
    intro z
    rw [← Finset.mul_sum]
    by_cases hz : (z : ℂ) ∈ tsupport χ
    · rw [hS1 z (subset_closure (hKV hz)), mul_one]
    · have : Δ χ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hz (tsupport_laplacian_subset χ h))
      simp [ha_def, this]
  have hint1 : ∀ g ∈ S, Integrable fun z => a z * χ ((g • z : UpperHalfPlane) : ℂ) :=
    fun g _ => ha.mul_bdd (hmeasg g) (Eventually.of_forall fun z => hC _)
  rw [integral_congr_ae (Eventually.of_forall e1), integral_finsetSum _ hint1]
  -- step (iii)-(iv)
  have e2 : ∀ g : permG (subG hΓ), ∀ z : UpperHalfPlane,
      a (g⁻¹ • z) * χ z = Φ z * χ z * ((z : ℂ).im ^ 2 * Δ (χ ∘ mob (rep g⁻¹)) z) := by
    intro g z
    have hdet := rep_det hΓ g⁻¹
    rw [im_sq_laplacian_comp_mob hdet hχ z.im_pos]
    simp only [ha_def]
    rw [hΦ g⁻¹ z, rep_smul g⁻¹ z, coe_smul_eq_mob hdet]
    ring
  have e3 : ∀ g : permG (subG hΓ),
      ∫ z, a z * χ ((g • z : UpperHalfPlane) : ℂ) =
        ∫ z : UpperHalfPlane, Φ z * χ z * ((z : ℂ).im ^ 2 * Δ (χ ∘ mob (rep g⁻¹)) z) := by
    intro g
    have := integral_smul_eq_self (μ := (volume : Measure UpperHalfPlane))
      (fun z => a (g⁻¹ • z) * χ z) (g := g)
    simp only [inv_smul_smul] at this
    rw [this]
    exact integral_congr_ae (Eventually.of_forall fun z => e2 g z)
  simp_rw [e3]
  have hint2 : ∀ g ∈ S, Integrable fun z : UpperHalfPlane =>
      Φ z * χ z * ((z : ℂ).im ^ 2 * Δ (χ ∘ mob (rep g⁻¹)) z) := by
    intro g _
    have h1 : Integrable fun z : UpperHalfPlane => a (g⁻¹ • z) :=
      ((measurePreserving_smul g⁻¹ volume).integrable_comp ha.aestronglyMeasurable).2 ha
    have h2 := h1.mul_bdd (hχ.continuous.measurable.comp
      UpperHalfPlane.measurable_coe).aestronglyMeasurable (Eventually.of_forall fun z => hC z)
    exact h2.congr (Eventually.of_forall fun z => e2 g z)
  rw [← integral_finsetSum _ hint2]
  -- step (v)-(vi)
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.zero_apply]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  by_cases hz : χ z = 0
  · simp [hz]
  · have hzV : (z : ℂ) ∈ V := hKV (subset_tsupport _ hz)
    have hsumΔ : ∑ g ∈ S, Δ (χ ∘ mob (rep g⁻¹)) z = 0 := by
      rw [← laplacian_finset_sum S (fun g => χ ∘ mob (rep g⁻¹)) z
        (fun g _ => hχ.contDiffAt.comp _
          ((analyticAt_mob _ z.im_pos).contDiffAt.restrict_scalars ℝ))]
      have hev : (fun w => ∑ g ∈ S, (χ ∘ mob (rep g⁻¹)) w) =ᶠ[𝓝 (z : ℂ)] fun _ => (1 : ℝ) := by
        filter_upwards [hVo.mem_nhds hzV] with w hw
        have hwim : 0 < w.im := hVU (subset_closure hw)
        have := hS2 ⟨w, hwim⟩ (subset_closure hw : w ∈ closure V)
        rw [← this]
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [Function.comp_apply]
        rw [rep_smul_coe hΓ g⁻¹ hwim]
      rw [(laplacian_congr_nhds hev).eq_of_nhds, laplacian_const]; rfl
    rw [hsumΔ]; ring

end ValenceCocompact
