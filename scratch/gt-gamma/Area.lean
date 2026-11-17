import Mathlib

/-! gt-gamma: the hyperbolic area of the triangle `T` (calculus part). -/

noncomputable section

namespace HDec.GammaStarArea.AreaCalc

open Real

/-- `L = 1 + √2`, `k = 9 + 6√2`. -/
def LL : ℝ := 1 + √2
def kk : ℝ := 9 + 6 * √2

/-- `h(x) = 1/√(3 + 6|x| − x²) − 1/√(k − x²)`: the `y`-integral of `dy/y²` over the vertical section of `T`. -/
def hc (x : ℝ) : ℝ := 1 / √(3 + 6 * |x| - x ^ 2) - 1 / √(kk - x ^ 2)

theorem s2_sq : √2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
theorem s3_sq : √3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
theorem s2_pos : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
theorem s3_pos : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
theorem s2_lt : √2 < (3 / 2 : ℝ) := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num
theorem s2_gt : (1 : ℝ) < √2 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

theorem LL_pos : 0 < LL := by unfold LL; linarith [s2_pos]
theorem LL_lt : LL < 3 := by unfold LL; linarith [s2_lt]

theorem kk_sub_pos {x : ℝ} (hx : |x| ≤ LL) : 0 < kk - x ^ 2 := by
  have h1 : x ^ 2 ≤ LL ^ 2 := by
    have := abs_nonneg x
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ LL ^ 2 := by gcongr
  unfold kk; unfold LL at h1; nlinarith [s2_sq, s2_pos]

theorem lo_pos {x : ℝ} (hx : |x| ≤ LL) : 0 < 3 + 6 * |x| - x ^ 2 := by
  have h0 := abs_nonneg x
  have h1 := LL_lt
  have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  nlinarith

theorem hc_neg (x : ℝ) : hc (-x) = hc x := by simp [hc, abs_neg]

theorem hc_cont : ContinuousOn hc (Set.Icc (-LL) LL) := by
  intro x hx
  have hx' : |x| ≤ LL := abs_le.2 hx
  apply ContinuousAt.continuousWithinAt
  unfold hc
  apply ContinuousAt.sub
  · apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact (Real.sqrt_pos.2 (lo_pos hx')).ne'
  · apply ContinuousAt.div continuousAt_const (by fun_prop)
    exact (Real.sqrt_pos.2 (kk_sub_pos hx')).ne'

/-- `√k = √3 (1 + √2)`. -/
theorem sqrt_kk : √kk = √3 * LL := by
  have : kk = (√3 * LL) ^ 2 := by
    unfold kk LL; rw [mul_pow, s3_sq]; nlinarith [s2_sq]
  rw [this, Real.sqrt_sq (by have := s3_pos; have := LL_pos; positivity)]

theorem arcsin_sqrt3_half : arcsin (√3 / 2) = π / 3 := by
  rw [← Real.sin_pi_div_three, Real.arcsin_sin] <;> linarith [Real.pi_pos]

/-- `arcsin((√2 − 2)/(2√3)) = arcsin(1/√3) − π/4`. -/
theorem arcsin_key : arcsin ((√2 - 2) / (2 * √3)) = arcsin (1 / √3) - π / 4 := by
  set a := arcsin (1 / √3)
  have h3 := s3_pos
  have hb : 1 / √3 ≤ 1 := by
    rw [div_le_one h3]; rw [Real.le_sqrt' one_pos]; norm_num
  have hb' : -1 ≤ 1 / √3 := by linarith [show (0 : ℝ) ≤ 1 / √3 by positivity]
  have hsa : sin a = 1 / √3 := Real.sin_arcsin hb' hb
  have hca : cos a = √(1 - (1 / √3) ^ 2) := Real.cos_arcsin _
  have hc2 : √(1 - (1 / √3) ^ 2) = √2 / √3 := by
    rw [show 1 - (1 / √3) ^ 2 = 2 / 3 by rw [div_pow, s3_sq]; norm_num, Real.sqrt_div' 2 (by norm_num : (0:ℝ) ≤ 3)]
  have hsin : sin (a - π / 4) = (√2 - 2) / (2 * √3) := by
    rw [Real.sin_sub, hsa, hca, hc2, Real.cos_pi_div_four, Real.sin_pi_div_four]
    field_simp
    nlinarith [s2_sq]
  have ha0 : 0 ≤ a := Real.arcsin_nonneg.2 (by positivity)
  have ha1 : a ≤ π / 2 := Real.arcsin_le_pi_div_two _
  rw [← hsin, Real.arcsin_sin] <;> linarith [Real.pi_pos]

theorem hasDerivAt_F {x : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ LL) :
    HasDerivAt (fun x => arcsin ((x - 3) / (2 * √3)) - arcsin (x / √kk)) (hc x) x := by
  have h3 := s3_pos
  have hk := kk_sub_pos (x := x) (by rw [abs_of_nonneg hx0]; exact hxL)
  have hk0 : 0 < kk := by unfold kk; linarith [s2_pos]
  have hsk : 0 < √kk := Real.sqrt_pos.2 hk0
  have hL3 := LL_lt
  -- the arguments stay in `(-1, 1)`
  have hu1 : -1 < (x - 3) / (2 * √3) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [s3_sq, Real.sqrt_nonneg 3, show (3 / 2 : ℝ) < √3 by rw [Real.lt_sqrt (by norm_num)]; norm_num]
  have hu2 : (x - 3) / (2 * √3) < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hv1 : -1 < x / √kk := by
    have : 0 ≤ x / √kk := by positivity
    linarith
  have hv2 : x / √kk < 1 := by
    rw [div_lt_one hsk, Real.lt_sqrt hx0]; linarith
  have hu : HasDerivAt (fun x : ℝ => (x - 3) / (2 * √3)) (1 / (2 * √3)) x :=
    ((hasDerivAt_id x).sub_const 3).div_const _
  have hv : HasDerivAt (fun x : ℝ => x / √kk) (1 / √kk) x := (hasDerivAt_id x).div_const _
  have hA := (Real.hasDerivAt_arcsin hu1.ne' hu2.ne).comp x hu
  have hB := (Real.hasDerivAt_arcsin hv1.ne' hv2.ne).comp x hv
  refine (hA.sub hB).congr_deriv ?_
  unfold hc
  rw [abs_of_nonneg hx0]
  congr 1
  · have hw : 0 ≤ 1 - ((x - 3) / (2 * √3)) ^ 2 := by nlinarith
    have e : √(1 - ((x - 3) / (2 * √3)) ^ 2) * (2 * √3) = √(3 + 6 * x - x ^ 2) := by
      have hsq : (√(1 - ((x - 3) / (2 * √3)) ^ 2) * (2 * √3)) ^ 2 = 3 + 6 * x - x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw, mul_pow, div_pow, mul_pow, s3_sq]; field_simp; ring
      rw [← hsq, Real.sqrt_sq (by positivity)]
    rw [← e]; field_simp
  · have hw : 0 ≤ 1 - (x / √kk) ^ 2 := by nlinarith
    have e : √(1 - (x / √kk) ^ 2) * √kk = √(kk - x ^ 2) := by
      have hsq : (√(1 - (x / √kk) ^ 2) * √kk) ^ 2 = kk - x ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hw, div_pow, Real.sq_sqrt hk0.le]; field_simp
      rw [← hsq, Real.sqrt_sq (by positivity)]
    rw [← e]; field_simp

theorem integral_half : ∫ x in (0 : ℝ)..LL, hc x = π / 12 := by
  have hL := LL_pos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x => arcsin ((x - 3) / (2 * √3)) - arcsin (x / √kk))]
  · simp only [zero_sub, zero_div, Real.arcsin_zero, sub_zero]
    have e1 : (-3) / (2 * √3) = -(√3 / 2) := by
      have := s3_pos; field_simp; nlinarith [s3_sq]
    have e2 : LL / √kk = 1 / √3 := by
      rw [sqrt_kk]; have := s3_pos; field_simp
    have e3 : (LL - 3) / (2 * √3) = (√2 - 2) / (2 * √3) := by unfold LL; ring_nf
    rw [e1, e2, e3, Real.arcsin_neg, arcsin_sqrt3_half, arcsin_key]
    ring
  · intro x hx
    rw [Set.uIcc_of_le hL.le] at hx
    exact hasDerivAt_F hx.1 hx.2
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL.le]
    exact hc_cont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)

theorem integral_full : ∫ x in (-LL)..LL, hc x = π / 6 := by
  have hL := LL_pos
  have hi1 : IntervalIntegrable hc MeasureTheory.volume (-LL) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact hc_cont.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hi2 : IntervalIntegrable hc MeasureTheory.volume 0 LL := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hL.le]
    exact hc_cont.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2, integral_half]
  have : ∫ x in (-LL)..0, hc x = ∫ x in (0 : ℝ)..LL, hc x := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := LL) hc
    simp only [neg_zero, hc_neg] at h
    exact h.symm
  rw [this, integral_half]; ring


/-! ## The measure-theoretic part -/

open MeasureTheory

/-- The triangle `T` in `ℂ`. -/
def TC : Set ℂ := {z : ℂ | 0 < z.im ∧ 6 * z.re ≤ Complex.normSq z - 3 ∧
  -(6 * z.re) ≤ Complex.normSq z - 3 ∧ Complex.normSq z - 3 ≤ 6 + 6 * √2}

/-- `T` in coordinates. -/
def Rr : Set (ℝ × ℝ) := {q | 0 < q.2 ∧ 6 * q.1 ≤ q.1 ^ 2 + q.2 ^ 2 - 3 ∧
  -(6 * q.1) ≤ q.1 ^ 2 + q.2 ^ 2 - 3 ∧ q.1 ^ 2 + q.2 ^ 2 - 3 ≤ 6 + 6 * √2}

theorem measurableSet_Rr : MeasurableSet Rr := by
  unfold Rr
  have m1 : Measurable fun q : ℝ × ℝ => 6 * q.1 := by fun_prop
  have m2 : Measurable fun q : ℝ × ℝ => -(6 * q.1) := by fun_prop
  have m3 : Measurable fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 - 3 := by fun_prop
  exact (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_le m1 m3).inter ((measurableSet_le m2 m3).inter (measurableSet_le m3 measurable_const)))

theorem TC_eq : TC = Complex.measurableEquivRealProd ⁻¹' Rr := by
  ext z
  simp only [TC, Rr, Set.mem_preimage, Complex.measurableEquivRealProd_apply, Set.mem_ofPred_eq,
    Complex.normSq_apply]
  ring_nf

/-- The integrand `dy/y²`. -/
def G (q : ℝ × ℝ) : ENNReal := ENNReal.ofReal (1 / q.2 ^ 2)

theorem measurable_G : Measurable G := by unfold G; fun_prop

theorem mem_Rr_iff {x y : ℝ} (hx : |x| ≤ LL) :
    (x, y) ∈ Rr ↔ y ∈ Set.Icc (√(3 + 6 * |x| - x ^ 2)) (√(kk - x ^ 2)) := by
  have hlo := lo_pos hx
  have hk := kk_sub_pos hx
  simp only [Rr, Set.mem_ofPred_eq, Set.mem_Icc]
  constructor
  · rintro ⟨hy, h1, h2, h3⟩
    refine ⟨(Real.sqrt_le_left hy.le).2 ?_, (Real.le_sqrt' hy).2 ?_⟩
    · rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]; linarith
      · rw [abs_of_nonpos h]; linarith
    · unfold kk; linarith
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.sqrt_pos.2 hlo) h1
    have e1 := (Real.sqrt_le_left hy.le).1 h1
    have e2 := (Real.le_sqrt' hy).1 h2
    refine ⟨hy, ?_, ?_, ?_⟩
    · have := le_abs_self x; linarith
    · have := neg_abs_le x; linarith
    · unfold kk at e2; linarith

theorem not_mem_Rr {x y : ℝ} (hx : LL < |x|) : (x, y) ∉ Rr := by
  rintro ⟨hy, h1, h2, h3⟩
  have : 6 * |x| ≤ 6 + 6 * √2 := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  unfold LL at hx; linarith

/-- `∫ dy/y²` over `[a, b]`. -/
theorem lintegral_inv_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ y in Set.Icc a b, ENNReal.ofReal (1 / y ^ 2) = ENNReal.ofReal (1 / a - 1 / b) := by
  have hcont : ContinuousOn (fun y : ℝ => 1 / y ^ 2) (Set.Icc a b) := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    have : 0 < y := lt_of_lt_of_le ha hy.1
    positivity
  have hint : IntegrableOn (fun y : ℝ => 1 / y ^ 2) (Set.Icc a b) := hcont.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Icc (fun y hy => by positivity))]
  congr 1
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => -(1 / y))]
  · ring
  · intro y hy
    rw [Set.uIcc_of_le hab] at hy
    have hy0 : y ≠ 0 := (lt_of_lt_of_le ha hy.1).ne'
    have := (hasDerivAt_inv hy0).neg
    convert this using 1
    · funext t; simp
    · field_simp
  · exact (hcont.mono (by rw [Set.uIcc_of_le hab])).intervalIntegrable

theorem inner_eq (x : ℝ) :
    ∫⁻ y, Rr.indicator G (x, y) = ENNReal.ofReal ((Set.Icc (-LL) LL).indicator hc x) := by
  by_cases hx : |x| ≤ LL
  · have hx' : x ∈ Set.Icc (-LL) LL := abs_le.1 hx
    rw [Set.indicator_of_mem hx']
    have hlo := lo_pos hx
    have hk := kk_sub_pos hx
    have hle : √(3 + 6 * |x| - x ^ 2) ≤ √(kk - x ^ 2) := by
      apply Real.sqrt_le_sqrt
      have : 6 * |x| ≤ 6 + 6 * √2 := by unfold LL at hx; linarith
      unfold kk; linarith
    have e : (fun y => Rr.indicator G (x, y)) =
        (Set.Icc (√(3 + 6 * |x| - x ^ 2)) (√(kk - x ^ 2))).indicator
          (fun y => ENNReal.ofReal (1 / y ^ 2)) := by
      funext y
      by_cases hy : (x, y) ∈ Rr
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem ((mem_Rr_iff hx).1 hy)]; rfl
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (fun h => hy ((mem_Rr_iff hx).2 h))]
    rw [e, lintegral_indicator measurableSet_Icc, lintegral_inv_sq (Real.sqrt_pos.2 hlo) hle]
    rfl
  · push Not at hx
    have hx' : x ∉ Set.Icc (-LL) LL := fun h => by
      have := abs_le.2 h; linarith
    rw [Set.indicator_of_notMem hx', ENNReal.ofReal_zero]
    have : (fun y => Rr.indicator G (x, y)) = fun _ => 0 := by
      funext y; exact Set.indicator_of_notMem (not_mem_Rr hx) _
    rw [this, lintegral_zero]

theorem hc_nonneg {x : ℝ} (hx : x ∈ Set.Icc (-LL) LL) : 0 ≤ hc x := by
  have hx' : |x| ≤ LL := abs_le.2 hx
  have hlo := lo_pos hx'
  have hk := kk_sub_pos hx'
  unfold hc
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (Real.sqrt_pos.2 hlo)
  apply Real.sqrt_le_sqrt
  have : 6 * |x| ≤ 6 + 6 * √2 := by unfold LL at hx'; linarith
  unfold kk; linarith

/-- **The hyperbolic area of `T` is `π/6`.** -/
theorem area_TC : ∫⁻ z in TC, ENNReal.ofReal (1 / z.im ^ 2) = ENNReal.ofReal (π / 6) := by
  have h1 : ∫⁻ z in TC, ENNReal.ofReal (1 / z.im ^ 2) =
      ∫⁻ z in Complex.measurableEquivRealProd ⁻¹' Rr, G (Complex.measurableEquivRealProd z) := by
    rw [TC_eq]; rfl
  rw [h1, Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding G Rr]
  rw [← lintegral_indicator measurableSet_Rr, Measure.volume_eq_prod,
    lintegral_prod _ ((measurable_G.indicator measurableSet_Rr).aemeasurable)]
  simp_rw [inner_eq]
  have hint : Integrable ((Set.Icc (-LL) LL).indicator hc) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hc_cont.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith [LL_pos]), integral_full]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ Set.Icc (-LL) LL
    · rw [Set.indicator_of_mem hx]; exact hc_nonneg hx
    · rw [Set.indicator_of_notMem hx]; simp

end HDec.GammaStarArea.AreaCalc

#print axioms HDec.GammaStarArea.AreaCalc.area_TC
