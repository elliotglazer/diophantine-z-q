import VC.A1

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian

namespace ValenceCocompact

/-- `d2` as a second derivative along the line `t ↦ x + t v`. -/
theorem d2_eq_line {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    d2 f v x = deriv (deriv (fun t : ℝ => f (x + t • v))) 0 := by
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by simp)
  set φ : ℂ → ℝ := fun y => fderiv ℝ f y v
  have hφ : DifferentiableAt ℝ φ x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)
  have hline : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have : Continuous (fun t : ℝ => x + t • v) := by fun_prop
    simpa using this.tendsto 0
  have hev' : deriv (fun t : ℝ => f (x + t • v)) =ᶠ[𝓝 (0 : ℝ)] fun t => φ (x + t • v) := by
    filter_upwards [hline.eventually hev] with t ht
    have hd : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) :=
      (ht.differentiableAt (by norm_num)).hasFDerivAt
    have hl : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hd.comp_hasDerivAt t hl).deriv
  rw [hev'.deriv_eq]
  have hl0 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
  have hφ' : HasFDerivAt φ (fderiv ℝ φ x) (x + (0:ℝ) • v) := by simpa using hφ.hasFDerivAt
  have := (hφ'.comp_hasDerivAt (0:ℝ) hl0).deriv
  simp only [Function.comp_def] at this
  rw [this]
  rfl

/-- The regularized logarithm `½ log(|w|² + ε²)`. -/
noncomputable def ureg (ε : ℝ) (w : ℂ) : ℝ := Real.log (‖w‖ ^ 2 + ε ^ 2) / 2

theorem ureg_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 2 (ureg ε) := by
  unfold ureg
  apply ContDiff.div_const
  apply ContDiff.log ((contDiff_norm_sq ℝ).add contDiff_const)
  intro w; positivity

theorem norm_line_sq (x v : ℂ) (t : ℝ) :
    ‖x + t • v‖ ^ 2 = (x.re + t * v.re) ^ 2 + (x.im + t * v.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

/-- Second derivative of `t ↦ ½ log(a(t)² + b(t)² + ε²)` for affine `a, b`. -/
theorem deriv2_ureg_line {ε : ℝ} (hε : 0 < ε) (x v : ℂ) :
    deriv (deriv (fun t : ℝ => ureg ε (x + t • v))) 0 =
      ((v.re ^ 2 + v.im ^ 2) * (‖x‖ ^ 2 + ε ^ 2) - 2 * (x.re * v.re + x.im * v.im) ^ 2) /
        (‖x‖ ^ 2 + ε ^ 2) ^ 2 := by
  set q : ℝ → ℝ := fun t => (x.re + t * v.re) ^ 2 + (x.im + t * v.im) ^ 2 + ε ^ 2 with hq
  have hqpos : ∀ t, 0 < q t := fun t => by simp only [hq]; positivity
  have hfun : (fun t : ℝ => ureg ε (x + t • v)) = fun t => Real.log (q t) / 2 := by
    funext t; simp only [ureg, norm_line_sq, hq]
  have hq' : ∀ t, HasDerivAt q (2 * (x.re + t * v.re) * v.re + 2 * (x.im + t * v.im) * v.im) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x.re + t * v.re) v.re t := by
      simpa using ((hasDerivAt_id t).mul_const v.re).const_add x.re
    have h2 : HasDerivAt (fun t : ℝ => x.im + t * v.im) v.im t := by
      simpa using ((hasDerivAt_id t).mul_const v.im).const_add x.im
    have := ((h1.pow 2).add (h2.pow 2)).add_const (ε ^ 2)
    convert this using 1; simp
  have hd1 : deriv (fun t => Real.log (q t) / 2) =
      fun t => ((x.re + t * v.re) * v.re + (x.im + t * v.im) * v.im) / q t := by
    funext t
    have := ((hq' t).log (hqpos t).ne').div_const 2
    rw [this.deriv]; field_simp
  rw [hfun, hd1]
  have hn : HasDerivAt (fun t : ℝ => (x.re + t * v.re) * v.re + (x.im + t * v.im) * v.im)
      (v.re ^ 2 + v.im ^ 2) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x.re + t * v.re) v.re 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.re).const_add x.re
    have h2 : HasDerivAt (fun t : ℝ => x.im + t * v.im) v.im 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const v.im).const_add x.im
    convert (h1.mul_const v.re).add (h2.mul_const v.im) using 1; ring
  rw [(hn.fun_div (hq' 0) (hqpos 0).ne').deriv]
  have hq0 : q 0 = ‖x‖ ^ 2 + ε ^ 2 := by
    simp only [hq]; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hq0]; simp only [zero_mul, add_zero]
  field_simp

theorem laplacian_ureg {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Δ (ureg ε) x = 2 * ε ^ 2 / (‖x‖ ^ 2 + ε ^ 2) ^ 2 := by
  have hc := (ureg_contDiff hε).contDiffAt (x := x)
  rw [laplacian_eq_d2 hc, d2_eq_line hc, d2_eq_line hc, deriv2_ureg_line hε, deriv2_ureg_line hε]
  have hN : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hpos : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  rw [← add_div, div_eq_div_iff (by positivity) (by positivity)]
  simp only [Complex.one_re, Complex.one_im, I_re, I_im]
  rw [hN]; ring

/-- `Δ log(Im z) = -1/(Im z)²` on the upper half-plane. -/
theorem laplacian_log_im {x : ℂ} (hx : 0 < x.im) :
    Δ (fun z : ℂ => Real.log z.im) x = -1 / x.im ^ 2 := by
  have hc : ContDiffAt ℝ 2 (fun z : ℂ => Real.log z.im) x :=
    (Complex.imCLM.contDiff.contDiffAt).log hx.ne'
  rw [laplacian_eq_d2 hc, d2_eq_line hc, d2_eq_line hc]
  have e1 : (fun t : ℝ => Real.log (x + t • (1:ℂ)).im) = fun _ => Real.log x.im := by
    funext t; simp
  have e2 : (fun t : ℝ => Real.log (x + t • I).im) = fun t => Real.log (x.im + t) := by
    funext t; simp
  rw [e1, e2]
  simp only [deriv_const', zero_add]
  have hev : deriv (fun t : ℝ => Real.log (x.im + t)) =ᶠ[𝓝 0] fun t => (x.im + t)⁻¹ := by
    have : ∀ᶠ t in 𝓝 (0:ℝ), 0 < x.im + t := by
      have hc : Continuous (fun t : ℝ => x.im + t) := by fun_prop
      exact hc.continuousAt.eventually (lt_mem_nhds (by simpa using hx))
    filter_upwards [this] with t ht
    have := ((hasDerivAt_id t).const_add x.im).log ht.ne'
    simp only [id] at this
    rw [this.deriv]; simp
  rw [hev.deriv_eq]
  have := ((hasDerivAt_id (0:ℝ)).const_add x.im).fun_inv (by simpa using hx.ne')
  simp only [id] at this
  rw [this.deriv]; simp

end ValenceCocompact
