import Mathlib

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian

namespace ValenceCocompact

/-- Second directional derivative. -/
noncomputable def d2 (f : ℂ → ℝ) (v x : ℂ) : ℝ := fderiv ℝ (fun y => fderiv ℝ f y v) x v

theorem d2_eq_iter {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) (v : ℂ) :
    iteratedFDeriv ℝ 2 f x ![v, v] = d2 f v x := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [d2, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem laplacian_eq_d2 {f : ℂ → ℝ} {x : ℂ} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = d2 f 1 x + d2 f I x := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only
  rw [d2_eq_iter hf, d2_eq_iter hf]

theorem integrable_of_tsupport {h : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hh : ContinuousOn h V)
    (hs : tsupport h ⊆ V) (hc : HasCompactSupport h) : Integrable h :=
  (hh.continuous_of_tsupport_subset hV hs).integrable_of_hasCompactSupport hc

/-- Product of a function continuous on `V` with a continuous function compactly supported in `V`. -/
theorem integrable_mul_of {f g : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hf : ContinuousOn f V)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgV : tsupport g ⊆ V) :
    Integrable (fun x => f x * g x) := by
  refine integrable_of_tsupport hV (hf.mul hg.continuousOn) ?_ (hgc.mul_left)
  exact (tsupport_mul_subset_right).trans hgV

/-- One-direction double integration by parts. -/
theorem integral_mul_d2 {f χ : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f V)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) (v : ℂ) :
    ∫ x, f x * d2 χ v x = ∫ x, d2 f v x * χ x := by
  set g : ℂ → ℝ := fun y => fderiv ℝ χ y v with hg
  have hg1 : ContDiff ℝ 1 g := (hχ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgc : HasCompactSupport g := hχc.fderiv_apply (𝕜 := ℝ) v
  have hgV : tsupport g ⊆ V := (tsupport_fderiv_apply_subset ℝ v).trans hχV
  have hf1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) V :=
    (hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const
  have hfd : ∀ x ∈ V, DifferentiableAt ℝ f x := fun x hx =>
    (hf.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)
  have hf1d : ∀ x ∈ V, DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x := fun x hx =>
    (hf1.contDiffAt (hV.mem_nhds hx)).differentiableAt (by norm_num)
  have hgd' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgc' : HasCompactSupport (fun x => fderiv ℝ g x v) := hgc.fderiv_apply (𝕜 := ℝ) v
  have hgV' : tsupport (fun x => fderiv ℝ g x v) ⊆ V := (tsupport_fderiv_apply_subset ℝ v).trans hgV
  -- step 1
  have e1 : ∫ x, f x * fderiv ℝ g x v = - ∫ x, fderiv ℝ f x v * g x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of hV hf1.continuousOn hg1.continuous hgc hgV
    · exact integrable_mul_of hV hf.continuousOn hgd' hgc' hgV'
    · exact integrable_mul_of hV hf.continuousOn hg1.continuous hgc hgV
    · exact fun x hx => hfd x (hgV hx)
    · exact fun x _ => (hg1.differentiable (by norm_num)) x
  -- step 2
  have e2 : ∫ x, fderiv ℝ f x v * fderiv ℝ χ x v =
      - ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v * χ x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · have hcont : ContinuousOn (fun x => fderiv ℝ (fun y => fderiv ℝ f y v) x v) V :=
        ((hf1.continuousOn_fderiv_of_isOpen hV (by norm_num))).clm_apply continuousOn_const
      exact integrable_mul_of hV hcont hχ.continuous hχc hχV
    · exact integrable_mul_of hV hf1.continuousOn hg1.continuous hgc hgV
    · exact integrable_mul_of hV hf1.continuousOn hχ.continuous hχc hχV
    · exact fun x hx => hf1d x (hχV hx)
    · exact fun x _ => (hχ.differentiable (by norm_num)) x
  simp only [d2]
  rw [e1]
  change -∫ x, fderiv ℝ f x v * fderiv ℝ χ x v = _
  rw [e2, neg_neg]

/-- **Green's identity** for a test function: `∫ f Δχ = ∫ Δf χ` when `f` is `C²` on an open set containing the
support of `χ`. -/
theorem integral_mul_laplacian {f χ : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V) (hf : ContDiffOn ℝ 2 f V)
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχV : tsupport χ ⊆ V) :
    ∫ x, f x * Δ χ x = ∫ x, Δ f x * χ x := by
  have hd2 : ∀ v, Integrable (fun x => f x * d2 χ v x) := by
    intro v
    have hc : Continuous (d2 χ v) := by
      have := ((hχ.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiff_const (c := v)))
      exact (this.continuous_fderiv (by norm_num)).clm_apply continuous_const
    refine integrable_mul_of hV hf.continuousOn hc ?_ ?_
    · exact ((hχc.fderiv_apply (𝕜 := ℝ) v).fderiv_apply (𝕜 := ℝ) v)
    · exact (tsupport_fderiv_apply_subset ℝ v).trans ((tsupport_fderiv_apply_subset ℝ v).trans hχV)
  have hd2' : ∀ v, Integrable (fun x => d2 f v x * χ x) := by
    intro v
    have hf1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y v) V :=
      (hf.fderiv_of_isOpen hV (m := 1) (by norm_num)).clm_apply contDiffOn_const
    have hcont : ContinuousOn (d2 f v) V :=
      ((hf1.continuousOn_fderiv_of_isOpen hV (by norm_num))).clm_apply continuousOn_const
    exact integrable_mul_of hV hcont hχ.continuous hχc hχV
  have L1 : ∀ x, f x * Δ χ x = f x * d2 χ 1 x + f x * d2 χ I x := fun x => by
    rw [laplacian_eq_d2 (hχ.contDiffAt)]; ring
  have L2 : ∀ x, Δ f x * χ x = d2 f 1 x * χ x + d2 f I x * χ x ∨ χ x = 0 := by
    intro x
    by_cases hx : χ x = 0
    · exact Or.inr hx
    · left
      have hxV : x ∈ V := hχV (subset_tsupport _ hx)
      rw [laplacian_eq_d2 (hf.contDiffAt (hV.mem_nhds hxV))]; ring
  have L2' : (fun x => Δ f x * χ x) = fun x => d2 f 1 x * χ x + d2 f I x * χ x := by
    funext x
    rcases L2 x with h | h
    · exact h
    · simp [h]
  simp_rw [L1, L2']
  rw [integral_add (hd2 1) (hd2 I), integral_add (hd2' 1) (hd2' I),
    integral_mul_d2 hV hf hχ hχc hχV 1, integral_mul_d2 hV hf hχ hχc hχV I]

end ValenceCocompact
