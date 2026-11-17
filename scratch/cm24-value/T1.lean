import Mathlib

set_option linter.all false
open Complex
open scoped Real

noncomputable section
namespace CM24

/-- The general genus-2 theta term with real characteristics `c = (c0,c1)`, `d = (d0,d1)` at the symmetric
matrix `[[α, β], [β, γ]]`: `exp(πi vᵀΩv + 2πi v·d)`, `v = n + c`. -/
def term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) : ℂ :=
  cexp (π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
      + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
    + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1))

def Th2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : ℂ := ∑' n : ℤ × ℤ, term2 α β γ c0 c1 d0 d1 n

theorem re_exponent (α β γ : ℂ) (x y d0 d1 : ℝ) :
    (π * I * (α * (x : ℂ) ^ 2 + 2 * β * x * y + γ * (y : ℂ) ^ 2) + 2 * π * I * ((x : ℂ) * d0 + (y : ℂ) * d1)).re
      = -π * (α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2) := by
  simp [Complex.mul_re, Complex.mul_im, pow_two]

/-- 1D Gaussian summability. -/
theorem summable_gauss {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Summable (fun n : ℤ => Real.exp (-π * δ * ((n : ℝ) + c) ^ 2)) := by
  have h := ((summable_jacobiTheta₂_term_iff ((c * δ : ℝ) * I) ((δ : ℂ) * I)).2
    (by simpa using hδ)).norm.mul_left (Real.exp (-π * δ * c ^ 2))
  refine h.congr fun n => ?_
  rw [norm_jacobiTheta₂_term, ← Real.exp_add]
  congr 1
  simp
  ring

theorem norm_term2 (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n : ℤ × ℤ) :
    ‖term2 α β γ c0 c1 d0 d1 n‖ = Real.exp (-π * (α.im * ((n.1 : ℝ) + c0) ^ 2
      + 2 * β.im * ((n.1 : ℝ) + c0) * ((n.2 : ℝ) + c1) + γ.im * ((n.2 : ℝ) + c1) ^ 2)) := by
  rw [term2, Complex.norm_exp, re_exponent]

theorem summable_norm_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖) := by
  have h := (summable_gauss hδ c0).mul_of_nonneg (summable_gauss hδ c1)
    (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h
  rw [norm_term2, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have := hQ ((n.1 : ℝ) + c0) ((n.2 : ℝ) + c1)
  nlinarith [Real.pi_pos]

theorem summable_term2 {α β γ : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ : ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2)
    (c0 c1 d0 d1 : ℝ) : Summable (term2 α β γ c0 c1 d0 d1) :=
  (summable_norm_term2 hδ hQ c0 c1 d0 d1).of_norm


/-- Sum over `ℤ × ℤ` as an iterated sum, inner over the first coordinate. -/
theorem tsum_swap_iter {f : ℤ × ℤ → ℂ} (hf : Summable f) :
    ∑' n, f n = ∑' n1 : ℤ, ∑' n0 : ℤ, f (n0, n1) := by
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq]
  exact ((Equiv.prodComm ℤ ℤ).summable_iff.2 hf).tsum_prod

theorem term2_eq_jt (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (n0 n1 : ℤ) :
    term2 α β γ c0 c1 d0 d1 (n0, n1) =
      cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      jacobiTheta₂_term n0 (c0 * α + β * ((n1 : ℂ) + c1) + d0) α := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem jt_dual (α β γ : ℂ) (hα : α ≠ 0) (c0 c1 d0 d1 : ℝ) (m n1 : ℤ) :
    cexp (π * I * (α * (c0 : ℂ) ^ 2 + 2 * β * c0 * ((n1 : ℂ) + c1) + γ * ((n1 : ℂ) + c1) ^ 2)
        + 2 * π * I * ((c0 : ℂ) * d0 + ((n1 : ℂ) + c1) * d1)) *
      (cexp (-π * I * (c0 * α + β * ((n1 : ℂ) + c1) + d0) ^ 2 / α) *
        jacobiTheta₂_term m ((c0 * α + β * ((n1 : ℂ) + c1) + d0) / α) (-1 / α)) =
      cexp (2 * π * I * c0 * d0) * term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 (m, n1) := by
  rw [term2, jacobiTheta₂_term, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

/-- **Partial inversion in the first coordinate** (two applications of Mathlib's
`jacobiTheta₂_functional_equation` give the full inversion `Ω ↦ −Ω⁻¹`). -/
theorem pi0 {α β γ : ℂ} (hα : 0 < α.im) (c0 c1 d0 d1 : ℝ)
    (hs : Summable (term2 α β γ c0 c1 d0 d1))
    (hs' : Summable (term2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1)) :
    Th2 α β γ c0 c1 d0 d1 = 1 / (-I * α) ^ (1 / 2 : ℂ) * cexp (2 * π * I * c0 * d0) *
      Th2 (-1 / α) (β / α) (γ - β ^ 2 / α) (-d0) c1 c0 d1 := by
  have hα0 : α ≠ 0 := fun h => by simp [h] at hα
  rw [Th2, Th2, tsum_swap_iter hs, tsum_swap_iter hs', ← tsum_mul_left]
  congr 1; funext n1
  conv_lhs => enter [1]; ext n0; rw [term2_eq_jt]
  rw [tsum_mul_left]
  change _ * jacobiTheta₂ _ _ = _
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂, ← tsum_mul_left, ← tsum_mul_left,
    ← tsum_mul_left]
  congr 1; funext m
  conv_rhs => rw [mul_assoc, ← jt_dual α β γ hα0 c0 c1 d0 d1 m n1]
  ring


/-! ## Symmetries -/

theorem th2_swap (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) : Th2 α β γ c0 c1 d0 d1 = Th2 γ β α c1 c0 d1 d0 := by
  rw [Th2, Th2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  congr 1; ring

theorem th2_shift_c (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ (c0 + k0) (c1 + k1) d0 d1 = Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2]
  conv_rhs => rw [← (Equiv.addRight ((k0, k1) : ℤ × ℤ)).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.coe_addRight, Prod.fst_add, Prod.snd_add]
  congr 1; push_cast; ring

theorem th2_shift_d (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) (k0 k1 : ℤ) :
    Th2 α β γ c0 c1 (d0 + k0) (d1 + k1) =
      cexp (2 * π * I * (c0 * k0 + c1 * k1)) * Th2 α β γ c0 c1 d0 d1 := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n.1 * k0 + n.2 * k1) : ℤ) : ℂ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term2, term2, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

/-! ## Duplication -/

/-- `(σ, p, q) ↦ (p + q + σ, p − q)`, a bijection `Fin 2 × ℤ × ℤ ≃ ℤ × ℤ`. -/
def dupE1 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (w.2.1 + w.2.2 + (w.1 : ℕ), w.2.1 - w.2.2)
  invFun mn := (if (mn.1 - mn.2) % 2 = 0 then 0 else 1,
    (mn.2 + (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2,
     (mn.1 - mn.2 - (if (mn.1 - mn.2) % 2 = 0 then 0 else 1)) / 2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv mn := by
    obtain ⟨m, n⟩ := mn
    by_cases h : (m - n) % 2 = 0 <;> simp [h] <;> omega

/-- The 2D version: `((σ₀,σ₁), (p, q)) ↦ (p + q + σ, p − q)` on `ℤ² × ℤ²`. -/
def dupE2 : (Fin 2 × Fin 2) × ((ℤ × ℤ) × (ℤ × ℤ)) ≃ (ℤ × ℤ) × (ℤ × ℤ) where
  toFun w := ((w.2.1.1 + w.2.2.1 + (w.1.1 : ℕ), w.2.1.2 + w.2.2.2 + (w.1.2 : ℕ)),
    (w.2.1.1 - w.2.2.1, w.2.1.2 - w.2.2.2))
  invFun mn :=
    let s0 : ℤ := if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1
    let s1 : ℤ := if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1
    ((if (mn.1.1 - mn.2.1) % 2 = 0 then 0 else 1, if (mn.1.2 - mn.2.2) % 2 = 0 then 0 else 1),
      ((mn.2.1 + (mn.1.1 - mn.2.1 - s0) / 2, mn.2.2 + (mn.1.2 - mn.2.2 - s1) / 2),
       ((mn.1.1 - mn.2.1 - s0) / 2, (mn.1.2 - mn.2.2 - s1) / 2)))
  left_inv w := by
    obtain ⟨⟨σ0, σ1⟩, ⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
    fin_cases σ0 <;> fin_cases σ1 <;> simp <;> omega
  right_inv mn := by
    obtain ⟨⟨m0, m1⟩, ⟨n0, n1⟩⟩ := mn
    by_cases h0 : (m0 - n0) % 2 = 0 <;> by_cases h1 : (m1 - n1) % 2 = 0 <;> simp [h0, h1] <;> omega

theorem dupE2_apply (σ0 σ1 : Fin 2) (p0 p1 q0 q1 : ℤ) :
    dupE2 ((σ0, σ1), ((p0, p1), (q0, q1))) =
      ((p0 + q0 + (σ0 : ℕ), p1 + q1 + (σ1 : ℕ)), (p0 - q0, p1 - q1)) := rfl

theorem dup2 {α β γ : ℂ} (c0 c1 d0 d1 : ℝ)
    (hs : Summable (fun n => ‖term2 α β γ c0 c1 d0 d1 n‖))
    (hs2 : ∀ c0' c1' d0' d1' : ℝ, Summable (fun n => ‖term2 (2 * α) (2 * β) (2 * γ) c0' c1' d0' d1' n‖)) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = ∑ σ : Fin 2 × Fin 2,
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2 + c0) (((σ.2 : ℕ) : ℝ) / 2 + c1) (2 * d0) (2 * d1) *
      Th2 (2 * α) (2 * β) (2 * γ) (((σ.1 : ℕ) : ℝ) / 2) (((σ.2 : ℕ) : ℝ) / 2) 0 0 := by
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c => term2 α β γ c0 c1 d0 d1 (dupE2 c).1 *
      term2 α β γ c0 c1 d0 d1 (dupE2 c).2) := dupE2.summable_iff.2 hprod
  rw [sq, Th2, tsum_mul_tsum_of_summable_norm hs hs, ← dupE2.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [Th2, Th2, tsum_mul_tsum_of_summable_norm (hs2 _ _ _ _) (hs2 _ _ _ _)]
  congr 1; funext w
  obtain ⟨σ0, σ1⟩ := σ
  obtain ⟨⟨p0, p1⟩, ⟨q0, q1⟩⟩ := w
  rw [dupE2_apply]
  simp only [term2, ← Complex.exp_add]
  congr 1; push_cast; ring


/-! ## Genus one -/

/-- Genus-1 theta term with real characteristic: `exp(πiτ(n+c)² + 2πi(n+c)d)`. -/
def term1 (τ : ℂ) (c d : ℝ) (n : ℤ) : ℂ :=
  cexp (π * I * τ * (((n : ℝ) + c : ℝ) : ℂ) ^ 2 + 2 * π * I * (((n : ℝ) + c : ℝ) : ℂ) * d)

def th1 (τ : ℂ) (c d : ℝ) : ℂ := ∑' n : ℤ, term1 τ c d n

theorem term1_eq (τ : ℂ) (c d : ℝ) (n : ℤ) :
    term1 τ c d n = cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d) *
      jacobiTheta₂_term n (c * τ + d) τ := by
  rw [term1, jacobiTheta₂_term, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- The bridge to Mathlib: `th1 τ c d = exp(πiτc² + 2πicd)·jacobiTheta₂(cτ + d, τ)`. -/
theorem th1_eq (τ : ℂ) (c d : ℝ) :
    th1 τ c d = cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d) * jacobiTheta₂ (c * τ + d) τ := by
  rw [th1, jacobiTheta₂, ← tsum_mul_left]
  exact tsum_congr fun n => term1_eq τ c d n

theorem summable_norm_term1 {τ : ℂ} (hτ : 0 < τ.im) (c d : ℝ) :
    Summable (fun n => ‖term1 τ c d n‖) := by
  have h := ((summable_jacobiTheta₂_term_iff (c * τ + d) τ).2 hτ).norm.mul_left
    ‖cexp (π * I * τ * (c : ℂ) ^ 2 + 2 * π * I * c * d)‖
  refine h.congr fun n => ?_
  rw [term1_eq, norm_mul]

theorem th1_shift_c (τ : ℂ) (c d : ℝ) (k : ℤ) : th1 τ (c + k) d = th1 τ c d := by
  rw [th1, th1]
  conv_rhs => rw [← (Equiv.addRight k).tsum_eq]
  congr 1; funext n
  simp only [term1, Equiv.coe_addRight]
  congr 1; push_cast; ring

theorem th1_shift_d (τ : ℂ) (c d : ℝ) (k : ℤ) :
    th1 τ c (d + k) = cexp (2 * π * I * c * k) * th1 τ c d := by
  rw [th1, th1, ← tsum_mul_left]
  congr 1; funext n
  have h : cexp (((-(n * k)) : ℤ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I _
  rw [term1, term1, ← mul_one (cexp (_ + _)), ← h, ← Complex.exp_add, ← Complex.exp_add]
  congr 1; push_cast; ring

theorem dup1 {τ : ℂ} (hτ : 0 < τ.im) (c d : ℝ) :
    th1 τ c d ^ 2 = ∑ σ : Fin 2,
      th1 (2 * τ) (((σ : ℕ) : ℝ) / 2 + c) (2 * d) * th1 (2 * τ) (((σ : ℕ) : ℝ) / 2) 0 := by
  have hs := summable_norm_term1 hτ c d
  have hτ2 : 0 < (2 * τ).im := by simpa using hτ
  have hprod := summable_mul_of_summable_norm hs hs
  have h2 : Summable (fun c' => term1 τ c d (dupE1 c').1 * term1 τ c d (dupE1 c').2) :=
    dupE1.summable_iff.2 hprod
  rw [sq, th1, tsum_mul_tsum_of_summable_norm hs hs, ← dupE1.tsum_eq, h2.tsum_prod, tsum_fintype]
  congr 1; funext σ
  rw [th1, th1, tsum_mul_tsum_of_summable_norm (summable_norm_term1 hτ2 _ _)
    (summable_norm_term1 hτ2 _ _)]
  congr 1; funext w
  obtain ⟨p, q⟩ := w
  simp only [dupE1, Equiv.coe_fn_mk, term1, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Diagonal period matrices: the genus-2 theta factors. -/
theorem th2_diag {τ0 τ1 : ℂ} (h0 : 0 < τ0.im) (h1 : 0 < τ1.im) (c0 c1 d0 d1 : ℝ) :
    Th2 τ0 0 τ1 c0 c1 d0 d1 = th1 τ0 c0 d0 * th1 τ1 c1 d1 := by
  rw [th1, th1, tsum_mul_tsum_of_summable_norm (summable_norm_term1 h0 _ _)
    (summable_norm_term1 h1 _ _), Th2]
  congr 1; funext n
  simp only [term2, term1, ← Complex.exp_add]
  congr 1; ring

/-- The odd genus-1 theta constant vanishes. -/
theorem th1_odd (τ : ℂ) : th1 τ (1 / 2) (1 / 2) = 0 := by
  have h : th1 τ (1 / 2) (1 / 2) = -th1 τ (1 / 2) (1 / 2) := by
    conv_lhs => rw [th1, ← (Equiv.neg ℤ).tsum_eq, ← (Equiv.addRight (1 : ℤ)).tsum_eq]
    rw [th1, ← tsum_neg]
    congr 1; funext n
    simp only [term1, Equiv.coe_addRight, Equiv.neg_apply]
    have : π * I * τ * (((((-(n + 1) : ℤ) : ℝ) + 1 / 2 : ℝ)) : ℂ) ^ 2
        + 2 * π * I * (((((-(n + 1) : ℤ) : ℝ) + 1 / 2 : ℝ)) : ℂ) * ((1 / 2 : ℝ) : ℂ) =
        (π * I * τ * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * (((n : ℝ) + 1 / 2 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ))
          + ((-n - 1 : ℤ) : ℂ) * (2 * π * I) + π * I := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have : (2 : ℂ) * th1 τ (1 / 2) (1 / 2) = 0 := by linear_combination h
  simpa using this


/-! ## The explicit matrices: `Ω₂₄`, its partial inversion, and `W = −Ω₂₄⁻¹` -/

abbrev r6 : ℝ := √6
theorem r6_sq : r6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
theorem r6_pos : 0 < r6 := Real.sqrt_pos.2 (by norm_num)

/-- `Ω₂₄ = [[α0, β0], [β0, γ0]]`. -/
def α0 : ℂ := ⟨-2 / 7, 3 * r6 / 14⟩
def β0 : ℂ := ⟨-1 / 7, -r6 / 7⟩
def γ0 : ℂ := ⟨-4 / 7, 3 * r6 / 7⟩
/-- The partial inversion `[[−1/α0, β0/α0], [β0/α0, γ0 − β0²/α0]]`. -/
def α1 : ℂ := ⟨4 / 5, 3 * r6 / 5⟩
def β1 : ℂ := ⟨-2 / 5, r6 / 5⟩
def γ1 : ℂ := ⟨-4 / 5, 2 * r6 / 5⟩
/-- `W = −Ω₂₄⁻¹ = [[wa, wb], [wb, wc]] = [[1 + i√6/2, 1/2], [1/2, 1/2 + i√6/4]]`. -/
def wa : ℂ := ⟨1, r6 / 2⟩
def wb : ℂ := ⟨1 / 2, 0⟩
def wc : ℂ := ⟨1 / 2, r6 / 4⟩

theorem α0_ne : α0 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [α0] at this <;> linarith [r6_pos]
theorem γ1_ne : γ1 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [γ1] at this <;> linarith [r6_pos]

theorem eqA1 : -1 / α0 = α1 := by
  rw [div_eq_iff α0_ne]; apply Complex.ext <;> simp [α0, α1] <;> nlinarith [r6_sq]
theorem eqB1 : β0 / α0 = β1 := by
  rw [div_eq_iff α0_ne]; apply Complex.ext <;> simp [α0, β0, β1] <;> nlinarith [r6_sq]
theorem eqC1 : γ0 - β0 ^ 2 / α0 = γ1 := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff α0_ne]
  apply Complex.ext <;> simp [α0, β0, γ0, γ1, pow_two] <;> nlinarith [r6_sq]
theorem eqA2 : -1 / γ1 = wc := by
  rw [div_eq_iff γ1_ne]; apply Complex.ext <;> simp [γ1, wc] <;> nlinarith [r6_sq]
theorem eqB2 : β1 / γ1 = wb := by
  rw [div_eq_iff γ1_ne]; apply Complex.ext <;> simp [γ1, β1, wb] <;> nlinarith [r6_sq]
theorem eqC2 : α1 - β1 ^ 2 / γ1 = wa := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', eq_div_iff γ1_ne]
  apply Complex.ext <;> simp [α1, β1, γ1, wa, pow_two] <;> nlinarith [r6_sq]

theorem pos0 : ∀ x y : ℝ, r6 / 7 * (x ^ 2 + y ^ 2) ≤
    α0.im * x ^ 2 + 2 * β0.im * x * y + γ0.im * y ^ 2 := by
  intro x y; simp only [α0, β0, γ0]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg (x - 2 * y))]
theorem pos1 : ∀ x y : ℝ, r6 / 5 * (x ^ 2 + y ^ 2) ≤
    α1.im * x ^ 2 + 2 * β1.im * x * y + γ1.im * y ^ 2 := by
  intro x y; simp only [α1, β1, γ1]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x), mul_nonneg r6_pos.le (sq_nonneg (x + y))]
theorem pos1s : ∀ x y : ℝ, r6 / 5 * (x ^ 2 + y ^ 2) ≤
    γ1.im * x ^ 2 + 2 * β1.im * x * y + α1.im * y ^ 2 := by
  intro x y; simp only [α1, β1, γ1]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg y), mul_nonneg r6_pos.le (sq_nonneg (x + y))]
theorem posW : ∀ x y : ℝ, r6 / 4 * (x ^ 2 + y ^ 2) ≤
    wa.im * x ^ 2 + 2 * wb.im * x * y + wc.im * y ^ 2 := by
  intro x y; simp only [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x)]
theorem posW2 : ∀ x y : ℝ, r6 / 2 * (x ^ 2 + y ^ 2) ≤
    (2 * wa).im * x ^ 2 + 2 * (2 * wb).im * x * y + (2 * wc).im * y ^ 2 := by
  intro x y; simp [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg x)]
theorem posWs : ∀ x y : ℝ, r6 / 4 * (x ^ 2 + y ^ 2) ≤
    wc.im * x ^ 2 + 2 * wb.im * x * y + wa.im * y ^ 2 := by
  intro x y; simp only [wa, wb, wc]
  nlinarith [mul_nonneg r6_pos.le (sq_nonneg y)]

theorem d0pos : (0 : ℝ) < r6 / 7 := div_pos r6_pos (by norm_num)
theorem d1pos : (0 : ℝ) < r6 / 5 := div_pos r6_pos (by norm_num)
theorem d2pos : (0 : ℝ) < r6 / 4 := div_pos r6_pos (by norm_num)
theorem d3pos : (0 : ℝ) < r6 / 2 := div_pos r6_pos (by norm_num)

/-- **The inversion `Ω₂₄ ↦ W`** on theta constants with characteristics: two partial inversions
(each Mathlib's one-variable functional equation) and two coordinate swaps. -/
theorem invert (a0 a1 : ℝ) (b0 b1 : ℤ) :
    Th2 α0 β0 γ0 (a0 / 2) (a1 / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) =
      1 / (-I * α0) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (a0 / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) *
      (1 / (-I * γ1) ^ (1 / 2 : ℂ) * cexp (2 * π * I * (a1 / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ))) *
      Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) (a0 / 2) (a1 / 2) := by
  have hα : 0 < α0.im := by simp [α0] <;> exact r6_pos
  have hγ : 0 < γ1.im := by simp [γ1] <;> exact r6_pos
  rw [pi0 hα _ _ _ _ (summable_term2 d0pos pos0 _ _ _ _)
    (by rw [eqA1, eqB1, eqC1]; exact summable_term2 d1pos pos1 _ _ _ _), eqA1, eqB1, eqC1,
    th2_swap, pi0 hγ _ _ _ _ (summable_term2 d1pos pos1s _ _ _ _)
    (by rw [eqA2, eqB2, eqC2]; exact summable_term2 d2pos posWs _ _ _ _), eqA2, eqB2, eqC2,
    th2_swap]
  have e0 : ((b0 : ℝ) / 2) = -((b0 : ℝ) / 2) + (b0 : ℤ) := by ring
  have e1 : ((b1 : ℝ) / 2) = -((b1 : ℝ) / 2) + (b1 : ℤ) := by ring
  conv_rhs => rw [e0, e1, th2_shift_c]
  ring_nf


/-! ## `2W = diag(i√6, i√6/2) + [[2,1],[1,1]]`: translation to a diagonal matrix -/

/-- `τ₆ = i√6`, `τ₃ = i√6/2`: the two CM points of discriminant `−24` (one per ideal class). -/
def τ6 : ℂ := ⟨0, r6⟩
def τ3 : ℂ := ⟨0, r6 / 2⟩

theorem τ6_im : 0 < τ6.im := by simp [τ6] <;> exact r6_pos
theorem τ3_im : 0 < τ3.im := by simp [τ3] <;> exact div_pos r6_pos (by norm_num)

theorem h2wa : 2 * wa = τ6 + 2 := by apply Complex.ext <;> simp [wa, τ6] <;> ring
theorem h2wb : 2 * wb = 1 := by apply Complex.ext <;> simp [wb]
theorem h2wc : 2 * wc = τ3 + 1 := by apply Complex.ext <;> simp [wc, τ3] <;> ring

theorem th2_phase {α β γ α' β' γ' : ℂ} {c0 c1 d0 d1 d0' d1' : ℝ} (κ : ℂ)
    (h : ∀ n : ℤ × ℤ, ∃ k : ℤ,
      π * I * (α * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
        + γ * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
        + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0 + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1) =
      (π * I * (α' * (((n.1 : ℝ) + c0 : ℝ) : ℂ) ^ 2 + 2 * β' * (((n.1 : ℝ) + c0 : ℝ) : ℂ) * (((n.2 : ℝ) + c1 : ℝ) : ℂ)
        + γ' * (((n.2 : ℝ) + c1 : ℝ) : ℂ) ^ 2)
        + 2 * π * I * ((((n.1 : ℝ) + c0 : ℝ) : ℂ) * d0' + (((n.2 : ℝ) + c1 : ℝ) : ℂ) * d1'))
        + κ + k * (2 * π * I)) :
    Th2 α β γ c0 c1 d0 d1 = cexp κ * Th2 α' β' γ' c0 c1 d0' d1' := by
  rw [Th2, Th2, ← tsum_mul_left]
  congr 1; funext n
  obtain ⟨k, hk⟩ := h n
  rw [term2, hk, Complex.exp_add, Complex.exp_add, exp_int_mul_two_pi_mul_I, term2]
  ring

theorem cast_even (n : ℤ) : ∃ t : ℤ, ((n : ℂ) * (n + 1)) = t + t := by
  obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
  exact ⟨t, by exact_mod_cast ht⟩

/-- `U(c) = θ[c; 0](2W)` for `c ∈ {0, 1/2}²`. -/
def U (c0 c1 : ℝ) : ℂ := Th2 (2 * wa) (2 * wb) (2 * wc) c0 c1 0 0

theorem U00 : U 0 0 = th1 τ6 0 0 * th1 τ3 0 (1 / 2) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 0) (d1' := 1 / 2) 0, th2_diag τ6_im τ3_im]
  · simp
  intro n
  obtain ⟨t, ht⟩ := cast_even (n.2 - 1)
  refine ⟨n.1 ^ 2 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U10 : U (1 / 2) 0 = I * (th1 τ6 (1 / 2) 0 * th1 τ3 0 0) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 0) (d1' := 0) (π * I / 2),
    th2_diag τ6_im τ3_im]
  · congr 1
    rw [show (π : ℂ) * I / 2 = π / 2 * I by ring, Complex.exp_mul_I]
    have h1 : Complex.cos (π / 2) = 0 := by exact_mod_cast Real.cos_pi_div_two
    have h2 : Complex.sin (π / 2) = 1 := by exact_mod_cast Real.sin_pi_div_two
    rw [h1, h2]; ring
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U01 : U 0 (1 / 2) = cexp (π * I / 4) * (th1 τ6 0 (1 / 2) * th1 τ3 (1 / 2) 0) := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 1 / 2) (d1' := 0) (π * I / 4),
    th2_diag τ6_im τ3_im]
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 * n.2 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

theorem U11 : U (1 / 2) (1 / 2) = 0 := by
  rw [U, th2_phase (α' := τ6) (β' := 0) (γ' := τ3) (d0' := 1 / 2) (d1' := 1 / 2) (π * I / 4),
    th2_diag τ6_im τ3_im, th1_odd]
  · simp
  intro n
  obtain ⟨t, ht⟩ := cast_even n.2
  refine ⟨n.1 ^ 2 + n.1 * n.2 + n.1 + t, ?_⟩
  rw [h2wa, h2wb, h2wc]; push_cast at ht ⊢
  linear_combination (π * I) * ht

/-! ## The cubic modular equation `θ₃(τ)θ₃(3τ) = θ₂(τ)θ₂(3τ) + θ₄(τ)θ₄(3τ)` -/

/-- `(ε, r, s) ↦ (r + s + ε, r − s)`. -/
def cubE1 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (w.2.1 + w.2.2 + (w.1 : ℕ), w.2.1 - w.2.2)
  invFun mn := (if (mn.1 + mn.2) % 2 = 0 then 0 else 1,
    ((mn.1 + mn.2 - (if (mn.1 + mn.2) % 2 = 0 then 0 else 1)) / 2,
     (mn.1 + mn.2 - (if (mn.1 + mn.2) % 2 = 0 then 0 else 1)) / 2 - mn.2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv mn := by
    obtain ⟨m, n⟩ := mn
    by_cases h : (m + n) % 2 = 0 <;> simp [h] <;> omega

/-- `(ε, r, s) ↦ (2r − s + ε, s)`. -/
def cubE2 : Fin 2 × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun w := (2 * w.2.1 - w.2.2 + (w.1 : ℕ), w.2.2)
  invFun uv := (if (uv.1 + uv.2) % 2 = 0 then 0 else 1,
    ((uv.1 + uv.2 - (if (uv.1 + uv.2) % 2 = 0 then 0 else 1)) / 2, uv.2))
  left_inv w := by
    obtain ⟨σ, p, q⟩ := w
    fin_cases σ <;> simp <;> omega
  right_inv uv := by
    obtain ⟨u, v⟩ := uv
    by_cases h : (u + v) % 2 = 0 <;> simp [h] <;> omega

/-- `(r, s) ↦ (r − s, −1 − s)`. -/
def cubE3 : ℤ × ℤ ≃ ℤ × ℤ where
  toFun w := (w.1 - w.2, -1 - w.2)
  invFun w := (w.1 - 1 - w.2, -1 - w.2)
  left_inv w := by obtain ⟨r, s⟩ := w; simp <;> omega
  right_inv w := by obtain ⟨r, s⟩ := w; simp <;> omega

theorem cubic {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 * th1 (3 * τ) 0 0 =
      th1 τ (1 / 2) 0 * th1 (3 * τ) (1 / 2) 0 + th1 τ 0 (1 / 2) * th1 (3 * τ) 0 (1 / 2) := by
  have h3 : 0 < (3 * τ).im := by simp; linarith
  have hQ : ∀ x y : ℝ, τ.im * (x ^ 2 + y ^ 2) ≤ τ.im * x ^ 2 + 2 * (0 : ℂ).im * x * y + (3 * τ).im * y ^ 2 := by
    intro x y; simp; nlinarith [sq_nonneg y]
  rw [← th2_diag hτ h3, ← th2_diag hτ h3, ← th2_diag hτ h3]
  set F := term2 τ 0 (3 * τ) 0 0 0 0
  set G := term2 τ 0 (3 * τ) 0 0 (1 / 2) (1 / 2)
  set H := term2 τ 0 (3 * τ) (1 / 2) (1 / 2) 0 0
  have hF : Summable F := summable_term2 hτ hQ _ _ _ _
  have hG : Summable G := summable_term2 hτ hQ _ _ _ _
  have hH : Summable H := summable_term2 hτ hQ _ _ _ _
  -- the phase: `G(m,n) = (−1)^{m+n} F(m,n)`
  have hGF : ∀ m n : ℤ, G (m, n) = cexp (((m + n : ℤ) : ℂ) * (π * I)) * F (m, n) := by
    intro m n
    simp only [G, F, term2, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hev : ∀ r s : ℤ, G (r + s, r - s) = F (r + s, r - s) := by
    intro r s
    rw [hGF, show (((r + s + (r - s) : ℤ) : ℂ) * (π * I)) = ((r : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      exp_int_mul_two_pi_mul_I, one_mul]
  have hod : ∀ r s : ℤ, G (r + s + 1, r - s) = -F (r + s + 1, r - s) := by
    intro r s
    rw [hGF, show (((r + s + 1 + (r - s) : ℤ) : ℂ) * (π * I)) = ((r : ℤ) : ℂ) * (2 * π * I) + π * I by
      push_cast; ring, Complex.exp_add, exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I]
    ring
  have hFH : ∀ r s : ℤ, F (r + s + 1, r - s) = H (2 * r - s, s) := by
    intro r s
    simp only [F, H, term2]
    congr 1; push_cast; ring
  have hHH : ∀ r s : ℤ, H (2 * r - s + 1, s) = H (2 * (r - s) - (-1 - s), -1 - s) := by
    intro r s
    simp only [H, term2]
    congr 1; push_cast; ring
  -- LHS − θ₄θ₄' = 2 Σ F(r+s+1, r−s)
  have hL : Th2 τ 0 (3 * τ) 0 0 0 0 - Th2 τ 0 (3 * τ) 0 0 (1 / 2) (1 / 2) =
      2 * ∑' w : ℤ × ℤ, F (w.1 + w.2 + 1, w.1 - w.2) := by
    rw [Th2, Th2, ← hF.tsum_sub hG]
    have hs : Summable (fun w => (F - G) (cubE1 w)) := cubE1.summable_iff.2 (hF.sub hG)
    rw [show (fun n => F n - G n) = (F - G) from rfl, ← cubE1.tsum_eq, hs.tsum_prod, tsum_fintype,
      Fin.sum_univ_two, ← tsum_mul_left]
    have h0 : ∀ w : ℤ × ℤ, (F - G) (cubE1 (0, w)) = 0 := by
      intro w; simp only [cubE1, Equiv.coe_fn_mk, Pi.sub_apply, Fin.val_zero, Nat.cast_zero, add_zero]
      rw [hev]; ring
    have h1 : ∀ w : ℤ × ℤ, (F - G) (cubE1 (1, w)) = 2 * F (w.1 + w.2 + 1, w.1 - w.2) := by
      intro w; simp only [cubE1, Equiv.coe_fn_mk, Pi.sub_apply, Fin.val_one, Nat.cast_one]
      rw [hod]; ring
    simp only [h0, h1, tsum_zero, zero_add]
  have hR : Th2 τ 0 (3 * τ) (1 / 2) (1 / 2) 0 0 = 2 * ∑' w : ℤ × ℤ, H (2 * w.1 - w.2, w.2) := by
    rw [Th2]
    have hs : Summable (fun w => H (cubE2 w)) := cubE2.summable_iff.2 hH
    rw [← cubE2.tsum_eq, hs.tsum_prod, tsum_fintype, Fin.sum_univ_two]
    have h1 : ∑' w : ℤ × ℤ, H (cubE2 (1, w)) = ∑' w : ℤ × ℤ, H (2 * w.1 - w.2, w.2) := by
      simp only [cubE2, Equiv.coe_fn_mk, Fin.val_one, Nat.cast_one]
      conv_rhs => rw [← cubE3.tsum_eq]
      congr 1; funext w
      simp only [cubE3, Equiv.coe_fn_mk]
      exact hHH w.1 w.2
    rw [h1]
    simp only [cubE2, Equiv.coe_fn_mk, Fin.val_zero, Nat.cast_zero, add_zero]
    ring
  have hLR : ∑' w : ℤ × ℤ, F (w.1 + w.2 + 1, w.1 - w.2) = ∑' w : ℤ × ℤ, H (2 * w.1 - w.2, w.2) :=
    tsum_congr fun w => hFH w.1 w.2
  linear_combination hL - hR + 2 * hLR

end CM24
