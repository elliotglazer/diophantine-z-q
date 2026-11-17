import ZInQKernel.OneProof.H.TailZ18

set_option linter.all false
open Complex Matrix
open scoped Real

noncomputable section

namespace GapTheta
open CM24

/-- Positive-definite imaginary part of the symmetric matrix `[[α, β], [β, γ]]`. -/
def PDq (α β γ : ℂ) : Prop := 0 < α.im ∧ 0 < α.im * γ.im - β.im ^ 2

theorem PDq.bound {α β γ : ℂ} (h : PDq α β γ) : ∃ δ : ℝ, 0 < δ ∧
    ∀ x y : ℝ, δ * (x ^ 2 + y ^ 2) ≤ α.im * x ^ 2 + 2 * β.im * x * y + γ.im * y ^ 2 := by
  obtain ⟨ha, hd⟩ := h
  have hc : 0 < γ.im := by nlinarith [sq_nonneg β.im]
  refine ⟨(α.im * γ.im - β.im ^ 2) / (α.im + γ.im), div_pos hd (by linarith), fun x y => ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (α.im * x + β.im * y), sq_nonneg (β.im * x + γ.im * y)]

theorem PDq.summable {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Summable (term2 α β γ c0 c1 d0 d1) := by
  obtain ⟨δ, hδ, hQ⟩ := h.bound
  exact summable_term2 hδ hQ c0 c1 d0 d1

theorem PDq.swap {α β γ : ℂ} (h : PDq α β γ) : PDq γ β α := by
  obtain ⟨ha, hd⟩ := h
  exact ⟨by nlinarith [sq_nonneg β.im], by linarith⟩

theorem PDq.ne_zero {α β γ : ℂ} (h : PDq α β γ) : α ≠ 0 := fun h0 => by
  have := h.1; rw [h0] at this; simp at this

theorem PDq.j1 {α β γ : ℂ} (h : PDq α β γ) : PDq (-1 / α) (β / α) (γ - β ^ 2 / α) := by
  obtain ⟨ha, hd⟩ := h
  have hn : 0 < Complex.normSq α := Complex.normSq_pos.2 (fun h0 => by rw [h0] at ha; simp at ha)
  have e1 : (-1 / α).im = α.im / Complex.normSq α := by
    rw [Complex.div_im]; simp [neg_div]
  have key : (-1 / α).im * (γ - β ^ 2 / α).im - (β / α).im ^ 2 =
      (α.im * γ.im - β.im ^ 2) / Complex.normSq α := by
    simp only [Complex.div_im, Complex.div_re, Complex.sub_im, pow_two, Complex.mul_im,
      Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    rw [Complex.normSq_apply] at hn ⊢
    field_simp
    ring
  refine ⟨by rw [e1]; exact div_pos ha hn, by rw [key]; exact div_pos hd hn⟩

theorem PDq.det_ne {α β γ : ℂ} (h : PDq α β γ) : α * γ - β ^ 2 ≠ 0 := by
  have h1 := h.j1.swap.ne_zero
  have h0 := h.ne_zero
  have : α * γ - β ^ 2 = α * (γ - β ^ 2 / α) := by field_simp
  rw [this]; exact mul_ne_zero h0 h1

/-- **Full inversion `Ω ↦ −Ω⁻¹`**, squared (two partial inversions `pi0` and two swaps). -/
theorem inv_sq {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = -(1 / (α * γ - β ^ 2)) * cexp (4 * π * I * (c0 * d0 + c1 * d1)) *
      Th2 (-γ / (α * γ - β ^ 2)) (β / (α * γ - β ^ 2)) (-α / (α * γ - β ^ 2)) (-d0) (-d1) c0 c1 ^ 2 := by
  have h1 := h.j1
  have h1s := h1.swap
  have h2 := h1s.j1
  have hα := h.ne_zero
  have hγ1 := h1s.ne_zero
  have hΔ := h.det_ne
  rw [pi0 h.1 c0 c1 d0 d1 (h.summable _ _ _ _) (h1.summable _ _ _ _), th2_swap,
    pi0 h1s.1 _ _ _ _ (h1s.summable _ _ _ _) (h2.summable _ _ _ _), th2_swap]
  have e1 : -1 / α - (β / α) ^ 2 / (γ - β ^ 2 / α) = -γ / (α * γ - β ^ 2) := by
    field_simp; ring
  have e2 : β / α / (γ - β ^ 2 / α) = β / (α * γ - β ^ 2) := by
    field_simp
  have e3 : -1 / (γ - β ^ 2 / α) = -α / (α * γ - β ^ 2) := by
    field_simp
  rw [e1, e2, e3]
  simp only [mul_pow, cpow_half_sq]
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have ex : cexp (4 * π * I * (c0 * d0 + c1 * d1)) =
      cexp (((2 : ℕ) : ℂ) * (2 * π * I * c0 * d0)) * cexp (((2 : ℕ) : ℂ) * (2 * π * I * c1 * d1)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [ex]
  have : (γ - β ^ 2 / α) = (α * γ - β ^ 2) / α := by field_simp
  rw [this]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring


/-- `inv_sq` solved for the inverted side. -/
theorem inv_sq' {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Th2 (-γ / (α * γ - β ^ 2)) (β / (α * γ - β ^ 2)) (-α / (α * γ - β ^ 2)) c0 c1 d0 d1 ^ 2 =
      -(α * γ - β ^ 2) * cexp (4 * π * I * (c0 * d0 + c1 * d1)) * Th2 α β γ d0 d1 (-c0) (-c1) ^ 2 := by
  have e := inv_sq h d0 d1 (-c0) (-c1)
  simp only [neg_neg] at e
  rw [e]
  have hΔ := h.det_ne
  have hx : cexp (4 * π * I * (c0 * d0 + c1 * d1)) * cexp (4 * π * I * (d0 * ((-c0 : ℝ) : ℂ) + d1 * ((-c1 : ℝ) : ℂ))) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; ring
  rw [show ∀ (D e1 e2 X : ℂ), -D * e1 * (-(1 / D) * e2 * X) = (D * (1 / D)) * (e1 * e2) * X from
    fun _ _ _ _ => by ring, hx, mul_one_div_cancel hΔ, one_mul, one_mul]

/-- **Translation `Ω ↦ Ω + S`** by an integral symmetric `S = [[s00, s01], [s01, s11]]`. -/
theorem th2_trans {α β γ α' β' γ' : ℂ} (s00 s01 s11 : ℤ) (hα : α' = α + s00) (hβ : β' = β + s01)
    (hγ : γ' = γ + s11) (c0 c1 d0 d1 : ℝ) :
    Th2 α' β' γ' c0 c1 d0 d1 =
      cexp (-(π * I * (s00 * ((c0 : ℂ) ^ 2 + c0) + s11 * ((c1 : ℂ) ^ 2 + c1) + 2 * s01 * c0 * c1))) *
      Th2 α β γ c0 c1 (d0 + s00 * (c0 + 1 / 2) + s01 * c1) (d1 + s11 * (c1 + 1 / 2) + s01 * c0) := by
  subst hα hβ hγ
  apply th2_phase
  intro n
  obtain ⟨t0, ht0⟩ := cast_even (n.1 - 1)
  obtain ⟨t1, ht1⟩ := cast_even (n.2 - 1)
  refine ⟨s00 * t0 + s11 * t1 + s01 * (n.1 * n.2), ?_⟩
  push_cast at ht0 ht1 ⊢
  linear_combination (π * I * s00) * ht0 + (π * I * s11) * ht1

/-- **Rotation by `diag(1, −1)`**: negating the off-diagonal entry. -/
theorem th2_neg (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) :
    Th2 α (-β) γ c0 c1 d0 d1 = Th2 α β γ c0 (-c1) d0 (-d1) := by
  rw [Th2, Th2, ← (Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)).tsum_eq]
  congr 1; funext n
  simp only [term2, Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.neg_apply, Prod.map_fst, Prod.map_snd, id]
  congr 1; push_cast; ring

/-- **Reduction of half-integral characteristics mod `ℤ`**, squared (the sign `±1` squares away). -/
theorem th2_sq_red (α β γ : ℂ) {c0 c1 d0 d1 : ℝ} (x0 x1 y0 y1 : ℤ) (h0 : c0 = (x0 : ℝ) / 2)
    (h1 : c1 = (x1 : ℝ) / 2) (h2 : d0 = (y0 : ℝ) / 2) (h3 : d1 = (y1 : ℝ) / 2) :
    Th2 α β γ c0 c1 d0 d1 ^ 2 = Th2 α β γ (((x0 % 2 : ℤ) : ℝ) / 2) (((x1 % 2 : ℤ) : ℝ) / 2)
      (((y0 % 2 : ℤ) : ℝ) / 2) (((y1 % 2 : ℤ) : ℝ) / 2) ^ 2 := by
  have r : ∀ x : ℤ, (x : ℝ) / 2 = ((x % 2 : ℤ) : ℝ) / 2 + ((x / 2 : ℤ) : ℝ) := fun x => by
    have := Int.emod_add_mul_ediv x 2
    have : (x : ℝ) = ((x % 2 : ℤ) : ℝ) + 2 * ((x / 2 : ℤ) : ℝ) := by exact_mod_cast this.symm
    linarith
  rw [h0, h1, h2, h3, r x0, r x1, r y0, r y1, th2_shift_c, th2_shift_d, mul_pow, ← Complex.exp_nat_mul]
  have : cexp (((2 : ℕ) : ℂ) * (2 * π * I * ((((x0 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y0 / 2 : ℤ) : ℂ) +
      (((x1 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y1 / 2 : ℤ) : ℂ)))) = 1 := by
    rw [show ((2 : ℕ) : ℂ) * (2 * π * I * ((((x0 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y0 / 2 : ℤ) : ℂ) +
      (((x1 % 2 : ℤ) : ℝ) / 2 : ℝ) * ((y1 / 2 : ℤ) : ℂ))) =
      (((x0 % 2) * (y0 / 2) + (x1 % 2) * (y1 / 2) : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
    exact exp_int_mul_two_pi_mul_I _
  rw [this, one_mul]


/-! ## Siegel space, characteristics, assembly -/

open HDec.PkgI1 (SiegelH2 thetaConst evenChars thetaSum8 thetaProd2 spAct spFactor Char2 card_evenChars)

theorem pdq_of_siegel {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    Ω 1 0 = Ω 0 1 ∧ PDq (Ω 0 0) (Ω 0 1) (Ω 1 1) := by
  obtain ⟨hT, hP⟩ := hΩ
  have hs : Ω 1 0 = Ω 0 1 := by
    have := congrFun (congrFun hT 0) 1; simpa [Matrix.transpose_apply] using this
  refine ⟨hs, ?_, ?_⟩
  · have := hP.diag_pos (i := 0); simpa using this
  · have := hP.det_pos
    rw [Matrix.det_fin_two] at this
    simp only [Matrix.map_apply, hs] at this
    nlinarith

theorem PDq.add {α β γ : ℂ} (h : PDq α β γ) (s00 s01 s11 : ℤ) :
    PDq (α + s00) (β + s01) (γ + s11) := by
  simpa [PDq] using h

/-- The residue of an integer mod 2 as an element of `Fin 2`. -/
def fin2 (x : ℤ) : Fin 2 := ⟨(x % 2).toNat, by omega⟩

theorem fin2_cast (x : ℤ) : (((fin2 x : Fin 2) : ℕ) : ℝ) = ((x % 2 : ℤ) : ℝ) := by
  have h : (((x % 2).toNat : ℕ) : ℤ) = x % 2 := Int.toNat_of_nonneg (Int.emod_nonneg x (by norm_num))
  rw [fin2, Fin.val_mk, ← h]; norm_cast

theorem exp_quarter_pow4 (N : ℤ) (h : N % 2 = 0) : cexp (π * I * (N : ℂ) / 4) ^ 4 = 1 := by
  rw [← Complex.exp_nat_mul]
  obtain ⟨k, hk⟩ : ∃ k, N = 2 * k := ⟨N / 2, by omega⟩
  rw [show ((4 : ℕ) : ℂ) * (π * I * (N : ℂ) / 4) = (k : ℂ) * (2 * π * I) by rw [hk]; push_cast; ring]
  exact exp_int_mul_two_pi_mul_I k

/-- **Assembly.** A permutation of the even characteristics with quarter-root phases gives both
transformation laws. -/
theorem assemble {Ω Ω' : Matrix (Fin 2) (Fin 2) ℂ} (D : ℂ) (σ : Char2 → Char2) (N : Char2 → ℤ)
    (h : ∀ m ∈ evenChars, thetaConst m Ω' ^ 2 = -D * cexp (π * I * (N m : ℂ) / 4) * thetaConst (σ m) Ω ^ 2)
    (himg : evenChars.image σ = evenChars)
    (hinj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ a = σ b → a = b)
    (hev : ∀ m ∈ evenChars, N m % 2 = 0) (hsum : (∑ m ∈ evenChars, N m) % 8 = 0) :
    thetaSum8 Ω' = D ^ 4 * thetaSum8 Ω ∧ thetaProd2 Ω' = D ^ 10 * thetaProd2 Ω := by
  have hinj' : Set.InjOn σ (evenChars : Set Char2) := fun a ha b hb e => hinj a ha b hb e
  have e8 : ∑ m ∈ evenChars, thetaConst m Ω ^ 8 = ∑ m ∈ evenChars, thetaConst (σ m) Ω ^ 8 := by
    rw [← Finset.sum_image (f := fun m => thetaConst m Ω ^ 8) hinj', himg]
  have e2 : ∏ m ∈ evenChars, thetaConst m Ω ^ 2 = ∏ m ∈ evenChars, thetaConst (σ m) Ω ^ 2 := by
    rw [← Finset.prod_image (f := fun m => thetaConst m Ω ^ 2) hinj', himg]
  constructor
  · rw [thetaSum8, thetaSum8, e8, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show thetaConst m Ω' ^ 8 = (thetaConst m Ω' ^ 2) ^ 4 by ring, h m hm, mul_pow, mul_pow,
      exp_quarter_pow4 _ (hev m hm)]
    ring
  · rw [thetaProd2, thetaProd2, e2, Finset.prod_congr rfl h,
      Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, card_evenChars,
      ← Complex.exp_sum]
    obtain ⟨k, hk⟩ : ∃ k, ∑ m ∈ evenChars, N m = 8 * k := ⟨(∑ m ∈ evenChars, N m) / 8, by omega⟩
    have : ∑ m ∈ evenChars, π * I * (N m : ℂ) / 4 = (k : ℂ) * (2 * π * I) := by
      rw [← Finset.sum_div, ← Finset.mul_sum, ← Int.cast_sum, hk]; push_cast; ring
    rw [this, exp_int_mul_two_pi_mul_I]
    ring


/-! ## `M6` -/

open HDec.HSyn.G0Split.FibreQM.PeriodGlue (M4 M6 M4_map M6_map A4 B4 C4 D4 A6 B6 C6 D6)

theorem spAct_M6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1)
    (hΔ : (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 ≠ 0) :
    spAct M6 Ω = !![-(Ω 0 0 + 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2),
      -((Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2));
      -((Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)),
      -(Ω 1 1 + 2) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)] := by
  unfold spAct
  simp only [M6_map, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  have hdet : (C6 * Ω + D6).det = (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [C6, D6, hs]
    ring
  letI := Matrix.invertibleOfIsUnitDet (C6 * Ω + D6) (isUnit_iff_ne_zero.mpr (hdet ▸ hΔ))
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [A6, B6, C6, D6, hs] <;> field_simp <;> ring

theorem spFactor_M6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spFactor M6 Ω = (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 := by
  unfold spFactor
  simp only [M6_map, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [C6, D6, hs]
  ring

/-- The characteristic permutation of `M6`. -/
def σ6 (m : Char2) : Char2 :=
  (![fin2 (-((m.2 1 : ℕ) : ℤ)), fin2 ((m.2 0 : ℕ) : ℤ)],
   ![fin2 (((m.1 1 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 1 - ((m.2 0 : ℕ) : ℤ)),
     fin2 (-((m.1 0 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) + 2 + ((m.2 1 : ℕ) : ℤ))])

/-- The phase exponent of `M6` (in units of `πi/4`). -/
def N6 (m : Char2) : ℤ :=
  4 * ((m.1 0 : ℕ) : ℤ) * ((m.2 0 : ℕ) : ℤ) + 4 * ((m.1 1 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)
    - 2 * ((m.2 1 : ℕ) : ℤ) ^ 2 + 4 * ((m.2 1 : ℕ) : ℤ) - 4 * ((m.2 0 : ℕ) : ℤ) ^ 2
    - 8 * ((m.2 0 : ℕ) : ℤ) - 4 * ((m.2 0 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)

theorem sq6 (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (spAct M6 Ω) ^ 2 =
      -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) * cexp (π * I * (N6 m : ℂ) / 4) *
        thetaConst (σ6 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  have hpd1 : PDq (Ω 0 0 + 1) (Ω 0 1 - 1) (Ω 1 1 + 2) := by simpa [PDq] using hpd
  rw [spAct_M6 hs hpd1.det_ne, thetaConst_eq _ _ (by simp), thetaConst_eq _ _ hs]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_neg, th2_swap, inv_sq' hpd1,
    th2_trans (α := Ω 0 0) (β := Ω 0 1) (γ := Ω 1 1) 1 (-1) 2 (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring), mul_pow]
  rw [th2_sq_red _ _ _ (-((m.2 1 : ℕ) : ℤ)) ((m.2 0 : ℕ) : ℤ)
    (((m.1 1 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 1 - ((m.2 0 : ℕ) : ℤ))
    (-((m.1 0 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) + 2 + ((m.2 1 : ℕ) : ℤ))
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σ6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  rw [show ∀ (D e1 e2 T : ℂ), -D * e1 * (e2 ^ 2 * T) = -D * (e1 * e2 ^ 2) * T from
    fun _ _ _ _ => by ring]
  congr 2
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  simp only [N6]
  push_cast
  ring


theorem σ6_img : evenChars.image σ6 = evenChars := by decide
theorem σ6_inj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ6 a = σ6 b → a = b := by decide
theorem N6_even : ∀ m ∈ evenChars, N6 m % 2 = 0 := by decide
theorem N6_sum : (∑ m ∈ evenChars, N6 m) % 8 = 0 := by decide

/-- **`M6` on the Siegel space.** -/
theorem thetaM6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaSum8 (spAct M6 Ω) = spFactor M6 Ω ^ 4 * thetaSum8 Ω ∧
      thetaProd2 (spAct M6 Ω) = spFactor M6 Ω ^ 10 * thetaProd2 Ω := by
  rw [spFactor_M6 (pdq_of_siegel hΩ).1]
  exact assemble _ σ6 N6 (fun m _ => sq6 m hΩ) σ6_img σ6_inj N6_even N6_sum

/-! ## `M4` -/

theorem spAct_M4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1)
    (hΔ : (Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2 ≠ 0) :
    spAct M4 Ω = !![-(Ω 0 0 + 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2),
      (Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) + 1;
      (Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) + 1,
      -(Ω 1 1 + 2) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)] := by
  unfold spAct
  simp only [M4_map, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  have hdet : (C4 * Ω + D4).det = -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp [C4, D4, hs]
    ring
  letI := Matrix.invertibleOfIsUnitDet (C4 * Ω + D4) (isUnit_iff_ne_zero.mpr (hdet ▸ neg_ne_zero.2 hΔ))
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp [A4, B4, C4, D4, hs] <;> field_simp <;> ring

theorem spFactor_M4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spFactor M4 Ω = -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) := by
  unfold spFactor
  simp only [M4_map, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
  simp [C4, D4, hs]
  ring

/-- The characteristic permutation of `M4`. -/
def σ4 (m : Char2) : Char2 :=
  (![fin2 (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)), fin2 (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))],
   ![fin2 (((m.1 0 : ℕ) : ℤ) - 2 * ((m.1 1 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ) - ((m.2 0 : ℕ) : ℤ) + 1),
     fin2 (-2 * ((m.1 0 : ℕ) : ℤ) + 2 * ((m.1 1 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 2)])

/-- The phase exponent of `M4` (in units of `πi/4`). -/
def N4 (m : Char2) : ℤ :=
  4 * ((m.1 0 : ℕ) : ℤ) * ((m.1 1 : ℕ) : ℤ) + 4 * ((m.1 1 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)
    + 4 * ((m.1 0 : ℕ) : ℤ) * ((m.2 0 : ℕ) : ℤ)
    - 2 * (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) ^ 2 - 4 * (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ))
    - 4 * (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ)) ^ 2 - 8 * (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))
    + 4 * (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) * (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))

theorem sq4 (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (spAct M4 Ω) ^ 2 =
      -((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2) * cexp (π * I * (N4 m : ℂ) / 4) *
        thetaConst (σ4 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  have hpd1 : PDq (Ω 0 0 + 1) (Ω 0 1 - 1) (Ω 1 1 + 2) := by simpa [PDq] using hpd
  rw [spAct_M4 hs hpd1.det_ne, thetaConst_eq _ _ (by simp), thetaConst_eq _ _ hs]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_trans (α := -(Ω 0 0 + 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2))
      (β := (Ω 0 1 - 1) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2))
      (γ := -(Ω 1 1 + 2) / ((Ω 0 0 + 1) * (Ω 1 1 + 2) - (Ω 0 1 - 1) ^ 2)) 0 1 0
      (by push_cast; ring) (by push_cast; ring) (by push_cast; ring),
    mul_pow, th2_swap, inv_sq' hpd1,
    th2_trans (α := Ω 0 0) (β := Ω 0 1) (γ := Ω 1 1) 1 (-1) 2 (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring), mul_pow]
  rw [th2_sq_red _ _ _ (((m.1 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) (((m.1 1 : ℕ) : ℤ) + ((m.2 0 : ℕ) : ℤ))
    (((m.1 0 : ℕ) : ℤ) - 2 * ((m.1 1 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ) - ((m.2 0 : ℕ) : ℤ) + 1)
    (-2 * ((m.1 0 : ℕ) : ℤ) + 2 * ((m.1 1 : ℕ) : ℤ) + 2 * ((m.2 0 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ) + 2)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σ4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  rw [show ∀ (D e0 e1 e2 T : ℂ), e0 ^ 2 * (-D * e1 * (e2 ^ 2 * T)) = -D * (e0 ^ 2 * e1 * e2 ^ 2) * T from
    fun _ _ _ _ _ => by ring]
  congr 2
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  simp only [N4]
  push_cast
  ring

theorem σ4_img : evenChars.image σ4 = evenChars := by decide
theorem σ4_inj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ4 a = σ4 b → a = b := by decide
theorem N4_even : ∀ m ∈ evenChars, N4 m % 2 = 0 := by decide
theorem N4_sum : (∑ m ∈ evenChars, N4 m) % 8 = 0 := by decide

/-- **`M4` on the Siegel space.** -/
theorem thetaM4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaSum8 (spAct M4 Ω) = spFactor M4 Ω ^ 4 * thetaSum8 Ω ∧
      thetaProd2 (spAct M4 Ω) = spFactor M4 Ω ^ 10 * thetaProd2 Ω := by
  have h := assemble _ σ4 N4 (fun m _ => sq4 m hΩ) σ4_img σ4_inj N4_even N4_sum
  rw [spFactor_M4 (pdq_of_siegel hΩ).1, Even.neg_pow (by decide), Even.neg_pow (by decide)]
  exact h


/-! ## The specialized target of gap-triage A2 -/

open HDec.QMSplit.Theta (psi4 chi10)

/-- **`ThetaModularityM46`** (gap-triage A2, verbatim up to name qualification): Igusa's `ψ₄`, `χ₁₀`
transform with weights 4 and 10 under the two symplectic matrices `M4`, `M6` at the period matrices
`Ω(z)`, the only instances every consumer of `IgusaPsi4`/`IgusaChi10` uses. -/
def ThetaModularityM46 : Prop :=
  ∀ M ∈ ({M4, M6} : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)), ∀ z : ℂ, 0 < z.im →
    psi4 (spAct M (HDec.PkgI1.Omega z)) = spFactor M (HDec.PkgI1.Omega z) ^ 4 * psi4 (HDec.PkgI1.Omega z) ∧
    chi10 (spAct M (HDec.PkgI1.Omega z)) = spFactor M (HDec.PkgI1.Omega z) ^ 10 * chi10 (HDec.PkgI1.Omega z)

/-- The same at every point of the Siegel space (stronger; what is proved). -/
def ThetaModularityM46Siegel : Prop :=
  ∀ M ∈ ({M4, M6} : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)), ∀ Ω ∈ SiegelH2,
    psi4 (spAct M Ω) = spFactor M Ω ^ 4 * psi4 Ω ∧ chi10 (spAct M Ω) = spFactor M Ω ^ 10 * chi10 Ω

theorem thetaModularityM46Siegel : ThetaModularityM46Siegel := by
  intro M hM Ω hΩ
  have h : thetaSum8 (spAct M Ω) = spFactor M Ω ^ 4 * thetaSum8 Ω ∧
      thetaProd2 (spAct M Ω) = spFactor M Ω ^ 10 * thetaProd2 Ω := by
    rcases hM with rfl | rfl
    · exact thetaM4 hΩ
    · exact thetaM6 hΩ
  simp only [psi4, chi10]
  exact ⟨by rw [h.1]; ring, by rw [h.2]; ring⟩

/-- **`ThetaModularityM46` (proved, no hypotheses).** -/
theorem thetaModularityM46 : ThetaModularityM46 := fun M hM z hz =>
  thetaModularityM46Siegel M hM _ (HDec.HSyn.G0Split.FibreQM.PeriodMap.omegaSiegel_proof z hz)

/-! ## Consumer forms: `S8WeightExact` and the weight-20 automorphy without `ThetaModularity` -/

section Consumers
open HDec.HSyn.G0Split.FibreQM HDec.HSyn.G0Split.FibreQM.PeriodMap HDec.HSyn.G0Split.FibreQM.PeriodGlue
open UpperHalfPlane (num denom coe_smul_of_det_pos denom_ne_zero)

theorem thetaSum8_M (hT : ThetaModularityM46) {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hM : M ∈ ({M4, M6} : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ))) (z : ℂ) (hz : 0 < z.im) :
    thetaSum8 (spAct M (HDec.PkgI1.Omega z)) =
      spFactor M (HDec.PkgI1.Omega z) ^ 4 * thetaSum8 (HDec.PkgI1.Omega z) := by
  have h := (hT M hM z hz).1
  simp only [psi4] at h
  linear_combination 4 * h

theorem thetaProd2_M (hT : ThetaModularityM46) {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ}
    (hM : M ∈ ({M4, M6} : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ))) (z : ℂ) (hz : 0 < z.im) :
    thetaProd2 (spAct M (HDec.PkgI1.Omega z)) =
      spFactor M (HDec.PkgI1.Omega z) ^ 10 * thetaProd2 (HDec.PkgI1.Omega z) := by
  have h := (hT M hM z hz).2
  simp only [chi10] at h
  linear_combination (-(2 : ℂ) ^ 14) * h

/-- `g8Auto_of_sp` with the modularity at the one matrix `M` in place of `ThetaModularity`. -/
theorem g8Auto_of_sp' (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (hT : ∀ z : ℂ, 0 < z.im → thetaSum8 (spAct M (HDec.PkgI1.Omega z)) =
      spFactor M (HDec.PkgI1.Omega z) ^ 4 * thetaSum8 (HDec.PkgI1.Omega z))
    (hrel : ∀ z : ℂ, 0 < z.im →
      HDec.PkgI1.spAct M (HDec.PkgI1.Omega z) = HDec.PkgI1.Omega (num g z / denom g z))
    (ε : ℂ) (hε : ε ^ 4 = 1)
    (hfac : ∀ z : ℂ, 0 < z.im →
      HDec.PkgI1.spFactor M (HDec.PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
        ((z - 3) * (z + 1)) =
      ε * denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) :
    G8Auto g := by
  refine ⟨hdet, fun z => ?_⟩
  have hw : ((g • z : UpperHalfPlane) : ℂ) = num g z / denom g z :=
    coe_smul_of_det_pos (by rwa [detv]) z
  have hwim : 0 < (num g z / denom g z).im := by rw [← hw]; exact (g • z).im_pos
  have hmod := hT z z.im_pos
  rw [hrel z z.im_pos] at hmod
  have hf := hfac z z.im_pos
  unfold G8
  rw [hw, hmod]
  have hf4 : (HDec.PkgI1.spFactor M (HDec.PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1))) ^ 4 =
      (denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) ^ 4 := by
    rw [hf, mul_assoc, mul_pow, hε, one_mul]
  obtain ⟨h3, h4⟩ := sub3_add1_ne z.im_pos
  obtain ⟨h5, h6⟩ := sub3_add1_ne hwim
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  generalize num g z / denom g z = w at *
  field_simp
  linear_combination (HDec.PkgI1.thetaSum8 (HDec.PkgI1.Omega z)) * hf4

/-- `g8Auto_gen` with the modularity at `M` in place of `ThetaModularity`. -/
theorem g8Auto_gen' (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (hT : ∀ z : ℂ, 0 < z.im → thetaSum8 (spAct M (HDec.PkgI1.Omega z)) =
      spFactor M (HDec.PkgI1.Omega z) ^ 4 * thetaSum8 (HDec.PkgI1.Omega z))
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (hI1 : ∀ z : ℂ, dFh (num g z) (denom g z) • (A * Nf z + dF z • B) =
      Nfh (num g z) (denom g z) * (C * Nf z + dF z • D))
    (hI2 : ∀ z : ℂ, (C * Nf z + dF z • D).det * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1)) = -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z))) :
    G8Auto g := by
  have hw : ∀ z : ℂ, 0 < z.im → 0 < (num g z / denom g z).im := fun z hz => by
    have := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_smul_of_det_pos (by rwa [detv])] at this
  have hV : ∀ z : ℂ, 0 < z.im → denom g z ≠ 0 := fun z hz =>
    UpperHalfPlane.denom_ne_zero_of_im g hz.ne'
  have hP : ∀ z : ℂ, 0 < z.im → (C * Nf z + dF z • D).det ≠ 0 := fun z hz h0 => by
    have e := hI2 z
    rw [h0, zero_mul, zero_mul] at e
    obtain ⟨h5, h6⟩ := sub3_add1_ne (hw z hz)
    have h7 : num g z - 3 * denom g z ≠ 0 := fun h => h5 (by
      rw [show num g z = 3 * denom g z by linear_combination h, mul_div_assoc,
        div_self (hV z hz)]; ring)
    have h8 : num g z + denom g z ≠ 0 := fun h => h6 (by
      rw [show num g z = -denom g z by linear_combination h, neg_div, div_self (hV z hz)]; ring)
    have := dF_ne hz
    have : -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ this)) (mul_ne_zero h7 h8)
    exact this e.symm
  refine g8Auto_of_sp' g hdet M hT (fun z hz => ?_) (-1) (by norm_num) (fun z hz => ?_)
  · exact spAct_of_poly M A B C D hM z _ _ (hV z hz) (dF_ne hz) (dF_ne (hw z hz)) (hP z hz) (hI1 z)
  · exact spFactor_of_poly M A B C D hM z _ _ _ (hV z hz) (dF_ne hz) (hI2 z)

theorem g8Auto_g4' (hT : ThetaModularityM46) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = HDec.PkgI1.iota HDec.HSyn.G0Split.FibreQM.PeriodGlue.x4) : G8Auto g := by
  rw [iota_x4] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 2 := by
    rw [hg, Matrix.det_fin_two_of]; linear_combination (-1 : ℝ) * sqrt2_sq'
  have hnum : ∀ z : ℂ, num g z = (√2 : ℂ) * z + z - 3 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = -(√2 : ℂ) + z + 1 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g8Auto_gen' g (by rw [hdet]; norm_num) M4 (thetaSum8_M hT (Or.inl rfl)) A4 B4 C4 D4 M4_map
    (fun z => by rw [hnum, hden]; exact I1_g4 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g4 z

theorem g8Auto_g6' (hT : ThetaModularityM46) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = HDec.PkgI1.iota HDec.HSyn.G0Split.FibreQM.PeriodGlue.x6) : G8Auto g := by
  rw [iota_x6] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
    rw [hg, Matrix.det_fin_two_of]; norm_num
  have hnum : ∀ z : ℂ, num g z = -3 * z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g8Auto_gen' g (by rw [hdet]; norm_num) M6 (thetaSum8_M hT (Or.inr rfl)) A6 B6 C6 D6 M6_map
    (fun z => by rw [hnum, hden]; exact I1_g6 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g6 z

/-- **`S8WeightExact` from `ThetaModularityM46` and `GammaStarGen`** (gap-triage A2's consumer form). -/
theorem s8WeightExact_of' (hT : ThetaModularityM46) (hG : GammaStarGen) : S8WeightExact := by
  intro γ hγ z
  have hmem : γ ∈ G8AutoSubgroup := by
    refine (Subgroup.closure_le (K := G8AutoSubgroup)).mpr ?_ (hG γ hγ)
    rintro g ((hg | hg) | ⟨q, hq, hg⟩)
    · exact g8Auto_g4' hT hg
    · exact g8Auto_g6' hT hg
    · exact g8Auto_scalar q hq hg
  exact hmem.2 z

/-- **`S8WeightExact` from `GammaStarGen` alone.** -/
theorem s8WeightExact_of_gen (hG : GammaStarGen) : S8WeightExact :=
  s8WeightExact_of' thetaModularityM46 hG


/-- `g20Auto_of_sp` with the modularity at the one matrix `M` in place of `ThetaModularity`. -/
theorem g20Auto_of_sp' (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (hT : ∀ z : ℂ, 0 < z.im → thetaProd2 (spAct M (HDec.PkgI1.Omega z)) =
      spFactor M (HDec.PkgI1.Omega z) ^ 10 * thetaProd2 (HDec.PkgI1.Omega z))
    (hrel : ∀ z : ℂ, 0 < z.im →
      HDec.PkgI1.spAct M (HDec.PkgI1.Omega z) = HDec.PkgI1.Omega (num g z / denom g z))
    (ε : ℂ) (hε : ε ^ 10 = 1)
    (hfac : ∀ z : ℂ, 0 < z.im →
      HDec.PkgI1.spFactor M (HDec.PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
        ((z - 3) * (z + 1)) =
      ε * denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) :
    LQ20.G20Auto g := by
  refine ⟨hdet, fun z => ?_⟩
  have hw : ((g • z : UpperHalfPlane) : ℂ) = num g z / denom g z :=
    coe_smul_of_det_pos (by rwa [detv]) z
  have hwim : 0 < (num g z / denom g z).im := by rw [← hw]; exact (g • z).im_pos
  have hmod := hT z z.im_pos
  rw [hrel z z.im_pos] at hmod
  have hf := hfac z z.im_pos
  unfold LQ20.G20
  rw [hw, hmod]
  have hf10 : (HDec.PkgI1.spFactor M (HDec.PkgI1.Omega z) * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1))) ^ 10 =
      (denom g z ^ 2 * ((num g z / denom g z - 3) * (num g z / denom g z + 1))) ^ 10 := by
    rw [hf, mul_assoc, mul_pow, hε, one_mul]
  obtain ⟨h3, h4⟩ := sub3_add1_ne z.im_pos
  obtain ⟨h5, h6⟩ := sub3_add1_ne hwim
  have hD : denom g z ≠ 0 := denom_ne_zero g z
  have hW : ((num g z / denom g z - 3) * (num g z / denom g z + 1)) ^ 10 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero h5 h6)
  have hZ : (((z : ℂ) - 3) * ((z : ℂ) + 1)) ^ 10 ≠ 0 := pow_ne_zero _ (mul_ne_zero h3 h4)
  rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_div_iff hW hZ]
  linear_combination (HDec.PkgI1.thetaProd2 (HDec.PkgI1.Omega z)) * hf10

/-- `g20Auto_gen` with the modularity at `M` in place of `ThetaModularity`. -/
theorem g20Auto_gen' (g : GL (Fin 2) ℝ)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det)
    (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (hT : ∀ z : ℂ, 0 < z.im → thetaProd2 (spAct M (HDec.PkgI1.Omega z)) =
      spFactor M (HDec.PkgI1.Omega z) ^ 10 * thetaProd2 (HDec.PkgI1.Omega z))
    (A B C D : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D)
    (hI1 : ∀ z : ℂ, dFh (num g z) (denom g z) • (A * Nf z + dF z • B) =
      Nfh (num g z) (denom g z) * (C * Nf z + dF z • D))
    (hI2 : ∀ z : ℂ, (C * Nf z + dF z • D).det * ((g : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) *
      ((z - 3) * (z + 1)) = -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z))) :
    LQ20.G20Auto g := by
  have hw : ∀ z : ℂ, 0 < z.im → 0 < (num g z / denom g z).im := fun z hz => by
    have := (g • (⟨z, hz⟩ : UpperHalfPlane)).im_pos
    rwa [← UpperHalfPlane.coe_im, coe_smul_of_det_pos (by rwa [detv])] at this
  have hV : ∀ z : ℂ, 0 < z.im → denom g z ≠ 0 := fun z hz =>
    UpperHalfPlane.denom_ne_zero_of_im g hz.ne'
  have hP : ∀ z : ℂ, 0 < z.im → (C * Nf z + dF z • D).det ≠ 0 := fun z hz h0 => by
    have e := hI2 z
    rw [h0, zero_mul, zero_mul] at e
    obtain ⟨h5, h6⟩ := sub3_add1_ne (hw z hz)
    have h7 : num g z - 3 * denom g z ≠ 0 := fun h => h5 (by
      rw [show num g z = 3 * denom g z by linear_combination h, mul_div_assoc,
        div_self (hV z hz)]; ring)
    have h8 : num g z + denom g z ≠ 0 := fun h => h6 (by
      rw [show num g z = -denom g z by linear_combination h, neg_div, div_self (hV z hz)]; ring)
    have := dF_ne hz
    have : -1 * dF z ^ 2 * ((num g z - 3 * denom g z) * (num g z + denom g z)) ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ this)) (mul_ne_zero h7 h8)
    exact this e.symm
  refine g20Auto_of_sp' g hdet M hT (fun z hz => ?_) (-1) (by norm_num) (fun z hz => ?_)
  · exact spAct_of_poly M A B C D hM z _ _ (hV z hz) (dF_ne hz) (dF_ne (hw z hz)) (hP z hz) (hI1 z)
  · exact spFactor_of_poly M A B C D hM z _ _ _ (hV z hz) (dF_ne hz) (hI2 z)

theorem g20Auto_g4' (hT : ThetaModularityM46) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = HDec.PkgI1.iota HDec.HSyn.G0Split.FibreQM.PeriodGlue.x4) :
    LQ20.G20Auto g := by
  rw [iota_x4] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 2 := by
    rw [hg, Matrix.det_fin_two_of]; linear_combination (-1 : ℝ) * sqrt2_sq'
  have hnum : ∀ z : ℂ, num g z = (√2 : ℂ) * z + z - 3 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = -(√2 : ℂ) + z + 1 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g20Auto_gen' g (by rw [hdet]; norm_num) M4 (thetaProd2_M hT (Or.inl rfl)) A4 B4 C4 D4 M4_map
    (fun z => by rw [hnum, hden]; exact I1_g4 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g4 z

theorem g20Auto_g6' (hT : ThetaModularityM46) {g : GL (Fin 2) ℝ}
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = HDec.PkgI1.iota HDec.HSyn.G0Split.FibreQM.PeriodGlue.x6) :
    LQ20.G20Auto g := by
  rw [iota_x6] at hg
  have hdet : (g : Matrix (Fin 2) (Fin 2) ℝ).det = 3 := by
    rw [hg, Matrix.det_fin_two_of]; norm_num
  have hnum : ∀ z : ℂ, num g z = -3 * z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.num, hg]; simp; ring
  have hden : ∀ z : ℂ, denom g z = z / 2 - 3 / 2 := fun z => by
    simp only [UpperHalfPlane.denom, hg]; simp; ring
  refine g20Auto_gen' g (by rw [hdet]; norm_num) M6 (thetaProd2_M hT (Or.inr rfl)) A6 B6 C6 D6 M6_map
    (fun z => by rw [hnum, hden]; exact I1_g6 z) (fun z => ?_)
  rw [hnum, hden, hdet]; push_cast; exact I2_g6 z

/-- **The exact weight-20 automorphy of `G20` on `Γ*` from `ThetaModularityM46` and `GammaStarGen`**
(same statement as `LQ20.s20WeightExact_of`; gap-triage A2's consumer form). -/
theorem s20WeightExact_of' (hT : ThetaModularityM46) (hG : GammaStarGen) :
    ∀ γ ∈ HDec.PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      LQ20.G20 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 10 =
        denom γ z ^ 20 * LQ20.G20 (z : ℂ) := by
  intro γ hγ z
  have hmem : γ ∈ LQ20.G20AutoSubgroup := by
    refine (Subgroup.closure_le (K := LQ20.G20AutoSubgroup)).mpr ?_ (hG γ hγ)
    rintro g ((hg | hg) | ⟨q, hq, hg⟩)
    · exact g20Auto_g4' hT hg
    · exact g20Auto_g6' hT hg
    · exact LQ20.g20Auto_scalar q hq hg
  exact hmem.2 z

/-- **The weight-20 automorphy from `GammaStarGen` alone.** -/
theorem s20WeightExact_of_gen (hG : GammaStarGen) :
    ∀ γ ∈ HDec.PkgI1.GammaStar, ∀ z : UpperHalfPlane,
      LQ20.G20 ((γ • z : UpperHalfPlane) : ℂ) * (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℝ) : ℂ) ^ 10 =
        denom γ z ^ 20 * LQ20.G20 (z : ℂ) :=
  s20WeightExact_of' thetaModularityM46 hG

end Consumers

end GapTheta
