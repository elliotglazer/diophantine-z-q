namespace CM24
open HDec.LeafQCheck.HM.QMSplit.Value24

/-! ## Bridge to `PkgI1.thetaConst` -/

theorem thetaConst_eq (m : HDec.PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : Ω 1 0 = Ω 0 1) :
    HDec.PkgI1.thetaConst m Ω = Th2 (Ω 0 0) (Ω 0 1) (Ω 1 1) (((m.1 0 : ℕ) : ℝ) / 2) (((m.1 1 : ℕ) : ℝ) / 2)
      (((m.2 0 : ℕ) : ℝ) / 2) (((m.2 1 : ℕ) : ℝ) / 2) := by
  rw [HDec.PkgI1.thetaConst, Th2, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  congr 1; funext p
  simp only [finTwoArrowEquiv_symm_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, term2,
    Matrix.cons_val_zero, Matrix.cons_val_one, hΩ]
  congr 1; push_cast; ring

theorem om24_00 : Om24 0 0 = α0 := by
  apply Complex.ext <;> simp [Om24, α0] <;> ring
theorem om24_01 : Om24 0 1 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_10 : Om24 1 0 = β0 := by
  apply Complex.ext <;> simp [Om24, β0] <;> ring
theorem om24_11 : Om24 1 1 = γ0 := by
  apply Complex.ext <;> simp [Om24, γ0] <;> ring


/-! ## Squares of theta constants at `Ω₂₄` in terms of `U` -/

/-- `𝓔 = 1/((−iα0)(−iγ1))`: the square of the two automorphy factors. -/
def Ecal : ℂ := 1 / (-I * α0) * (1 / (-I * γ1))

theorem cpow_half_sq (x : ℂ) : (1 / x ^ (1 / 2 : ℂ)) ^ 2 = 1 / x := by
  rw [div_pow, one_pow, show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num, Complex.cpow_nat_inv_pow x two_ne_zero]

theorem sq_inv (a0 a1 b0 b1 : ℕ) :
    Th2 α0 β0 γ0 ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ^ 2 =
      Ecal * cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) *
        Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 := by
  have h := invert (a0 : ℝ) (a1 : ℝ) (b0 : ℤ) (b1 : ℤ)
  simp only [Int.cast_natCast] at h
  have e1 : cexp (2 * π * I * ((a0 : ℝ) / 2 : ℝ) * ((b0 : ℝ) / 2 : ℝ)) ^ 2 *
      cexp (2 * π * I * ((a1 : ℝ) / 2 : ℝ) * ((b1 : ℝ) / 2 : ℝ)) ^ 2 =
      cexp (π * I * ((a0 * b0 + a1 * b1 : ℕ) : ℂ)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  rw [h]
  simp only [mul_pow]
  rw [cpow_half_sq, cpow_half_sq, ← e1, Ecal]
  ring

/-- `U` with characteristic reduced mod `ℤ²`. -/
def Uf (s0 s1 : ℕ) : ℂ := U (((s0 % 2 : ℕ) : ℝ) / 2) (((s1 % 2 : ℕ) : ℝ) / 2)

theorem U_nat (s0 s1 : ℕ) : U ((s0 : ℝ) / 2) ((s1 : ℝ) / 2) = Uf s0 s1 := by
  rw [Uf, U, U]
  conv_rhs => rw [← th2_shift_c _ _ _ _ _ _ _ ((s0 / 2 : ℕ) : ℤ) ((s1 / 2 : ℕ) : ℤ)]
  simp only [Int.cast_natCast]
  have h0 : (s0 : ℝ) = ((s0 % 2 : ℕ) : ℝ) + 2 * ((s0 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s0 2).symm
  have h1 : (s1 : ℝ) = ((s1 % 2 : ℕ) : ℝ) + 2 * ((s1 / 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div s1 2).symm
  congr 1 <;> linarith

theorem exp_pi_nat (k : ℕ) : cexp (π * I * (k : ℂ)) = (-1) ^ k := by
  rw [mul_comm, Complex.exp_nat_mul, Complex.exp_pi_mul_I]

/-- **Duplication at `W`, with the translation reductions.** -/
theorem sqW (a0 a1 b0 b1 : ℕ) :
    Th2 wa wb wc ((b0 : ℝ) / 2) ((b1 : ℝ) / 2) ((a0 : ℝ) / 2) ((a1 : ℝ) / 2) ^ 2 =
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + b0) * a0 + ((σ.2 : ℕ) + b1) * a1) *
        Uf ((σ.1 : ℕ) + b0) ((σ.2 : ℕ) + b1) * Uf σ.1 σ.2 := by
  rw [dup2 _ _ _ _ (summable_norm_term2 d2pos posW _ _ _ _)
    (fun _ _ _ _ => summable_norm_term2 d3pos posW2 _ _ _ _)]
  congr 1; funext σ
  have e0 : 2 * ((a0 : ℝ) / 2) = 0 + ((a0 : ℤ) : ℝ) := by push_cast; ring
  have e1 : 2 * ((a1 : ℝ) / 2) = 0 + ((a1 : ℤ) : ℝ) := by push_cast; ring
  rw [e0, e1, th2_shift_d]
  have c0 : ((σ.1 : ℕ) : ℝ) / 2 + (b0 : ℝ) / 2 = (((σ.1 : ℕ) + b0 : ℕ) : ℝ) / 2 := by push_cast; ring
  have c1 : ((σ.2 : ℕ) : ℝ) / 2 + (b1 : ℝ) / 2 = (((σ.2 : ℕ) + b1 : ℕ) : ℝ) / 2 := by push_cast; ring
  rw [c0, c1]
  change _ * U _ _ * U _ _ = _
  rw [U_nat, U_nat, ← exp_pi_nat]
  congr 2
  congr 1; push_cast; ring

theorem om24_sym : Om24 1 0 = Om24 0 1 := by rw [om24_10, om24_01]

theorem sq_char (m : HDec.PkgI1.Char2) :
    HDec.PkgI1.thetaConst m Om24 ^ 2 =
      Ecal * cexp (π * I * (((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ) : ℕ) : ℂ)) *
      ∑ σ : Fin 2 × Fin 2, (-1 : ℂ) ^ (((σ.1 : ℕ) + (m.2 0 : ℕ)) * (m.1 0 : ℕ) + ((σ.2 : ℕ) + (m.2 1 : ℕ)) * (m.1 1 : ℕ)) *
        Uf ((σ.1 : ℕ) + (m.2 0 : ℕ)) ((σ.2 : ℕ) + (m.2 1 : ℕ)) * Uf σ.1 σ.2 := by
  rw [thetaConst_eq m Om24 om24_sym, om24_00, om24_01, om24_11, sq_inv, sqW]

theorem U11' : U (1 / 2) (1 / 2) = 0 := U11
theorem U11'' : U 2⁻¹ 2⁻¹ = 0 := by rw [← one_div]; exact U11

theorem exp_pi_two : cexp (π * I * 2) = 1 := by
  rw [show (π : ℂ) * I * 2 = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring, exp_int_mul_two_pi_mul_I]

theorem sqc0 : HDec.PkgI1.thetaConst (![0, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc1 : HDec.PkgI1.thetaConst (![0, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 + U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc2 : HDec.PkgI1.thetaConst (![1, 0], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 + U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc3 : HDec.PkgI1.thetaConst (![1, 1], ![0, 0]) Om24 ^ 2 =
    Ecal * (U 0 0 ^ 2 - U (1 / 2) 0 ^ 2 - U 0 (1 / 2) ^ 2) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc4 : HDec.PkgI1.thetaConst (![0, 0], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc5 : HDec.PkgI1.thetaConst (![0, 1], ![1, 0]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc6 : HDec.PkgI1.thetaConst (![0, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc7 : HDec.PkgI1.thetaConst (![1, 0], ![0, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 0 * U 0 (1 / 2)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc8 : HDec.PkgI1.thetaConst (![0, 0], ![1, 1]) Om24 ^ 2 =
    Ecal * (2 * U 0 (1 / 2) * U (1 / 2) 0) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

theorem sqc9 : HDec.PkgI1.thetaConst (![1, 1], ![1, 1]) Om24 ^ 2 =
    Ecal * (-(2 * U 0 (1 / 2) * U (1 / 2) 0)) := by
  rw [sq_char]
  simp [Fin.sum_univ_two, Fintype.sum_prod_type, Uf, exp_pi_two, U11'']
  first | (left; ring1) | ring1

/-! ## Genus one: duplication (Landen) and Jacobi's identity -/

theorem th1_c1 (τ : ℂ) (d : ℝ) : th1 τ 1 d = th1 τ 0 d := by
  simpa using th1_shift_c τ 0 d 1

theorem th1_d1 (τ : ℂ) (c : ℝ) : th1 τ c 1 = cexp (2 * π * I * c) * th1 τ c 0 := by
  simpa using th1_shift_d τ c 0 1

theorem exp_half : cexp (2 * π * I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
  rw [show (2 : ℂ) * π * I * ((1 / 2 : ℝ) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

theorem dupA {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 2 = th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]; norm_num; ring

theorem dupB {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 (1 / 2) ^ 2 = th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [e, th1_d1, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add,
    add_zero, exp_half]
  push_cast; simp only [mul_zero, Complex.exp_zero]; ring

theorem dupC {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ (1 / 2) 0 ^ 2 = 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0 := by
  rw [dup1 hτ, Fin.sum_univ_two]
  have e : (1 : ℝ) / 2 + 1 / 2 = 1 := by norm_num
  simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, zero_div, zero_add, mul_zero, e, th1_c1]
  ring

/-- **Jacobi's quartic identity** `θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴`, from the duplication formulas. -/
theorem jacobi {τ : ℂ} (hτ : 0 < τ.im) :
    th1 τ 0 0 ^ 4 = th1 τ 0 (1 / 2) ^ 4 + th1 τ (1 / 2) 0 ^ 4 := by
  have hA := dupA hτ; have hB := dupB hτ; have hC := dupC hτ
  linear_combination (th1 τ 0 0 ^ 2 + th1 (2 * τ) 0 0 ^ 2 + th1 (2 * τ) (1 / 2) 0 ^ 2) * hA
    - (th1 τ 0 (1 / 2) ^ 2 + th1 (2 * τ) 0 0 ^ 2 - th1 (2 * τ) (1 / 2) 0 ^ 2) * hB
    - (th1 τ (1 / 2) 0 ^ 2 + 2 * th1 (2 * τ) 0 0 * th1 (2 * τ) (1 / 2) 0) * hC

theorem h2τ3 : 2 * τ3 = τ6 := by apply Complex.ext <;> simp [τ3, τ6] <;> ring

/-! ## The leaf: the singular modulus `k₆` -/

end CM24

/-- **The singular modulus `k₆`** (Weber, Ramanujan; disc `−24`; first used here as an intermediate leaf,
now PROVED below as `CM24.singularModulus6`, so it is not needed). With Mathlib's `jacobiTheta₂`,
`θ₃(τ) = jacobiTheta₂ 0 τ = Σ exp(πin²τ)` and `θ₂(τ) = exp(πiτ/4)·jacobiTheta₂ (τ/2) τ = Σ exp(πi(n+½)²τ)`,
at `τ = i√6` (nome `q = e^{−π√6}`): `θ₃(i√6) ≠ 0` and `k₆ = θ₂(i√6)²/θ₃(i√6)² = (2−√3)(√3−√2)`.

Published form: the singular modulus `k_n = λ*(n)` of the elliptic integral (`K'(k_n)/K(k_n) = √n`, and
`k = θ₂²/θ₃²` with `q = e^{−π√n}`, Jacobi) at `n = 6`: `λ*(6) = (2−√3)(√3−√2)`. Sources (locators
UNVERIFIED, from memory): J. M. Borwein and P. B. Borwein, *Pi and the AGM* (Wiley 1987), Table 4.6 (singular
values `λ*(n)`) and Thm 2.3/§2.6 for `k = θ₂²/θ₃²`; B. C. Berndt, *Ramanujan's Notebooks Part V*, Ch. 34
(class invariants `g₆`, `G₆` and the modulus); H. Weber, *Lehrbuch der Algebra* III (1908), §§ 125-127 and the
table of class invariants. Numerically VERIFIED (`py/split.py`, 30 digits). -/
def SingularModulus6 : Prop :=
  jacobiTheta₂ 0 (I * ((√6 : ℝ) : ℂ)) ≠ 0 ∧
    (cexp (π * I * (I * ((√6 : ℝ) : ℂ)) / 4) * jacobiTheta₂ (I * ((√6 : ℝ) : ℂ) / 2) (I * ((√6 : ℝ) : ℂ))) ^ 2 =
      (((2 - √3) * (√3 - √2) : ℝ) : ℂ) * jacobiTheta₂ 0 (I * ((√6 : ℝ) : ℂ)) ^ 2

namespace CM24
open HDec.LeafQCheck.HM.QMSplit.Value24

theorem τ6_eq : τ6 = I * ((√6 : ℝ) : ℂ) := by apply Complex.ext <;> simp [τ6]

theorem A0_eq : th1 τ6 0 0 = jacobiTheta₂ 0 (I * ((√6 : ℝ) : ℂ)) := by
  rw [th1_eq, τ6_eq]; simp

theorem A2_eq : th1 τ6 (1 / 2) 0 =
    cexp (π * I * (I * ((√6 : ℝ) : ℂ)) / 4) * jacobiTheta₂ (I * ((√6 : ℝ) : ℂ) / 2) (I * ((√6 : ℝ) : ℂ)) := by
  rw [th1_eq, τ6_eq]
  congr 1
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring


/-! ## Final assembly -/

theorem evenChars_eq : HDec.PkgI1.evenChars =
    {(![0, 0], ![0, 0]), (![0, 1], ![0, 0]), (![1, 0], ![0, 0]), (![1, 1], ![0, 0]), (![0, 0], ![1, 0]),
     (![0, 1], ![1, 0]), (![0, 0], ![0, 1]), (![1, 0], ![0, 1]), (![0, 0], ![1, 1]), (![1, 1], ![1, 1])} := by
  decide

theorem Ecal_ne : Ecal ≠ 0 := by
  unfold Ecal
  have h1 : -I * α0 ≠ 0 := mul_ne_zero (by simp) α0_ne
  have h2 : -I * γ1 ≠ 0 := mul_ne_zero (by simp) γ1_ne
  exact mul_ne_zero (one_div_ne_zero h1) (one_div_ne_zero h2)

theorem zeta_sq : cexp (π * I / 4) ^ 2 = I := by
  rw [← Complex.exp_nat_mul, show ((2 : ℕ) : ℂ) * (π * I / 4) = π / 2 * I by push_cast; ring, Complex.exp_mul_I]
  have h1 : Complex.cos (π / 2) = 0 := by exact_mod_cast Real.cos_pi_div_two
  have h2 : Complex.sin (π / 2) = 1 := by exact_mod_cast Real.sin_pi_div_two
  rw [h1, h2]; ring

theorem sum8 : HDec.PkgI1.thetaSum8 Om24 = Ecal ^ 4 *
    CM24Alg.Sp (U 0 0 ^ 2) (U (1 / 2) 0 ^ 2) ((U 0 (1 / 2) ^ 2) ^ 2) := by
  rw [HDec.PkgI1.thetaSum8, evenChars_eq]
  simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
  simp only [show ∀ x : ℂ, x ^ 8 = (x ^ 2) ^ 4 from fun x => by ring, sqc0, sqc1, sqc2, sqc3, sqc4, sqc5,
    sqc6, sqc7, sqc8, sqc9]
  unfold CM24Alg.Sp; ring

theorem prod2 : HDec.PkgI1.thetaProd2 Om24 ^ 2 = Ecal ^ 20 *
    CM24Alg.Pp (U 0 0 ^ 2) (U (1 / 2) 0 ^ 2) ((U 0 (1 / 2) ^ 2) ^ 2) := by
  rw [HDec.PkgI1.thetaProd2, evenChars_eq]
  simp (disch := decide) only [Finset.prod_insert, Finset.prod_singleton]
  simp only [sqc0, sqc1, sqc2, sqc3, sqc4, sqc5, sqc6, sqc7, sqc8, sqc9]
  unfold CM24Alg.Pp; ring

/-- **Core: the closed numeric statement from `mpoly(θ₁₀(i√6)²/θ₀₀(i√6)²) = 0`.** -/
theorem thetaValueAtOmega24_of_mpoly (k : ℂ) (hA0' : th1 τ6 0 0 ≠ 0)
    (hk' : th1 τ6 (1 / 2) 0 ^ 2 = k * th1 τ6 0 0 ^ 2) (hm : CM24Alg.mpoly k = 0) : ThetaValueAtOmega24 := by
  set A0 := th1 τ6 0 0
  set A1 := th1 τ6 0 (1 / 2)
  set A2 := th1 τ6 (1 / 2) 0
  set B0 := th1 τ3 0 0
  set B1 := th1 τ3 0 (1 / 2)
  set B2 := th1 τ3 (1 / 2) 0
  have rB0 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2 := by have := dupA τ3_im; rw [h2τ3] at this; exact this
  have rB1 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2 := by have := dupB τ3_im; rw [h2τ3] at this; exact this
  have rB2 : B2 ^ 2 = 2 * A0 * A2 := by have := dupC τ3_im; rw [h2τ3] at this; exact this
  have rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4 := jacobi τ6_im
  have hk : A2 ^ 2 = k * A0 ^ 2 := hk'
  have hζ := zeta_sq
  set ζ := cexp (π * I / 4)
  have hx : U 0 0 ^ 2 = A0 ^ 4 * (1 - k) := by
    rw [U00]; linear_combination A0 ^ 2 * rB1 - A0 ^ 2 * hk
  have hy : U (1 / 2) 0 ^ 2 = A0 ^ 4 * (-k * (1 + k)) := by
    rw [U10]; linear_combination (A2 ^ 2 * B0 ^ 2) * I_sq - A2 ^ 2 * rB0 - (A0 ^ 2 + A2 ^ 2 + k * A0 ^ 2) * hk
  have hz : (U 0 (1 / 2) ^ 2) ^ 2 = A0 ^ 8 * (-4 * k * (1 - k ^ 2)) := by
    rw [U01]
    linear_combination (ζ ^ 2 + I) * A1 ^ 4 * B2 ^ 4 * hζ + A1 ^ 4 * B2 ^ 4 * I_sq
      - A1 ^ 4 * (B2 ^ 2 + 2 * A0 * A2) * rB2 + 4 * A0 ^ 2 * A2 ^ 2 * rJ
      + (-4 * A0 ^ 6 + 4 * A0 ^ 2 * (A2 ^ 4 + k * A0 ^ 2 * A2 ^ 2 + k ^ 2 * A0 ^ 4)) * hk
  have hS : HDec.PkgI1.thetaSum8 Om24 = Ecal ^ 4 * A0 ^ 16 *
      CM24Alg.Sp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) := by
    rw [sum8, hx, hy, hz]; unfold CM24Alg.Sp; ring
  have hP : HDec.PkgI1.thetaProd2 Om24 ^ 2 = Ecal ^ 20 * A0 ^ 80 *
      CM24Alg.Pp (1 - k) (-k * (1 + k)) (-4 * k * (1 - k ^ 2)) := by
    rw [prod2, hx, hy, hz]; unfold CM24Alg.Pp; ring
  have hS0 : HDec.PkgI1.thetaSum8 Om24 ≠ 0 := by
    rw [hS]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ Ecal_ne) (pow_ne_zero _ hA0')) (CM24Alg.core_ne k hm)
  have hD : HDec.PkgI1.jDen Om24 ≠ 0 := pow_ne_zero _ hS0
  refine ⟨hD, ?_⟩
  rw [div_eq_iff hD, HDec.PkgI1.jNum, HDec.PkgI1.jDen, hP, hS]
  have := CM24Alg.core k hm
  linear_combination (Ecal ^ 20 * A0 ^ 80) * this

/-- **Main theorem (leaf form): the closed numeric statement from the singular modulus `k₆`.** -/
theorem thetaValueAtOmega24_of_singularModulus6 (h : SingularModulus6) : ThetaValueAtOmega24 := by
  obtain ⟨hA0', hk'⟩ := h
  rw [← A0_eq] at hA0' hk'
  rw [← A2_eq] at hk'
  refine thetaValueAtOmega24_of_mpoly _ hA0' hk' ?_
  have ha : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hb : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have := CM24Alg.mpoly_k6 _ _ ha hb
  push_cast; exact this

/-! ## Removing the leaf: `mpoly(k) = 0` from the cubic modular equation -/

/-- The `S`-transformation of the three theta constants (Mathlib's functional equation). -/
theorem sA {τ : ℂ} : th1 τ 0 0 = 1 / (-I * τ) ^ (1 / 2 : ℂ) * th1 (-1 / τ) 0 0 := by
  rw [th1_eq, th1_eq, jacobiTheta₂_functional_equation]; simp

theorem sB {τ : ℂ} (hτ : τ ≠ 0) : th1 τ 0 (1 / 2) = 1 / (-I * τ) ^ (1 / 2 : ℂ) * th1 (-1 / τ) (1 / 2) 0 := by
  rw [th1_eq, th1_eq, jacobiTheta₂_functional_equation]
  have e : ((1 / 2 : ℝ) : ℂ) * (-1 / τ) + ((0 : ℝ) : ℂ) = -((((0 : ℝ) : ℂ) * τ + ((1 / 2 : ℝ) : ℂ)) / τ) := by
    field_simp; push_cast; ring
  rw [e, jacobiTheta₂_neg_left]
  have e2 : cexp (π * I * (-1 / τ) * ((1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * ((1 / 2 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) =
      cexp (-π * I * (((0 : ℝ) : ℂ) * τ + ((1 / 2 : ℝ) : ℂ)) ^ 2 / τ) := by
    congr 1; push_cast; field_simp; ring
  rw [e2]; simp; ring

theorem sC {τ : ℂ} (hτ : τ ≠ 0) : th1 τ (1 / 2) 0 = 1 / (-I * τ) ^ (1 / 2 : ℂ) * th1 (-1 / τ) 0 (1 / 2) := by
  rw [th1_eq, th1_eq, jacobiTheta₂_functional_equation]
  have e : (((1 / 2 : ℝ) : ℂ) * τ + ((0 : ℝ) : ℂ)) / τ = ((0 : ℝ) : ℂ) * (-1 / τ) + ((1 / 2 : ℝ) : ℂ) := by
    field_simp; push_cast; ring
  rw [e]
  have e2 : cexp (π * I * τ * ((1 / 2 : ℝ) : ℂ) ^ 2 + 2 * π * I * ((1 / 2 : ℝ) : ℂ) * ((0 : ℝ) : ℂ)) *
      cexp (-π * I * (((1 / 2 : ℝ) : ℂ) * τ + ((0 : ℝ) : ℂ)) ^ 2 / τ) = 1 := by
    rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; field_simp; ring
  have e3 : cexp (π * I * (-1 / τ) * ((0 : ℝ) : ℂ) ^ 2 + 2 * π * I * ((0 : ℝ) : ℂ) * ((1 / 2 : ℝ) : ℂ)) = 1 := by
    simp
  rw [e3]
  linear_combination (1 / (-I * τ) ^ (1 / 2 : ℂ) *
    jacobiTheta₂ (((0 : ℝ) : ℂ) * (-1 / τ) + ((1 / 2 : ℝ) : ℂ)) (-1 / τ)) * e2

/-- On the imaginary axis `th1 (it) c 0` is the real sum `Σ exp(−πt(n+c)²)`. -/
theorem th1_imag (t c : ℝ) :
    th1 (I * t) c 0 = ((∑' n : ℤ, Real.exp (-π * t * ((n : ℝ) + c) ^ 2) : ℝ) : ℂ) := by
  rw [th1, Complex.ofReal_tsum]
  congr 1; funext n
  rw [term1, Complex.ofReal_exp]
  congr 1; push_cast; ring_nf; rw [I_sq]; ring

theorem th1_imag_pos {t : ℝ} (ht : 0 < t) (c : ℝ) : 0 < ∑' n : ℤ, Real.exp (-π * t * ((n : ℝ) + c) ^ 2) :=
  (summable_gauss ht c).tsum_pos (fun _ => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- `τ' = i√6/3 = −1/τ₃`, `3τ' = τ₆`. -/
def τp : ℂ := I * ((r6 / 3 : ℝ) : ℂ)

theorem τ3_ne : τ3 ≠ 0 := fun h => by
  have := congrArg Complex.im h; simp [τ3] at this <;> linarith [r6_pos]
theorem τp_eq : -1 / τ3 = τp := by
  rw [div_eq_iff τ3_ne]; apply Complex.ext <;> simp [τ3, τp] <;> nlinarith [r6_sq]
theorem τp_im : 0 < τp.im := by simp [τp] <;> exact div_pos r6_pos (by norm_num)
theorem h3τp : 3 * τp = τ6 := by apply Complex.ext <;> simp [τp, τ6] <;> ring
theorem τ6_eq' : τ6 = I * ((r6 : ℝ) : ℂ) := by apply Complex.ext <;> simp [τ6]

/-- `K = 1/(−iτ₃)^{1/2}` is a positive real. -/
theorem K_real : 1 / (-I * τ3) ^ (1 / 2 : ℂ) = (((1 / (r6 / 2) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) := by
  have e : -I * τ3 = ((r6 / 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp [τ3]
  rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (div_pos r6_pos (by norm_num)).le]
  push_cast; ring
theorem K_pos : (0 : ℝ) < 1 / (r6 / 2) ^ (1 / 2 : ℝ) :=
  div_pos one_pos (Real.rpow_pos_of_pos (div_pos r6_pos (by norm_num)) _)

/-- **`mpoly(θ₁₀(i√6)²/θ₀₀(i√6)²) = 0`** (no leaf): cubic modular equation at `τ'`, `S`, Landen, Jacobi. -/
theorem mpoly_A (A0 A1 A2 B0 B1 B2 : ℂ) (hA0 : A0 ≠ 0)
    (R1 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2) (R2 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2) (R3 : B2 ^ 2 = 2 * A0 * A2)
    (rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4) (R5 : A0 * B0 = A2 * B1 + A1 * B2)
    (hne : A2 ^ 4 - 2 * A0 ^ 2 * A2 ^ 2 - A0 ^ 4 ≠ 0) :
    CM24Alg.mpoly (A2 ^ 2 / A0 ^ 2) = 0 := by
  set Q := A0 ^ 4 + A2 ^ 4 - 2 * A0 * A1 ^ 2 * A2
  have E1 : 2 * A1 * A2 * B1 * B2 = Q := by
    linear_combination (-(A0 * B0 + A2 * B1 + A1 * B2)) * R5 + A0 ^ 2 * R1 - A2 ^ 2 * R2 - A1 ^ 2 * R3
  have E2 : 8 * A0 * A1 ^ 2 * A2 ^ 3 * (A0 ^ 2 - A2 ^ 2) = Q ^ 2 := by
    linear_combination (2 * A1 * A2 * B1 * B2 + Q) * E1 - 4 * A1 ^ 2 * A2 ^ 2 * B2 ^ 2 * R2
      - 4 * A1 ^ 2 * A2 ^ 2 * (A0 ^ 2 - A2 ^ 2) * R3
  set W := A0 ^ 4 + 2 * A0 ^ 2 * A2 ^ 2 - A2 ^ 4
  set V := (A0 ^ 4 + A2 ^ 4) ^ 2 + 4 * A0 ^ 2 * A2 ^ 2 * (A0 ^ 4 - A2 ^ 4)
  have E3 : 4 * A0 * A2 * A1 ^ 2 * W = V := by
    linear_combination E2 - 4 * A0 ^ 2 * A2 ^ 2 * rJ
  have E4 : 16 * A0 ^ 2 * A2 ^ 2 * (A0 ^ 4 - A2 ^ 4) * W ^ 2 = V ^ 2 := by
    linear_combination (4 * A0 * A2 * A1 ^ 2 * W + V) * E3 + 16 * A0 ^ 2 * A2 ^ 2 * W ^ 2 * rJ
  have E5 : (A2 ^ 4 - 2 * A0 ^ 2 * A2 ^ 2 - A0 ^ 4) ^ 2 * (A2 ^ 8 + 12 * A2 ^ 6 * A0 ^ 2 + 2 * A2 ^ 4 * A0 ^ 4
      - 12 * A2 ^ 2 * A0 ^ 6 + A0 ^ 8) = 0 := by
    linear_combination -E4
  have hmh := (mul_eq_zero.1 E5).resolve_left (pow_ne_zero _ hne)
  unfold CM24Alg.mpoly
  field_simp
  linear_combination hmh

/-- **`mpoly(θ₁₀(i√6)²/θ₀₀(i√6)²) = 0`, proved (no leaf).** -/
theorem mpoly_theta : th1 τ6 0 0 ≠ 0 ∧ CM24Alg.mpoly (th1 τ6 (1 / 2) 0 ^ 2 / th1 τ6 0 0 ^ 2) = 0 := by
  set A0 := th1 τ6 0 0
  set A1 := th1 τ6 0 (1 / 2)
  set A2 := th1 τ6 (1 / 2) 0
  set B0 := th1 τ3 0 0
  set B1 := th1 τ3 0 (1 / 2)
  set B2 := th1 τ3 (1 / 2) 0
  set K := 1 / (-I * τ3) ^ (1 / 2 : ℂ)
  -- real positive values on the imaginary axis
  set a0 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 0) ^ 2)
  set a2 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2)
  set p1 := ∑' n : ℤ, Real.exp (-π * (r6 / 3) * ((n : ℝ) + 1 / 2) ^ 2)
  set kr := 1 / (r6 / 2) ^ (1 / 2 : ℝ)
  have ha0 : 0 < a0 := th1_imag_pos r6_pos 0
  have hp1 : 0 < p1 := th1_imag_pos (div_pos r6_pos (by norm_num)) _
  have hA0 : A0 = (a0 : ℂ) := by simp only [A0, a0]; rw [τ6_eq', th1_imag]
  have hA2 : A2 = (a2 : ℂ) := by simp only [A2, a2]; rw [τ6_eq', th1_imag]
  have hA0ne : A0 ≠ 0 := by rw [hA0]; exact_mod_cast ha0.ne'
  -- `S`: the theta constants at `τ₃` from those at `τ' = −1/τ₃`
  have hB0 : B0 = K * th1 τp 0 0 := by simp only [B0, K]; rw [sA, τp_eq]
  have hB1 : B1 = K * th1 τp (1 / 2) 0 := by simp only [B1, K]; rw [sB τ3_ne, τp_eq]
  have hB2 : B2 = K * th1 τp 0 (1 / 2) := by simp only [B2, K]; rw [sC τ3_ne, τp_eq]
  have hB1r : B1 = ((kr * p1 : ℝ) : ℂ) := by
    rw [hB1, show K = (kr : ℂ) from K_real, τp, th1_imag, Complex.ofReal_mul]
  -- Landen at `τ₃` and Jacobi at `τ₆`
  have R1 : B0 ^ 2 = A0 ^ 2 + A2 ^ 2 := by have := dupA τ3_im; rw [h2τ3] at this; exact this
  have R2 : B1 ^ 2 = A0 ^ 2 - A2 ^ 2 := by have := dupB τ3_im; rw [h2τ3] at this; exact this
  have R3 : B2 ^ 2 = 2 * A0 * A2 := by have := dupC τ3_im; rw [h2τ3] at this; exact this
  have rJ : A0 ^ 4 = A1 ^ 4 + A2 ^ 4 := jacobi τ6_im
  -- the cubic modular equation at `τ'` (`3τ' = τ₆`)
  have hc := cubic τp_im
  rw [h3τp] at hc
  have R5 : A0 * B0 = A2 * B1 + A1 * B2 := by
    rw [hB0, hB1, hB2]; linear_combination K * hc
  -- `0 < θ₁₀(i√6)² < θ₀₀(i√6)²` excludes the spurious factor
  have hlt : a2 ^ 2 < a0 ^ 2 := by
    have h := R2
    rw [hB1r, hA0, hA2] at h
    have h' : (kr * p1) ^ 2 = a0 ^ 2 - a2 ^ 2 := by exact_mod_cast h
    have : 0 < (kr * p1) ^ 2 := by have := K_pos; positivity
    linarith
  have hne : A2 ^ 4 - 2 * A0 ^ 2 * A2 ^ 2 - A0 ^ 4 ≠ 0 := by
    rw [hA0, hA2]
    have : a2 ^ 4 - 2 * a0 ^ 2 * a2 ^ 2 - a0 ^ 4 < 0 := by nlinarith [sq_nonneg a2, sq_nonneg a0]
    exact_mod_cast this.ne
  exact ⟨hA0ne, mpoly_A A0 A1 A2 B0 B1 B2 hA0ne R1 R2 R3 rJ R5 hne⟩

/-- **`ThetaValueAtOmega24`, proved (no leaf).** -/
theorem thetaValueAtOmega24 : ThetaValueAtOmega24 :=
  thetaValueAtOmega24_of_mpoly _ mpoly_theta.1
    (div_mul_cancel₀ (th1 τ6 (1 / 2) 0 ^ 2) (pow_ne_zero 2 mpoly_theta.1)).symm mpoly_theta.2

/-! ## Bonus: the classical singular modulus `λ*(6) = (2−√3)(√3−√2)`, proved -/

theorem a0_ge_one : 1 ≤ ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 0) ^ 2) := by
  have := (summable_gauss r6_pos 0).le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  simpa using this

theorem a2_le : ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2) ≤
    2 * (Real.exp (-(π * r6) / 4) * (1 - Real.exp (-(π * r6)))⁻¹) := by
  set c := π * r6 with hcdef
  have hc : 0 < c := mul_pos Real.pi_pos r6_pos
  have hs := summable_gauss r6_pos (1 / 2)
  have hinj : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro x y h; simp only [neg_inj, add_left_inj, Nat.cast_inj] at h; exact h
  have h1 : Summable (fun n : ℕ => Real.exp (-π * r6 * (((n : ℤ) : ℝ) + 1 / 2) ^ 2)) :=
    hs.comp_injective Nat.cast_injective
  have h2 : Summable (fun n : ℕ => Real.exp (-π * r6 * (((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2)) :=
    hs.comp_injective hinj
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ => Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2)) h1 h2]
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hg : Summable (fun n : ℕ => Real.exp (-c / 4) * Real.exp (-c) ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hgs : ∑' n : ℕ, Real.exp (-c / 4) * Real.exp (-c) ^ n = Real.exp (-c / 4) * (1 - Real.exp (-c))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have b1 : ∀ n : ℕ, Real.exp (-π * r6 * (((n : ℤ) : ℝ) + 1 / 2) ^ 2) ≤ Real.exp (-c / 4) * Real.exp (-c) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    push_cast
    nlinarith [mul_nonneg hc.le (sq_nonneg (n : ℝ))]
  have b2 : ∀ n : ℕ, Real.exp (-π * r6 * (((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2) ≤
      Real.exp (-c / 4) * Real.exp (-c) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg
    push_cast
    nlinarith [mul_nonneg hc.le (sq_nonneg (n : ℝ))]
  have t1 := h1.tsum_le_tsum b1 hg
  have t2 := h2.tsum_le_tsum b2 hg
  rw [hgs] at t1 t2
  linarith

theorem a2_lt : ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2) < 7 / 10 := by
  refine lt_of_le_of_lt a2_le ?_
  have hpi := Real.pi_gt_three
  have hr6 : 12 / 5 < r6 := by nlinarith [r6_sq, r6_pos]
  have hc : 36 / 5 < π * r6 := by nlinarith
  have e8 : 1 + π * r6 / 8 ≤ Real.exp (π * r6 / 8) := by linarith [Real.add_one_le_exp (π * r6 / 8)]
  have e4 : Real.exp (π * r6 / 4) = Real.exp (π * r6 / 8) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e1 : 1 + π * r6 ≤ Real.exp (π * r6) := by linarith [Real.add_one_le_exp (π * r6)]
  have q1 : Real.exp (-(π * r6) / 4) = (Real.exp (π * r6 / 4))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have q2 : Real.exp (-(π * r6)) = (Real.exp (π * r6))⁻¹ := by rw [← Real.exp_neg]
  have hE4 : 361 / 100 ≤ Real.exp (π * r6 / 4) := by rw [e4]; nlinarith
  have hE1 : 41 / 5 ≤ Real.exp (π * r6) := by linarith
  rw [q1, q2]
  have p4 : 0 < Real.exp (π * r6 / 4) := Real.exp_pos _
  have p1 : 0 < Real.exp (π * r6) := Real.exp_pos _
  have i4 : (Real.exp (π * r6 / 4))⁻¹ ≤ 100 / 361 := by
    rw [inv_le_comm₀ p4 (by norm_num)]; linarith
  have i1 : (Real.exp (π * r6))⁻¹ ≤ 5 / 41 := by
    rw [inv_le_comm₀ p1 (by norm_num)]; linarith
  have i1' : 36 / 41 ≤ 1 - (Real.exp (π * r6))⁻¹ := by linarith
  have i2 : (1 - (Real.exp (π * r6))⁻¹)⁻¹ ≤ 41 / 36 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have : 0 ≤ (Real.exp (π * r6 / 4))⁻¹ := inv_nonneg.2 p4.le
  have : 0 ≤ (1 - (Real.exp (π * r6))⁻¹)⁻¹ := inv_nonneg.2 (by linarith)
  nlinarith

/-- The four roots of `mpoly`: only `(2−√3)(√3−√2)` lies in `(0, 1/2)`. -/
theorem root_select (k : ℝ) (hm : k ^ 4 + 12 * k ^ 3 + 2 * k ^ 2 - 12 * k + 1 = 0) (h0 : 0 < k) (h1 : k < 1 / 2) :
    k = (2 - √3) * (√3 - √2) := by
  set a := √2 with ha'
  set b := √3 with hb'
  have ha : a ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hb : b ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have a0 : 0 < a := Real.sqrt_pos.2 (by norm_num)
  have b0 : 0 < b := Real.sqrt_pos.2 (by norm_num)
  have hfac : (k - (2 - b) * (b - a)) * (k + (2 + b) * (b - a)) * (k - (2 - b) * (b + a)) * (k + (2 + b) * (b + a)) =
      k ^ 4 + 12 * k ^ 3 + 2 * k ^ 2 - 12 * k + 1 := by
    linear_combination (a^2*b^4 - 8*a^2*b^2 + 16*a^2 - 2*b^6 + b^4*(18 - 4*k) + b^2*(-2*k^2 + 16*k - 48) - 8*k^2 + 32) * ha + (b^6 + b^4*(4*k - 9) + b^2*(6*k^2 - 12*k + 25) + 4*k^3 + 6*k^2 - 4*k - 21) * hb
  rw [hm] at hfac
  have hba : a < b := by nlinarith
  have hb2 : b < 7 / 4 := by nlinarith
  have hab : 3 < a + b := by nlinarith
  have f2 : 0 < k + (2 + b) * (b - a) := by nlinarith
  have f3 : k - (2 - b) * (b + a) < 0 := by nlinarith
  have f4 : 0 < k + (2 + b) * (b + a) := by nlinarith
  have hne : (k + (2 + b) * (b - a)) * (k - (2 - b) * (b + a)) * (k + (2 + b) * (b + a)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero f2.ne' f3.ne) f4.ne'
  have : (k - (2 - b) * (b - a)) * ((k + (2 + b) * (b - a)) * (k - (2 - b) * (b + a)) * (k + (2 + b) * (b + a))) = 0 := by
    linear_combination hfac
  have := (mul_eq_zero.1 this).resolve_right hne
  linarith

/-- **The singular modulus `k₆`, proved**: the leaf variant `SingularModulus6` is a theorem. -/
theorem singularModulus6 : SingularModulus6 := by
  obtain ⟨hA0ne, hm⟩ := mpoly_theta
  set a0 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 0) ^ 2)
  set a2 := ∑' n : ℤ, Real.exp (-π * r6 * ((n : ℝ) + 1 / 2) ^ 2)
  have hA0 : th1 τ6 0 0 = (a0 : ℂ) := by rw [τ6_eq', th1_imag]
  have hA2 : th1 τ6 (1 / 2) 0 = (a2 : ℂ) := by rw [τ6_eq', th1_imag]
  have ha0 : 1 ≤ a0 := a0_ge_one
  have ha2 : 0 < a2 := th1_imag_pos r6_pos _
  have ha2' : a2 < 7 / 10 := a2_lt
  rw [hA0, hA2] at hm
  have hmr : (a2 ^ 2 / a0 ^ 2) ^ 4 + 12 * (a2 ^ 2 / a0 ^ 2) ^ 3 + 2 * (a2 ^ 2 / a0 ^ 2) ^ 2
      - 12 * (a2 ^ 2 / a0 ^ 2) + 1 = 0 := by
    unfold CM24Alg.mpoly at hm; exact_mod_cast hm
  have hk0 : 0 < a2 ^ 2 / a0 ^ 2 := by positivity
  have hk1 : a2 ^ 2 / a0 ^ 2 < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hk := root_select _ hmr hk0 hk1
  refine ⟨by rw [← A0_eq, hA0]; exact_mod_cast (by linarith : (0 : ℝ) < a0).ne', ?_⟩
  rw [← A0_eq, ← A2_eq, hA0, hA2, ← hk]
  have : (a0 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (0 : ℝ) < a0).ne'
  push_cast
  field_simp

/-- **The field `igusaCMValue24`, proved.** -/
theorem igusaCMValue24 : IgusaCMValue24 :=
  igusa_of_thetaQuotientValue24 (thetaQuotientValue24_iff.2 thetaValueAtOmega24)

/-- **The glue `ThetaQuotientValue24`, proved.** -/
theorem thetaQuotientValue24 : HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24 :=
  thetaQuotientValue24_iff.2 thetaValueAtOmega24

/-- **The field `igusaCMValue24` from the singular modulus `k₆`.** -/
theorem igusaCMValue24_of_singularModulus6 (h : SingularModulus6) : IgusaCMValue24 :=
  igusa_of_thetaQuotientValue24 (thetaQuotientValue24_iff.2 (thetaValueAtOmega24_of_singularModulus6 h))

/-- The glue `ThetaQuotientValue24` from the singular modulus `k₆`. -/
theorem thetaQuotientValue24_of_singularModulus6 (h : SingularModulus6) :
    HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24 :=
  thetaQuotientValue24_iff.2 (thetaValueAtOmega24_of_singularModulus6 h)

end CM24

/-- The field `igusaCMValue24`, at its fully qualified type. -/
theorem CM24.igusaCMValue24_field : HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24 := CM24.igusaCMValue24
/-- The glue `ThetaQuotientValue24`, at its fully qualified type. -/
theorem CM24.thetaQuotientValue24_field : HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24 :=
  CM24.thetaQuotientValue24
/-- The closed numeric statement, at its fully qualified type. -/
theorem CM24.thetaValueAtOmega24_field : HDec.LeafQCheck.HM.QMSplit.Value24.ThetaValueAtOmega24 :=
  CM24.thetaValueAtOmega24

#print axioms CM24.igusaCMValue24_field
#print axioms CM24.singularModulus6
#print axioms CM24.thetaQuotientValue24_field
#print axioms CM24.thetaValueAtOmega24_of_singularModulus6
#print axioms CM24.igusaCMValue24_of_singularModulus6
#print axioms CM24.thetaValueAtOmega24
#print axioms CM24.igusaCMValue24
#print axioms CM24.thetaQuotientValue24
