import ZInQKernel.OneProof.H.TailA

noncomputable section

namespace HDec.ThetaGlue

open Complex Matrix

/-- The summand of `PkgI1.thetaConst m Ω` (verbatim body). -/
def thetaTerm (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (n : Fin 2 → ℤ) : ℂ :=
  let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
  Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

theorem thetaConst_eq_tsum (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    PkgI1.thetaConst m Ω = ∑' n, thetaTerm m Ω n := rfl

/-- The real point `x = n + a/2`. -/
def xr (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) : ℝ := (n k : ℝ) + ((m.1 k : ℕ) : ℝ) / 2

theorem thetaTerm_coord (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (n : Fin 2 → ℤ) :
    thetaTerm m Ω n = Complex.exp (Real.pi * I *
      ((xr m n 0 : ℂ) * (Ω 0 0 * xr m n 0 + Ω 0 1 * xr m n 1) +
        (xr m n 1 : ℂ) * (Ω 1 0 * xr m n 0 + Ω 1 1 * xr m n 1)) +
      Real.pi * I * ((xr m n 0 : ℂ) * ((m.2 0 : ℕ) : ℂ) + (xr m n 1 : ℂ) * ((m.2 1 : ℕ) : ℂ))) := by
  simp only [thetaTerm, xr, dotProduct, mulVec, Fin.sum_univ_two]
  push_cast
  ring_nf

/-- The quadratic form of `Im Ω` at a real point. -/
def qY (Ω : Matrix (Fin 2) (Fin 2) ℂ) (x0 x1 : ℝ) : ℝ :=
  x0 * ((Ω 0 0).im * x0 + (Ω 0 1).im * x1) + x1 * ((Ω 1 0).im * x0 + (Ω 1 1).im * x1)

theorem norm_thetaTerm (m : PkgI1.Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (n : Fin 2 → ℤ) :
    ‖thetaTerm m Ω n‖ = Real.exp (-Real.pi * qY Ω (xr m n 0) (xr m n 1)) := by
  rw [thetaTerm_coord, Complex.norm_exp]
  congr 1
  simp only [qY, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.natCast_re, Complex.natCast_im]
  ring

/-- Positive-definiteness bound: `(y₀₀+y₁₁)·q_Y(x) ≥ det(Y)·|x|²` (sum of two squares). -/
theorem qY_lower (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hs : (Ω 0 1).im = (Ω 1 0).im) (x0 x1 : ℝ) :
    ((Ω 0 0).im * (Ω 1 1).im - (Ω 0 1).im ^ 2) * (x0 ^ 2 + x1 ^ 2) ≤
      ((Ω 0 0).im + (Ω 1 1).im) * qY Ω x0 x1 := by
  have h : ((Ω 0 0).im + (Ω 1 1).im) * qY Ω x0 x1 -
      ((Ω 0 0).im * (Ω 1 1).im - (Ω 0 1).im ^ 2) * (x0 ^ 2 + x1 ^ 2) =
      ((Ω 0 0).im * x0 + (Ω 0 1).im * x1) ^ 2 + ((Ω 0 1).im * x0 + (Ω 1 1).im * x1) ^ 2 := by
    simp only [qY]; rw [← hs]; ring
  nlinarith [sq_nonneg ((Ω 0 0).im * x0 + (Ω 0 1).im * x1),
    sq_nonneg ((Ω 0 1).im * x0 + (Ω 1 1).im * x1)]

/-- From `IsSiegel`: a uniform positive lower bound for `q_Y`. -/
theorem exists_qY_lower {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    ∃ ε > 0, ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY Ω x0 x1 := by
  obtain ⟨hT, hP⟩ := hΩ
  have hs : (Ω 0 1).im = (Ω 1 0).im := by
    have := congrFun (congrFun hT 1) 0
    simp only [Matrix.transpose_apply] at this
    rw [this]
  have hdet := hP.det_pos
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.map_apply] at hdet
  have h00 : 0 < (Ω 0 0).im := by
    simpa using hP.diag_pos (i := 0)
  have h11 : 0 < (Ω 1 1).im := by
    simpa using hP.diag_pos (i := 1)
  refine ⟨((Ω 0 0).im * (Ω 1 1).im - (Ω 0 1).im ^ 2) / ((Ω 0 0).im + (Ω 1 1).im), ?_, ?_⟩
  · apply div_pos _ (by linarith)
    rw [← hs] at hdet; nlinarith
  · intro x0 x1
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), mul_comm _ ((Ω 0 0).im + (Ω 1 1).im)]
    exact qY_lower Ω hs x0 x1


theorem sq_xr_ge (m : PkgI1.Char2) (n : Fin 2 → ℤ) (k : Fin 2) :
    (n k : ℝ) ^ 2 - |(n k : ℝ)| ≤ xr m n k ^ 2 := by
  have ha0 : (0 : ℝ) ≤ ((m.1 k : ℕ) : ℝ) := by positivity
  have ha1 : ((m.1 k : ℕ) : ℝ) ≤ 1 := by
    have := (m.1 k).isLt; exact_mod_cast Nat.lt_succ_iff.mp this
  simp only [xr]
  have h1 : -|(n k : ℝ)| ≤ (n k : ℝ) := neg_abs_le _
  have h2 : 0 ≤ |(n k : ℝ)| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (le_abs_self (-(n k : ℝ))) ha0,
    mul_le_mul_of_nonneg_right ha1 h2, sq_nonneg (((m.1 k : ℕ) : ℝ))]

/-- The Gaussian majorant `n ↦ exp(-π(εn² - ε|n|))` (Mathlib's `jacobiTheta₂` bound). -/
def gMaj (ε : ℝ) (n : ℤ) : ℝ := Real.exp (-Real.pi * (ε * (n : ℝ) ^ 2 - 2 * (ε / 2) * |(n : ℝ)|))

theorem summable_gMaj {ε : ℝ} (hε : 0 < ε) : Summable (gMaj ε) := by
  have := summable_pow_mul_jacobiTheta₂_term_bound (ε / 2) hε 0
  simp only [pow_zero, one_mul] at this
  exact this.congr fun n => by simp [gMaj, Int.cast_abs]

theorem norm_thetaTerm_le {Ω : Matrix (Fin 2) (Fin 2) ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY Ω x0 x1) (m : PkgI1.Char2) (n : Fin 2 → ℤ) :
    ‖thetaTerm m Ω n‖ ≤ gMaj ε (n 0) * gMaj ε (n 1) := by
  rw [norm_thetaTerm, gMaj, gMaj, ← Real.exp_add, Real.exp_le_exp]
  have h0 := sq_xr_ge m n 0
  have h1 := sq_xr_ge m n 1
  have hq := h (xr m n 0) (xr m n 1)
  have hpi := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h0 h1) hε.le]

theorem summable_norm_thetaTerm {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∃ ε > 0, ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY Ω x0 x1) (m : PkgI1.Char2) :
    Summable (fun n => ‖thetaTerm m Ω n‖) := by
  obtain ⟨ε, hε, h⟩ := h
  have hg := summable_gMaj hε
  have hpos : 0 ≤ gMaj ε := fun n => (Real.exp_pos _).le
  have hp : Summable (fun p : ℤ × ℤ => gMaj ε p.1 * gMaj ε p.2) := hg.mul_of_nonneg hg hpos hpos
  have hp' : Summable (fun n : Fin 2 → ℤ => gMaj ε (n 0) * gMaj ε (n 1)) :=
    (finTwoArrowEquiv ℤ).summable_iff.mpr hp
  exact hp'.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaTerm_le hε h m)

theorem qY_two_smul (Ω : Matrix (Fin 2) (Fin 2) ℂ) (x0 x1 : ℝ) :
    qY ((2 : ℂ) • Ω) x0 x1 = 2 * qY Ω x0 x1 := by
  simp only [qY, Matrix.smul_apply, smul_eq_mul, Complex.mul_im]
  norm_num
  ring

theorem exists_qY_lower_two {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    ∃ ε > 0, ∀ x0 x1 : ℝ, ε * (x0 ^ 2 + x1 ^ 2) ≤ qY ((2 : ℂ) • Ω) x0 x1 := by
  obtain ⟨ε, hε, h⟩ := exists_qY_lower hΩ
  refine ⟨2 * ε, by positivity, fun x0 x1 => ?_⟩
  rw [qY_two_smul]; nlinarith [h x0 x1]


/-! ## The duplication formula -/

theorem fin2_add_cast (x y : Fin 2) :
    (((x + y : Fin 2) : ℕ) : ℝ) = ((x : ℕ) : ℝ) + ((y : ℕ) : ℝ) - 2 * ((x : ℕ) : ℝ) * ((y : ℕ) : ℝ) := by
  fin_cases x <;> fin_cases y <;> norm_num

theorem fin2_add_castC (x y : Fin 2) :
    (((x + y : Fin 2) : ℕ) : ℂ) = ((x : ℕ) : ℂ) + ((y : ℕ) : ℂ) - 2 * ((x : ℕ) : ℂ) * ((y : ℕ) : ℂ) := by
  fin_cases x <;> fin_cases y <;> norm_num

/-- The change of variables `(c, k, l) ↦ (n₁, n₂)`, `n₁ = l + k + c(1-a)`, `n₂ = l - k - ca`
(so `n₁ + a/2 = q + p`, `n₂ + a/2 = q - p` with `p = k + c/2`, `q = l + (c⊕a)/2`). -/
def dupMap (a : Fin 2 → Fin 2) (x : (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    (Fin 2 → ℤ) × (Fin 2 → ℤ) :=
  (fun i => x.2.2 i + x.2.1 i + ((x.1 i : ℕ) : ℤ) * (1 - ((a i : ℕ) : ℤ)),
   fun i => x.2.2 i - x.2.1 i - ((x.1 i : ℕ) : ℤ) * ((a i : ℕ) : ℤ))

/-- Parity of an integer as an element of `Fin 2`. -/
def par (z : ℤ) : Fin 2 := if z % 2 = 0 then 0 else 1

theorem fin2_cases (x : Fin 2) : ((x : ℕ) : ℤ) = 0 ∨ ((x : ℕ) : ℤ) = 1 := by
  fin_cases x <;> simp

theorem par_two_mul_add (K : ℤ) (c : Fin 2) : par (2 * K + ((c : ℕ) : ℤ)) = c := by
  fin_cases c
  · simp [par]
  · simp only [par]
    split_ifs with h
    · simp at h
    · rfl

theorem par_cast (z : ℤ) : (((par z : Fin 2) : ℕ) : ℤ) = z % 2 := by
  unfold par; split_ifs with h
  · simp [h]
  · simp; omega

/-- Its inverse. -/
def dupInv (a : Fin 2 → Fin 2) (y : (Fin 2 → ℤ) × (Fin 2 → ℤ)) :
    (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  (fun i => par (y.1 i - y.2 i), fun i => (y.1 i - y.2 i) / 2,
    fun i => y.1 i - (y.1 i - y.2 i) / 2 - ((par (y.1 i - y.2 i) : ℕ) : ℤ) * (1 - ((a i : ℕ) : ℤ)))

def dupEquiv (a : Fin 2 → Fin 2) :
    (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ)) ≃ (Fin 2 → ℤ) × (Fin 2 → ℤ) where
  toFun := dupMap a
  invFun := dupInv a
  left_inv := by
    rintro ⟨c, k, l⟩
    have hd : ∀ i, (dupMap a (c, k, l)).1 i - (dupMap a (c, k, l)).2 i =
        2 * k i + ((c i : ℕ) : ℤ) := by
      intro i; simp only [dupMap]; ring
    have hk : ∀ i, (2 * k i + ((c i : ℕ) : ℤ)) / 2 = k i := by
      intro i; rcases fin2_cases (c i) with h | h <;> rw [h] <;> omega
    simp only [dupInv, hd, par_two_mul_add, hk, Prod.mk.injEq]
    refine ⟨trivial, trivial, funext fun i => ?_⟩
    simp only [dupMap]; ring
  right_inv := by
    rintro ⟨n1, n2⟩
    simp only [dupInv, dupMap, Prod.mk.injEq, par_cast]
    constructor
    · funext i; ring
    · funext i
      rcases fin2_cases (a i) with h' | h' <;> rw [h'] <;> omega

/-- The sign `exp(πi (c⊕a)·b)`. -/
def dupSign (a b c : Fin 2 → Fin 2) : ℂ :=
  Complex.exp (Real.pi * I * (((((c + a) 0 : Fin 2) : ℕ) : ℂ) * ((b 0 : ℕ) : ℂ) +
    ((((c + a) 1 : Fin 2) : ℕ) : ℂ) * ((b 1 : ℕ) : ℂ)))

theorem thetaTerm_mul_dupMap (Ω : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2 → Fin 2)
    (x : (Fin 2 → Fin 2) × ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    thetaTerm (a, b) Ω (dupMap a x).1 * thetaTerm (a, b) Ω (dupMap a x).2 =
      dupSign a b x.1 * (thetaTerm (x.1, 0) ((2 : ℂ) • Ω) x.2.1 *
        thetaTerm (x.1 + a, 0) ((2 : ℂ) • Ω) x.2.2) := by
  obtain ⟨c, k, l⟩ := x
  simp only [thetaTerm_coord, dupSign, xr, dupMap, Pi.add_apply, Pi.zero_apply, Fin.val_zero,
    Matrix.smul_apply, smul_eq_mul]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  apply Complex.exp_eq_exp_iff_exists_int.mpr
  refine ⟨l 0 * ((b 0 : ℕ) : ℤ) + l 1 * ((b 1 : ℕ) : ℤ), ?_⟩
  push_cast
  rw [fin2_add_castC, fin2_add_castC]
  ring


/-- **Duplication formula (proved).** For `Ω ∈ 𝔥₂` and any characteristic `(a, b)`:
`θ[a;b](Ω)² = Σ_c exp(πi (c⊕a)·b) θ[c;0](2Ω) θ[c⊕a;0](2Ω)`. -/
theorem thetaConst_sq_eq {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω)
    (a b : Fin 2 → Fin 2) :
    PkgI1.thetaConst (a, b) Ω ^ 2 = ∑ c : Fin 2 → Fin 2, dupSign a b c *
      (PkgI1.thetaConst (c, 0) ((2 : ℂ) • Ω) * PkgI1.thetaConst (c + a, 0) ((2 : ℂ) • Ω)) := by
  have h1 := summable_norm_thetaTerm (exists_qY_lower hΩ)
  have h2 := summable_norm_thetaTerm (exists_qY_lower_two hΩ)
  simp only [thetaConst_eq_tsum]
  rw [sq, tsum_mul_tsum_of_summable_norm (h1 (a, b)) (h1 (a, b))]
  have hF : Summable (fun p : (Fin 2 → ℤ) × (Fin 2 → ℤ) =>
      thetaTerm (a, b) Ω p.1 * thetaTerm (a, b) Ω p.2) :=
    (summable_mul_of_summable_norm (h1 (a, b)) (h1 (a, b)))
  rw [← (dupEquiv a).tsum_eq]
  have hG : Summable (fun x => thetaTerm (a, b) Ω (dupEquiv a x).1 *
      thetaTerm (a, b) Ω (dupEquiv a x).2) := (dupEquiv a).summable_iff.mpr hF
  rw [hG.tsum_prod, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hc : ∀ y : (Fin 2 → ℤ) × (Fin 2 → ℤ), thetaTerm (a, b) Ω (dupEquiv a (c, y)).1 *
      thetaTerm (a, b) Ω (dupEquiv a (c, y)).2 = dupSign a b c *
        (thetaTerm (c, 0) ((2 : ℂ) • Ω) y.1 * thetaTerm (c + a, 0) ((2 : ℂ) • Ω) y.2) :=
    fun y => thetaTerm_mul_dupMap Ω a b (c, y)
  simp only [hc]
  rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm (h2 (c, 0)) (h2 (c + a, 0))]


/-! ## The ten explicit squares -/

theorem univ_fin2_fin2 : (Finset.univ : Finset (Fin 2 → Fin 2)) =
    {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by decide

theorem dupSign_eq (a b c : Fin 2 → Fin 2) : dupSign a b c =
    (-1) ^ ((((c + a) 0 : Fin 2) : ℕ) * (b 0 : ℕ) + (((c + a) 1 : Fin 2) : ℕ) * (b 1 : ℕ)) := by
  rw [dupSign, ← Complex.exp_pi_mul_I, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-- `U c = θ[c;0](2Ω)`, indexed `U₀ = U_{00}, U₁ = U_{01}, U₂ = U_{10}, U₃ = U_{11}`. -/
def U2 (Ω : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) : ℂ :=
  PkgI1.thetaConst (![![0, 0], ![0, 1], ![1, 0], ![1, 1]] i, 0) ((2 : ℂ) • Ω)

theorem sq_expand {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω)
    (a b : Fin 2 → Fin 2) :
    PkgI1.thetaConst (a, b) Ω ^ 2 =
      dupSign a b ![0, 0] * (U2 Ω 0 * PkgI1.thetaConst (![0, 0] + a, 0) ((2 : ℂ) • Ω)) +
      dupSign a b ![0, 1] * (U2 Ω 1 * PkgI1.thetaConst (![0, 1] + a, 0) ((2 : ℂ) • Ω)) +
      dupSign a b ![1, 0] * (U2 Ω 2 * PkgI1.thetaConst (![1, 0] + a, 0) ((2 : ℂ) • Ω)) +
      dupSign a b ![1, 1] * (U2 Ω 3 * PkgI1.thetaConst (![1, 1] + a, 0) ((2 : ℂ) • Ω)) := by
  rw [thetaConst_sq_eq hΩ, univ_fin2_fin2, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [U2, Matrix.cons_val]; ring

theorem sq0 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![0, 0]) Ω ^ 2 = U2 Ω 0 ^ 2 + U2 Ω 1 ^ 2 + U2 Ω 2 ^ 2 + U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq1 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![0, 1]) Ω ^ 2 = U2 Ω 0 ^ 2 - U2 Ω 1 ^ 2 + U2 Ω 2 ^ 2 - U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq2 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![1, 0]) Ω ^ 2 = U2 Ω 0 ^ 2 + U2 Ω 1 ^ 2 - U2 Ω 2 ^ 2 - U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq3 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 0], ![1, 1]) Ω ^ 2 = U2 Ω 0 ^ 2 - U2 Ω 1 ^ 2 - U2 Ω 2 ^ 2 + U2 Ω 3 ^ 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq4 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 1], ![0, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 1 + 2 * U2 Ω 2 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq5 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![0, 1], ![1, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 1 - 2 * U2 Ω 2 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq6 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 0], ![0, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 2 + 2 * U2 Ω 1 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq7 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 0], ![0, 1]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 2 - 2 * U2 Ω 1 * U2 Ω 3 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq8 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 1], ![0, 0]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 3 + 2 * U2 Ω 1 * U2 Ω 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem sq9 {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    PkgI1.thetaConst (![1, 1], ![1, 1]) Ω ^ 2 = 2 * U2 Ω 0 * U2 Ω 3 - 2 * U2 Ω 1 * U2 Ω 2 := by
  rw [sq_expand hΩ]; simp [dupSign_eq, U2]; ring

theorem evenChars_eq : PkgI1.evenChars = {(![0, 0], ![0, 0]), (![0, 0], ![0, 1]), (![0, 0], ![1, 0]), (![0, 0], ![1, 1]), (![0, 1], ![0, 0]), (![0, 1], ![1, 0]), (![1, 0], ![0, 0]), (![1, 0], ![0, 1]), (![1, 1], ![0, 0]), (![1, 1], ![1, 1])} := by decide

theorem sum_evenChars (f : PkgI1.Char2 → ℂ) :
    ∑ m ∈ PkgI1.evenChars, f m = f (![0, 0], ![0, 0]) + f (![0, 0], ![0, 1]) + f (![0, 0], ![1, 0]) + f (![0, 0], ![1, 1]) + f (![0, 1], ![0, 0]) + f (![0, 1], ![1, 0]) + f (![1, 0], ![0, 0]) + f (![1, 0], ![0, 1]) + f (![1, 1], ![0, 0]) + f (![1, 1], ![1, 1]) := by
  rw [evenChars_eq]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, not_false_eq_true]
  ring

theorem pow16_of_sq {x q : ℂ} (h : x ^ 2 = q) : x ^ 16 = q ^ 8 := by rw [← h]; ring
theorem pow8_of_sq {x q : ℂ} (h : x ^ 2 = q) : x ^ 8 = q ^ 4 := by rw [← h]; ring

theorem thetaEightSquare' (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : ZInQ.LeafPush2.IsSiegel Ω) :
    ∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 16 =
      (∑ m ∈ PkgI1.evenChars, PkgI1.thetaConst m Ω ^ 8) ^ 2 / 4 := by
  rw [sum_evenChars, sum_evenChars]
  rw [pow16_of_sq (sq0 hΩ), pow8_of_sq (sq0 hΩ), pow16_of_sq (sq1 hΩ), pow8_of_sq (sq1 hΩ), pow16_of_sq (sq2 hΩ), pow8_of_sq (sq2 hΩ), pow16_of_sq (sq3 hΩ), pow8_of_sq (sq3 hΩ), pow16_of_sq (sq4 hΩ), pow8_of_sq (sq4 hΩ), pow16_of_sq (sq5 hΩ), pow8_of_sq (sq5 hΩ), pow16_of_sq (sq6 hΩ), pow8_of_sq (sq6 hΩ), pow16_of_sq (sq7 hΩ), pow8_of_sq (sq7 hΩ), pow16_of_sq (sq8 hΩ), pow8_of_sq (sq8 hΩ), pow16_of_sq (sq9 hΩ), pow8_of_sq (sq9 hΩ)]
  ring

end HDec.ThetaGlue
#print axioms HDec.ThetaGlue.thetaEightSquare'
#print axioms HDec.ThetaGlue.thetaConst_sq_eq
