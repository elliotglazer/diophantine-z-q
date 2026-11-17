import Mathlib

/-!
# t5-glue, part 1: elliptic-function toolkit over Mathlib's `PeriodPair` (Mathlib only)

Task t5-glue (2026-11-14). Report: `docs/research/t5-glue.md`; log: `scratch/t5-glue/log.md`.

* §0 verbatim copies of tyz-split's moduli coordinates (`scratch/tyz-split/T5.lean` §1):
  `pp`, `discL`, `jL`, `weber`, `modCoord`.
* §1 homotheties: if `Λ_P = c·Λ_Q` then `G_n(P) = c⁻ⁿ G_n(Q)`, `℘_P(cz) = c⁻²℘_Q(z)`,
  `℘'_P(cz) = c⁻³℘'_Q(z)`, hence `j(P) = j(Q)` and `h_P(cz) = h_Q(z)` (Weber function).
* §2 conjugation data: if `σ(g₂(P)) = μ⁴g₂(Q)`, `σ(g₃(P)) = μ⁶g₃(Q)` and `σ(℘_P(z)) = μ²℘_Q(w)` then
  `σ(j(P)) = j(Q)` and `σ(h_P(z)) = h_Q(w)`; conversely from `σ(j(P)) = j(Q)` (nonzero
  discriminants) there is such a `μ`, and from `σ(h_P(z)) = h_Q(w)` one may adjust `μ` by a root of
  unity so that `σ(℘_P(z)) = μ²℘_Q(w)`; then `σ(℘'_P(z)) = ±μ³℘'_Q(w)`.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace T5Glue

open Complex Pointwise

/-! ## §0. Verbatim copies (tyz-split, `scratch/tyz-split/T5.lean` §1) -/

theorem linIndep_one_tau (τ : UpperHalfPlane) : LinearIndependent ℝ ![(1 : ℂ), (τ : ℂ)] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have him : t * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa [Complex.real_smul] using this
  have ht : t = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt τ.im_pos)
  subst ht
  simp only [zero_smul, add_zero, Complex.real_smul, mul_one] at h
  exact ⟨by exact_mod_cast h, rfl⟩

/-- The period pair `(1, τ)`: lattice `ℤ + ℤτ`, elliptic curve `ℂ/⟨1, τ⟩`. -/
def pp (τ : UpperHalfPlane) : PeriodPair := ⟨1, τ, linIndep_one_tau τ⟩

/-- `Δ(L) = g₂³ − 27 g₃²`. -/
def discL (L : PeriodPair) : ℂ := L.g₂ ^ 3 - 27 * L.g₃ ^ 2

/-- `j(L) = 1728 g₂³/Δ`. -/
def jL (L : PeriodPair) : ℂ := 1728 * L.g₂ ^ 3 / discL L

/-- Weber's function (verbatim). -/
def weber (L : PeriodPair) (z : ℂ) : ℂ :=
  if L.g₃ = 0 then L.g₂ ^ 2 / discL L * L.weierstrassP z ^ 2
  else if L.g₂ = 0 then L.g₃ / discL L * L.weierstrassP z ^ 3
  else L.g₂ * L.g₃ / discL L * L.weierstrassP z

/-- Moduli coordinates of `(ℂ/⟨1, τ⟩, ⟨1/N⟩)` (verbatim). -/
def modCoord (N : ℕ) (τ : UpperHalfPlane) (i : ℕ) : ℂ :=
  if i = 0 then jL (pp τ)
  else ((Multiset.range (N - 1)).map fun k : ℕ => weber (pp τ) (((k : ℂ) + 1) / N)).esymm i

/-! ## §1. Homotheties -/

/-- `Λ_P = c·Λ_Q` with `c ≠ 0`. -/
def IsScale (P Q : PeriodPair) (c : ℂ) : Prop :=
  c ≠ 0 ∧ (P.lattice : Set ℂ) = c • (Q.lattice : Set ℂ)

section Scale

variable {P Q : PeriodPair} {c : ℂ}

theorem IsScale.mem_iff (h : IsScale P Q c) (x : ℂ) : x ∈ P.lattice ↔ c⁻¹ * x ∈ Q.lattice := by
  have h1 : x ∈ (P.lattice : Set ℂ) ↔ x ∈ c • (Q.lattice : Set ℂ) := by rw [h.2]
  rw [SetLike.mem_coe] at h1
  rw [h1, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [smul_eq_mul, inv_mul_cancel_left₀ h.1]
  · intro hx
    exact ⟨c⁻¹ * x, hx, by rw [smul_eq_mul, mul_inv_cancel_left₀ h.1]⟩

theorem IsScale.mul_mem (h : IsScale P Q c) {y : ℂ} (hy : y ∈ Q.lattice) : c * y ∈ P.lattice := by
  rw [h.mem_iff, inv_mul_cancel_left₀ h.1]; exact hy

/-- The bijection `Λ_Q → Λ_P`, `l ↦ c·l`. -/
def IsScale.equiv (h : IsScale P Q c) : Q.lattice ≃ P.lattice where
  toFun l := ⟨c * l, h.mul_mem l.2⟩
  invFun l := ⟨c⁻¹ * l, (h.mem_iff l).1 l.2⟩
  left_inv l := by ext; simp [inv_mul_cancel_left₀ h.1]
  right_inv l := by ext; simp [mul_inv_cancel_left₀ h.1]

theorem IsScale.G (h : IsScale P Q c) (n : ℕ) : P.G n = (c ^ n)⁻¹ * Q.G n := by
  rw [PeriodPair.G, PeriodPair.G, ← (h.equiv).tsum_eq, ← tsum_mul_left]
  congr 1; ext l
  simp [IsScale.equiv, mul_pow, mul_comm]

theorem IsScale.g₂ (h : IsScale P Q c) : P.g₂ = (c ^ 4)⁻¹ * Q.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, h.G]; ring

theorem IsScale.g₃ (h : IsScale P Q c) : P.g₃ = (c ^ 6)⁻¹ * Q.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, h.G]; ring

theorem IsScale.discL (h : IsScale P Q c) : discL P = (c ^ 12)⁻¹ * discL Q := by
  rw [T5Glue.discL, T5Glue.discL, h.g₂, h.g₃]; ring

theorem IsScale.weierstrassP (h : IsScale P Q c) (z : ℂ) :
    P.weierstrassP (c * z) = (c ^ 2)⁻¹ * Q.weierstrassP z := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, ← (h.equiv).tsum_eq, ← tsum_mul_left]
  congr 1; ext l
  simp only [IsScale.equiv, Equiv.coe_fn_mk]
  rw [show c * z - c * (l : ℂ) = c * (z - l) by ring]
  simp only [one_div, mul_pow, mul_inv]
  ring

theorem IsScale.derivWeierstrassP (h : IsScale P Q c) (z : ℂ) :
    P.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * Q.derivWeierstrassP z := by
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, ← (h.equiv).tsum_eq,
    mul_neg, ← tsum_mul_left]
  congr 1; congr 1; ext l
  simp only [IsScale.equiv, Equiv.coe_fn_mk]
  rw [show c * z - c * (l : ℂ) = c * (z - l) by ring]
  simp only [div_eq_mul_inv, mul_pow, mul_inv]
  ring

theorem IsScale.jL (h : IsScale P Q c) : jL P = jL Q := by
  rw [T5Glue.jL, T5Glue.jL, h.g₂, h.discL]
  have hc := h.1
  rcases eq_or_ne (T5Glue.discL Q) 0 with hd | hd
  · simp [hd]
  · field_simp

theorem IsScale.weber (h : IsScale P Q c) (z : ℂ) : weber P (c * z) = weber Q z := by
  have hc := h.1
  have e3 : P.g₃ = 0 ↔ Q.g₃ = 0 := by rw [h.g₃]; simp [hc]
  have e2 : P.g₂ = 0 ↔ Q.g₂ = 0 := by rw [h.g₂]; simp [hc]
  rw [T5Glue.weber, T5Glue.weber, h.weierstrassP, h.discL, h.g₂, h.g₃]
  rw [h.g₃] at e3; rw [h.g₂] at e2
  rcases eq_or_ne (T5Glue.discL Q) 0 with hd | hd
  · simp [hd]
  by_cases h3 : Q.g₃ = 0
  · simp only [h3, mul_zero, ↓reduceIte]
    field_simp
  · have h3' : ¬ (c ^ 6)⁻¹ * Q.g₃ = 0 := by simp [hc, h3]
    simp only [h3, h3', ↓reduceIte]
    by_cases h2 : Q.g₂ = 0
    · simp only [h2, mul_zero, ↓reduceIte]
      field_simp
    · have h2' : ¬ (c ^ 4)⁻¹ * Q.g₂ = 0 := by simp [hc, h2]
      simp only [h2, h2', ↓reduceIte]
      field_simp

end Scale

/-! ## §2. Conjugation data -/

section Conj

variable (σ : ℂ →+* ℂ) {P Q : PeriodPair} {μ : ℂ}

/-- `σ(E_P) ≅ E_Q` through `(x, y) ↦ (μ⁻²x, μ⁻³y)`: `σ(g₂(P)) = μ⁴g₂(Q)`, `σ(g₃(P)) = μ⁶g₃(Q)`. -/
def IsConjModel (P Q : PeriodPair) (μ : ℂ) : Prop :=
  μ ≠ 0 ∧ σ P.g₂ = μ ^ 4 * Q.g₂ ∧ σ P.g₃ = μ ^ 6 * Q.g₃

variable {σ}

theorem IsConjModel.discL (h : IsConjModel σ P Q μ) : σ (discL P) = μ ^ 12 * discL Q := by
  rw [T5Glue.discL, T5Glue.discL, map_sub, map_mul, map_pow, map_pow, h.2.1, h.2.2]
  simp only [map_ofNat]; ring

theorem IsConjModel.jL (h : IsConjModel σ P Q μ) : σ (jL P) = jL Q := by
  rw [T5Glue.jL, T5Glue.jL, map_div₀, map_mul, map_pow, h.discL, h.2.1]
  simp only [map_ofNat]
  have hμ := h.1
  rcases eq_or_ne (T5Glue.discL Q) 0 with hd | hd
  · simp [hd]
  · field_simp

theorem IsConjModel.g₃_iff (h : IsConjModel σ P Q μ) : P.g₃ = 0 ↔ Q.g₃ = 0 := by
  constructor
  · intro h0; have := h.2.2; rw [h0, map_zero] at this
    rcases mul_eq_zero.1 this.symm with h' | h'
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h') h.1
    · exact h'
  · intro h0; have := h.2.2; rw [h0, mul_zero] at this
    exact (map_eq_zero σ).1 this

theorem IsConjModel.g₂_iff (h : IsConjModel σ P Q μ) : P.g₂ = 0 ↔ Q.g₂ = 0 := by
  constructor
  · intro h0; have := h.2.1; rw [h0, map_zero] at this
    rcases mul_eq_zero.1 this.symm with h' | h'
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h') h.1
    · exact h'
  · intro h0; have := h.2.1; rw [h0, mul_zero] at this
    exact (map_eq_zero σ).1 this

/-- **Weber values transform by conjugation**: `σ(h_P(z)) = h_Q(w)`. -/
theorem IsConjModel.weber (h : IsConjModel σ P Q μ) {z w : ℂ}
    (hz : σ (P.weierstrassP z) = μ ^ 2 * Q.weierstrassP w) : σ (weber P z) = weber Q w := by
  have hμ := h.1
  have hd := h.discL
  have h2 := h.2.1
  have h3 := h.2.2
  unfold T5Glue.weber
  by_cases c3 : Q.g₃ = 0
  · have c3' : P.g₃ = 0 := h.g₃_iff.2 c3
    simp only [c3, c3', ↓reduceIte, map_mul, map_div₀, map_pow, h2, hd, hz]
    rcases eq_or_ne (T5Glue.discL Q) 0 with hq | hq
    · simp [hq]
    · field_simp
  · have c3' : ¬ P.g₃ = 0 := fun e => c3 (h.g₃_iff.1 e)
    simp only [c3, c3', ↓reduceIte]
    by_cases c2 : Q.g₂ = 0
    · have c2' : P.g₂ = 0 := h.g₂_iff.2 c2
      simp only [c2, c2', ↓reduceIte, map_mul, map_div₀, map_pow, h3, hd, hz]
      rcases eq_or_ne (T5Glue.discL Q) 0 with hq | hq
      · simp [hq]
      · field_simp
    · have c2' : ¬ P.g₂ = 0 := fun e => c2 (h.g₂_iff.1 e)
      simp only [c2, c2', ↓reduceIte, map_mul, map_div₀, h2, h3, hd, hz]
      rcases eq_or_ne (T5Glue.discL Q) 0 with hq | hq
      · simp [hq]
      · field_simp

/-- **From `σ(j(P)) = j(Q)` to a conjugation model** (nonzero discriminants). -/
theorem exists_conjModel_of_jL (hP : discL P ≠ 0) (hQ : discL Q ≠ 0) (hj : σ (jL P) = jL Q) :
    ∃ μ, IsConjModel σ P Q μ := by
  set a := σ P.g₂ with ha
  set b := σ P.g₃ with hb
  set a' := Q.g₂
  set b' := Q.g₃
  have hΔ : a ^ 3 - 27 * b ^ 2 ≠ 0 := by
    have : σ (discL P) ≠ 0 := (map_ne_zero σ).2 hP
    rw [T5Glue.discL, map_sub, map_mul, map_pow, map_pow, map_ofNat] at this
    exact this
  have hΔ' : a' ^ 3 - 27 * b' ^ 2 ≠ 0 := hQ
  have hj' : a ^ 3 * (a' ^ 3 - 27 * b' ^ 2) = a' ^ 3 * (a ^ 3 - 27 * b ^ 2) := by
    simp only [T5Glue.jL, T5Glue.discL, map_div₀, map_mul, map_pow, map_sub, map_ofNat] at hj
    rw [div_eq_div_iff hΔ hΔ'] at hj
    change 1728 * a ^ 3 * (a' ^ 3 - 27 * b' ^ 2) = 1728 * a' ^ 3 * (a ^ 3 - 27 * b ^ 2) at hj
    linear_combination hj / 1728
  by_cases e2 : a' = 0
  · -- `j = 0`
    have ea : a = 0 := by
      have : a ^ 3 * (a' ^ 3 - 27 * b' ^ 2) = 0 := by
        linear_combination hj' + (a' ^ 2 * (a ^ 3 - 27 * b ^ 2)) * e2
      rcases mul_eq_zero.1 this with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.1 h
      · exact absurd h hΔ'
    have eb : b' ≠ 0 := fun h0 => hΔ' (by rw [e2, h0]; ring)
    have eb2 : b ≠ 0 := fun h0 => hΔ (by rw [ea, h0]; ring)
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (b / b') (by norm_num : 0 < 6)
    have hμ0 : μ ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at hμ
      exact div_ne_zero eb2 eb hμ.symm
    refine ⟨μ, hμ0, ?_, ?_⟩
    · show a = μ ^ 4 * a'; rw [ea, e2]; ring
    · show b = μ ^ 6 * b'; rw [hμ]; field_simp
  by_cases e3 : b' = 0
  · -- `j = 1728`
    have eb : b = 0 := by
      have : a' ^ 3 * (27 * b ^ 2) = 0 := by linear_combination hj' + (27 * a ^ 3 * b') * e3
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.1 h) e2
      · have : b ^ 2 = 0 := by linear_combination h / 27
        exact pow_eq_zero_iff (by norm_num) |>.1 this
    have ea : a ≠ 0 := fun h0 => hΔ (by rw [h0, eb]; ring)
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (a / a') (by norm_num : 0 < 4)
    have hμ0 : μ ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at hμ
      exact div_ne_zero ea e2 hμ.symm
    refine ⟨μ, hμ0, ?_, ?_⟩
    · show a = μ ^ 4 * a'; rw [hμ]; field_simp
    · show b = μ ^ 6 * b'; rw [eb, e3]; ring
  · -- generic
    have ea : a ≠ 0 := by
      intro h0
      have : a' ^ 3 * (a ^ 3 - 27 * b ^ 2) = 0 := by
        linear_combination -hj' + (a ^ 2 * (a' ^ 3 - 27 * b' ^ 2)) * h0
      rcases mul_eq_zero.1 this with h | h
      · exact e2 (pow_eq_zero_iff (by norm_num) |>.1 h)
      · exact hΔ h
    have eb : b ≠ 0 := by
      intro h0
      have : a ^ 3 * (27 * b' ^ 2) = 0 := by
        linear_combination -hj' + (27 * a' ^ 3 * b) * h0
      rcases mul_eq_zero.1 this with h | h
      · exact ea (pow_eq_zero_iff (by norm_num) |>.1 h)
      · have : b' ^ 2 = 0 := by linear_combination h / 27
        exact e3 (pow_eq_zero_iff (by norm_num) |>.1 this)
    have key : b ^ 2 * a' ^ 3 = a ^ 3 * b' ^ 2 := by linear_combination hj' / 27
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (b * a' / (a * b')) (by norm_num : 0 < 2)
    have hμ0 : μ ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at hμ
      exact div_ne_zero (mul_ne_zero eb e2) (mul_ne_zero ea e3) hμ.symm
    have hμ' : μ ^ 2 * (a * b') = b * a' := by rw [hμ]; field_simp
    have hab : a ^ 2 * b' ^ 2 ≠ 0 := by positivity
    have hab3 : a ^ 3 * b' ^ 2 ≠ 0 := by positivity
    refine ⟨μ, hμ0, ?_, ?_⟩
    · show a = μ ^ 4 * a'
      have : (μ ^ 4 * a' - a) * (a ^ 2 * b' ^ 2) = 0 := by
        linear_combination (a' * (μ ^ 2 * (a * b') + b * a')) * hμ' + key
      rcases mul_eq_zero.1 this with h | h
      · exact (sub_eq_zero.1 h).symm
      · exact absurd h hab
    · show b = μ ^ 6 * b'
      have : (μ ^ 6 * b' - b) * (a ^ 3 * b' ^ 2) = 0 := by
        linear_combination ((μ ^ 2 * (a * b')) ^ 2 + (μ ^ 2 * (a * b')) * (b * a') + (b * a') ^ 2) *
          hμ' + b * key
      rcases mul_eq_zero.1 this with h | h
      · exact (sub_eq_zero.1 h).symm
      · exact absurd h hab3

/-- A primitive cube root of unity. -/
def omega3 : ℂ := (-1 + I * (Real.sqrt 3 : ℂ)) / 2

theorem sqrt3_sq : (Real.sqrt 3 : ℂ) ^ 2 = 3 := by
  rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; push_cast; ring

theorem omega3_sq_add : omega3 ^ 2 + omega3 + 1 = 0 := by
  unfold omega3
  linear_combination (-(1 : ℂ) / 4) * sqrt3_sq + (1 / 4 * (Real.sqrt 3 : ℂ) ^ 2) * I_sq

theorem omega3_cube : omega3 ^ 3 = 1 := by
  linear_combination (omega3 - 1) * omega3_sq_add

theorem cube_eq_cube {x y : ℂ} (h : x ^ 3 = y ^ 3) :
    x = y ∨ x = omega3 * y ∨ x = omega3 ^ 2 * y := by
  have : (x - y) * (x - omega3 * y) * (x - omega3 ^ 2 * y) = 0 := by
    linear_combination h + (x * y ^ 2 - x ^ 2 * y) * omega3_sq_add + (x * y ^ 2 - y ^ 3) * omega3_cube
  rcases mul_eq_zero.1 this with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (sub_eq_zero.1 h2)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h2))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h1))

/-- **Adjusting the model to a Weber value**: if `σ(h_P(z)) = h_Q(w)` then for some `μ'`,
`σ(E_P) ≅ E_Q` by `μ'` and `σ(℘_P(z)) = μ'²℘_Q(w)` (nonzero discriminant of `Q`). -/
theorem IsConjModel.adjust (h : IsConjModel σ P Q μ) (hQ : T5Glue.discL Q ≠ 0) {z w : ℂ}
    (hw : σ (T5Glue.weber P z) = T5Glue.weber Q w) :
    ∃ μ', IsConjModel σ P Q μ' ∧ σ (P.weierstrassP z) = μ' ^ 2 * Q.weierstrassP w := by
  have hμ := h.1
  have hd := h.discL
  have h2 := h.2.1
  have h3 := h.2.2
  unfold T5Glue.weber at hw
  by_cases c3 : Q.g₃ = 0
  · have c3' : P.g₃ = 0 := h.g₃_iff.2 c3
    have c2 : Q.g₂ ≠ 0 := fun e => hQ (by rw [T5Glue.discL, e, c3]; ring)
    simp only [c3, c3', ↓reduceIte, map_mul, map_div₀, map_pow, h2, hd] at hw
    have hx : σ (P.weierstrassP z) ^ 2 = (μ ^ 2 * Q.weierstrassP w) ^ 2 := by
      field_simp at hw
      linear_combination hw
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hx with e | e
    · exact ⟨μ, h, e⟩
    · refine ⟨I * μ, ⟨mul_ne_zero I_ne_zero hμ, ?_, ?_⟩, ?_⟩
      · have hI4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, I_sq]; norm_num
        rw [h2, mul_pow, hI4]; ring
      · rw [h3, c3]; ring
      · rw [e, mul_pow, I_sq]; ring
  · have c3' : ¬ P.g₃ = 0 := fun e => c3 (h.g₃_iff.1 e)
    simp only [c3, c3', ↓reduceIte] at hw
    by_cases c2 : Q.g₂ = 0
    · have c2' : P.g₂ = 0 := h.g₂_iff.2 c2
      simp only [c2, c2', ↓reduceIte, map_mul, map_div₀, map_pow, h3, hd] at hw
      have hx : σ (P.weierstrassP z) ^ 3 = (μ ^ 2 * Q.weierstrassP w) ^ 3 := by
        field_simp at hw
        linear_combination hw
      have hw3 : omega3 ≠ 0 := fun e => by simpa [e] using omega3_cube
      rcases cube_eq_cube hx with e | e | e
      · exact ⟨μ, h, e⟩
      · -- `ν = ω²`, `ν² = ω⁴ = ω`, `ν⁶ = 1`
        refine ⟨omega3 ^ 2 * μ, ⟨mul_ne_zero (pow_ne_zero _ hw3) hμ, ?_, ?_⟩, ?_⟩
        · rw [h2, c2]; ring
        · rw [h3]
          linear_combination (-(μ ^ 6 * Q.g₃) * (omega3 ^ 9 + omega3 ^ 6 + omega3 ^ 3 + 1)) *
            omega3_cube
        · rw [e]; linear_combination (-(omega3 * μ ^ 2 * Q.weierstrassP w)) * omega3_cube
      · -- `ν = ω`, `ν² = ω²`
        refine ⟨omega3 * μ, ⟨mul_ne_zero hw3 hμ, ?_, ?_⟩, ?_⟩
        · rw [h2, c2]; ring
        · rw [h3]; linear_combination (-(μ ^ 6 * Q.g₃) * (omega3 ^ 3 + 1)) * omega3_cube
        · rw [e]; ring
    · have c2' : ¬ P.g₂ = 0 := fun e => c2 (h.g₂_iff.1 e)
      simp only [c2, c2', ↓reduceIte, map_mul, map_div₀, h2, h3, hd] at hw
      refine ⟨μ, h, ?_⟩
      field_simp at hw
      linear_combination hw

/-- **`℘'` up to sign**: from `σ(℘_P(z)) = μ²℘_Q(w)` (`z`, `w` not lattice points),
`σ(℘'_P(z)) = μ³℘'_Q(w)` or `= −μ³℘'_Q(w)`. -/
theorem IsConjModel.deriv_sign (h : IsConjModel σ P Q μ) {z w : ℂ} (hz : z ∉ P.lattice)
    (hw : w ∉ Q.lattice) (hp : σ (P.weierstrassP z) = μ ^ 2 * Q.weierstrassP w) :
    σ (P.derivWeierstrassP z) = μ ^ 3 * Q.derivWeierstrassP w ∨
      σ (P.derivWeierstrassP z) = -(μ ^ 3 * Q.derivWeierstrassP w) := by
  have e1 := P.derivWeierstrassP_sq z hz
  have e2 := Q.derivWeierstrassP_sq w hw
  have : σ (P.derivWeierstrassP z) ^ 2 = (μ ^ 3 * Q.derivWeierstrassP w) ^ 2 := by
    rw [← map_pow, e1]
    simp only [map_sub, map_mul, map_pow, map_ofNat, hp, h.2.1, h.2.2]
    linear_combination (-(μ ^ 6)) * e2
  exact sq_eq_sq_iff_eq_or_eq_neg.1 this

end Conj

end T5Glue
