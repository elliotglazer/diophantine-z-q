import Mathlib

/-!
# t5-glue, part 3: `Δ(ℂ/⟨1, τ⟩) ≠ 0` from Mathlib's modular forms (Mathlib only)

Task t5-glue (2026-11-14). `G_k(⟨1, τ⟩) = 2ζ(k)E_k(τ)` (Mathlib's
`tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`), `ζ(4) = π⁴/90`, `ζ(6) = π⁶/945`
(`riemannZeta_two_mul_nat`, `bernoulli 6 = 1/42`), so
`g₂³ − 27g₃² = (64π¹²/27)(E₄³ − E₆²) = (64π¹²/27)·1728·Δ(τ)` (Mathlib's
`discriminant_eq_E₄_cube_sub_E₆_sq`), and `Δ(τ) ≠ 0` (`discriminant_ne_zero`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace T5Glue

open Complex

/-- The period pair `(1, τ)` (same definition as `pp` in `Elliptic.lean`). -/
def ppD (τ : UpperHalfPlane) : PeriodPair :=
  ⟨1, τ, by
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
    exact ⟨by exact_mod_cast h, rfl⟩⟩

/-- `ℤ² ≃ ⟨1, τ⟩`, `v ↦ v₁ + v₀τ`. -/
def latEquiv (τ : UpperHalfPlane) : (Fin 2 → ℤ) ≃ (ppD τ).lattice :=
  ((finTwoArrowEquiv ℤ).trans (Equiv.prodComm ℤ ℤ)).trans (ppD τ).latticeEquivProd.symm.toEquiv

theorem latEquiv_apply (τ : UpperHalfPlane) (v : Fin 2 → ℤ) :
    ((latEquiv τ v : (ppD τ).lattice) : ℂ) = v 0 * τ + v 1 := by
  simp only [latEquiv, Equiv.trans_apply, LinearEquiv.coe_toEquiv]
  rw [PeriodPair.latticeEquiv_symm_apply]
  simp [ppD, add_comm]

/-- `G_k(⟨1, τ⟩) = 2ζ(k)E_k(τ)` for `k ≥ 3`. -/
theorem G_eq_E {k : ℕ} (hk : 3 ≤ k) (τ : UpperHalfPlane) :
    (ppD τ).G k = 2 * riemannZeta k * ModularForm.E hk τ := by
  rw [PeriodPair.G, ← (latEquiv τ).tsum_eq]
  have h1 : ∀ v : Fin 2 → ℤ, (((latEquiv τ v : (ppD τ).lattice) : ℂ) ^ k)⁻¹ =
      EisensteinSeries.eisSummand k v τ := by
    intro v
    rw [latEquiv_apply, EisensteinSeries.eisSummand, zpow_neg, zpow_natCast]
  simp_rw [h1]
  rw [tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk]
  have h2 : ModularForm.E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [h2]
  ring

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_def]
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have c1 : Nat.choose 6 2 = 15 := by decide
  have c2 : Nat.choose 6 3 = 20 := by decide
  have c3 : Nat.choose 6 4 = 15 := by decide
  norm_num [Finset.sum_range_succ, h5, c1, c2, c3]

theorem riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 : ℂ) * ((3 : ℕ) : ℂ) = 6 by norm_num] at h
  rw [h, bernoulli_six]
  simp [Nat.factorial]
  ring

/-- **`Δ(ℂ/⟨1, τ⟩) ≠ 0`.** -/
theorem disc_ppD_ne_zero (τ : UpperHalfPlane) :
    (ppD τ).g₂ ^ 3 - 27 * (ppD τ).g₃ ^ 2 ≠ 0 := by
  have h4 := G_eq_E (k := 4) (by norm_num) τ
  have h6 := G_eq_E (k := 6) (by norm_num) τ
  have hz4 : riemannZeta ((4 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 4 / 90 := by
    rw [show ((4 : ℕ) : ℂ) = 4 by norm_num]; exact riemannZeta_four
  have hz6 : riemannZeta ((6 : ℕ) : ℂ) = (Real.pi : ℂ) ^ 6 / 945 := by
    rw [show ((6 : ℕ) : ℂ) = 6 by norm_num]; exact riemannZeta_six
  rw [hz4] at h4
  rw [hz6] at h6
  have hΔ := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  have hne := ModularForm.discriminant_ne_zero τ
  have key : (ppD τ).g₂ ^ 3 - 27 * (ppD τ).g₃ ^ 2 =
      64 * (Real.pi : ℂ) ^ 12 / 27 * 1728 * ModularForm.discriminant τ := by
    rw [PeriodPair.g₂, PeriodPair.g₃, h4, h6, hΔ]
    simp only [ModularForm.E₄, ModularForm.E₆]
    ring
  rw [key]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h64 : (64 : ℂ) * (Real.pi : ℂ) ^ 12 / 27 * 1728 ≠ 0 := by
    have : (Real.pi : ℂ) ^ 12 ≠ 0 := pow_ne_zero _ hπ
    field_simp
    norm_num [this]
  exact mul_ne_zero h64 hne

end T5Glue
