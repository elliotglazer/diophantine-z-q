import ZInQKernel.Contrib.OneProof.ThetaModularityM46

set_option linter.all false

noncomputable section

namespace GapTheta

/-! # Part II: Igusa's `ψ₄`, `χ₁₀` on all of `Sp₄(ℤ)`

## II.1 Generation of `Sp₄(ℤ)` -/

section Generation
open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups


/-- Integer `4 × 4` matrices with the block index of `Matrix.symplecticGroup (Fin 2) ℤ`. -/
abbrev Mat4 := Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

/-- `SL₂(ℤ)` on the coordinates `(a₁, c₁)`. -/
def iota1 : SL(2, ℤ) →* Mat4 where
  toFun g := Matrix.fromBlocks !![(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0, 0; 0, 1]
    !![(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, 0; 0, 0] !![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0, 0; 0, 0]
    !![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 1, 0; 0, 1]
  map_one' := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul]

/-- `SL₂(ℤ)` on the coordinates `(a₂, c₂)`. -/
def iota2 : SL(2, ℤ) →* Mat4 where
  toFun g := Matrix.fromBlocks !![1, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0]
    !![0, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1] !![0, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0]
    !![1, 0; 0, (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1]
  map_one' := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul]

/-- The rotation `[[U, 0], [0, U⁻ᵀ]]` (`U⁻ᵀ` written as the transposed adjugate). -/
def rot : SL(2, ℤ) →* Mat4 where
  toFun g := Matrix.fromBlocks (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    !![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0;
       -(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0]
  map_one' := by
    ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_mul' g h := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_mul] <;>
      ring

/-- The translation `[[1, S], [0, 1]]`. -/
def Tm (S : Matrix (Fin 2) (Fin 2) ℤ) : Mat4 := Matrix.fromBlocks 1 S 0 1

theorem Tm_mul (S S' : Matrix (Fin 2) (Fin 2) ℤ) : Tm S * Tm S' = Tm (S + S') := by
  simp [Tm, Matrix.fromBlocks_multiply, add_comm]

theorem det_sl (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
  have := g.2; rwa [Matrix.det_fin_two] at this

/-- The sixteen relations `ω(M eₐ, M e_b) = ω(eₐ, e_b)` of a symplectic matrix. -/
theorem sp_rel {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) (a b : Fin 2 ⊕ Fin 2) :
    -M (Sum.inl 0) a * M (Sum.inr 0) b - M (Sum.inl 1) a * M (Sum.inr 1) b +
      M (Sum.inr 0) a * M (Sum.inl 0) b + M (Sum.inr 1) a * M (Sum.inl 1) b = Matrix.J (Fin 2) ℤ a b := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff'.1 hM) a) b
  rw [← h]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J]
  ring

theorem iota1_mem (g : SL(2, ℤ)) : iota1 g ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff']
  have := det_sl g
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota1, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J] <;> linarith

theorem iota2_mem (g : SL(2, ℤ)) : iota2 g ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff']
  have := det_sl g
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota2, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J] <;> linarith

theorem rot_mem (g : SL(2, ℤ)) : rot g ∈ Matrix.symplecticGroup (Fin 2) ℤ := by
  rw [SymplecticGroup.mem_iff']
  have := det_sl g
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.J] <;> linarith


/-- Bezout in `SL₂(ℤ)`: some `U` kills the second coordinate of `(x, y)`. -/
theorem bezout_sl (x y : ℤ) : ∃ U : SL(2, ℤ),
    (U : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * x + (U : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * y = 0 := by
  by_cases h0 : Int.gcd x y = 0
  · refine ⟨1, ?_⟩
    have hx : x = 0 := Int.gcd_eq_zero_iff.1 h0 |>.1
    have hy : y = 0 := Int.gcd_eq_zero_iff.1 h0 |>.2
    simp [hx, hy]
  · obtain ⟨x', hx'⟩ := Int.gcd_dvd_left (a := x) (b := y)
    obtain ⟨y', hy'⟩ := Int.gcd_dvd_right (a := x) (b := y)
    have hg := Int.gcd_eq_gcd_ab x y
    have hg0 : (Int.gcd x y : ℤ) ≠ 0 := by exact_mod_cast h0
    generalize (Int.gcd x y : ℤ) = G at hx' hy' hg hg0
    generalize x.gcdA y = A at hg
    generalize x.gcdB y = B at hg
    subst hx' hy'
    have hdet : A * x' + B * y' = 1 := by
      have : G * (A * x' + B * y') = G * 1 := by linear_combination -hg
      exact mul_left_cancel₀ hg0 this
    refine ⟨⟨!![A, B; -y', x'], by rw [Matrix.det_fin_two_of]; linarith⟩, ?_⟩
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring

section Reduction

variable (H : Submonoid Mat4) (h1 : ∀ g, iota1 g ∈ H) (h2 : ∀ g, iota2 g ∈ H) (hr : ∀ g, rot g ∈ H)
  (hT : ∀ x s : ℤ, Tm !![x, s; s, 0] ∈ H)
include h1 h2 hr hT

theorem red_stab {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (e0 : M (Sum.inl 0) (Sum.inl 0) = 1) (e1 : M (Sum.inl 1) (Sum.inl 0) = 0)
    (e2 : M (Sum.inr 0) (Sum.inl 0) = 0) (e3 : M (Sum.inr 1) (Sum.inl 0) = 0) : M ∈ H := by
  have r := sp_rel hM
  have k1 := r (Sum.inl 0) (Sum.inl 1)
  have k2 := r (Sum.inl 0) (Sum.inr 0)
  have k3 := r (Sum.inl 0) (Sum.inr 1)
  have k4 := r (Sum.inl 1) (Sum.inr 1)
  have k5 := r (Sum.inl 1) (Sum.inr 0)
  have k6 := r (Sum.inr 0) (Sum.inr 1)
  simp only [e0, e1, e2, e3, Matrix.J, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] at k1 k2 k3 k4 k5 k6
  simp at k1 k2 k3
  simp only [k1, k2, k3] at k4 k5 k6
  simp at k4 k5 k6
  have hp : M (Sum.inl 0) (Sum.inl 1) =
      M (Sum.inr 1) (Sum.inl 1) * M (Sum.inl 1) (Sum.inr 0) -
        M (Sum.inl 1) (Sum.inl 1) * M (Sum.inr 1) (Sum.inr 0) := by linear_combination -k5
  have hr' : M (Sum.inl 0) (Sum.inr 1) =
      M (Sum.inl 1) (Sum.inr 0) * M (Sum.inr 1) (Sum.inr 1) -
        M (Sum.inr 1) (Sum.inr 0) * M (Sum.inl 1) (Sum.inr 1) := by linear_combination k6
  have hγ : !![M (Sum.inl 1) (Sum.inl 1), M (Sum.inl 1) (Sum.inr 1);
      M (Sum.inr 1) (Sum.inl 1), M (Sum.inr 1) (Sum.inr 1)].det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination -k4
  let γ : SL(2, ℤ) := ⟨_, hγ⟩
  have key : M = Tm !![M (Sum.inl 0) (Sum.inr 0) - M (Sum.inl 1) (Sum.inr 0) * M (Sum.inr 1) (Sum.inr 0),
      M (Sum.inl 1) (Sum.inr 0); M (Sum.inl 1) (Sum.inr 0), 0] *
      rot (T ^ (-M (Sum.inr 1) (Sum.inr 0))) * iota2 γ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Tm, rot, iota2, γ, coe_T_zpow, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
        e0, e1, e2, e3, k1, k2, k3, hp, hr'] <;> ring
  rw [key]
  exact H.mul_mem (H.mul_mem (hT _ _) (hr _)) (h2 _)

omit h1 h2 hr hT in
theorem of_left {M X X' : Mat4} (hXX' : X' * X = 1) (hX' : X' ∈ H) (hN : X * M ∈ H) : M ∈ H := by
  rw [show M = X' * (X * M) by rw [← mul_assoc, hXX', one_mul]]
  exact H.mul_mem hX' hN

theorem red_sign {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (e1 : M (Sum.inl 1) (Sum.inl 0) = 0) (e2 : M (Sum.inr 0) (Sum.inl 0) = 0)
    (e3 : M (Sum.inr 1) (Sum.inl 0) = 0) : M ∈ H := by
  have k := sp_rel hM (Sum.inl 0) (Sum.inr 0)
  simp only [e1, e2, e3, Matrix.J, Matrix.fromBlocks_apply₁₂] at k
  simp at k
  have hg : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inr 0) (Sum.inr 0) = 1 := by linarith
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hg with h | h
  · exact red_stab H h1 h2 hr hT hM h e1 e2 e3
  · refine of_left H (X := iota1 (-1)) (X' := iota1 (-1)) (by rw [← map_mul]; simp) (h1 _) ?_
    refine red_stab H h1 h2 hr hT (Submonoid.mul_mem _ (iota1_mem _) hM) ?_ ?_ ?_ ?_ <;>
      simp [iota1, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, h, e1, e2, e3]

theorem red_c0 {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (e2 : M (Sum.inr 0) (Sum.inl 0) = 0) (e3 : M (Sum.inr 1) (Sum.inl 0) = 0) : M ∈ H := by
  obtain ⟨U, hU⟩ := bezout_sl (M (Sum.inl 0) (Sum.inl 0)) (M (Sum.inl 1) (Sum.inl 0))
  refine of_left H (X := rot U) (X' := rot U⁻¹) (by rw [← map_mul]; simp) (hr _) ?_
  refine red_sign H h1 h2 hr hT (Submonoid.mul_mem _ (rot_mem _) hM) ?_ ?_ ?_ <;>
    simp [rot, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, e2, e3, hU]

theorem red_c2 {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ)
    (e3 : M (Sum.inr 1) (Sum.inl 0) = 0) : M ∈ H := by
  obtain ⟨U, hU⟩ := bezout_sl (M (Sum.inl 0) (Sum.inl 0)) (M (Sum.inr 0) (Sum.inl 0))
  refine of_left H (X := iota1 U) (X' := iota1 U⁻¹) (by rw [← map_mul]; simp) (h1 _) ?_
  refine red_c0 H h1 h2 hr hT (Submonoid.mul_mem _ (iota1_mem _) hM) ?_ ?_ <;>
    simp [iota1, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, e3, hU]

/-- **Every element of `Sp₄(ℤ)` lies in `H`.** -/
theorem red_all {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) : M ∈ H := by
  obtain ⟨U, hU⟩ := bezout_sl (M (Sum.inl 1) (Sum.inl 0)) (M (Sum.inr 1) (Sum.inl 0))
  refine of_left H (X := iota2 U) (X' := iota2 U⁻¹) (by rw [← map_mul]; simp) (h2 _) ?_
  refine red_c2 H h1 h2 hr hT (Submonoid.mul_mem _ (iota2_mem _) hM) ?_
  simp [iota2, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hU]

end Reduction


/-! ## The generating set -/

/-- Eleven generators: the images of `S, T, T⁻¹` under `iota1`, `iota2`, `rot`, and the translations by
`±[[0, 1], [1, 0]]`. -/
def gens : Set Mat4 :=
  {iota1 S, iota1 T, iota1 T⁻¹, iota2 S, iota2 T, iota2 T⁻¹, rot S, rot T, rot T⁻¹,
    Tm !![0, 1; 1, 0], Tm !![0, -1; -1, 0]}

theorem S_inv_eq : (S⁻¹ : SL(2, ℤ)) = S * S * S := by decide

theorem hom_mem {φ : SL(2, ℤ) →* Mat4} {H : Submonoid Mat4} (hS : φ S ∈ H) (hT : φ T ∈ H)
    (hT' : φ T⁻¹ ∈ H) (g : SL(2, ℤ)) : φ g ∈ H := by
  have hg : g ∈ (Subgroup.closure ({S, T} : Set SL(2, ℤ))).toSubmonoid := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  rw [Subgroup.closure_toSubmonoid] at hg
  have hle : Submonoid.closure (({S, T} : Set SL(2, ℤ)) ∪ ({S, T} : Set SL(2, ℤ))⁻¹) ≤ H.comap φ := by
    rw [Submonoid.closure_le]
    rintro x (hx | hx)
    · rcases hx with rfl | rfl
      · exact hS
      · exact hT
    · rw [Set.mem_inv] at hx
      rcases hx with hx | hx
      · rw [← inv_inv x, hx, S_inv_eq]
        show φ (S * S * S) ∈ H
        rw [map_mul, map_mul]; exact H.mul_mem (H.mul_mem hS hS) hS
      · rw [← inv_inv x, hx]; exact hT'
  exact hle hg

theorem sp_mem_closure {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) :
    M ∈ Submonoid.closure gens := by
  set H := Submonoid.closure gens
  have g : ∀ x ∈ gens, x ∈ H := fun x hx => Submonoid.subset_closure hx
  have h1 : ∀ g', iota1 g' ∈ H := hom_mem (g _ (by simp [gens])) (g _ (by simp [gens]))
    (g _ (by simp [gens]))
  have h2 : ∀ g', iota2 g' ∈ H := hom_mem (g _ (by simp [gens])) (g _ (by simp [gens]))
    (g _ (by simp [gens]))
  have hr : ∀ g', rot g' ∈ H := hom_mem (g _ (by simp [gens])) (g _ (by simp [gens]))
    (g _ (by simp [gens]))
  have hod : ∀ k : ℤ, Tm !![0, k; k, 0] ∈ H := by
    intro k
    induction k using Int.induction_on with
    | zero => rw [show Tm !![0, (0 : ℤ); 0, 0] = 1 by
                ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
                  simp [Tm]]
              exact H.one_mem
    | succ k ih =>
      rw [show Tm !![0, (k : ℤ) + 1; (k : ℤ) + 1, 0] = Tm !![0, (k : ℤ); k, 0] * Tm !![0, 1; 1, 0] by
        rw [Tm_mul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp]
      exact H.mul_mem ih (g _ (by simp [gens]))
    | pred k ih =>
      rw [show Tm !![0, -(k : ℤ) - 1; -(k : ℤ) - 1, 0] = Tm !![0, -(k : ℤ); -k, 0] * Tm !![0, -1; -1, 0] by
        rw [Tm_mul]; congr 1; ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring]
      exact H.mul_mem ih (g _ (by simp [gens]))
  have hT : ∀ x s : ℤ, Tm !![x, s; s, 0] ∈ H := by
    intro x s
    rw [show Tm !![x, s; s, 0] = iota1 (T ^ x) * Tm !![0, s; s, 0] by
      ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [Tm, iota1, coe_T_zpow, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]]
    exact H.mul_mem (h1 _) (hod s)
  exact red_all H h1 h2 hr hT hM


end Generation

/-! ## II.2 The cocycle and the automorphy monoid -/

section Theta
open Complex Matrix CM24
open scoped Real MatrixGroups
open HDec.PkgI1 (SiegelH2 thetaConst evenChars thetaSum8 thetaProd2 spAct spFactor Char2)

theorem siegel_of {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) (h : PDq (Ω 0 0) (Ω 0 1) (Ω 1 1)) :
    Ω ∈ SiegelH2 := by
  refine ⟨?_, HDec.HSyn.G0Split.FibreQM.PeriodMap.posDef_fin_two (by simp [hs]) (by simpa using h.1)
    (by simp only [Matrix.map_apply, hs]; nlinarith [h.2])⟩
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, hs]

theorem siegel_of' {p q r : ℂ} (h : PDq p q r) : !![p, q; q, r] ∈ SiegelH2 :=
  siegel_of (by simp) (by simpa using h)

/-- **The cocycle** of the action `(AΩ + B)(CΩ + D)⁻¹` and of `det(CΩ + D)`. -/
theorem sp_comp (M N : Mat4) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hN : spFactor N Ω ≠ 0)
    (hM : spFactor M (spAct N Ω) ≠ 0) :
    spAct (M * N) Ω = spAct M (spAct N Ω) ∧ spFactor (M * N) Ω = spFactor M (spAct N Ω) * spFactor N Ω := by
  simp only [spAct, spFactor] at hN hM ⊢
  have hmul : (M * N).map (Int.cast : ℤ → ℂ) = M.map (Int.cast : ℤ → ℂ) * N.map (Int.cast : ℤ → ℂ) :=
    Matrix.map_mul (f := Int.castRingHom ℂ)
  rw [hmul]
  set Mc := M.map (Int.cast : ℤ → ℂ)
  set Nc := N.map (Int.cast : ℤ → ℂ)
  rw [← Matrix.fromBlocks_toBlocks Mc, ← Matrix.fromBlocks_toBlocks Nc, Matrix.fromBlocks_multiply]
  simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
    Matrix.toBlocks_fromBlocks₂₂]
  set A := Mc.toBlocks₁₁; set B := Mc.toBlocks₁₂; set C := Mc.toBlocks₂₁; set D := Mc.toBlocks₂₂
  set A' := Nc.toBlocks₁₁; set B' := Nc.toBlocks₁₂; set C' := Nc.toBlocks₂₁; set D' := Nc.toBlocks₂₂
  set Y := C' * Ω + D'
  set X := A' * Ω + B'
  have hY : IsUnit Y.det := isUnit_iff_ne_zero.2 hN
  have hYY : Y⁻¹ * Y = 1 := Matrix.nonsing_inv_mul Y hY
  have hYY' : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hY
  have e1 : (C * A' + D * C') * Ω + (C * B' + D * D') = (C * (X * Y⁻¹) + D) * Y := by
    rw [show (C * (X * Y⁻¹) + D) * Y = C * X + D * Y by
      rw [Matrix.add_mul, Matrix.mul_assoc C, Matrix.mul_assoc X, hYY, Matrix.mul_one]]
    simp only [X, Y, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]; abel
  have e2 : (A * A' + B * C') * Ω + (A * B' + B * D') = (A * (X * Y⁻¹) + B) * Y := by
    rw [show (A * (X * Y⁻¹) + B) * Y = A * X + B * Y by
      rw [Matrix.add_mul, Matrix.mul_assoc A, Matrix.mul_assoc X, hYY, Matrix.mul_one]]
    simp only [X, Y, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]; abel
  rw [e1, e2, Matrix.det_mul]
  refine ⟨?_, rfl⟩
  rw [Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc Y, hYY', Matrix.one_mul]

/-- `M` acts on the Siegel space with Igusa's two transformation laws. -/
def Good (M : Mat4) : Prop :=
  ∀ Ω ∈ SiegelH2, spFactor M Ω ≠ 0 ∧ spAct M Ω ∈ SiegelH2 ∧
    thetaSum8 (spAct M Ω) = spFactor M Ω ^ 4 * thetaSum8 Ω ∧
    thetaProd2 (spAct M Ω) = spFactor M Ω ^ 10 * thetaProd2 Ω

theorem spAct_one (Ω : Matrix (Fin 2) (Fin 2) ℂ) : spAct 1 Ω = Ω ∧ spFactor 1 Ω = 1 := by
  have h1 : (1 : Mat4).map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks 1 0 0 1 := by
    rw [Matrix.map_one (Int.cast : ℤ → ℂ) Int.cast_zero Int.cast_one, Matrix.fromBlocks_one]
  simp only [spAct, spFactor, h1, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  simp

theorem good_one : Good 1 := fun Ω hΩ => by
  obtain ⟨h1, h2⟩ := spAct_one Ω
  rw [h1, h2]; exact ⟨one_ne_zero, hΩ, by ring, by ring⟩

theorem good_mul {M N : Mat4} (hM : Good M) (hN : Good N) : Good (M * N) := fun Ω hΩ => by
  obtain ⟨n1, n2, n3, n4⟩ := hN Ω hΩ
  obtain ⟨m1, m2, m3, m4⟩ := hM _ n2
  obtain ⟨c1, c2⟩ := sp_comp M N Ω n1 m1
  rw [c1, c2]
  refine ⟨mul_ne_zero m1 n1, m2, ?_, ?_⟩
  · rw [m3, n3]; ring
  · rw [m4, n4]; ring

/-- The automorphy monoid. -/
def goodSub : Submonoid Mat4 where
  carrier := {M | Good M}
  mul_mem' := good_mul
  one_mem' := good_one

/-- A generator is good once its action, factor and per-characteristic law are known. -/
theorem good_of {G : Mat4} (act : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (f D : Matrix (Fin 2) (Fin 2) ℂ → ℂ) (σ : Char2 → Char2) (N : Char2 → ℤ)
    (hact : ∀ Ω ∈ SiegelH2, spAct G Ω = act Ω) (hf : ∀ Ω ∈ SiegelH2, spFactor G Ω = f Ω)
    (hne : ∀ Ω ∈ SiegelH2, f Ω ≠ 0) (hD4 : ∀ Ω, D Ω ^ 4 = f Ω ^ 4) (hD10 : ∀ Ω, D Ω ^ 10 = f Ω ^ 10)
    (hS : ∀ Ω ∈ SiegelH2, act Ω ∈ SiegelH2)
    (hsq : ∀ Ω ∈ SiegelH2, ∀ m : Char2,
      thetaConst m (act Ω) ^ 2 = -D Ω * cexp (π * I * (N m : ℂ) / 4) * thetaConst (σ m) Ω ^ 2)
    (himg : evenChars.image σ = evenChars)
    (hinj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σ a = σ b → a = b)
    (hev : ∀ m ∈ evenChars, N m % 2 = 0) (hsum : (∑ m ∈ evenChars, N m) % 8 = 0) : Good G := by
  intro Ω hΩ
  have h := assemble (D Ω) σ N (fun m _ => hsq Ω hΩ m) himg hinj hev hsum
  rw [hact Ω hΩ, hf Ω hΩ, ← hD4, ← hD10]
  exact ⟨by rw [← hf Ω hΩ]; exact (hf Ω hΩ).symm ▸ hne Ω hΩ, hS Ω hΩ, h.1, h.2⟩

/-- `spAct` from a block identity `AΩ + B = Z(CΩ + D)`. -/
theorem spAct_eq_of {M : Mat4} {A B C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D) {Ω Z : Matrix (Fin 2) (Fin 2) ℂ}
    (hdet : (C * Ω + D).det ≠ 0) (h : A * Ω + B = Z * (C * Ω + D)) : spAct M Ω = Z := by
  simp only [spAct, hM, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]
  letI := Matrix.invertibleOfIsUnitDet (C * Ω + D) (isUnit_iff_ne_zero.mpr hdet)
  rw [Matrix.mul_inv_eq_iff_eq_mul_of_invertible]; exact h

theorem spFactor_eq_of {M : Mat4} {A B C D : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks A B C D) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    spFactor M Ω = (C * Ω + D).det := by
  simp only [spFactor, hM, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]


/-! ## II.3 The eleven generators -/

/-- Phase of a squared theta constant: `exp(πi/2)·exp(πi a b) = exp(πi(2 + 4ab)/4)`. -/
theorem phase_I (a b : ℤ) (x y : ℝ) (hx : x = (a : ℝ) / 2) (hy : y = (b : ℝ) / 2) :
    I * cexp (4 * π * I * ((x : ℂ) * y)) = cexp (π * I * ((2 + 4 * a * b : ℤ) : ℂ) / 4) := by
  rw [show I * cexp (4 * π * I * ((x : ℂ) * y)) = cexp (π / 2 * I) * cexp (4 * π * I * ((x : ℂ) * y)) by
    rw [Complex.exp_pi_div_two_mul_I], ← Complex.exp_add]
  congr 1; subst hx hy; push_cast; ring

/-! ### Translations -/

theorem Tm_map (S : Matrix (Fin 2) (Fin 2) ℤ) :
    (Tm S).map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks 1 (S.map (Int.cast : ℤ → ℂ)) 0 1 := by
  rw [Tm, Matrix.fromBlocks_map, Matrix.map_one _ Int.cast_zero Int.cast_one, Matrix.map_zero _ Int.cast_zero]

/-- `Ω + S`. -/
def tAct (s00 s01 s11 : ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Ω 0 0 + s00, Ω 0 1 + s01; Ω 0 1 + s01, Ω 1 1 + s11]

theorem spAct_Tm (s00 s01 s11 : ℤ) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spAct (Tm !![s00, s01; s01, s11]) Ω = tAct s00 s01 s11 Ω := by
  refine spAct_eq_of (Tm_map _) (by simp) ?_
  ext i j; fin_cases i <;> fin_cases j <;> simp [tAct, hs]

theorem spFactor_Tm (S : Matrix (Fin 2) (Fin 2) ℤ) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : spFactor (Tm S) Ω = 1 := by
  rw [spFactor_eq_of (Tm_map _)]; simp

def σT (s00 s01 s11 : ℤ) (m : Char2) : Char2 :=
  (![fin2 ((m.1 0 : ℕ) : ℤ), fin2 ((m.1 1 : ℕ) : ℤ)],
   ![fin2 (((m.2 0 : ℕ) : ℤ) + s00 * (((m.1 0 : ℕ) : ℤ) + 1) + s01 * ((m.1 1 : ℕ) : ℤ)),
     fin2 (((m.2 1 : ℕ) : ℤ) + s11 * (((m.1 1 : ℕ) : ℤ) + 1) + s01 * ((m.1 0 : ℕ) : ℤ))])

def NT (s00 s01 s11 : ℤ) (m : Char2) : ℤ :=
  -2 * s00 * (((m.1 0 : ℕ) : ℤ) ^ 2 + 2 * ((m.1 0 : ℕ) : ℤ))
    - 2 * s11 * (((m.1 1 : ℕ) : ℤ) ^ 2 + 2 * ((m.1 1 : ℕ) : ℤ))
    - 4 * s01 * ((m.1 0 : ℕ) : ℤ) * ((m.1 1 : ℕ) : ℤ)

theorem sqT (s00 s01 s11 : ℤ) (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (tAct s00 s01 s11 Ω) ^ 2 =
      -(-1) * cexp (π * I * (NT s00 s01 s11 m : ℂ) / 4) * thetaConst (σT s00 s01 s11 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  rw [thetaConst_eq _ _ (by simp [tAct]), thetaConst_eq _ _ hs]
  simp only [tAct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_trans (α := Ω 0 0) (β := Ω 0 1) (γ := Ω 1 1) s00 s01 s11 rfl rfl rfl, mul_pow]
  rw [th2_sq_red _ _ _ ((m.1 0 : ℕ) : ℤ) ((m.1 1 : ℕ) : ℤ)
    (((m.2 0 : ℕ) : ℤ) + s00 * (((m.1 0 : ℕ) : ℤ) + 1) + s01 * ((m.1 1 : ℕ) : ℤ))
    (((m.2 1 : ℕ) : ℤ) + s11 * (((m.1 1 : ℕ) : ℤ) + 1) + s01 * ((m.1 0 : ℕ) : ℤ))
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  rw [show -(-1 : ℂ) = 1 by ring, one_mul]
  congr 1
  rw [← Complex.exp_nat_mul]
  congr 1
  simp only [NT]
  push_cast
  ring

theorem good_Tm (s00 s01 s11 : ℤ)
    (himg : evenChars.image (σT s00 s01 s11) = evenChars)
    (hinj : ∀ a ∈ evenChars, ∀ b ∈ evenChars, σT s00 s01 s11 a = σT s00 s01 s11 b → a = b)
    (hev : ∀ m ∈ evenChars, NT s00 s01 s11 m % 2 = 0)
    (hsum : (∑ m ∈ evenChars, NT s00 s01 s11 m) % 8 = 0) : Good (Tm !![s00, s01; s01, s11]) :=
  good_of (tAct s00 s01 s11) (fun _ => 1) (fun _ => -1) (σT s00 s01 s11) (NT s00 s01 s11)
    (fun Ω hΩ => spAct_Tm s00 s01 s11 (pdq_of_siegel hΩ).1) (fun Ω _ => spFactor_Tm _ Ω)
    (fun _ _ => one_ne_zero) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun Ω hΩ => siegel_of' ((pdq_of_siegel hΩ).2.add s00 s01 s11))
    (fun Ω hΩ m => sqT s00 s01 s11 m hΩ) himg hinj hev hsum

theorem good_T11 : Good (Tm !![1, 0; 0, 0]) := good_Tm 1 0 0 (by decide) (by decide) (by decide) (by decide)
theorem good_T11' : Good (Tm !![-1, 0; 0, 0]) := good_Tm (-1) 0 0 (by decide) (by decide) (by decide) (by decide)
theorem good_T22 : Good (Tm !![0, 0; 0, 1]) := good_Tm 0 0 1 (by decide) (by decide) (by decide) (by decide)
theorem good_T22' : Good (Tm !![0, 0; 0, -1]) := good_Tm 0 0 (-1) (by decide) (by decide) (by decide) (by decide)
theorem good_Tod : Good (Tm !![0, 1; 1, 0]) := good_Tm 0 1 0 (by decide) (by decide) (by decide) (by decide)
theorem good_Tod' : Good (Tm !![0, -1; -1, 0]) := good_Tm 0 (-1) 0 (by decide) (by decide) (by decide) (by decide)


/-! ### Rotations -/

/-- Reindexing `(n₀, n₁) ↦ (n₀, n₀ + n₁)`: the rotation by `T = [[1,1],[0,1]]`. -/
theorem th2_rotT (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) :
    Th2 (α + 2 * β + γ) (β + γ) γ c0 c1 d0 d1 = Th2 α β γ c0 (c0 + c1) (d0 - d1) d1 := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun n => (n.1, n.1 + n.2), invFun := fun n => (n.1, n.2 - n.1),
      left_inv := fun n => by simp, right_inv := fun n => by simp }
  rw [Th2, Th2]
  conv_rhs => rw [← e.tsum_eq]
  congr 1; funext n
  simp only [term2, e, Equiv.coe_fn_mk]
  congr 1; push_cast; ring

/-- Reindexing `(n₀, n₁) ↦ (n₀, n₁ − n₀)`: the rotation by `T⁻¹`. -/
theorem th2_rotTinv (α β γ : ℂ) (c0 c1 d0 d1 : ℝ) :
    Th2 (α - 2 * β + γ) (β - γ) γ c0 c1 d0 d1 = Th2 α β γ c0 (c1 - c0) (d0 + d1) d1 := by
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun n => (n.1, n.2 - n.1), invFun := fun n => (n.1, n.1 + n.2),
      left_inv := fun n => by simp, right_inv := fun n => by simp }
  rw [Th2, Th2]
  conv_rhs => rw [← e.tsum_eq]
  congr 1; funext n
  simp only [term2, e, Equiv.coe_fn_mk]
  congr 1; push_cast; ring

theorem rot_map (g : SL(2, ℤ)) : (rot g).map (Int.cast : ℤ → ℂ) = Matrix.fromBlocks
    ((g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℂ)) 0 0
    (!![(g : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0;
       -(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0].map (Int.cast : ℤ → ℂ)) := by
  simp only [rot, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.fromBlocks_map, Matrix.map_zero _ Int.cast_zero]

theorem spFactor_rot (g : SL(2, ℤ)) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : spFactor (rot g) Ω = 1 := by
  rw [spFactor_eq_of (rot_map g), Matrix.zero_mul, zero_add, Matrix.det_fin_two]
  have := det_sl g
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  have h : (((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ℂ) = 1 := by
    rw [this]; simp
  push_cast at h ⊢
  linear_combination h

/-- `SΩSᵀ`. -/
def rsAct (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![Ω 1 1, -Ω 0 1; -Ω 0 1, Ω 0 0]
/-- `TΩTᵀ`. -/
def rtAct (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Ω 0 0 + 2 * Ω 0 1 + Ω 1 1, Ω 0 1 + Ω 1 1; Ω 0 1 + Ω 1 1, Ω 1 1]
/-- `T⁻¹ΩT⁻ᵀ`. -/
def rtiAct (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Ω 0 0 - 2 * Ω 0 1 + Ω 1 1, Ω 0 1 - Ω 1 1; Ω 0 1 - Ω 1 1, Ω 1 1]

theorem spAct_rotS {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spAct (rot ModularGroup.S) Ω = rsAct Ω := by
  refine spAct_eq_of (rot_map _) ?_ ?_
  · simp [Matrix.det_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rsAct, hs, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]

theorem spAct_rotT {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spAct (rot ModularGroup.T) Ω = rtAct Ω := by
  refine spAct_eq_of (rot_map _) ?_ ?_
  · simp [Matrix.det_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rtAct, hs, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T] <;> ring

theorem spAct_rotTinv {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hs : Ω 1 0 = Ω 0 1) :
    spAct (rot ModularGroup.T⁻¹) Ω = rtiAct Ω := by
  refine spAct_eq_of (rot_map _) ?_ ?_
  · simp [Matrix.det_fin_two, ModularGroup.coe_T_inv]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rtiAct, hs, Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T_inv] <;> ring

def σRS (m : Char2) : Char2 :=
  (![fin2 (-((m.1 1 : ℕ) : ℤ)), fin2 ((m.1 0 : ℕ) : ℤ)], ![fin2 (-((m.2 1 : ℕ) : ℤ)), fin2 ((m.2 0 : ℕ) : ℤ)])
def σRT (m : Char2) : Char2 :=
  (![fin2 ((m.1 0 : ℕ) : ℤ), fin2 (((m.1 0 : ℕ) : ℤ) + ((m.1 1 : ℕ) : ℤ))],
   ![fin2 (((m.2 0 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ)), fin2 ((m.2 1 : ℕ) : ℤ)])
def σRTi (m : Char2) : Char2 :=
  (![fin2 ((m.1 0 : ℕ) : ℤ), fin2 (((m.1 1 : ℕ) : ℤ) - ((m.1 0 : ℕ) : ℤ))],
   ![fin2 (((m.2 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)), fin2 ((m.2 1 : ℕ) : ℤ)])

theorem exp_zero_quarter : cexp (π * I * ((0 : ℤ) : ℂ) / 4) = 1 := by simp

theorem sqRS (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (rsAct Ω) ^ 2 = -(-1) * cexp (π * I * ((fun _ => (0 : ℤ)) m : ℂ) / 4) *
      thetaConst (σRS m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  rw [exp_zero_quarter, thetaConst_eq _ _ (by simp [rsAct]), thetaConst_eq _ _ hs]
  simp only [rsAct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_neg, th2_swap]
  rw [th2_sq_red _ _ _ (-((m.1 1 : ℕ) : ℤ)) ((m.1 0 : ℕ) : ℤ) (-((m.2 1 : ℕ) : ℤ)) ((m.2 0 : ℕ) : ℤ)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σRS, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  ring

theorem sqRT (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (rtAct Ω) ^ 2 = -(-1) * cexp (π * I * ((fun _ => (0 : ℤ)) m : ℂ) / 4) *
      thetaConst (σRT m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  rw [exp_zero_quarter, thetaConst_eq _ _ (by simp [rtAct]), thetaConst_eq _ _ hs]
  simp only [rtAct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_rotT]
  rw [th2_sq_red _ _ _ ((m.1 0 : ℕ) : ℤ) (((m.1 0 : ℕ) : ℤ) + ((m.1 1 : ℕ) : ℤ))
    (((m.2 0 : ℕ) : ℤ) - ((m.2 1 : ℕ) : ℤ)) ((m.2 1 : ℕ) : ℤ)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σRT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  ring

theorem sqRTi (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (rtiAct Ω) ^ 2 = -(-1) * cexp (π * I * ((fun _ => (0 : ℤ)) m : ℂ) / 4) *
      thetaConst (σRTi m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  rw [exp_zero_quarter, thetaConst_eq _ _ (by simp [rtiAct]), thetaConst_eq _ _ hs]
  simp only [rtiAct, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [th2_rotTinv]
  rw [th2_sq_red _ _ _ ((m.1 0 : ℕ) : ℤ) (((m.1 1 : ℕ) : ℤ) - ((m.1 0 : ℕ) : ℤ))
    (((m.2 0 : ℕ) : ℤ) + ((m.2 1 : ℕ) : ℤ)) ((m.2 1 : ℕ) : ℤ)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σRTi, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast]
  ring

theorem pdq_rs {α β γ : ℂ} (h : PDq α β γ) : PDq γ (-β) α := by
  have := h.swap; simpa [PDq] using this
theorem pdq_rt {α β γ : ℂ} (h : PDq α β γ) : PDq (α + 2 * β + γ) (β + γ) γ := by
  obtain ⟨ha, hd⟩ := h
  have hc : 0 < γ.im := by nlinarith [sq_nonneg β.im]
  refine ⟨?_, ?_⟩ <;> simp <;> nlinarith [sq_nonneg (α.im + β.im), sq_nonneg (β.im + γ.im)]
theorem pdq_rti {α β γ : ℂ} (h : PDq α β γ) : PDq (α - 2 * β + γ) (β - γ) γ := by
  obtain ⟨ha, hd⟩ := h
  have hc : 0 < γ.im := by nlinarith [sq_nonneg β.im]
  refine ⟨?_, ?_⟩ <;> simp <;> nlinarith [sq_nonneg (α.im - β.im), sq_nonneg (β.im - γ.im)]

theorem good_rotS : Good (rot ModularGroup.S) :=
  good_of rsAct (fun _ => 1) (fun _ => -1) σRS (fun _ => 0)
    (fun Ω hΩ => spAct_rotS (pdq_of_siegel hΩ).1) (fun Ω _ => spFactor_rot _ Ω)
    (fun _ _ => one_ne_zero) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun Ω hΩ => siegel_of' (pdq_rs (pdq_of_siegel hΩ).2))
    (fun Ω hΩ m => sqRS m hΩ) (by decide) (by decide) (by decide) (by decide)

theorem good_rotT : Good (rot ModularGroup.T) :=
  good_of rtAct (fun _ => 1) (fun _ => -1) σRT (fun _ => 0)
    (fun Ω hΩ => spAct_rotT (pdq_of_siegel hΩ).1) (fun Ω _ => spFactor_rot _ Ω)
    (fun _ _ => one_ne_zero) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun Ω hΩ => siegel_of' (pdq_rt (pdq_of_siegel hΩ).2))
    (fun Ω hΩ m => sqRT m hΩ) (by decide) (by decide) (by decide) (by decide)

theorem good_rotTinv : Good (rot ModularGroup.T⁻¹) :=
  good_of rtiAct (fun _ => 1) (fun _ => -1) σRTi (fun _ => 0)
    (fun Ω hΩ => spAct_rotTinv (pdq_of_siegel hΩ).1) (fun Ω _ => spFactor_rot _ Ω)
    (fun _ _ => one_ne_zero) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun Ω hΩ => siegel_of' (pdq_rti (pdq_of_siegel hΩ).2))
    (fun Ω hΩ m => sqRTi m hΩ) (by decide) (by decide) (by decide) (by decide)


/-! ### Partial inversions -/

/-- **Partial inversion** in the first coordinate, squared, solved for the inverted side
(cm24-value's `pi0`, i.e. Mathlib's `jacobiTheta₂_functional_equation`). -/
theorem j1_sq {α β γ : ℂ} (h : PDq α β γ) (c0 c1 d0 d1 : ℝ) :
    Th2 (-1 / α) (β / α) (γ - β ^ 2 / α) c0 c1 d0 d1 ^ 2 =
      (-I * α) * cexp (4 * π * I * ((c0 : ℂ) * d0)) * Th2 α β γ d0 c1 (-c0) d1 ^ 2 := by
  have e := pi0 h.1 d0 c1 (-c0) d1 (h.summable _ _ _ _) (h.j1.summable _ _ _ _)
  simp only [neg_neg] at e
  rw [e, mul_pow, mul_pow, cpow_half_sq]
  have ha : -I * α ≠ 0 := mul_ne_zero (by simp) h.ne_zero
  have hx : cexp (4 * π * I * ((c0 : ℂ) * d0)) * cexp (2 * π * I * d0 * ((-c0 : ℝ) : ℂ)) ^ 2 = 1 := by
    rw [sq, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_zero]; congr 1; push_cast; ring
  rw [show ∀ (a e1 e2 X : ℂ), a * e1 * (1 / a * e2 ^ 2 * X) = (a * (1 / a)) * (e1 * e2 ^ 2) * X from
    fun _ _ _ _ => by ring, mul_one_div_cancel ha, hx, one_mul, one_mul]

def j1Act (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 / Ω 0 0, Ω 0 1 / Ω 0 0; Ω 0 1 / Ω 0 0, Ω 1 1 - Ω 0 1 ^ 2 / Ω 0 0]
def j2Act (Ω : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Ω 0 0 - Ω 0 1 ^ 2 / Ω 1 1, Ω 0 1 / Ω 1 1; Ω 0 1 / Ω 1 1, -1 / Ω 1 1]

def σJ1 (m : Char2) : Char2 :=
  (![fin2 ((m.2 0 : ℕ) : ℤ), fin2 ((m.1 1 : ℕ) : ℤ)], ![fin2 (-((m.1 0 : ℕ) : ℤ)), fin2 ((m.2 1 : ℕ) : ℤ)])
def σJ2 (m : Char2) : Char2 :=
  (![fin2 ((m.1 0 : ℕ) : ℤ), fin2 ((m.2 1 : ℕ) : ℤ)], ![fin2 ((m.2 0 : ℕ) : ℤ), fin2 (-((m.1 1 : ℕ) : ℤ))])
def NJ1 (m : Char2) : ℤ := 2 + 4 * ((m.1 0 : ℕ) : ℤ) * ((m.2 0 : ℕ) : ℤ)
def NJ2 (m : Char2) : ℤ := 2 + 4 * ((m.1 1 : ℕ) : ℤ) * ((m.2 1 : ℕ) : ℤ)

theorem sqJ1 (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (j1Act Ω) ^ 2 = -(Ω 0 0) * cexp (π * I * (NJ1 m : ℂ) / 4) * thetaConst (σJ1 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  rw [thetaConst_eq _ _ (by simp [j1Act]), thetaConst_eq _ _ hs]
  simp only [j1Act, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  rw [j1_sq hpd]
  rw [th2_sq_red _ _ _ ((m.2 0 : ℕ) : ℤ) ((m.1 1 : ℕ) : ℤ) (-((m.1 0 : ℕ) : ℤ)) ((m.2 1 : ℕ) : ℤ)
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σJ1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast, NJ1]
  rw [← phase_I ((m.1 0 : ℕ) : ℤ) ((m.2 0 : ℕ) : ℤ) (((m.1 0 : ℕ) : ℝ) / 2) (((m.2 0 : ℕ) : ℝ) / 2)
    (by push_cast; ring) (by push_cast; ring)]
  ring

theorem sqJ2 (m : Char2) {Ω : Matrix (Fin 2) (Fin 2) ℂ} (hΩ : Ω ∈ SiegelH2) :
    thetaConst m (j2Act Ω) ^ 2 = -(Ω 1 1) * cexp (π * I * (NJ2 m : ℂ) / 4) * thetaConst (σJ2 m) Ω ^ 2 := by
  obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
  rw [thetaConst_eq _ _ (by simp [j2Act]), thetaConst_eq _ _ hs]
  simp only [j2Act, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
  conv_lhs => rw [th2_swap, j1_sq hpd.swap, th2_swap]
  rw [th2_sq_red _ _ _ ((m.1 0 : ℕ) : ℤ) ((m.2 1 : ℕ) : ℤ) ((m.2 0 : ℕ) : ℤ) (-((m.1 1 : ℕ) : ℤ))
    (by push_cast; ring) (by push_cast; ring) (by push_cast; ring) (by push_cast; ring)]
  simp only [σJ2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, fin2_cast, NJ2]
  rw [← phase_I ((m.1 1 : ℕ) : ℤ) ((m.2 1 : ℕ) : ℤ) (((m.1 1 : ℕ) : ℝ) / 2) (((m.2 1 : ℕ) : ℝ) / 2)
    (by push_cast; ring) (by push_cast; ring)]
  ring

theorem iota1_S_map : (iota1 ModularGroup.S).map (Int.cast : ℤ → ℂ) =
    Matrix.fromBlocks !![0, 0; 0, 1] !![-1, 0; 0, 0] !![1, 0; 0, 0] !![0, 0; 0, 1] := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota1, ModularGroup.coe_S]

theorem iota2_S_map : (iota2 ModularGroup.S).map (Int.cast : ℤ → ℂ) =
    Matrix.fromBlocks !![1, 0; 0, 0] !![0, 0; 0, -1] !![0, 0; 0, 1] !![1, 0; 0, 0] := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota2, ModularGroup.coe_S]

theorem good_J1 : Good (iota1 ModularGroup.S) := by
  refine good_of j1Act (fun Ω => Ω 0 0) (fun Ω => Ω 0 0) σJ1 NJ1 (fun Ω hΩ => ?_) (fun Ω hΩ => ?_)
    (fun Ω hΩ => (pdq_of_siegel hΩ).2.ne_zero) (fun _ => rfl) (fun _ => rfl)
    (fun Ω hΩ => siegel_of' (pdq_of_siegel hΩ).2.j1) (fun Ω hΩ m => sqJ1 m hΩ)
    (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
    have h0 := hpd.ne_zero
    refine spAct_eq_of iota1_S_map ?_ ?_
    · rw [Matrix.det_fin_two]; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
      simpa [hs] using h0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp [j1Act, hs] <;> field_simp <;> ring
  · rw [spFactor_eq_of iota1_S_map, Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp

theorem good_J2 : Good (iota2 ModularGroup.S) := by
  refine good_of j2Act (fun Ω => Ω 1 1) (fun Ω => Ω 1 1) σJ2 NJ2 (fun Ω hΩ => ?_) (fun Ω hΩ => ?_)
    (fun Ω hΩ => (pdq_of_siegel hΩ).2.swap.ne_zero) (fun _ => rfl) (fun _ => rfl)
    (fun Ω hΩ => siegel_of' (pdq_of_siegel hΩ).2.swap.j1.swap) (fun Ω hΩ m => sqJ2 m hΩ)
    (by decide) (by decide) (by decide) (by decide)
  · obtain ⟨hs, hpd⟩ := pdq_of_siegel hΩ
    have h0 := hpd.swap.ne_zero
    refine spAct_eq_of iota2_S_map ?_ ?_
    · rw [Matrix.det_fin_two]; simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
      simpa [hs] using h0
    · ext i j; fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two] <;>
        simp [j2Act, hs] <;> field_simp <;> ring
  · rw [spFactor_eq_of iota2_S_map, Matrix.det_fin_two]
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two]
    simp

/-! ## II.4 Every element of `Sp₄(ℤ)` -/

theorem iota1_T : iota1 ModularGroup.T = Tm !![1, 0; 0, 0] := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota1, Tm, ModularGroup.coe_T]
theorem iota1_Tinv : iota1 ModularGroup.T⁻¹ = Tm !![-1, 0; 0, 0] := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota1, Tm, ModularGroup.coe_T_inv]
theorem iota2_T : iota2 ModularGroup.T = Tm !![0, 0; 0, 1] := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota2, Tm, ModularGroup.coe_T]
theorem iota2_Tinv : iota2 ModularGroup.T⁻¹ = Tm !![0, 0; 0, -1] := by
  ext i j; rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [iota2, Tm, ModularGroup.coe_T_inv]

theorem gens_good : ∀ M ∈ gens, Good M := by
  intro M hM
  simp only [gens, Set.mem_insert_iff, Set.mem_singleton_iff] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact good_J1
  · rw [iota1_T]; exact good_T11
  · rw [iota1_Tinv]; exact good_T11'
  · exact good_J2
  · rw [iota2_T]; exact good_T22
  · rw [iota2_Tinv]; exact good_T22'
  · exact good_rotS
  · exact good_rotT
  · exact good_rotTinv
  · exact good_Tod
  · exact good_Tod'

/-- **Igusa's two transformation laws on all of `Sp₄(ℤ)`.** -/
theorem good_sp {M : Mat4} (hM : M ∈ Matrix.symplecticGroup (Fin 2) ℤ) : Good M :=
  (Submonoid.closure_le (S := goodSub).2 gens_good) (sp_mem_closure hM)

end Theta

/-! ## II.5 The two open hypotheses -/

/-- **`igusaPsi4` proved** (`ψ₄` is a Siegel modular form of weight 4 for `Sp₄(ℤ)`, in its theta
expression). -/
theorem igusaPsi4_proof : HDec.QMSplit.Theta.IgusaPsi4 := by
  intro M hM Ω hΩ
  obtain ⟨-, -, h, -⟩ := good_sp hM Ω hΩ
  simp only [HDec.QMSplit.Theta.psi4]; rw [h]; ring

/-- **`igusaChi10` proved** (`χ₁₀` is a Siegel modular form of weight 10 for `Sp₄(ℤ)`, in its theta
expression). -/
theorem igusaChi10_proof : HDec.QMSplit.Theta.IgusaChi10 := by
  intro M hM Ω hΩ
  obtain ⟨-, -, -, h⟩ := good_sp hM Ω hΩ
  simp only [HDec.QMSplit.Theta.chi10]; rw [h]; ring

/-- pkg-I1's `ThetaModularity` (row H-2), proved. -/
theorem thetaModularity_proof : HDec.PkgI1.ThetaModularity :=
  HDec.QMSplit.Theta.thetaModularity_of igusaPsi4_proof igusaChi10_proof

end GapTheta

#print axioms GapTheta.igusaPsi4_proof
#print axioms GapTheta.igusaChi10_proof
#print axioms GapTheta.thetaModularity_proof
