import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Tactic

set_option linter.all false
open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

namespace GapTheta

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

end GapTheta
