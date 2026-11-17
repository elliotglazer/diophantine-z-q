import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Vendor.AnthropicFLT.BoxDefinitions

/-!
# Generic box multiplication and both-inverse stabilizer criterion

Extracted from the `StabBox` section (L272–358) of
`P2M/Sol/S_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits.lean`
at canonical FLT revision `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Original blob `dee63ff10cb0a55b3b28896ce1fc56da1f5ef6a8`.
LICENSE/NOTICE retained. Only namespace/name/type-alias adaptations; no order,
FG, maximality or ramification caller hypothesis is added.
-/

open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField
set_option autoImplicit false

namespace TYZSquareOddness.AdelicLattice

private abbrev AF := FiniteAdeleRing (𝓞 ℚ) ℚ

variable {D : Type*} [Ring D] [Algebra ℚ D]

lemma one_integral (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : AF) v ∈ v.adicCompletionIntegers ℚ := by
  have h : (1 : AF) v = 1 := rfl
  rw [h]
  exact one_mem _

lemma tmul_one_mem_box (Λ : Submodule ℤ D) {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : AF) ∈ finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, 1, one_integral, rfl⟩

private lemma gen_mul_mem_box (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {z : D} (hz : z ∈ Λ) {a : AF}
    (ha : ∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ)
    {y : D ⊗[ℚ] AF} (hy : y ∈ finiteAdeleBox Λ) :
    (z ⊗ₜ[ℚ] a) * y ∈ finiteAdeleBox Λ := by
  unfold finiteAdeleBox at hy ⊢
  refine AddSubgroup.closure_induction (p := fun y _ => (z ⊗ₜ[ℚ] a) * y ∈ _) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z', hz', a', ha', rfl⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul]
    refine AddSubgroup.subset_closure ⟨z * z', hmul z z' hz hz', a * a', fun v => ?_, rfl⟩
    have h : (a * a') v = a v * a' v := rfl
    rw [h]
    exact mul_mem (ha v) (ha' v)
  · show z ⊗ₜ[ℚ] a * 0 ∈ _
    rw [mul_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    rw [mul_add]
    exact add_mem hx hy
  · intro x _ hx
    convert neg_mem hx using 1
    exact mul_neg (z ⊗ₜ[ℚ] a) x

lemma box_mul_mem (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] AF} (hx : x ∈ finiteAdeleBox Λ) (hy : y ∈ finiteAdeleBox Λ) :
    x * y ∈ finiteAdeleBox Λ := by
  have hy' := hy
  unfold finiteAdeleBox at hx
  refine AddSubgroup.closure_induction (p := fun x _ => x * y ∈ finiteAdeleBox Λ) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨z, hz, a, ha, rfl⟩
    exact gen_mul_mem_box Λ hmul hz ha hy'
  · show 0 * y ∈ _
    rw [zero_mul]
    exact zero_mem _
  · intro x₁ x₂ _ _ h₁ h₂
    rw [add_mul]
    exact add_mem h₁ h₂
  · intro x₁ _ h₁
    convert neg_mem h₁ using 1
    exact neg_mul x₁ y

lemma val_mem_box_of_mem_stab (Λ : Submodule ℤ D) (h1 : (1 : D) ∈ Λ)
    {u : (D ⊗[ℚ] AF)ˣ} (hu : u ∈ finiteIdeleStabilizer Λ) :
    (u : D ⊗[ℚ] AF) ∈ finiteAdeleBox Λ := by
  rw [mem_finiteIdeleStabilizer_iff] at hu
  have h1box : (1 : D ⊗[ℚ] AF) ∈ (finiteAdeleBox Λ : Set _) := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_one_mem_box Λ h1
  have := Set.smul_mem_smul_set (a := u) h1box
  rw [hu, Units.smul_def, smul_eq_mul, mul_one] at this
  exact this

lemma mem_stab_of_mem_box (Λ : Submodule ℤ D)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    (u : (D ⊗[ℚ] AF)ˣ) (hu : (u : D ⊗[ℚ] AF) ∈ finiteAdeleBox Λ)
    (hu' : ((u⁻¹ : (D ⊗[ℚ] AF)ˣ) : D ⊗[ℚ] AF) ∈ finiteAdeleBox Λ) :
    u ∈ finiteIdeleStabilizer Λ := by
  rw [mem_finiteIdeleStabilizer_iff]
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact box_mul_mem Λ hmul hu hs
  · intro ht
    refine ⟨((u⁻¹ : (D ⊗[ℚ] AF)ˣ) : D ⊗[ℚ] AF) * t, box_mul_mem Λ hmul hu' ht, ?_⟩
    show (u : D ⊗[ℚ] AF) * (((u⁻¹ : (D ⊗[ℚ] AF)ˣ) : D ⊗[ℚ] AF) * t) = t
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- For genuine tensor units, stabilizing the integral box is equivalent to
membership of BOTH the unit and its actual inverse in that same box. -/
theorem mem_stab_iff_both_box (Λ : Submodule ℤ D) (h1 : (1 : D) ∈ Λ)
    (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ) (u : (D ⊗[ℚ] AF)ˣ) :
    u ∈ finiteIdeleStabilizer Λ ↔
      (u : D ⊗[ℚ] AF) ∈ finiteAdeleBox Λ ∧
        ((u⁻¹ : (D ⊗[ℚ] AF)ˣ) : D ⊗[ℚ] AF) ∈ finiteAdeleBox Λ := by
  constructor
  · intro hu
    exact ⟨val_mem_box_of_mem_stab Λ h1 hu,
      val_mem_box_of_mem_stab Λ h1 (Subgroup.inv_mem _ hu)⟩
  · rintro ⟨hu, hu'⟩
    exact mem_stab_of_mem_box Λ hmul u hu hu'

end TYZSquareOddness.AdelicLattice
