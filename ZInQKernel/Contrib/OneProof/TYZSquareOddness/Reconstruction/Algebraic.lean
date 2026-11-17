import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Reconstruction.Coordinates
/-! Exact canonical source extraction: see Coordinates.lean and complete notices alongside.
Ranges 657–673, 741–751, 797–829. The generic FG construction is deliberately omitted.
The generic lattice interface below is instantiated by CLOSED actual all-unit FG/span proofs.
-/
open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField
noncomputable section
namespace TYZSquareOddness.AdelicLattice.Reconstruction
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem scalar_strong_approximation (a : 𝔸f) :
    ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat := by
  obtain ⟨q, hq⟩ := ScalarFiniteAdeles.exists_sub_diagonal_integral a
  exact ⟨q, hq⟩
theorem s3_box_mul_one_tmul_mem (Λ : Submodule ℤ K) {t : K ⊗[ℚ] 𝔸f}
    (ht : t ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ) {c : 𝔸f} (hc : c ∈ s1_Zhat) :
    t * ((1 : K) ⊗ₜ[ℚ] c) ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ := by
  refine AddSubgroup.closure_induction (p := fun t _ => t * ((1 : K) ⊗ₜ[ℚ] c) ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ)
    ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨z, hz, a, ha, rfl⟩
    show z ⊗ₜ[ℚ] a * ((1 : K) ⊗ₜ[ℚ] c) ∈ _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact s1_tmul_mem_finiteAdeleBox hz (mul_mem ha hc)
  · show (0 : K ⊗[ℚ] 𝔸f) * ((1 : K) ⊗ₜ[ℚ] c) ∈ _
    rw [zero_mul]; exact zero_mem _
  · intro x y _ _ hx hy
    show (x + y) * ((1 : K) ⊗ₜ[ℚ] c) ∈ _
    rw [add_mul]; exact add_mem hx hy
  · intro x _ hx
    convert neg_mem hx using 1
    exact neg_mul x _
theorem s3_mem_ofFiniteIdele_iff_inv_mul_mem (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) (z : K) :
    z ∈ TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g ↔ ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f))
      ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ := by
  rw [TYZSquareOddness.AdelicLattice.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    rw [AddMonoidHom.coe_mulLeft] at hyz
    rw [← hyz, ← mul_assoc, Units.inv_mul, one_mul]
    exact hy
  · intro h
    exact ⟨_, h, by rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]⟩
theorem s3_finiteAdeleBox_ofFiniteIdele
    (hSA : ∀ a : 𝔸f, ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat)
    (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (g : (K ⊗[ℚ] 𝔸f)ˣ) [Submodule.IsLattice ℚ (TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g)] :
    TYZSquareOddness.AdelicLattice.finiteAdeleBox (TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g)
      = (TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) := by
  classical
  -- Lattice premise is an interface here, supplied by actual all-g proofs at application.
  have hle : TYZSquareOddness.AdelicLattice.finiteAdeleBox (TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g)
      ≤ (TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) := by
    rw [s1_finiteAdeleBox_le_iff]
    intro w hw a ha
    rw [s3_mem_ofFiniteIdele_iff_inv_mul_mem] at hw
    refine ⟨((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (w ⊗ₜ[ℚ] (1 : 𝔸f)) * ((1 : K) ⊗ₜ[ℚ] a),
      s3_box_mul_one_tmul_mem Λ hw ha, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine le_antisymm hle ?_
  obtain ⟨n, bJ, hbJ⟩ := s1_exists_basis_of_isLattice (TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g)
  rintro y ⟨u, hu, rfl⟩
  obtain ⟨x, hx⟩ := s3_exists_sub_tmul_one_mem_finiteAdeleBox hSA bJ ((AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) u)
  rw [hbJ] at hx
  have hgu : (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) u
      ∈ (TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) :=
    AddSubgroup.mem_map_of_mem _ hu
  have hx1 : x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ (TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f)) := by
    have := sub_mem hgu (hle hx)
    rwa [sub_sub_cancel] at this
  have hxΦ : x ∈ TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g := (TYZSquareOddness.AdelicLattice.mem_ofFiniteIdele_iff Λ g x).mpr hx1
  have hx2 : x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox (TYZSquareOddness.AdelicLattice.ofFiniteIdele Λ g) :=
    s1_tmul_mem_finiteAdeleBox hxΦ (one_mem _)
  have := add_mem hx hx2
  rwa [sub_add_cancel] at this
end TYZSquareOddness.AdelicLattice.Reconstruction
