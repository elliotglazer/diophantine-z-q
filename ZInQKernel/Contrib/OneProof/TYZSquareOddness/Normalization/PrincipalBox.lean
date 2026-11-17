import ZInQKernel.Contrib.OneProof.TYZSquareOddness.ActualAdelicLattice

/-!
# Exact principal-box transport (normalization prerequisites only)

These lemmas use the literal rational Hamilton Hurwitz lattice, the actual
Hamilton tensor equivalence and the actual finite-adelic Hurwitz carrier.
No translated-box reconstruction, global normalization or hP23 closure is
asserted here. In particular, the nonzero rational generator is a unit of the
rational division ring, not thereby a unit of the integral Hurwitz order.
-/

open scoped Quaternion TensorProduct
open TYZSquareOddness.ScalarFiniteAdeles
open IsDedekindDomain NumberField
set_option autoImplicit false

namespace TYZSquareOddness.Normalization

/-- Nonzero rational Hamilton generators are genuine division-ring units. -/
noncomputable def rationalGeneratorUnit (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) : ℍ[ℚ]ˣ :=
  Units.mk0 gamma hgamma

@[simp] lemma rationalGeneratorUnit_val (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) :
    (rationalGeneratorUnit gamma hgamma : ℍ[ℚ]) = gamma := rfl

/-- The actual diagonal unit: no inverse operation is assumed on ℍ[AQ]. -/
noncomputable def diagonalGeneratorUnit (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) : ℍ[AQ]ˣ :=
  Units.map qι.toMonoidHom (rationalGeneratorUnit gamma hgamma)

@[simp] lemma diagonalGeneratorUnit_val (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) :
    (diagonalGeneratorUnit gamma hgamma : ℍ[AQ]) = qι gamma := rfl

@[simp] lemma diagonalGeneratorUnit_inv_val (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) :
    (((diagonalGeneratorUnit gamma hgamma)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) = qι gamma⁻¹ := rfl

/-- The mapped additive box of an actual rational lattice. -/
noncomputable def transportedBox (L : Submodule ℤ ℍ[ℚ]) : AddSubgroup ℍ[AQ] :=
  (AdelicLattice.finiteAdeleBox L).map hamiltonAdeleTensorEquiv.toAddMonoidHom

lemma transportedBox_hurwitz : transportedBox hurwitzLattice = hurwitzHatAddSubgroup := by
  apply SetLike.coe_injective
  exact tensor_box_image_eq_hurwitzHat

/-- Exact RIGHT-principal lattice gives the corresponding LEFT adelic box
translate. This algebraic prerequisite does not reconstruct I(g)'s box. -/
theorem transportedBox_principal (L : Submodule ℤ ℍ[ℚ]) (gamma : ℍ[ℚ])
    (hL : ∀ q : ℍ[ℚ], q ∈ L ↔ ∃ a : ℍ[ℚ], a ∈ hurwitzLattice ∧ q = gamma * a) :
    transportedBox L = hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (qι gamma)) := by
  let T := hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (qι gamma))
  have forward : ∀ t ∈ AdelicLattice.finiteAdeleBox L,
      hamiltonAdeleTensorEquiv t ∈ T := by
    intro t ht
    unfold AdelicLattice.finiteAdeleBox at ht
    refine AddSubgroup.closure_induction
      (p := fun t _ => hamiltonAdeleTensorEquiv t ∈ T) ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨q, hq, a, ha, rfl⟩
      obtain ⟨z, hz, rfl⟩ := (hL q).mp hq
      refine ⟨a • qι z, hurwitzHat_integral_smul
        (ScalarFiniteAdeles.mem_integralAdeles.mpr ha) (qι_hurwitz_mem_hat hz), ?_⟩
      change qι gamma * (a • qι z) = hamiltonAdeleTensorEquiv ((gamma * z) ⊗ₜ[ℚ] a)
      rw [hamiltonAdeleTensorEquiv_tmul, map_mul, Algebra.mul_smul_comm]
    · simpa using T.zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using T.add_mem hx hy
    · intro x _ hx
      simpa only [map_neg] using T.neg_mem hx
  have reverse : ∀ t ∈ AdelicLattice.finiteAdeleBox hurwitzLattice,
      (gamma ⊗ₜ[ℚ] (1 : AQ)) * t ∈ AdelicLattice.finiteAdeleBox L := by
    intro t ht
    unfold AdelicLattice.finiteAdeleBox at ht
    refine AddSubgroup.closure_induction
      (p := fun t _ => (gamma ⊗ₜ[ℚ] (1 : AQ)) * t ∈ AdelicLattice.finiteAdeleBox L)
      ?_ ?_ ?_ ?_ ht
    · rintro _ ⟨q, hq, a, ha, rfl⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact AddSubgroup.subset_closure ⟨gamma * q, (hL _).mpr ⟨q, hq, rfl⟩, a, ha, rfl⟩
    · simpa only [mul_zero] using (AdelicLattice.finiteAdeleBox L).zero_mem
    · intro x y _ _ hx hy
      simpa only [mul_add] using (AdelicLattice.finiteAdeleBox L).add_mem hx hy
    · intro x _ hx
      convert (AdelicLattice.finiteAdeleBox L).neg_mem hx using 1
      exact mul_neg (gamma ⊗ₜ[ℚ] (1 : AQ)) x
  apply le_antisymm
  · rintro x ⟨t, ht, rfl⟩
    exact forward t ht
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hat_mem_tensor_box_image hy
    refine ⟨(gamma ⊗ₜ[ℚ] (1 : AQ)) * t, reverse t ht, ?_⟩
    change hamiltonAdeleTensorEquiv ((gamma ⊗ₜ[ℚ] (1 : AQ)) * t) =
      qι gamma * hamiltonAdeleTensorEquiv t
    rw [map_mul, hamiltonAdeleTensorEquiv_tmul_one]

/-- Every actual I(g) has a nonzero rational generator and its exact principal
box transport, with no FG or full-span caller hypotheses. Still a prerequisite:
it does not equate this box with the translated adelic Hurwitz lattice. -/
theorem actual_principal_box (g : ℍ[AQ]ˣ) :
    ∃ gamma : ℍ[ℚ], gamma ∈ hurwitzIntersection g ∧ gamma ≠ 0 ∧
      transportedBox (hurwitzIntersection g) =
        hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (qι gamma)) := by
  obtain ⟨gamma, hmem, hne, hprincipal⟩ := hurwitzIntersection_principal g
  exact ⟨gamma, hmem, hne, transportedBox_principal _ gamma hprincipal⟩

end TYZSquareOddness.Normalization
