import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Reconstruction.Algebraic
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.ActualAdelicLattice

/-! Exact reconstruction in the ACTUAL Hamilton finite-adele algebra.
All FG/full-span inputs are closed all-unit theorems, not caller hypotheses.
Translation is ordered LEFT multiplication by the given actual unit.
-/
open scoped Quaternion TensorProduct
open IsDedekindDomain NumberField
open TYZSquareOddness.ScalarFiniteAdeles
noncomputable section
namespace TYZSquareOddness
open AdelicLattice.Reconstruction

/-- The existing algebraic box transported through the checked actual Hamilton equivalence. -/
def hamiltonBox (L : Submodule ℤ ℍ[ℚ]) : AddSubgroup ℍ[AQ] :=
  (AdelicLattice.finiteAdeleBox L).map hamiltonAdeleTensorEquiv.toAddMonoidHom

/-- The frozen actual inverse-left intersection is precisely the tensor LEFT-translate slice. -/
theorem hurwitzIntersection_eq_ofFiniteIdele (g : ℍ[AQ]ˣ) :
    hurwitzIntersection g = AdelicLattice.ofFiniteIdele hurwitzLattice
      (hamiltonAdeleUnitEquiv.symm g) := by
  ext q
  rw [mem_hurwitzIntersection_iff, s3_mem_ofFiniteIdele_iff_inv_mul_mem,
    tensor_box_mem_iff_hurwitzHat, map_mul, hamiltonAdeleTensorEquiv_tmul_one]
  have hi : hamiltonAdeleTensorEquiv
      (((hamiltonAdeleUnitEquiv.symm g)⁻¹ : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) : ℍ[ℚ] ⊗[ℚ] AQ) =
      ((g⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) := by
    change (hamiltonAdeleUnitEquiv ((hamiltonAdeleUnitEquiv.symm g)⁻¹) : ℍ[AQ]) = _
    simp
  rw [hi]

theorem actual_tensor_box_reconstruction (g : ℍ[AQ]ˣ) :
    AdelicLattice.finiteAdeleBox (hurwitzIntersection g) =
      (AdelicLattice.finiteAdeleBox hurwitzLattice).map
        (AddMonoidHom.mulLeft ((hamiltonAdeleUnitEquiv.symm g : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) :
          ℍ[ℚ] ⊗[ℚ] AQ)) := by
  letI : Submodule.IsLattice ℚ hurwitzLattice :=
    ⟨hurwitzLattice_fg, hurwitzLattice_span_rat⟩
  letI : Submodule.IsLattice ℚ
      (AdelicLattice.ofFiniteIdele hurwitzLattice (hamiltonAdeleUnitEquiv.symm g)) := by
    rw [← hurwitzIntersection_eq_ofFiniteIdele]
    exact ⟨hurwitzIntersection_fg g, hurwitzIntersection_span_rat g⟩
  rw [hurwitzIntersection_eq_ofFiniteIdele]
  exact s3_finiteAdeleBox_ofFiniteIdele scalar_strong_approximation hurwitzLattice _

/-- CLOSED exact translated-box reconstruction: box(I(g)) = g * Hhat.
No density, compactness, open-box, FG, or desired reconstruction caller premise. -/
theorem hamiltonBox_hurwitzIntersection (g : ℍ[AQ]ˣ) :
    hamiltonBox (hurwitzIntersection g) =
      hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (g : ℍ[AQ])) := by
  have hH : hamiltonBox hurwitzLattice = hurwitzHatAddSubgroup := by
    apply SetLike.coe_injective
    exact tensor_box_image_eq_hurwitzHat
  have hf : hamiltonAdeleTensorEquiv.toAddMonoidHom.comp
      (AddMonoidHom.mulLeft ((hamiltonAdeleUnitEquiv.symm g : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) :
        ℍ[ℚ] ⊗[ℚ] AQ)) =
      (AddMonoidHom.mulLeft (g : ℍ[AQ])).comp hamiltonAdeleTensorEquiv.toAddMonoidHom := by
    apply AddMonoidHom.ext
    intro x
    change hamiltonAdeleTensorEquiv (_ * x) = (g : ℍ[AQ]) * hamiltonAdeleTensorEquiv x
    rw [map_mul]
    have hg : hamiltonAdeleTensorEquiv
        ((hamiltonAdeleUnitEquiv.symm g : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) : ℍ[ℚ] ⊗[ℚ] AQ) = (g : ℍ[AQ]) := by
      change (hamiltonAdeleUnitEquiv (hamiltonAdeleUnitEquiv.symm g) : ℍ[AQ]) = _
      rw [MulEquiv.apply_symm_apply]
    rw [hg]
  unfold hamiltonBox
  rw [actual_tensor_box_reconstruction, AddSubgroup.map_map, hf, ← AddSubgroup.map_map]
  change (hamiltonBox hurwitzLattice).map _ = _
  rw [hH]

end TYZSquareOddness
