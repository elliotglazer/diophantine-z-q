import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Definitions.Def_QuaternionAlgebra_BaseChange
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.HurwitzRing
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Vendor.AnthropicFLT.BoxDefinitions

/-!
# The actual Hamilton algebra, rational diagonal and finite-adèle tensor transport

The unique generic BaseChange dependency is the owning W28 source from upstream PR130,
`1c1eeabb26315bc9065a2829b08067befbc454a8`, originally FLT `6e837e75355538c7f80bab5b956861e86c4eacc2`.
No second BaseChange implementation or ambient finite-adèle field instance is introduced.
The diagonal map has the exact four coordinate algebra maps of the original fork `qι`.
-/

open scoped Quaternion TensorProduct
set_option autoImplicit false

namespace TYZSquareOddness

/-- Canonical coordinatewise rational diagonal, obtained from the existing W28 generic map. -/
noncomputable def qι : ℍ[ℚ] →ₐ[ℚ] ℍ[AQ] :=
  QuaternionAlgebra.mapOfAlgebraMapEq (R := ℚ) (S := AQ)
    (c₁ := (-1 : ℚ)) (c₂ := (0 : ℚ)) (c₃ := (-1 : ℚ))
    (d₁ := (-1 : AQ)) (d₂ := (0 : AQ)) (d₃ := (-1 : AQ))
    (by simp) (by simp) (by simp)

@[simp] theorem qι_apply (q : ℍ[ℚ]) :
    qι q = ⟨algebraMap ℚ AQ q.re, algebraMap ℚ AQ q.imI,
      algebraMap ℚ AQ q.imJ, algebraMap ℚ AQ q.imK⟩ := by
  exact QuaternionAlgebra.mapOfAlgebraMapEq_apply _ _ _ q

noncomputable def hamiltonAdeleTensorEquiv : (ℍ[ℚ] ⊗[ℚ] AQ) ≃ₐ[ℚ] ℍ[AQ] :=
  QuaternionAlgebra.baseChangeRight (R := ℚ) (S := AQ)
    (c₁ := (-1 : ℚ)) (c₂ := (0 : ℚ)) (c₃ := (-1 : ℚ))
    (d₁ := (-1 : AQ)) (d₂ := (0 : AQ)) (d₃ := (-1 : AQ))
    (by simp) (by simp) (by simp)

lemma hamiltonAdeleTensorEquiv_tmul (q : ℍ[ℚ]) (a : AQ) :
    hamiltonAdeleTensorEquiv (q ⊗ₜ[ℚ] a) = a • qι q := by
  rw [hamiltonAdeleTensorEquiv, QuaternionAlgebra.baseChangeRight_tmul, qι_apply]
  rfl

lemma hamiltonAdeleTensorEquiv_tmul_one (q : ℍ[ℚ]) :
    hamiltonAdeleTensorEquiv (q ⊗ₜ[ℚ] (1 : AQ)) = qι q := by
  simpa using hamiltonAdeleTensorEquiv_tmul q (1 : AQ)

lemma hamiltonAdeleTensorEquiv_one_tmul (a : AQ) :
    hamiltonAdeleTensorEquiv ((1 : ℍ[ℚ]) ⊗ₜ[ℚ] a) = algebraMap AQ ℍ[AQ] a := by
  exact QuaternionAlgebra.baseChangeRight_one_tmul _ _ _ a

/-- All actual units, not a chosen model of invertible finite-adèle quaternions. -/
noncomputable def hamiltonAdeleUnitEquiv : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ ≃* ℍ[AQ]ˣ :=
  Units.mapEquiv hamiltonAdeleTensorEquiv.toMulEquiv

@[simp] lemma hamiltonAdeleUnitEquiv_val (u : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) :
    (hamiltonAdeleUnitEquiv u : ℍ[AQ]) = hamiltonAdeleTensorEquiv (u : ℍ[ℚ] ⊗[ℚ] AQ) := rfl

@[simp] lemma hamiltonAdeleUnitEquiv_inv_val (u : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) :
    ((hamiltonAdeleUnitEquiv u)⁻¹ : ℍ[AQ]ˣ) =
      hamiltonAdeleUnitEquiv (u⁻¹ : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) := by
  exact (map_inv hamiltonAdeleUnitEquiv u).symm

lemma hamiltonAdeleUnitEquiv_inv_coe (u : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) :
    (((hamiltonAdeleUnitEquiv u)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) =
      hamiltonAdeleTensorEquiv ((u⁻¹ : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) : ℍ[ℚ] ⊗[ℚ] AQ) := by
  rw [hamiltonAdeleUnitEquiv_inv_val, hamiltonAdeleUnitEquiv_val]

end TYZSquareOddness
