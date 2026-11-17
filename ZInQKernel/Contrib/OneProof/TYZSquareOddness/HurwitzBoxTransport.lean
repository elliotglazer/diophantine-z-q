import ZInQKernel.Contrib.OneProof.TYZSquareOddness.HurwitzHat
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Vendor.AnthropicFLT.BoxStabilizer

/-!
# Tensor-box transport to the literal finite-adelic Hurwitz set

The image is proved against the ACTUAL `H29Split.hurwitzHat` coefficient set.
No topological completion, representative model, or substitute order is used.
-/

open scoped Quaternion TensorProduct
open TYZSquareOddness.ScalarFiniteAdeles
open IsDedekindDomain NumberField
set_option autoImplicit false

namespace TYZSquareOddness

private abbrev Zhat := ScalarFiniteAdeles.integralAdeles

lemma qι_hurwitz_mem_hat {q : ℍ[ℚ]} (hq : q ∈ hurwitzLattice) : qι q ∈ hurwitzHatAddSubgroup := by
  obtain ⟨a, b, c, d, e, rfl⟩ := hq
  refine ⟨(a : AQ), (b : AQ), (c : AQ), (d : AQ), (e : AQ),
    intCast_mem_Zhat a, intCast_mem_Zhat b, intCast_mem_Zhat c,
    intCast_mem_Zhat d, intCast_mem_Zhat e, ?_⟩
  have half (z : ℤ) : algebraMap ℚ AQ ((z : ℚ) / 2) =
      (z : AQ) * algebraMap ℚ AQ (1 / 2) := by
    calc
      algebraMap ℚ AQ ((z : ℚ) / 2) =
          algebraMap ℚ AQ ((z : ℚ) * (1 / 2)) := by congr 1; ring
      _ = algebraMap ℚ AQ (z : ℚ) * algebraMap ℚ AQ (1 / 2) := by rw [map_mul]
      _ = (z : AQ) * algebraMap ℚ AQ (1 / 2) := by simp
  apply Quaternion.ext <;> simp [qι_apply, half e]

private lemma tmul_mem_box {q : ℍ[ℚ]} (hq : q ∈ hurwitzLattice) {a : AQ} (ha : a ∈ Zhat) :
    q ⊗ₜ[ℚ] a ∈ AdelicLattice.finiteAdeleBox hurwitzLattice := by
  exact AddSubgroup.subset_closure ⟨q, hq, a, ScalarFiniteAdeles.mem_integralAdeles.mp ha, rfl⟩

lemma tensor_box_image_mem_hat {x : ℍ[ℚ] ⊗[ℚ] AQ}
    (hx : x ∈ AdelicLattice.finiteAdeleBox hurwitzLattice) :
    hamiltonAdeleTensorEquiv x ∈ hurwitzHatAddSubgroup := by
  unfold AdelicLattice.finiteAdeleBox at hx
  refine AddSubgroup.closure_induction
    (p := fun z _ => hamiltonAdeleTensorEquiv z ∈ hurwitzHatAddSubgroup) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨q, hq, a, ha, rfl⟩
    rw [hamiltonAdeleTensorEquiv_tmul]
    exact hurwitzHat_integral_smul (ScalarFiniteAdeles.mem_integralAdeles.mpr ha)
      (qι_hurwitz_mem_hat hq)
  · simpa using hurwitzHat_zero
  · intro z w _hz _hw hz hw
    change hamiltonAdeleTensorEquiv (z + w) ∈ hurwitzHatAddSubgroup
    change hamiltonAdeleTensorEquiv z ∈ hurwitzHatAddSubgroup at hz
    change hamiltonAdeleTensorEquiv w ∈ hurwitzHatAddSubgroup at hw
    rw [map_add]
    exact hurwitzHat_add hz hw
  · intro z _hz hz
    change hamiltonAdeleTensorEquiv (-z) ∈ hurwitzHatAddSubgroup
    change hamiltonAdeleTensorEquiv z ∈ hurwitzHatAddSubgroup at hz
    rw [map_neg]
    exact hurwitzHat_neg hz

lemma hat_mem_tensor_box_image {x : ℍ[AQ]} (hx : x ∈ hurwitzHatAddSubgroup) :
    ∃ t ∈ AdelicLattice.finiteAdeleBox hurwitzLattice, hamiltonAdeleTensorEquiv t = x := by
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, hx⟩ := hx
  let k : ℍ[ℚ] := ⟨0, 0, 0, 1⟩
  have hk : k ∈ hurwitzLattice := by
    refine ⟨0, 0, 0, 1, 0, ?_⟩
    apply Quaternion.ext <;> norm_num [k]
  let t : ℍ[ℚ] ⊗[ℚ] AQ :=
    (1 : ℍ[ℚ]) ⊗ₜ[ℚ] a + hurwitzBasisVector 1 ⊗ₜ[ℚ] b +
      hurwitzBasisVector 2 ⊗ₜ[ℚ] c + k ⊗ₜ[ℚ] d + hurwitzBasisVector 3 ⊗ₜ[ℚ] e
  have ht : t ∈ AdelicLattice.finiteAdeleBox hurwitzLattice :=
    (AdelicLattice.finiteAdeleBox hurwitzLattice).add_mem
      ((AdelicLattice.finiteAdeleBox hurwitzLattice).add_mem
        ((AdelicLattice.finiteAdeleBox hurwitzLattice).add_mem
          ((AdelicLattice.finiteAdeleBox hurwitzLattice).add_mem (tmul_mem_box hurwitz_one ha)
            (tmul_mem_box (hurwitzBasisVector_mem 1) hb))
          (tmul_mem_box (hurwitzBasisVector_mem 2) hc)) (tmul_mem_box hk hd))
      (tmul_mem_box (hurwitzBasisVector_mem 3) he)
  refine ⟨t, ht, ?_⟩
  rw [hx]
  dsimp [t]
  simp only [map_add, hamiltonAdeleTensorEquiv_tmul]
  have hneg : algebraMap ℚ AQ (-1 / 2) = -algebraMap ℚ AQ (1 / 2) := by
    rw [show (-1 / 2 : ℚ) = -(1 / 2 : ℚ) by ring, map_neg]
  apply Quaternion.ext <;> simp [qι_apply, hurwitzBasisVector, k, hneg] <;> ring

/-- Exact equality of the transported algebraic additive box and the ACTUAL
five-integral-coefficient finite-adelic Hurwitz set. -/
theorem tensor_box_image_eq_hurwitzHat :
    (((AdelicLattice.finiteAdeleBox hurwitzLattice).map
      hamiltonAdeleTensorEquiv.toAddMonoidHom : AddSubgroup ℍ[AQ]) : Set ℍ[AQ]) = (hurwitzHatAddSubgroup : Set ℍ[AQ]) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact tensor_box_image_mem_hat ht
  · intro hx
    exact hat_mem_tensor_box_image hx

lemma tensor_box_mem_iff_hurwitzHat (t : ℍ[ℚ] ⊗[ℚ] AQ) :
    t ∈ AdelicLattice.finiteAdeleBox hurwitzLattice ↔
      hamiltonAdeleTensorEquiv t ∈ hurwitzHatAddSubgroup := by
  constructor
  · exact tensor_box_image_mem_hat
  · intro ht
    obtain ⟨s, hs, hst⟩ := hat_mem_tensor_box_image ht
    have heq : s = t := hamiltonAdeleTensorEquiv.injective hst
    subst s
    exact hs

/-- Multiplication closure of the ACTUAL finite-adelic Hurwitz set follows from
its proved tensor-box identity and the ACTUAL rational Hurwitz ring closure. -/
lemma hurwitzHat_mul {x y : ℍ[AQ]} (hx : x ∈ hurwitzHatAddSubgroup) (hy : y ∈ hurwitzHatAddSubgroup) :
    x * y ∈ hurwitzHatAddSubgroup := by
  obtain ⟨s, hs, hsx⟩ := hat_mem_tensor_box_image hx
  obtain ⟨t, ht, hty⟩ := hat_mem_tensor_box_image hy
  rw [← hsx, ← hty, ← map_mul]
  apply tensor_box_image_mem_hat
  exact AdelicLattice.box_mul_mem hurwitzLattice (fun a b ha hb => hurwitz_mul ha hb) hs ht

/-- Both actual finite-adelic unit and inverse memberships, after the proved
Hamilton algebra and literal Hurwitz-hat box transport. -/
theorem hamilton_stabilizer_iff_both_hurwitzHat (u : (ℍ[ℚ] ⊗[ℚ] AQ)ˣ) :
    u ∈ AdelicLattice.finiteIdeleStabilizer hurwitzLattice ↔
      (hamiltonAdeleUnitEquiv u : ℍ[AQ]) ∈ hurwitzHatAddSubgroup ∧
        (((hamiltonAdeleUnitEquiv u)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
  rw [AdelicLattice.mem_stab_iff_both_box hurwitzLattice hurwitz_one
    (fun a b ha hb => hurwitz_mul ha hb)]
  simp only [tensor_box_mem_iff_hurwitzHat, hamiltonAdeleUnitEquiv_val,
    hamiltonAdeleUnitEquiv_inv_coe]

end TYZSquareOddness
