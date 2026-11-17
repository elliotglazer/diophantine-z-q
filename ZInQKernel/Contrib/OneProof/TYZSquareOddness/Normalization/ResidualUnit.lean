import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Normalization.PrincipalBox

/-!
# Residual-unit algebra, conditional prerequisites only

The reconstruction equality is an explicit prerequisite of the conditional
statements in this file. It is NOT supplied by principality and is NOT claimed
proved here. A closed normalization theorem must compose a separately checked
actual reconstruction theorem. Both memberships use the genuine unit inverse
and the literal Hurwitz-hat subgroup; no ambient adelic division-ring instance,
commutativity of quaternion factors, or normalizer premise is assumed.
-/

open scoped Quaternion
open TYZSquareOddness.ScalarFiniteAdeles
set_option autoImplicit false

namespace TYZSquareOddness.Normalization

noncomputable def residualUnit (g : ℍ[AQ]ˣ) (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) : ℍ[AQ]ˣ :=
  (diagonalGeneratorUnit gamma hgamma)⁻¹ * g

@[simp] lemma residualUnit_val (g : ℍ[AQ]ˣ) (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) :
    (residualUnit g gamma hgamma : ℍ[AQ]) =
      (((diagonalGeneratorUnit gamma hgamma)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * (g : ℍ[AQ]) := rfl

/-- This is the ACTUAL inverse, with its factors in reversed order. -/
lemma residualUnit_inv_val (g : ℍ[AQ]ˣ) (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) :
    (((residualUnit g gamma hgamma)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) =
      ((g⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * qι gamma := by
  simp [residualUnit, mul_inv_rev]

lemma residual_factorization (g : ℍ[AQ]ˣ) (gamma : ℍ[ℚ]) (hgamma : gamma ≠ 0) :
    (g : ℍ[AQ]) = qι gamma * (residualUnit g gamma hgamma : ℍ[AQ]) := by
  rw [residualUnit_val, ← diagonalGeneratorUnit_val gamma hgamma, ← mul_assoc,
    Units.mul_inv, one_mul]

/-- Algebraic prerequisite: equality of the two LEFT translates implies the
residual unit stabilizes the literal Hurwitz-hat subgroup. -/
theorem residual_stabilizes_of_translate_eq (g : ℍ[AQ]ˣ) (gamma : ℍ[ℚ])
    (hgamma : gamma ≠ 0)
    (htranslate : hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (g : ℍ[AQ])) =
      hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (qι gamma))) :
    hurwitzHatAddSubgroup.map
      (AddMonoidHom.mulLeft (residualUnit g gamma hgamma : ℍ[AQ])) = hurwitzHatAddSubgroup := by
  let d := diagonalGeneratorUnit gamma hgamma
  have cancel (x : ℍ[AQ]) : ((d⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * ((d : ℍ[AQ]) * x) = x := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    have hgy : (g : ℍ[AQ]) * y ∈ hurwitzHatAddSubgroup.map
        (AddMonoidHom.mulLeft (qι gamma)) := by
      rw [← htranslate]
      exact ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzg⟩ := hgy
    change qι gamma * z = (g : ℍ[AQ]) * y at hzg
    have heq : (residualUnit g gamma hgamma : ℍ[AQ]) * y = z := by
      change (((d⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * (g : ℍ[AQ])) * y = z
      rw [mul_assoc, ← hzg]
      exact cancel z
    change (residualUnit g gamma hgamma : ℍ[AQ]) * y ∈ hurwitzHatAddSubgroup
    rw [heq]
    exact hz
  · intro x hx
    have hdx : qι gamma * x ∈ hurwitzHatAddSubgroup.map
        (AddMonoidHom.mulLeft (g : ℍ[AQ])) := by
      rw [htranslate]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyg⟩ := hdx
    refine ⟨y, hy, ?_⟩
    change (g : ℍ[AQ]) * y = qι gamma * x at hyg
    change (((d⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * (g : ℍ[AQ])) * y = x
    rw [mul_assoc, hyg]
    exact cancel x

/-- BOTH memberships follow from 1 in the literal subgroup and equality of its
image under an ACTUAL unit. The inverse conclusion is not an ambient inverse. -/
theorem both_mem_of_stabilizes (u : ℍ[AQ]ˣ)
    (hstab : hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (u : ℍ[AQ])) =
      hurwitzHatAddSubgroup) :
    (u : ℍ[AQ]) ∈ hurwitzHatAddSubgroup ∧ ((u⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
  have h1 : (1 : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
    change (1 : ℍ[AQ]) ∈ hurwitzHatAddSubgroup
    simpa only [map_one] using qι_hurwitz_mem_hat hurwitz_one
  have hu : (u : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
    rw [← hstab]
    exact ⟨1, h1, mul_one _⟩
  have h1image : (1 : ℍ[AQ]) ∈ hurwitzHatAddSubgroup.map
      (AddMonoidHom.mulLeft (u : ℍ[AQ])) := by rw [hstab]; exact h1
  obtain ⟨y, hy, huy⟩ := h1image
  change (u : ℍ[AQ]) * y = 1 at huy
  have hyinv : y = ((u⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) := by
    calc
      y = ((u⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * ((u : ℍ[AQ]) * y) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((u⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) := by rw [huy, mul_one]
  exact ⟨hu, hyinv ▸ hy⟩

/-- CONDITIONAL prerequisite only, not closed normalization: its sole open
input is reconstruction for this actual g. The generator/FG/principality,
principal-box transport, actual residual inverse, and BOTH memberships are
proved inside this statement. -/
theorem factorization_of_actual_reconstruction (g : ℍ[AQ]ˣ)
    (hreconstruction : transportedBox (hurwitzIntersection g) =
      hurwitzHatAddSubgroup.map (AddMonoidHom.mulLeft (g : ℍ[AQ]))) :
    ∃ gamma : ℍ[ℚ], gamma ≠ 0 ∧ ∃ u : ℍ[AQ]ˣ,
      (g : ℍ[AQ]) = qι gamma * (u : ℍ[AQ]) ∧
        (u : ℍ[AQ]) ∈ hurwitzHatAddSubgroup ∧ ((u⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
  obtain ⟨gamma, _hmem, hne, hbox⟩ := actual_principal_box g
  have htranslate := hreconstruction.symm.trans hbox
  have hstab := residual_stabilizes_of_translate_eq g gamma hne htranslate
  have hboth := both_mem_of_stabilizes (residualUnit g gamma hne) hstab
  exact ⟨gamma, hne, residualUnit g gamma hne,
    residual_factorization g gamma hne, hboth.1, hboth.2⟩

end TYZSquareOddness.Normalization
