import ZInQKernel.Contrib.OneProof.TYZSquareOddness.HurwitzDiagonalSlice

/-!
# Actual finite-adelic Hamilton denominators

Existing scalar finite-adele denominator clearing is applied to all four actual
AQ coordinates. One nonzero INTEGER clears the quaternion into the literal
Hurwitz-hat set (indeed into its integral Lipschitz part, with e=0).
-/

open scoped Quaternion BigOperators
open IsDedekindDomain NumberField
open TYZSquareOddness.ScalarFiniteAdeles
set_option autoImplicit false

namespace TYZSquareOddness

private abbrev Zhat := ScalarFiniteAdeles.integralAdeles

lemma exists_int_mul_mem_Zhat (a : AQ) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : AQ) * a ∈ Zhat := by
  obtain ⟨b, hb, hab⟩ := ScalarFiniteAdeles.mul_nonZeroDivisor_mem_integralAdeles a
  let n : ℤ := Rat.ringOfIntegersEquiv b
  have hbEq : b = (n : 𝓞 ℚ) := by
    apply Rat.ringOfIntegersEquiv.injective
    simp [n]
  have hn : n ≠ 0 := by
    intro hn0
    apply nonZeroDivisors.ne_zero hb
    rw [hbEq, hn0]
    simp
  refine ⟨n, hn, ?_⟩
  rw [hbEq, map_intCast] at hab
  simpa only [mul_comm] using hab

private def adelicCoordinate (x : ℍ[AQ]) : Fin 4 → AQ := ![x.re, x.imI, x.imJ, x.imK]

/-- Every actual finite-adelic quaternion has one nonzero integer denominator
making it a member of the existing Hurwitz-hat carrier. -/
theorem exists_int_smul_mem_hurwitzHat (x : ℍ[AQ]) :
    ∃ m : ℤ, m ≠ 0 ∧ m • x ∈ hurwitzHatAddSubgroup := by
  classical
  choose d hdne hdmem using fun i : Fin 4 => exists_int_mul_mem_Zhat (adelicCoordinate x i)
  let m : ℤ := ∏ i : Fin 4, d i
  have hm : m ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hdne i)
  have hcoef (i : Fin 4) : (m : AQ) * adelicCoordinate x i ∈ Zhat := by
    have hdiv : d i ∣ m := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdiv
    have h : (k : AQ) * ((d i : AQ) * adelicCoordinate x i) ∈ Zhat :=
      Zhat.mul_mem (intCast_mem_Zhat k) (hdmem i)
    rw [hk]
    simpa only [Int.cast_mul, mul_assoc, mul_comm, mul_left_comm] using h
  refine ⟨m, hm, (m : AQ) * x.re, (m : AQ) * x.imI, (m : AQ) * x.imJ,
    (m : AQ) * x.imK, 0, ?_, ?_, ?_, ?_, Zhat.zero_mem, ?_⟩
  · simpa [adelicCoordinate] using hcoef 0
  · simpa [adelicCoordinate] using hcoef 1
  · simpa [adelicCoordinate] using hcoef 2
  · simpa [adelicCoordinate] using hcoef 3
  · apply Quaternion.ext <;> dsimp <;> simp [zsmul_eq_mul]

end TYZSquareOddness
