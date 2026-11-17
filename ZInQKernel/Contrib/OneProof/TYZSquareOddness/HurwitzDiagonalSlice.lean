import ZInQKernel.Contrib.OneProof.TYZSquareOddness.HurwitzBoxTransport

/-!
# Exact rational diagonal slice of the ACTUAL finite-adelic Hurwitz carrier

Integral scalar adeles meet diagonal rationals in integer casts. Applied to
`re+imK`, `imI-imK`, `imJ-imK`, and `2*imK`, this reconstructs literal Hurwitz
integer coefficients. No norm/maximality or substitute lattice hypothesis.
-/

open scoped Quaternion
open IsDedekindDomain NumberField
open TYZSquareOddness.ScalarFiniteAdeles
set_option autoImplicit false

namespace TYZSquareOddness

private abbrev Zhat := ScalarFiniteAdeles.integralAdeles

lemma exists_int_of_diagonal_integral (r : ℚ) (hr : algebraMap ℚ AQ r ∈ Zhat) :
    ∃ n : ℤ, r = (n : ℚ) := by
  obtain ⟨z, hz⟩ := (ScalarFiniteAdeles.algebraMap_mem_integralAdeles_iff r).mp hr
  exact ⟨Rat.ringOfIntegersEquiv z,
    hz.symm.trans (Rat.ringOfIntegersEquiv_apply_coe z).symm⟩

lemma hurwitz_of_qι_mem_hat (q : ℍ[ℚ]) (hq : qι q ∈ hurwitzHatAddSubgroup) : q ∈ hurwitzLattice := by
  obtain ⟨a, b, c, d, e, ha, hb, hc, hd, he, hq⟩ := hq
  have hre : algebraMap ℚ AQ q.re = a - e * algebraMap ℚ AQ (1 / 2) := by
    simpa [qι_apply] using congrArg (fun x : ℍ[AQ] => x.re) hq
  have hi : algebraMap ℚ AQ q.imI = b + e * algebraMap ℚ AQ (1 / 2) := by
    simpa [qι_apply] using congrArg (fun x : ℍ[AQ] => x.imI) hq
  have hj : algebraMap ℚ AQ q.imJ = c + e * algebraMap ℚ AQ (1 / 2) := by
    simpa [qι_apply] using congrArg (fun x : ℍ[AQ] => x.imJ) hq
  have hk : algebraMap ℚ AQ q.imK = d + e * algebraMap ℚ AQ (1 / 2) := by
    simpa [qι_apply] using congrArg (fun x : ℍ[AQ] => x.imK) hq
  have hhalf : (2 : AQ) * algebraMap ℚ AQ (1 / 2) = 1 := by
    have h : (2 : ℚ) * (1 / 2) = 1 := by norm_num
    simpa only [map_mul, map_ofNat, map_one] using congrArg (algebraMap ℚ AQ) h
  have hA : algebraMap ℚ AQ (q.re + q.imK) = a + d := by
    rw [map_add, hre, hk]
    ring
  have hB : algebraMap ℚ AQ (q.imI - q.imK) = b - d := by
    rw [map_sub, hi, hk]
    ring
  have hC : algebraMap ℚ AQ (q.imJ - q.imK) = c - d := by
    rw [map_sub, hj, hk]
    ring
  have hE : algebraMap ℚ AQ (2 * q.imK) = e + 2 * d := by
    rw [map_mul, map_ofNat, hk]
    calc
      (2 : AQ) * (d + e * algebraMap ℚ AQ (1 / 2)) =
          2 * d + e * (2 * algebraMap ℚ AQ (1 / 2)) := by ring
      _ = e + 2 * d := by rw [hhalf]; ring
  obtain ⟨r, hr⟩ := exists_int_of_diagonal_integral (q.re + q.imK)
    (by rw [hA]; exact Zhat.add_mem ha hd)
  obtain ⟨s, hs⟩ := exists_int_of_diagonal_integral (q.imI - q.imK)
    (by rw [hB]; exact Zhat.sub_mem hb hd)
  obtain ⟨t, ht⟩ := exists_int_of_diagonal_integral (q.imJ - q.imK)
    (by rw [hC]; exact Zhat.sub_mem hc hd)
  obtain ⟨u, hu⟩ := exists_int_of_diagonal_integral (2 * q.imK)
    (by rw [hE]; exact Zhat.add_mem he (Zhat.mul_mem (intCast_mem_Zhat 2) hd))
  refine ⟨r, s, t, 0, u, ?_⟩
  apply Quaternion.ext <;> dsimp <;> push_cast <;> linarith

/-- The exact rational diagonal slice uses the existing `qι` and literal
`hurwitzHat`/`IsHurwitz` definitions. -/
theorem qι_mem_hurwitzHat_iff (q : ℍ[ℚ]) : qι q ∈ hurwitzHatAddSubgroup ↔ q ∈ hurwitzLattice :=
  ⟨hurwitz_of_qι_mem_hat q, qι_hurwitz_mem_hat⟩

end TYZSquareOddness
