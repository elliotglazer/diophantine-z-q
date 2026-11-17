import ZInQKernel.Contrib.OneProof.TYZSquareOddness.PrincipalRightLattices

/-!
# One common denominator for an actual rational Hurwitz lattice

The denominator is chosen once from all coordinates of a finite integer
spanning family. The conclusion uses the literal `H29Split.IsHurwitz` carrier.
No integrality of a raw fractional adelic intersection is assumed.
-/

open scoped Quaternion BigOperators
open TYZSquareOddness.ScalarFiniteAdeles

set_option autoImplicit false

namespace TYZSquareOddness

private def coordinate (q : ℍ[ℚ]) : Fin 4 → ℚ := ![q.re, q.imI, q.imJ, q.imK]

private def coordinateDenominator (q : ℍ[ℚ]) : ℕ := ∏ i : Fin 4, (coordinate q i).den

private lemma coordinateDenominator_ne_zero (q : ℍ[ℚ]) : coordinateDenominator q ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.ne_of_gt (Rat.den_pos (coordinate q i)))

private lemma exists_int_mul_of_den_dvd (x : ℚ) (m : ℕ) (h : x.den ∣ m) :
    ∃ a : ℤ, (m : ℚ) * x = (a : ℚ) := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨x.num * (k : ℤ), ?_⟩
  push_cast
  calc
    (x.den : ℚ) * (k : ℚ) * x = (x * (x.den : ℚ)) * (k : ℚ) := by ring
    _ = (x.num : ℚ) * (k : ℚ) := by rw [Rat.mul_den_eq_num]

private lemma coordinate_den_smul_hurwitz (q : ℍ[ℚ]) :
    ((coordinateDenominator q : ℤ) • q) ∈ hurwitzLattice := by
  have hd (i : Fin 4) : (coordinate q i).den ∣ coordinateDenominator q :=
    Finset.dvd_prod_of_mem (fun i : Fin 4 => (coordinate q i).den) (Finset.mem_univ i)
  obtain ⟨a, ha⟩ := exists_int_mul_of_den_dvd q.re (coordinateDenominator q)
    (by simpa [coordinate] using hd 0)
  obtain ⟨b, hb⟩ := exists_int_mul_of_den_dvd q.imI (coordinateDenominator q)
    (by simpa [coordinate] using hd 1)
  obtain ⟨c, hc⟩ := exists_int_mul_of_den_dvd q.imJ (coordinateDenominator q)
    (by simpa [coordinate] using hd 2)
  obtain ⟨d, hdd⟩ := exists_int_mul_of_den_dvd q.imK (coordinateDenominator q)
    (by simpa [coordinate] using hd 3)
  refine ⟨a, b, c, d, 0, ?_⟩
  apply Quaternion.ext
  · simpa [Quaternion.re_smul, zsmul_eq_mul] using ha
  · simpa [Quaternion.imI_smul, zsmul_eq_mul] using hb
  · simpa [Quaternion.imJ_smul, zsmul_eq_mul] using hc
  · simpa [Quaternion.imK_smul, zsmul_eq_mul] using hdd

/-- Finite integer generation gives ONE nonzero integer denominator making
EVERY element of the actual rational lattice Hurwitz integral. -/
theorem exists_common_hurwitz_denominator (I : Submodule ℤ ℍ[ℚ]) (hFG : I.FG) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ q : ℍ[ℚ], q ∈ I → ((m : ℤ) • q) ∈ hurwitzLattice := by
  classical
  obtain ⟨S, hS⟩ := hFG
  let m : ℕ := ∏ q ∈ S, coordinateDenominator q
  have hm : m ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q _ => coordinateDenominator_ne_zero q)
  refine ⟨m, hm, ?_⟩
  intro q hq
  rw [← hS] at hq
  refine Submodule.span_induction (p := fun y _ => ((m : ℤ) • y) ∈ hurwitzLattice) ?_ ?_ ?_ ?_ hq
  · intro y hy
    have hdiv : coordinateDenominator y ∣ m := Finset.dvd_prod_of_mem coordinateDenominator hy
    obtain ⟨k, hk⟩ := hdiv
    have h := hurwitz_zsmul (k : ℤ) (coordinate_den_smul_hurwitz y)
    simpa [hk, smul_smul, mul_comm, mul_assoc] using h
  · simpa using hurwitz_zero
  · intro x y _hx _hy hx hy
    simpa only [smul_add] using hurwitz_add hx hy
  · intro z y _hy hy
    simpa only [smul_smul, mul_comm] using hurwitz_zsmul z hy

end TYZSquareOddness
