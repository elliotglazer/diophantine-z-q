import Mathlib.Tactic
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Coordinates

/-!
# Actual Hurwitz prerequisites for the TYZ square-oddness construction

The approximation and trace/norm criterion below spell out the full literal
five-integer conclusion of the fork's `H29Split.IsHurwitz`. Its defining module
is not yet accepted on upstream main. No replacement predicate or H29 assembly
is defined or copied.
They have no maximality, ramification, principal-ideal or test-vector premise.

These are prerequisites only. This module does not prove `TYZProp23Printed`:
actual right-lattice normalization, the local-2/Un dictionary and an actual
`InPiZ` odd-evaluation witness construction remain separate obligations.
-/

open scoped Quaternion

set_option autoImplicit false

namespace TYZSquareOddness

/-- Every rational Hamilton quaternion has a Hurwitz approximation with
Hamilton norm error strictly less than one. -/
theorem hurwitz_norm_approximation (q : ℍ[ℚ]) :
    ∃ a : ℍ[ℚ],
      (∃ r s t u e : ℤ, a =
        (⟨(r : ℚ) - (e : ℚ) / 2, (s : ℚ) + (e : ℚ) / 2,
          (t : ℚ) + (e : ℚ) / 2, (u : ℚ) + (e : ℚ) / 2⟩ : ℍ[ℚ])) ∧
      Quaternion.normSq (q - a) < 1 := by
  obtain ⟨a, b, c, d, e, h⟩ := exists_hurwitz_coordinates_norm_lt_one q
  exact ⟨⟨(a : ℚ) - (e : ℚ) / 2, (b : ℚ) + (e : ℚ) / 2,
    (c : ℚ) + (e : ℚ) / 2, (d : ℚ) + (e : ℚ) / 2⟩,
    ⟨a, b, c, d, e, rfl⟩, h⟩

/-- Integrality of the unconjugated reduced-trace products `Trd(q*b)` for
`b = 1,i,j,zeta`, together with the Hamilton norm, forces membership in the
actual Hurwitz predicate. These are not products `Trd(q*star b)`.
Here `zeta = (-1+i+j+k)/2`. -/
theorem hurwitz_of_integral_trace_norm (q : ℍ[ℚ])
    (hre : ∃ a : ℤ, 2 * q.re = (a : ℚ))
    (hi : ∃ b : ℤ, -2 * q.imI = (b : ℚ))
    (hj : ∃ c : ℤ, -2 * q.imJ = (c : ℚ))
    (hzeta : ∃ s : ℤ, -(q.re + q.imI + q.imJ + q.imK) = (s : ℚ))
    (hnorm : ∃ n : ℤ, Quaternion.normSq q = (n : ℚ)) :
    ∃ r s t u e : ℤ, q =
      (⟨(r : ℚ) - (e : ℚ) / 2, (s : ℚ) + (e : ℚ) / 2,
        (t : ℚ) + (e : ℚ) / 2, (u : ℚ) + (e : ℚ) / 2⟩ : ℍ[ℚ]) := by
  obtain ⟨a, ha⟩ := hre
  obtain ⟨b, hb⟩ := hi
  obtain ⟨c, hc⟩ := hj
  obtain ⟨s, hs⟩ := hzeta
  obtain ⟨n, hn⟩ := hnorm
  have hi' : 2 * q.imI = ((-b : ℤ) : ℚ) := by push_cast; linarith
  have hj' : 2 * q.imJ = ((-c : ℤ) : ℚ) := by push_cast; linarith
  have hk' : 2 * q.imK = ((-2 * s - a + b + c : ℤ) : ℚ) := by
    push_cast
    linarith
  exact exists_hurwitz_coordinates_of_double_integral_norm q
    a (-b) (-c) (-2 * s - a + b + c) n ha hi' hj' hk' hn

end TYZSquareOddness
