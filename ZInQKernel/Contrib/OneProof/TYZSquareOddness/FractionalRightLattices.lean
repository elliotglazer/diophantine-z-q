import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Denominators

/-!
# Principal RIGHT fractional Hurwitz lattices

For a finitely generated integer submodule of the actual rational Hamilton
algebra, clear ONE common integer denominator `m`. The minimum-norm argument
is applied to `J = m I`, which is now integral, NEVER to the raw fractional I.
A principal generator beta of J has an actual preimage gamma in I, so
`beta = m gamma` and `I = gamma O_H` on the RIGHT.

This is genuine lattice principality, not the remaining adelic normalization:
right stability/finite generation of the actual adelic intersection, the
AQ-tensor/Hamilton/box/qι transport, both residual unit/inverse memberships,
and the local-2/InPiZ construction still require their own proofs.
-/

open scoped Quaternion
open TYZSquareOddness.ScalarFiniteAdeles

set_option autoImplicit false

namespace TYZSquareOddness

/-- Every nonzero, finitely integer-generated rational Hamilton lattice stable
under RIGHT multiplication by the actual Hurwitz carrier is principal on the
RIGHT. There is no integrality assumption on I. -/
theorem principal_fractional_right_hurwitz (I : Submodule ℤ ℍ[ℚ])
    (hFG : I.FG)
    (hRight : ∀ gamma : ℍ[ℚ], gamma ∈ I → ∀ a : ℍ[ℚ], a ∈ hurwitzLattice → gamma * a ∈ I)
    (hNonzero : ∃ gamma : ℍ[ℚ], gamma ∈ I ∧ gamma ≠ 0) :
    ∃ gamma : ℍ[ℚ], gamma ∈ I ∧ gamma ≠ 0 ∧
      ∀ y : ℍ[ℚ], y ∈ I ↔ ∃ a : ℍ[ℚ], a ∈ hurwitzLattice ∧ y = gamma * a := by
  classical
  obtain ⟨m, hm, hClear⟩ := exists_common_hurwitz_denominator I hFG
  let f : ℍ[ℚ] →ₗ[ℤ] ℍ[ℚ] := LinearMap.lsmul ℤ ℍ[ℚ] (m : ℤ)
  let J : Submodule ℤ ℍ[ℚ] := I.map f
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hmCast : (((m : ℤ) : ℍ[ℚ])) ≠ 0 := by
    intro hz
    apply hmQ
    simpa using congrArg (fun q : ℍ[ℚ] => q.re) hz
  have hJIntegral : ∀ beta : ℍ[ℚ], beta ∈ J → beta ∈ hurwitzLattice := by
    intro beta hb
    obtain ⟨x, hx, hxb⟩ := Submodule.mem_map.mp hb
    rw [← hxb]
    exact hClear x hx
  have hJRight : ∀ beta : ℍ[ℚ], beta ∈ J → ∀ a : ℍ[ℚ], a ∈ hurwitzLattice → beta * a ∈ J := by
    intro beta hb a ha
    obtain ⟨x, hx, hxb⟩ := Submodule.mem_map.mp hb
    apply Submodule.mem_map.mpr
    refine ⟨x * a, hRight x hx a ha, ?_⟩
    rw [← hxb]
    simp [f, LinearMap.lsmul_apply, zsmul_eq_mul, mul_assoc]
  have hJNonzero : ∃ beta : ℍ[ℚ], beta ∈ J ∧ beta ≠ 0 := by
    obtain ⟨x, hx, hxne⟩ := hNonzero
    refine ⟨f x, Submodule.mem_map_of_mem hx, ?_⟩
    simpa only [f, LinearMap.lsmul_apply, zsmul_eq_mul] using mul_ne_zero hmCast hxne
  obtain ⟨beta, hb, hbne, hGen⟩ :=
    principal_integral_right_hurwitz J hJIntegral hJRight hJNonzero
  obtain ⟨gamma, hg, hgb⟩ := Submodule.mem_map.mp hb
  have hgne : gamma ≠ 0 := by
    intro hz
    apply hbne
    rw [← hgb, hz]
    simp [f]
  refine ⟨gamma, hg, hgne, ?_⟩
  intro y
  constructor
  · intro hy
    have hMy : f y ∈ J := Submodule.mem_map_of_mem hy
    obtain ⟨a, ha, hya⟩ := (hGen (f y)).mp hMy
    refine ⟨a, ha, ?_⟩
    apply mul_left_cancel₀ hmCast
    have heq : f y = f (gamma * a) := by
      calc
        f y = beta * a := hya
        _ = f gamma * a := by rw [hgb]
        _ = f (gamma * a) := by
          simp [f, LinearMap.lsmul_apply, zsmul_eq_mul, mul_assoc]
    simpa only [f, LinearMap.lsmul_apply, zsmul_eq_mul] using heq
  · rintro ⟨a, ha, rfl⟩
    exact hRight gamma hg a ha

end TYZSquareOddness
