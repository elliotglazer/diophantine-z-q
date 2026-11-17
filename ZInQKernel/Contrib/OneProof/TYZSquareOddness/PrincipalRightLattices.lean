import ZInQKernel.Contrib.OneProof.TYZSquareOddness
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.ScalarFiniteAdeles

/-!
# Principal integral right lattices in the literal rational Hurwitz carrier

Upstream port of the frozen coarse source. The real integer submodule below has exactly the
five-integer coordinate carrier; no missing H29 predicate/model or desired-result premise is
defined. Canonical A/B witnesses are imported, not reproved. Division in the minimum-norm proof
is rational Hamilton division on the correct side; finite adèles are never treated as a field.
-/

open scoped Quaternion
set_option autoImplicit false

namespace TYZSquareOddness

/-- The literal rational Hurwitz lattice as an actual integer submodule. -/
def hurwitzLattice : Submodule ℤ ℍ[ℚ] where
  carrier := {q | ∃ a b c d e : ℤ, q =
    ⟨(a : ℚ) - (e : ℚ) / 2, (b : ℚ) + (e : ℚ) / 2,
      (c : ℚ) + (e : ℚ) / 2, (d : ℚ) + (e : ℚ) / 2⟩}
  zero_mem' := by
    refine ⟨0, 0, 0, 0, 0, ?_⟩
    apply Quaternion.ext <;> norm_num
  add_mem' := by
    rintro q r ⟨a, b, c, d, e, rfl⟩ ⟨f, g, h, i, j, rfl⟩
    refine ⟨a + f, b + g, c + h, d + i, e + j, ?_⟩
    apply Quaternion.ext <;> dsimp <;> push_cast <;> ring
  smul_mem' := by
    rintro z q ⟨a, b, c, d, e, rfl⟩
    refine ⟨z * a, z * b, z * c, z * d, z * e, ?_⟩
    apply Quaternion.ext <;> dsimp <;> push_cast <;> simp only [zsmul_eq_mul] <;> ring

@[simp] lemma mem_hurwitzLattice (q : ℍ[ℚ]) :
    q ∈ hurwitzLattice ↔ ∃ a b c d e : ℤ, q =
      ⟨(a : ℚ) - (e : ℚ) / 2, (b : ℚ) + (e : ℚ) / 2,
        (c : ℚ) + (e : ℚ) / 2, (d : ℚ) + (e : ℚ) / 2⟩ := Iff.rfl

lemma hurwitz_zero : (0 : ℍ[ℚ]) ∈ hurwitzLattice := hurwitzLattice.zero_mem
lemma hurwitz_add {q r : ℍ[ℚ]} (hq : q ∈ hurwitzLattice) (hr : r ∈ hurwitzLattice) :
    q + r ∈ hurwitzLattice := hurwitzLattice.add_mem hq hr
lemma hurwitz_zsmul (z : ℤ) {q : ℍ[ℚ]} (hq : q ∈ hurwitzLattice) :
    z • q ∈ hurwitzLattice := hurwitzLattice.smul_mem z hq

lemma normSq_integral_of_hurwitz {q : ℍ[ℚ]} (hq : q ∈ hurwitzLattice) :
    ∃ n : ℤ, Quaternion.normSq q = (n : ℚ) := by
  obtain ⟨a, b, c, d, e, rfl⟩ := hq
  refine ⟨a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e * (-a + b + c + d) + e ^ 2, ?_⟩
  rw [Quaternion.normSq_def']
  dsimp
  push_cast
  ring

lemma normSq_nat_of_hurwitz {q : ℍ[ℚ]} (hq : q ∈ hurwitzLattice) :
    ∃ n : ℕ, Quaternion.normSq q = (n : ℚ) := by
  obtain ⟨z, hz⟩ := normSq_integral_of_hurwitz hq
  have hz0 : 0 ≤ z := by
    have h := Quaternion.normSq_nonneg (a := q)
    rw [hz] at h
    exact_mod_cast h
  refine ⟨z.toNat, ?_⟩
  rw [hz]
  exact_mod_cast (Int.toNat_of_nonneg hz0).symm

/-- Genuine right-principality of a nonzero integral right-stable submodule. -/
theorem principal_integral_right_hurwitz (I : Submodule ℤ ℍ[ℚ])
    (hI : ∀ q : ℍ[ℚ], q ∈ I → q ∈ hurwitzLattice)
    (hRight : ∀ beta : ℍ[ℚ], beta ∈ I → ∀ a : ℍ[ℚ], a ∈ hurwitzLattice → beta * a ∈ I)
    (hNonzero : ∃ beta : ℍ[ℚ], beta ∈ I ∧ beta ≠ 0) :
    ∃ beta : ℍ[ℚ], beta ∈ I ∧ beta ≠ 0 ∧
      ∀ y : ℍ[ℚ], y ∈ I ↔ ∃ a : ℍ[ℚ], a ∈ hurwitzLattice ∧ y = beta * a := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ beta : ℍ[ℚ], beta ∈ I ∧ beta ≠ 0 ∧ Quaternion.normSq beta = (n : ℚ)
  have hP : ∃ n, P n := by
    obtain ⟨beta, hb, hbne⟩ := hNonzero
    obtain ⟨n, hn⟩ := normSq_nat_of_hurwitz (hI beta hb)
    exact ⟨n, beta, hb, hbne, hn⟩
  obtain ⟨beta, hb, hbne, hnorm⟩ := Nat.find_spec hP
  have hmin (r : ℍ[ℚ]) (hr : r ∈ I) (hrne : r ≠ 0) :
      Quaternion.normSq beta ≤ Quaternion.normSq r := by
    obtain ⟨m, hm⟩ := normSq_nat_of_hurwitz (hI r hr)
    have hnle : Nat.find hP ≤ m := Nat.find_min' hP ⟨r, hr, hrne, hm⟩
    rw [hnorm, hm]
    exact_mod_cast hnle
  have hbpos : 0 < Quaternion.normSq beta :=
    lt_of_le_of_ne Quaternion.normSq_nonneg (Ne.symm (Quaternion.normSq_ne_zero.mpr hbne))
  refine ⟨beta, hb, hbne, ?_⟩
  intro y
  constructor
  · intro hy
    obtain ⟨a, ha, happrox⟩ := hurwitz_norm_approximation (beta⁻¹ * y)
    let r := y - beta * a
    have hr : r ∈ I := I.sub_mem hy (hRight beta hb a ha)
    have hfactor : r = beta * (beta⁻¹ * y - a) := by
      dsimp [r]
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hbne, one_mul]
    have hsmall : Quaternion.normSq r < Quaternion.normSq beta := by
      rw [hfactor, map_mul]
      simpa using mul_lt_mul_of_pos_left happrox hbpos
    have hrzero : r = 0 := by
      by_contra hrne
      exact (not_lt_of_ge (hmin r hr hrne)) hsmall
    exact ⟨a, ha, sub_eq_zero.mp hrzero⟩
  · rintro ⟨a, ha, rfl⟩
    exact hRight beta hb a ha

end TYZSquareOddness
