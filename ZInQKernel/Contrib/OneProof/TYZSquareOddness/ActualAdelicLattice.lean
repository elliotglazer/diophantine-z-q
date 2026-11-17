import ZInQKernel.Contrib.OneProof.TYZSquareOddness.AdelicDenominators
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.FractionalRightLattices

/-!
# The ACTUAL all-unit adelic Hurwitz intersection is a full finite right lattice

`I(g)` is the literal diagonal preimage of `g*hurwitzHat` under the existing qι.
Clear the FOUR coordinates of g and its ACTUAL inverse separately: the first
bounds one common scalar image of I(g) inside H; the second puts a scalar H
inside I(g). No finite-generation/full-span/normalization caller premise.
-/

open scoped Quaternion
open TYZSquareOddness.ScalarFiniteAdeles
set_option autoImplicit false

namespace TYZSquareOddness

/-- Actual right-lattice intersection: q belongs iff g⁻¹*qι(q) is Hurwitz integral. -/
noncomputable def hurwitzIntersection (g : ℍ[AQ]ˣ) : Submodule ℤ ℍ[ℚ] :=
  AddSubgroup.toIntSubmodule (hurwitzHatAddSubgroup.comap
    ((AddMonoidHom.mulLeft ((g⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ])).comp qι.toAddMonoidHom))

lemma mem_hurwitzIntersection_iff (g : ℍ[AQ]ˣ) (q : ℍ[ℚ]) :
    q ∈ hurwitzIntersection g ↔ ((g⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * qι q ∈ hurwitzHatAddSubgroup := Iff.rfl

private lemma intCast_hamilton_ne_zero {m : ℤ} (hm : m ≠ 0) : (m : ℍ[ℚ]) ≠ 0 := by
  have hmQ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm
  intro hz
  apply hmQ
  simpa using congrArg (fun q : ℍ[ℚ] => q.re) hz

private lemma zsmul_eq_rat_smul (m : ℤ) (q : ℍ[ℚ]) : m • q = (m : ℚ) • q := by
  apply Quaternion.ext <;> simp [zsmul_eq_mul]

lemma hurwitzIntersection_right_stable (g : ℍ[AQ]ˣ)
    {q a : ℍ[ℚ]} (hq : q ∈ hurwitzIntersection g) (ha : a ∈ hurwitzLattice) :
    q * a ∈ hurwitzIntersection g := by
  rw [mem_hurwitzIntersection_iff] at hq ⊢
  rw [map_mul, ← mul_assoc]
  exact hurwitzHat_mul hq (qι_hurwitz_mem_hat ha)

/-- One nonzero scalar image of every actual I(g) is contained in H. -/
lemma hurwitzIntersection_upper_bound (g : ℍ[AQ]ˣ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ q : ℍ[ℚ], q ∈ hurwitzIntersection g → (m • q) ∈ hurwitzLattice := by
  obtain ⟨m, hm, hmg⟩ := exists_int_smul_mem_hurwitzHat (g : ℍ[AQ])
  refine ⟨m, hm, ?_⟩
  intro q hq
  apply hurwitz_of_qι_mem_hat
  have heq : qι (m • q) = (m • (g : ℍ[AQ])) * (((g⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) * qι q) := by
    rw [map_zsmul, smul_mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
  rw [heq]
  exact hurwitzHat_mul hmg ((mem_hurwitzIntersection_iff g q).mp hq)

/-- Clearing the ACTUAL inverse gives a nonzero scalar H inside every I(g). -/
lemma hurwitzIntersection_lower_bound (g : ℍ[AQ]ˣ) :
    ∃ m : ℤ, m ≠ 0 ∧ ∀ q : ℍ[ℚ], q ∈ hurwitzLattice → m • q ∈ hurwitzIntersection g := by
  obtain ⟨m, hm, hmgi⟩ := exists_int_smul_mem_hurwitzHat ((g⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ])
  refine ⟨m, hm, ?_⟩
  intro q hq
  rw [mem_hurwitzIntersection_iff, map_zsmul, Algebra.mul_smul_comm]
  rw [← smul_mul_assoc]
  exact hurwitzHat_mul hmgi (qι_hurwitz_mem_hat hq)

/-- Finite integer generation for EVERY actual adelic unit, proved from an
injective scalar image bounded inside the actual finite Hurwitz lattice. -/
theorem hurwitzIntersection_fg (g : ℍ[AQ]ˣ) : (hurwitzIntersection g).FG := by
  obtain ⟨m, hm, hBound⟩ := hurwitzIntersection_upper_bound g
  let f : ℍ[ℚ] →ₗ[ℤ] ℍ[ℚ] := LinearMap.lsmul ℤ ℍ[ℚ] m
  have hMapLe : (hurwitzIntersection g).map f ≤ hurwitzLattice := by
    intro q hq
    obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.mp hq
    rw [← hfx]
    exact hBound x hx
  have hMapFG : ((hurwitzIntersection g).map f).FG := hurwitzLattice_fg.of_le hMapLe
  have hf : Function.Injective f := by
    intro x y hxy
    apply mul_left_cancel₀ (intCast_hamilton_ne_zero hm)
    simpa only [f, LinearMap.lsmul_apply, zsmul_eq_mul] using hxy
  exact Submodule.fg_of_fg_map_injective f hf hMapFG

/-- Full rational span for EVERY actual adelic unit: a nonzero scalar copy of
all of H lies in I(g), so its rational span is the whole Hamilton algebra. -/
theorem hurwitzIntersection_span_rat (g : ℍ[AQ]ˣ) :
    Submodule.span ℚ (↑(hurwitzIntersection g) : Set ℍ[ℚ]) = ⊤ := by
  obtain ⟨m, hm, hLower⟩ := hurwitzIntersection_lower_bound g
  let L : Submodule ℚ ℍ[ℚ] := Submodule.span ℚ (↑(hurwitzIntersection g) : Set ℍ[ℚ])
  have hHL : ∀ q : ℍ[ℚ], q ∈ hurwitzLattice → q ∈ L := by
    intro q hq
    have hmQ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hmq : m • q ∈ L := Submodule.subset_span (hLower q hq)
    have h := L.smul_mem (m : ℚ)⁻¹ hmq
    have heq : (m : ℚ)⁻¹ • (m • q) = q := by
      rw [zsmul_eq_rat_smul, smul_smul, inv_mul_cancel₀ hmQ, one_smul]
    rw [heq] at h
    exact h
  have hspan : Submodule.span ℚ (↑hurwitzLattice : Set ℍ[ℚ]) ≤ L :=
    Submodule.span_le.mpr hHL
  rw [hurwitzLattice_span_rat] at hspan
  exact top_unique hspan

lemma hurwitzIntersection_nonzero (g : ℍ[AQ]ˣ) :
    ∃ q : ℍ[ℚ], q ∈ hurwitzIntersection g ∧ q ≠ 0 := by
  obtain ⟨m, hm, hLower⟩ := hurwitzIntersection_lower_bound g
  refine ⟨m • (1 : ℍ[ℚ]), hLower 1 hurwitz_one, ?_⟩
  simpa only [zsmul_eq_mul, mul_one] using intCast_hamilton_ne_zero hm

/-- Genuine principal RIGHT lattice for every ACTUAL adelic quaternion unit;
all finite-generation/right-stability/nonzero inputs above are proved, not
extra assumptions named after the desired global result. -/
theorem hurwitzIntersection_principal (g : ℍ[AQ]ˣ) :
    ∃ gamma : ℍ[ℚ], gamma ∈ hurwitzIntersection g ∧ gamma ≠ 0 ∧
      ∀ q : ℍ[ℚ], q ∈ hurwitzIntersection g ↔
        ∃ a : ℍ[ℚ], a ∈ hurwitzLattice ∧ q = gamma * a := by
  exact principal_fractional_right_hurwitz (hurwitzIntersection g) (hurwitzIntersection_fg g)
    (fun q hq a ha => hurwitzIntersection_right_stable g hq ha) (hurwitzIntersection_nonzero g)

end TYZSquareOddness
