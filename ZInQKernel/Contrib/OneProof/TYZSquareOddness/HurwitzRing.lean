import ZInQKernel.Contrib.OneProof.TYZSquareOddness.HurwitzBasis

/-!
# Multiplication in the literal embedded Hurwitz lattice

Port of the frozen rational basis-product and span-induction argument, with the missing
H29 predicate spelled as membership in the actual five-coordinate integer submodule.
The finite checks are rational quaternion products, not an assumed adelic residue model.
-/

open scoped Quaternion
set_option autoImplicit false

namespace TYZSquareOddness

lemma hurwitz_one : (1 : ℍ[ℚ]) ∈ hurwitzLattice := by
  simpa [hurwitzBasisVector] using hurwitzBasisVector_mem 0

private lemma basis_product_hurwitz (i j : Fin 4) :
    hurwitzBasisVector i * hurwitzBasisVector j ∈ hurwitzLattice := by
  fin_cases i <;> fin_cases j
  all_goals first
    | (refine ⟨1, 0, 0, 0, 0, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, 1, 0, 0, 0, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, 0, 1, 0, 0, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, 0, 0, 1, 0, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, 0, 0, 0, 1, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨-1, 0, 0, 0, 0, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, 0, 0, -1, 0, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, -1, -1, 0, 1, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, -1, 0, -1, 1, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, 0, -1, -1, 1, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)
    | (refine ⟨0, -1, -1, -1, 1, ?_⟩
       apply Quaternion.ext <;> norm_num [hurwitzBasisVector, Quaternion.re_mul,
         Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
       done)

private lemma basis_mul_hurwitz (i : Fin 4) {y : ℍ[ℚ]} (hy : y ∈ hurwitzLattice) :
    hurwitzBasisVector i * y ∈ hurwitzLattice := by
  have hySpan : y ∈ Submodule.span ℤ (Set.range hurwitzBasisVector) := by
    rw [span_hurwitzBasisVector]
    exact hy
  refine Submodule.span_induction
    (p := fun z _ => hurwitzBasisVector i * z ∈ hurwitzLattice) ?_ ?_ ?_ ?_ hySpan
  · rintro z ⟨j, rfl⟩
    exact basis_product_hurwitz i j
  · simpa using hurwitz_zero
  · intro x z _hx _hz hx hz
    simpa only [mul_add] using hurwitz_add hx hz
  · intro n z _hz hz
    simpa only [Algebra.mul_smul_comm] using hurwitz_zsmul n hz

lemma hurwitz_mul {x y : ℍ[ℚ]} (hx : x ∈ hurwitzLattice) (hy : y ∈ hurwitzLattice) :
    x * y ∈ hurwitzLattice := by
  have hxSpan : x ∈ Submodule.span ℤ (Set.range hurwitzBasisVector) := by
    rw [span_hurwitzBasisVector]
    exact hx
  refine Submodule.span_induction (p := fun z _ => z * y ∈ hurwitzLattice) ?_ ?_ ?_ ?_ hxSpan
  · rintro z ⟨i, rfl⟩
    exact basis_mul_hurwitz i hy
  · simpa using hurwitz_zero
  · intro z w _hz _hw hz hw
    simpa only [add_mul] using hurwitz_add hz hw
  · intro n z _hz hz
    simpa only [smul_mul_assoc] using hurwitz_zsmul n hz

end TYZSquareOddness
