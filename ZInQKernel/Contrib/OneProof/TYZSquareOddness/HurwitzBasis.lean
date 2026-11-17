import ZInQKernel.Contrib.OneProof.TYZSquareOddness.PrincipalRightLattices

/-!
# Actual Hurwitz lattice: finite generation and full rational span

The four generators are `1,i,j,zeta`, with `zeta=(-1+i+j+k)/2`.
Their integer span is proved equal to the literal existing Hurwitz carrier.
This is a carrier/linear-algebra bridge, not a replacement order definition.
-/

open scoped Quaternion
open TYZSquareOddness.ScalarFiniteAdeles

set_option autoImplicit false

namespace TYZSquareOddness

/-- The four integral generators of the actual Hurwitz lattice. -/
def hurwitzBasisVector : Fin 4 → ℍ[ℚ] :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨-1 / 2, 1 / 2, 1 / 2, 1 / 2⟩]

lemma hurwitzBasisVector_mem (i : Fin 4) : hurwitzBasisVector i ∈ hurwitzLattice := by
  fin_cases i
  · refine ⟨1, 0, 0, 0, 0, ?_⟩
    apply Quaternion.ext <;> norm_num [hurwitzBasisVector]
  · refine ⟨0, 1, 0, 0, 0, ?_⟩
    apply Quaternion.ext <;> norm_num [hurwitzBasisVector]
  · refine ⟨0, 0, 1, 0, 0, ?_⟩
    apply Quaternion.ext <;> norm_num [hurwitzBasisVector]
  · refine ⟨0, 0, 0, 0, 1, ?_⟩
    apply Quaternion.ext <;> norm_num [hurwitzBasisVector]

lemma span_hurwitzBasisVector :
    Submodule.span ℤ (Set.range hurwitzBasisVector) = hurwitzLattice := by
  let L : Submodule ℤ ℍ[ℚ] := Submodule.span ℤ (Set.range hurwitzBasisVector)
  have hMem (i : Fin 4) : hurwitzBasisVector i ∈ L :=
    Submodule.subset_span (Set.mem_range_self i)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    exact hurwitzBasisVector_mem i
  · intro q hq
    obtain ⟨a, b, c, d, e, rfl⟩ := hq
    have hdecomp :
        (⟨(a : ℚ) - (e : ℚ) / 2, (b : ℚ) + (e : ℚ) / 2,
          (c : ℚ) + (e : ℚ) / 2, (d : ℚ) + (e : ℚ) / 2⟩ : ℍ[ℚ]) =
          (a + d) • hurwitzBasisVector 0 + (b - d) • hurwitzBasisVector 1 +
          (c - d) • hurwitzBasisVector 2 + (e + 2 * d) • hurwitzBasisVector 3 := by
      apply Quaternion.ext <;> dsimp [hurwitzBasisVector] <;>
        simp only [zsmul_eq_mul] <;> push_cast <;> ring
    rw [hdecomp]
    exact L.add_mem (L.add_mem (L.add_mem (L.smul_mem _ (hMem 0))
      (L.smul_mem _ (hMem 1))) (L.smul_mem _ (hMem 2))) (L.smul_mem _ (hMem 3))

lemma hurwitzLattice_fg : hurwitzLattice.FG := by
  classical
  refine ⟨Finset.univ.image hurwitzBasisVector, ?_⟩
  have hs : (↑(Finset.univ.image hurwitzBasisVector) : Set ℍ[ℚ]) =
      Set.range hurwitzBasisVector := by ext q; simp
  rw [hs]
  exact span_hurwitzBasisVector

lemma hurwitzLattice_span_rat :
    Submodule.span ℚ (↑hurwitzLattice : Set ℍ[ℚ]) = ⊤ := by
  let L : Submodule ℚ ℍ[ℚ] := Submodule.span ℚ (↑hurwitzLattice : Set ℍ[ℚ])
  have hMem (i : Fin 4) : hurwitzBasisVector i ∈ L :=
    Submodule.subset_span (hurwitzBasisVector_mem i)
  apply top_unique
  intro q _hq
  have hdecomp : q =
      (q.re + q.imK) • hurwitzBasisVector 0 +
      (q.imI - q.imK) • hurwitzBasisVector 1 +
      (q.imJ - q.imK) • hurwitzBasisVector 2 +
      (2 * q.imK) • hurwitzBasisVector 3 := by
    apply Quaternion.ext <;> dsimp [hurwitzBasisVector] <;> ring
  rw [hdecomp]
  exact L.add_mem (L.add_mem (L.add_mem (L.smul_mem _ (hMem 0))
    (L.smul_mem _ (hMem 1))) (L.smul_mem _ (hMem 2))) (L.smul_mem _ (hMem 3))

end TYZSquareOddness
