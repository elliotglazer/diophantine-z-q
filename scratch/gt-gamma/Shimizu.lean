import ZInQKernel.Contrib.OneProof.GammaStarArea

/-! gt-gamma, part 2 (draft): Shimizu's covolume `2π/3` of `Γ¹ = ι(𝒪¹)` from `T` and the four cosets. -/

set_option linter.all false

noncomputable section

namespace HDec.GammaStarArea

open LeafQCheck LeafQCheck.QMglue PkgI1 MeasureTheory
open scoped Pointwise

/-- `s₁ = ⋃ᵢ rᵢ⁻¹ T` (`rᵢ = 1, x₄, x₆, x₄x₆`): a fundamental domain of `Γ¹`. -/
def S1 : Set UpperHalfPlane := ⋃ i : Fin 4, (g4 i)⁻¹ • Tset

theorem gamma1_iff' {h : GL (Fin 2) ℝ} : h ∈ HM.QMSplit.Gamma1 ↔ h ∈ QMSplitVB.Gamma1 := Iff.rfl

theorem mem_S1 {z : UpperHalfPlane} : z ∈ S1 ↔ ∃ i : Fin 4, g4 i • z ∈ Tset := by
  simp only [S1, Set.mem_iUnion, Set.mem_inv_smul_set_iff]

theorem cover_S1 (z : UpperHalfPlane) : ∃ h ∈ QMSplitVB.Gamma1, h • z ∈ S1 := by
  obtain ⟨γ, hγ, hT⟩ := cover_T z
  obtain ⟨i, h, hh, hz⟩ := cover_mob hγ
  exact ⟨h, hh, mem_S1.2 ⟨i, by rw [← hz]; exact hT⟩⟩

theorem isCompact_S1 : IsCompact S1 :=
  isCompact_iUnion fun i => isCompact_T.smul _

theorem measurableSet_S1 : MeasurableSet S1 :=
  MeasurableSet.iUnion fun i => measurableSet_T.const_smul _

/-- `T ∩ γ⁻¹ T` for `γ = r_j h r_i⁻¹`: null unless `i = j` and `h` acts trivially. -/
theorem piece_null {i j : Fin 4} {h : GL (Fin 2) ℝ} (hh : h ∈ QMSplitVB.Gamma1)
    (hne : ¬ (i = j ∧ ∀ z : UpperHalfPlane, h • z = z)) :
    volume ((g4 i)⁻¹ • Tset ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' ((g4 j)⁻¹ • Tset)) = 0 := by
  set γ := g4 j * h * (g4 i)⁻¹ with hγdef
  have hγ : γ ∈ Γs := gs_mul (gs_mul (g4_mem j) (gamma1_sub hh)) (gs_inv (g4_mem i))
  have hγne : (fun z : UpperHalfPlane => γ • z) ≠ id := by
    intro hid
    apply hne
    have key : ∀ u : UpperHalfPlane, g4 i • u = g4 j • (h • u) := by
      intro u
      have := congrFun hid (g4 i • u)
      simp only [id, hγdef, mul_smul, inv_smul_smul] at this
      exact this.symm
    have hij : j = i := coset_eq hh key
    subst hij
    refine ⟨rfl, fun z => ?_⟩
    have := key z
    exact (smul_left_cancel _ this).symm
  have e : (g4 i)⁻¹ • Tset ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' ((g4 j)⁻¹ • Tset) =
      (fun z : UpperHalfPlane => g4 i • z) ⁻¹' (Tset ∩ (fun z : UpperHalfPlane => γ • z) ⁻¹' Tset) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_inv_smul_set_iff, hγdef, mul_smul,
      inv_smul_smul]
  rw [e, measure_preimage_smul]
  exact disjoint_T hγ hγne

theorem null_S1 {h : GL (Fin 2) ℝ} (hh : h ∈ QMSplitVB.Gamma1)
    (hne : (fun z : UpperHalfPlane => h • z) ≠ id) :
    volume (S1 ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' S1) = 0 := by
  have e : S1 ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' S1 =
      ⋃ i : Fin 4, ⋃ j : Fin 4, ((g4 i)⁻¹ • Tset ∩ (fun z : UpperHalfPlane => h • z) ⁻¹' ((g4 j)⁻¹ • Tset)) := by
    ext z
    simp only [S1, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; exact ⟨i, j, hi, hj⟩
    · rintro ⟨i, j, hi, hj⟩; exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  rw [e]
  refine measure_iUnion_null fun i => measure_iUnion_null fun j => piece_null hh ?_
  rintro ⟨-, htriv⟩
  exact hne (funext htriv)

theorem volume_S1 : volume S1 = ENNReal.ofReal (2 * Real.pi / 3) := by
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) fun i : Fin 4 => (g4 i)⁻¹ • Tset) := by
    intro i j hij
    have := piece_null (i := i) (j := j) (h := 1) one_mem_gamma1 (fun h => hij h.1)
    simpa [AEDisjoint] using this
  rw [S1, measure_iUnion₀ hdisj (fun i => (measurableSet_T.const_smul _).nullMeasurableSet),
    tsum_fintype, Fin.sum_univ_four]
  simp only [measure_smul, volume_T]
  have hp : 0 ≤ Real.pi / 6 := by positivity
  rw [← ENNReal.ofReal_add hp hp, ← ENNReal.ofReal_add (by positivity) hp,
    ← ENNReal.ofReal_add (by positivity) hp]
  congr 1; ring

/-- **Shimizu's covolume of `𝒪¹`** (`HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1`, the open leaf
`shimizuCovolumeO1`), with no hypotheses: `Γ¹` is cocompact Fuchsian with fundamental domain
`s₁ = ⋃ᵢ rᵢ⁻¹ T` of hyperbolic area `4 · π/6 = 2π/3`. -/
theorem shimizuCovolumeO1_proof : HM.QMSplit.ShimizuCovolumeO1 :=
  ⟨⟨one_mem_gamma1, fun a ha b hb => mul_mem_gamma1 ha hb, fun a ha => inv_mem_gamma1 ha,
      fun a ha => det_pos_of_mem (gamma1_sub ha),
      fun K hK => (properlyDiscontinuous K hK).subset (by
        rintro f ⟨γ, hγ, hf, hne⟩; exact ⟨γ, gamma1_sub hγ, hf, hne⟩),
      ⟨S1, isCompact_S1, cover_S1⟩⟩,
    S1, ⟨measurableSet_S1, cover_S1, fun γ hγ hne => null_S1 hγ hne⟩, volume_S1⟩

end HDec.GammaStarArea

#print axioms HDec.GammaStarArea.shimizuCovolumeO1_proof
