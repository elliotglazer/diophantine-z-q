import VC.B1

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise Manifold ContDiff

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

theorem isCompact_preimage_coe {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ {w | 0 < w.im}) :
    IsCompact ((↑) ⁻¹' K : Set UpperHalfPlane) := by
  rw [UpperHalfPlane.isOpenEmbedding_coe.isInducing.isCompact_preimage_iff]
  · exact hK
  · intro w hw; exact ⟨⟨w, hKU hw⟩, rfl⟩

theorem exists_bump {C : Set UpperHalfPlane} (hC : IsCompact C) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ {w | 0 < w.im} ∧
      (∀ w, 0 ≤ ψ w) ∧ ∀ z ∈ C, ψ (z : ℂ) = 1 := by
  have hC' : IsCompact (((↑) : UpperHalfPlane → ℂ) '' C) := hC.image UpperHalfPlane.continuous_coe
  have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hCU : ((↑) : UpperHalfPlane → ℂ) '' C ⊆ {w | 0 < w.im} := by
    rintro _ ⟨z, _, rfl⟩; exact z.im_pos
  obtain ⟨W, hWo, hCW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hC' hU hCU
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℂ)
    hWo.isClosed_compl hC'.isClosed (n := 2)
    (Set.disjoint_left.2 fun w hw hwC => hw (hCW hwC))
  have hsupp : tsupport f ⊆ closure W := by
    apply closure_mono
    intro w hw
    by_contra h
    exact hw (hf0 h)
  refine ⟨f, f.contMDiff.contDiff, hWc.of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans hWU, fun w => (hf01 w).1, fun z hz => hf1 ⟨z, hz, rfl⟩⟩

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

/-- Local finiteness: on a compact set, only finitely many translates of a compactly supported `χ`
are nonzero. -/
theorem locally_finite {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ S : Finset (permG (subG hΓ)), ∀ z ∈ K, ∀ g : permG (subG hΓ),
      (χ ((g • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S) ∧ (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S) := by
  have hL := isCompact_preimage_coe hχc hχU
  set L := ((↑) ⁻¹' tsupport χ : Set UpperHalfPlane)
  refine ⟨(finite_meet hΓ (hK.union hL)).toFinset, fun z hz g => ⟨fun h => ?_, fun h => ?_⟩⟩
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨g • z, ⟨z, Or.inl hz, rfl⟩, Or.inr (subset_tsupport _ h)⟩
  · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact ⟨z, ⟨g⁻¹ • z, Or.inr (subset_tsupport _ h), smul_inv_smul g z⟩, Or.inl hz⟩

theorem support_finite {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (z : UpperHalfPlane) :
    (Function.support fun g : permG (subG hΓ) => χ ((g • z : UpperHalfPlane) : ℂ)).Finite := by
  obtain ⟨S, hS⟩ := locally_finite hΓ hχc hχU (isCompact_singleton (x := z))
  exact S.finite_toSet.subset fun g hg => (hS z rfl g).1 hg

theorem finsum_eq_sum {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    {K : Set UpperHalfPlane} {S : Finset (permG (subG hΓ))}
    (hS : ∀ z ∈ K, ∀ g : permG (subG hΓ), (χ ((g • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S) ∧
      (χ ((g⁻¹ • z : UpperHalfPlane) : ℂ) ≠ 0 → g ∈ S)) {z : UpperHalfPlane} (hz : z ∈ K) :
    ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) =
      ∑ g ∈ S, χ ((g • z : UpperHalfPlane) : ℂ) :=
  finsum_eq_sum_of_support_subset _ fun g hg => (hS z hz g).1 hg

theorem finsum_smul_invariant (φ : UpperHalfPlane → ℝ) (h z : UpperHalfPlane) (k : permG (subG hΓ))
    (hk : k • z = h) :
    ∑ᶠ g : permG (subG hΓ), φ (g • h) = ∑ᶠ g : permG (subG hΓ), φ (g • z) := by
  rw [← hk]
  simp_rw [smul_smul]
  exact finsum_comp_equiv (Equiv.mulRight k) (f := fun g => φ (g • z))

theorem rep_smul_coe (g : permG (subG hΓ)) {w : ℂ} (hw : 0 < w.im) :
    ((g • (⟨w, hw⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) = mob (rep g) w := by
  rw [rep_smul, coe_smul_eq_mob (rep_det hΓ g)]

/-- **Automorphic partition of unity.** -/
theorem exists_partition :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ {w | 0 < w.im} ∧
      (∀ w, 0 ≤ χ w) ∧ ∀ z : UpperHalfPlane,
        ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1 := by
  obtain ⟨C, hC, hcov⟩ := hΓ.cocompact
  obtain ⟨ψ, hψ, hψc, hψU, hψ0, hψ1⟩ := exists_bump hC
  set Ψ : UpperHalfPlane → ℝ := fun z => ∑ᶠ g : permG (subG hΓ), ψ ((g • z : UpperHalfPlane) : ℂ)
  have hΨpos : ∀ z, 1 ≤ Ψ z := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hcov z
    have := single_le_finsum (f := fun g : permG (subG hΓ) => ψ ((g • z : UpperHalfPlane) : ℂ))
      ⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩ (support_finite hΓ hψc hψU z) (fun g => hψ0 _)
    rw [smul_def] at this
    simp only [MulAction.toPerm_apply] at this
    rw [hψ1 _ hz] at this
    exact this
  have hΨinv : ∀ (k : permG (subG hΓ)) z, Ψ (k • z) = Ψ z := fun k z =>
    finsum_smul_invariant hΓ (fun x => ψ (x : ℂ)) _ z k rfl
  set χ : ℂ → ℝ := fun w => ψ w / Ψ (UpperHalfPlane.ofComplex w)
  have hχsupp : Function.support χ ⊆ Function.support ψ := by
    intro w hw h; apply hw; simp only [χ, h, zero_div]
  have hχts : tsupport χ ⊆ tsupport ψ := closure_mono hχsupp
  refine ⟨χ, ?_, hψc.of_isClosed_subset (isClosed_tsupport _) hχts, hχts.trans hψU,
    fun w => div_nonneg (hψ0 w) (by linarith [hΨpos (UpperHalfPlane.ofComplex w)]), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro w0
    by_cases hw0 : 0 < w0.im
    · -- local finite sum
      have hball : closedBall w0 (w0.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
        intro w hw
        rw [mem_closedBall, dist_eq_norm] at hw
        have := (abs_im_le_norm (w - w0)).trans hw
        simp only [sub_im, Set.mem_ofPred_eq] at this ⊢
        rw [abs_le] at this; linarith
      obtain ⟨S, hS⟩ := locally_finite hΓ hψc hψU
        (isCompact_preimage_coe (isCompact_closedBall w0 (w0.im / 2)) hball)
      have hev : χ =ᶠ[𝓝 w0] fun w => ψ w / ∑ g ∈ S, ψ (mob (rep g) w) := by
        filter_upwards [closedBall_mem_nhds w0 (by linarith : 0 < w0.im / 2)] with w hw
        have hwim : 0 < w.im := hball hw
        simp only [χ]
        congr 1
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hwim]
        simp only [Ψ]
        rw [finsum_eq_sum hΓ hψc hψU hS (z := ⟨w, hwim⟩) hw]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [rep_smul_coe hΓ g hwim]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hev
      have hden : (∑ g ∈ S, ψ (mob (rep g) w0)) ≠ 0 := by
        have := hΨpos ⟨w0, hw0⟩
        simp only [Ψ] at this
        rw [finsum_eq_sum hΓ hψc hψU hS (z := ⟨w0, hw0⟩) (mem_closedBall_self (by linarith))] at this
        simp_rw [rep_smul_coe hΓ _ hw0] at this
        linarith
      refine hψ.contDiffAt.div ?_ hden
      refine ContDiffAt.sum fun g _ => hψ.contDiffAt.comp w0 ?_
      exact (analyticAt_mob (rep g) hw0).contDiffAt.restrict_scalars ℝ
    · have hnot : w0 ∉ tsupport ψ := fun h => hw0 (hψU h)
      have hev : χ =ᶠ[𝓝 w0] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hnot] with w hw
        simp only [χ, hw, Pi.zero_apply, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · intro z
    have e : ∀ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) =
        ψ ((g • z : UpperHalfPlane) : ℂ) * (Ψ z)⁻¹ := by
      intro g
      simp only [χ, UpperHalfPlane.ofComplex_apply, hΨinv, div_eq_mul_inv]
    simp_rw [e]
    rw [← finsum_mul]
    exact mul_inv_cancel₀ (by linarith [hΨpos z])

end ValenceCocompact
