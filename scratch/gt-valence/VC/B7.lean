import VC.B6

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

/-- Zeros of a nonzero analytic function in a compact subset of a preconnected open set are finite. -/
theorem zeros_finite {F : ℂ → ℂ} {U : Set ℂ} (hU : IsPreconnected U) (hF : AnalyticOnNhd ℂ F U)
    (hne : ∃ z ∈ U, F z ≠ 0) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {w | w ∈ K ∧ F w = 0}.Finite := by
  have hcl : IsClosed {w | w ∈ K ∧ F w = 0} :=
    (hF.continuousOn.mono hKU).preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton
  refine (hK.of_isClosed_subset hcl fun w hw => hw.1).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [zeros_isolated hU hF hne (hKU hx.1)] with w hw h
  exact hw h.2

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

theorem stabilizer_finite (t : UpperHalfPlane) :
    Finite (MulAction.stabilizer (permG (subG hΓ)) t) := by
  have h := finite_meet hΓ (isCompact_singleton (x := t))
  refine Set.Finite.to_subtype (h.subset ?_)
  intro g hg
  exact ⟨t, ⟨t, rfl, MulAction.mem_stabilizer_iff.1 hg⟩, rfl⟩

include hΓ in
theorem ellOrder_pos (t : UpperHalfPlane) : 0 < ellOrderOf Γ t := by
  rw [← card_stabilizer hΓ t]
  have := stabilizer_finite hΓ t
  exact Nat.card_pos

/-- **Orbit counting**: the points of the orbit of `t` where `χ ≠ 0`, weighted by `e_t`, sum to `1`. -/
theorem orbit_sum {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1)
    (t : UpperHalfPlane) :
    ∃ O : Finset ℂ, (∀ w ∈ O, χ w ≠ 0 ∧ ∃ g : permG (subG hΓ), ((g • t : UpperHalfPlane) : ℂ) = w) ∧
      (∀ g : permG (subG hΓ), χ ((g • t : UpperHalfPlane) : ℂ) ≠ 0 →
        ((g • t : UpperHalfPlane) : ℂ) ∈ O) ∧
      (ellOrderOf Γ t : ℝ) * ∑ w ∈ O, χ w = 1 := by
  classical
  set St := (support_finite hΓ hχc hχU t).toFinset
  set π : permG (subG hΓ) → ℂ := fun g => ((g • t : UpperHalfPlane) : ℂ)
  refine ⟨St.image π, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨(Set.Finite.mem_toFinset _).1 hg, g, rfl⟩
  · intro g hg
    exact Finset.mem_image_of_mem π ((Set.Finite.mem_toFinset _).2 hg)
  · have h1 : ∑ g ∈ St, χ (π g) = 1 := by
      rw [← hsum t]
      exact (finsum_eq_sum_of_support_subset _ fun g hg => (Set.Finite.mem_toFinset _).2 hg).symm
    rw [← Finset.sum_fiberwise_of_maps_to' (t := St.image π) (fun g hg => Finset.mem_image_of_mem π hg)
      χ] at h1
    rw [Finset.mul_sum, ← h1]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    obtain ⟨g0, hg0, rfl⟩ := Finset.mem_image.1 hw
    have hg0' : χ (π g0) ≠ 0 := (Set.Finite.mem_toFinset _).1 hg0
    rw [← card_stabilizer hΓ t]
    norm_cast
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.symm
      { toFun := fun x => ⟨g0⁻¹ * x.1, by
          have hx := (Finset.mem_filter.1 x.2).2
          have e : x.1 • t = g0 • t := UpperHalfPlane.ext hx
          rw [MulAction.mem_stabilizer_iff, mul_smul, e, inv_smul_smul]⟩
        invFun := fun h => ⟨g0 * h.1, by
          have e : (g0 * h.1) • t = g0 • t := by
            rw [mul_smul, MulAction.mem_stabilizer_iff.1 h.2]
          have e' : π (g0 * h.1) = π g0 := by simp only [π, e]
          refine Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ?_, e'⟩
          show χ (π (g0 * h.1)) ≠ 0
          rw [e']; exact hg0'⟩
        left_inv := fun x => by simp
        right_inv := fun h => by simp }

/-- The weighted orbit sum is bounded by the total zero count (equality when `T` covers the zeros). -/
theorem orbit_count {m : ℕ} {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F {w | 0 < w.im}) (hne : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0)
    (haut : ∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖)
    {χ : ℂ → ℝ} (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ {w | 0 < w.im})
    (hχ0 : ∀ w, 0 ≤ χ w)
    (hsum : ∀ z : UpperHalfPlane, ∑ᶠ g : permG (subG hΓ), χ ((g • z : UpperHalfPlane) : ℂ) = 1)
    (T : Finset UpperHalfPlane)
    (hT : (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w)) :
    ∑ t ∈ T, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) ≤
        ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w ∧
      (Covers Γ T F → ∑ t ∈ T, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) =
        ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w) := by
  classical
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  choose O hO1 hO2 hO3 using orbit_sum hΓ hχc hχU hsum
  set B := T.biUnion O
  set f : ℂ → ℝ := fun w => ((analyticOrderAt F w).toNat : ℝ) * χ w
  -- orders along orbits
  have hordg : ∀ (g : permG (subG hΓ)) (t : UpperHalfPlane),
      analyticOrderAt F ((g • t : UpperHalfPlane) : ℂ) = analyticOrderAt F t := by
    intro g t
    rw [rep_smul]
    exact ord_smul_eq hF (rep_det hΓ g) (haut _ (rep_memΓ hΓ g)) t
  have hterm : ∀ t : UpperHalfPlane, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) =
      ∑ w ∈ O t, f w := by
    intro t
    have he : (0 : ℝ) < ellOrderOf Γ t := by exact_mod_cast ellOrder_pos hΓ t
    have hsumO : ∑ w ∈ O t, χ w = 1 / (ellOrderOf Γ t : ℝ) := by
      rw [eq_div_iff he.ne', mul_comm]; exact hO3 t
    have : ∑ w ∈ O t, f w = ((analyticOrderAt F (t : ℂ)).toNat : ℝ) * ∑ w ∈ O t, χ w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w hw => ?_
      obtain ⟨-, g, rfl⟩ := hO1 t w hw
      simp only [f, hordg]
    rw [this, hsumO]; ring
  have hdisj : (T : Set UpperHalfPlane).PairwiseDisjoint O := by
    intro t ht t' ht' hne'
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw hw'
    obtain ⟨-, g, rfl⟩ := hO1 t w hw
    obtain ⟨-, g', hg'⟩ := hO1 t' _ hw'
    have e : (g'⁻¹ * g) • t = t' := by
      rw [mul_smul, UpperHalfPlane.ext hg'.symm, inv_smul_smul]
    rw [rep_smul] at e
    exact hT ht ht' hne' _ (rep_memΓ hΓ _) e
  have hsumT : ∑ t ∈ T, ((analyticOrderAt F (t : ℂ)).toNat : ℝ) / (ellOrderOf Γ t : ℝ) =
      ∑ w ∈ B, f w := by
    rw [Finset.sum_biUnion hdisj]
    exact Finset.sum_congr rfl fun t _ => hterm t
  -- finiteness of the support
  have hZ : (Function.support f).Finite := by
    refine (zeros_finite hUc hF hne hχc hχU).subset ?_
    intro w hw
    simp only [Function.mem_support, f, ne_eq, mul_eq_zero, not_or] at hw
    refine ⟨subset_tsupport _ hw.2, ?_⟩
    by_contra h
    apply hw.1
    rw [analyticOrderAt_eq_zero.2 (Or.inr h)]; simp
  have hf0 : ∀ w, 0 ≤ f w := fun w => mul_nonneg (Nat.cast_nonneg _) (hχ0 w)
  refine ⟨?_, fun hc => ?_⟩
  · rw [hsumT, finsum_eq_sum_of_support_subset f (s := B ∪ hZ.toFinset) (by
      intro w hw; simp only [Finset.coe_union, Set.Finite.coe_toFinset]; exact Or.inr hw)]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun w _ _ => hf0 w)
  · rw [hsumT, finsum_eq_sum_of_support_subset f (s := B) ?_]
    intro w hw
    simp only [Function.mem_support, f, ne_eq, mul_eq_zero, not_or] at hw
    have hwU : 0 < w.im := hχU (subset_tsupport _ hw.2)
    have hFw : F w = 0 := by
      by_contra h
      apply hw.1
      rw [analyticOrderAt_eq_zero.2 (Or.inr h)]; simp
    obtain ⟨t, ht, γ, hγ, e⟩ := hc ⟨w, hwU⟩ hFw
    have hg : ((⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩ : permG (subG hΓ)) • t : UpperHalfPlane) =
        ⟨w, hwU⟩ := e
    have := hO2 t ⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩ (by rw [hg]; exact hw.2)
    rw [hg] at this
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, B]
    exact ⟨t, ht, this⟩

end ValenceCocompact
