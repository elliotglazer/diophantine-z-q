import VC.B7

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace ValenceCocompact

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

include hΓ in
/-- The zeros lie in finitely many orbits: a finite set of pairwise inequivalent representatives. -/
theorem exists_reps {m : ℕ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F {w | 0 < w.im})
    (hne : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0)
    (haut : ∀ γ ∈ Γ, ∀ z : UpperHalfPlane,
      ‖F ((γ • z : UpperHalfPlane) : ℂ)‖ * ((γ : Matrix (Fin 2) (Fin 2) ℝ).det) ^ m =
        ‖UpperHalfPlane.denom γ z‖ ^ (2 * m) * ‖F (z : ℂ)‖) :
    ∃ T : Finset UpperHalfPlane, (T : Set UpperHalfPlane).Pairwise (fun z w => ∀ γ ∈ Γ, γ • z ≠ w) ∧
      Covers Γ T F := by
  classical
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨C, hC, hcov⟩ := hΓ.cocompact
  have hC' : IsCompact (((↑) : UpperHalfPlane → ℂ) '' C) := hC.image UpperHalfPlane.continuous_coe
  have hCU : ((↑) : UpperHalfPlane → ℂ) '' C ⊆ {w | 0 < w.im} := by
    rintro _ ⟨z, _, rfl⟩; exact z.im_pos
  have hZfin : {z : UpperHalfPlane | z ∈ C ∧ F z = 0}.Finite := by
    refine Set.Finite.of_finite_image ((zeros_finite hUc hF hne hC' hCU).subset ?_)
      UpperHalfPlane.coe_injective.injOn
    rintro _ ⟨z, ⟨hz, hFz⟩, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, hFz⟩
  set Zc := hZfin.toFinset
  let R : UpperHalfPlane → UpperHalfPlane → Prop := fun a b => ∃ γ ∈ Γ, γ • a = b
  have Rrefl : ∀ a, R a a := fun a => ⟨1, hΓ.one_mem, one_smul _ a⟩
  have Rsymm : ∀ a b, R a b → R b a := by
    rintro a b ⟨γ, hγ, rfl⟩; exact ⟨γ⁻¹, hΓ.inv_mem _ hγ, inv_smul_smul γ a⟩
  have Rtrans : ∀ a b c, R a b → R b c → R a c := by
    rintro a b c ⟨γ, hγ, rfl⟩ ⟨δ, hδ, rfl⟩
    exact ⟨δ * γ, hΓ.mul_mem _ hδ _ hγ, mul_smul δ γ a⟩
  let r : UpperHalfPlane → UpperHalfPlane := fun z => Classical.epsilon fun w => w ∈ Zc ∧ R w z
  have hr : ∀ z ∈ Zc, r z ∈ Zc ∧ R (r z) z := fun z hz =>
    Classical.epsilon_spec (p := fun w => w ∈ Zc ∧ R w z) ⟨z, hz, Rrefl z⟩
  have hr_eq : ∀ z z', R z z' → r z = r z' := by
    intro z z' h
    have : (fun w => w ∈ Zc ∧ R w z) = fun w => w ∈ Zc ∧ R w z' := by
      funext w
      apply propext
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, Rtrans _ _ _ h2 h⟩,
        fun ⟨h1, h2⟩ => ⟨h1, Rtrans _ _ _ h2 (Rsymm _ _ h)⟩⟩
    simp only [r, this]
  refine ⟨Zc.image r, ?_, ?_⟩
  · intro a ha b hb hab γ hγ e
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨z, hz, rfl⟩ := ha
    obtain ⟨z', hz', rfl⟩ := hb
    apply hab
    apply hr_eq
    exact Rtrans _ _ _ (Rsymm _ _ (hr z hz).2) (Rtrans _ _ _ ⟨γ, hγ, e⟩ (hr z' hz').2)
  · intro x hx
    obtain ⟨γ, hγ, hxC⟩ := hcov x
    have hFγ : F ((γ • x : UpperHalfPlane) : ℂ) = 0 := by
      have := haut γ hγ x
      rw [hx, norm_zero, mul_zero] at this
      have hd : (γ : Matrix (Fin 2) (Fin 2) ℝ).det ^ m ≠ 0 := pow_ne_zero _ (hΓ.det_pos γ hγ).ne'
      exact norm_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hd)
    have hz : γ • x ∈ Zc := (Set.Finite.mem_toFinset _).2 ⟨hxC, hFγ⟩
    refine ⟨r (γ • x), Finset.mem_image_of_mem r hz, ?_⟩
    have h1 : R (r (γ • x)) x := Rtrans _ _ _ (hr _ hz).2 (Rsymm _ _ ⟨γ, hγ, rfl⟩)
    exact h1

theorem enn_term {o : ℕ∞} (ho : o ≠ ⊤) {e : ℕ} (he : 0 < e) :
    ((o : ℕ∞) : ℝ≥0∞) / (e : ℝ≥0∞) = ENNReal.ofReal ((o.toNat : ℝ) / e) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast he)]
  conv_lhs => rw [← ENat.natCast_toNat ho]
  simp

theorem enn_rhs (m : ℕ) {v : ℝ≥0∞} (hv : v ≠ ⊤) :
    (2 * m : ℝ≥0∞) * v / ENNReal.ofReal (4 * Real.pi) =
      ENNReal.ofReal (2 * m * v.toReal / (4 * Real.pi)) := by
  have h1 : ENNReal.ofReal (2 * m * v.toReal) = 2 * m * v := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hv,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_div_of_pos (by positivity), h1]

/-- **The valence formula for a cocompact Fuchsian group** (Shimura 1971, Prop. 2.16 and Thm. 2.20),
in the equality form of the single proof. -/
theorem valenceFormulaCocompactEq_proof : HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq := by
  intro Γ hΓ s hs m F hF hne haut
  have hF' : AnalyticOnNhd ℂ F {w | 0 < w.im} := hF
  have hne' : ∃ z ∈ {w : ℂ | 0 < w.im}, F z ≠ 0 := hne
  have hUc : IsPreconnected {w : ℂ | 0 < w.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨χ, hχ, hχc, hχU, hχ0, hsum⟩ := exists_partition hΓ
  obtain ⟨hfin, hid⟩ := main_identity hΓ hs hF' hne' haut hχ hχc hχU hχ0 hsum
  have hval : ∑ᶠ w, ((analyticOrderAt F w).toNat : ℝ) * χ w =
      2 * m * (volume s).toReal / (4 * Real.pi) := by
    field_simp
    linarith
  have hconv : ∀ T : Finset UpperHalfPlane,
      ∑ z ∈ T, ((analyticOrderAt F (z : ℂ) : ℕ∞) : ℝ≥0∞) / (ellOrderOf Γ z : ℝ≥0∞) =
        ENNReal.ofReal (∑ z ∈ T, ((analyticOrderAt F (z : ℂ)).toNat : ℝ) / (ellOrderOf Γ z : ℝ)) := by
    intro T
    rw [ENNReal.ofReal_sum_of_nonneg (fun z _ => by positivity)]
    refine Finset.sum_congr rfl fun z _ => ?_
    exact enn_term (order_ne_top hUc hF' hne' z.im_pos) (ellOrder_pos hΓ z)
  refine ⟨exists_reps hΓ hF' hne' haut, fun T hT hc => ?_, fun T hT => ?_⟩
  · rw [hconv, enn_rhs m hfin, ← hval, ((orbit_count hΓ hF' hne' haut hχc hχU hχ0 hsum T hT).2 hc)]
  · rw [hconv, enn_rhs m hfin, ← hval]
    exact ENNReal.ofReal_le_ofReal (orbit_count hΓ hF' hne' haut hχc hχU hχ0 hsum T hT).1

end ValenceCocompact

#print axioms ValenceCocompact.valenceFormulaCocompactEq_proof
