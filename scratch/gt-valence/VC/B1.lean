import ZInQKernel.OneProof.H.TailZ2
import VC.A6

open MeasureTheory InnerProductSpace Complex Set Filter Topology Laplacian Metric
open scoped Pointwise

noncomputable section

namespace ValenceCocompact

/-- The Möbius map of `γ` on `ℂ`. -/
def mob (γ : GL (Fin 2) ℝ) (w : ℂ) : ℂ := UpperHalfPlane.num γ w / UpperHalfPlane.denom γ w

theorem det_val_eq (γ : GL (Fin 2) ℝ) :
    (γ.det : ℝ) = (γ : Matrix (Fin 2) (Fin 2) ℝ).det := Matrix.GeneralLinearGroup.val_det_apply γ

theorem coe_smul_eq_mob {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    (z : UpperHalfPlane) : ((γ • z : UpperHalfPlane) : ℂ) = mob γ z :=
  UpperHalfPlane.coe_smul_of_det_pos (by rw [det_val_eq]; exact hγ) z

theorem denom_ne {γ : GL (Fin 2) ℝ} {w : ℂ} (hw : 0 < w.im) : UpperHalfPlane.denom γ w ≠ 0 :=
  UpperHalfPlane.denom_ne_zero_of_im γ hw.ne'

theorem hasDerivAt_mob (γ : GL (Fin 2) ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasDerivAt (mob γ) (((γ : Matrix (Fin 2) (Fin 2) ℝ).det : ℂ) / UpperHalfPlane.denom γ w ^ 2) w := by
  have h1 : HasDerivAt (fun w : ℂ => UpperHalfPlane.num γ w) ((γ 0 0 : ℝ) : ℂ) w := by
    simpa [UpperHalfPlane.num] using
      ((hasDerivAt_id w).const_mul ((γ 0 0 : ℝ) : ℂ)).add_const ((γ 0 1 : ℝ) : ℂ)
  have h2 : HasDerivAt (fun w : ℂ => UpperHalfPlane.denom γ w) ((γ 1 0 : ℝ) : ℂ) w := by
    simpa [UpperHalfPlane.denom] using
      ((hasDerivAt_id w).const_mul ((γ 1 0 : ℝ) : ℂ)).add_const ((γ 1 1 : ℝ) : ℂ)
  have := h1.fun_div h2 (denom_ne hw)
  have e : mob γ = fun y => UpperHalfPlane.num γ y / UpperHalfPlane.denom γ y := rfl
  rw [e]
  convert this using 1
  rw [Matrix.det_fin_two]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  push_cast
  ring

theorem analyticAt_mob (γ : GL (Fin 2) ℝ) {w : ℂ} (hw : 0 < w.im) : AnalyticAt ℂ (mob γ) w := by
  unfold mob UpperHalfPlane.num UpperHalfPlane.denom
  apply AnalyticAt.div (by fun_prop) (by fun_prop)
  exact denom_ne hw

theorem mob_im {γ : GL (Fin 2) ℝ} (w : ℂ) :
    (mob γ w).im = (γ : Matrix (Fin 2) (Fin 2) ℝ).det * w.im /
      Complex.normSq (UpperHalfPlane.denom γ w) := by
  rw [mob, UpperHalfPlane.moebius_im, det_val_eq]

theorem mob_im_pos {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det) {w : ℂ}
    (hw : 0 < w.im) : 0 < (mob γ w).im := by
  rw [mob_im]
  exact div_pos (mul_pos hγ hw) (Complex.normSq_pos.2 (denom_ne hw))

theorem norm_deriv_mob_sq {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {w : ℂ} (hw : 0 < w.im) :
    ‖deriv (mob γ) w‖ ^ 2 * w.im ^ 2 = (mob γ w).im ^ 2 := by
  rw [(hasDerivAt_mob γ hw).deriv, mob_im, norm_div, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hγ.le]
  have hd := denom_ne (γ := γ) hw
  have hn : ‖UpperHalfPlane.denom γ w‖ ^ 2 = Complex.normSq (UpperHalfPlane.denom γ w) :=
    Complex.sq_norm _
  have hpos : 0 < ‖UpperHalfPlane.denom γ w‖ := norm_pos_iff.2 hd
  rw [← hn]
  field_simp

/-- Conformal invariance of `y² Δ` under `γ ∈ GL₂⁺(ℝ)`. -/
theorem im_sq_laplacian_comp_mob {γ : GL (Fin 2) ℝ} (hγ : 0 < (γ : Matrix (Fin 2) (Fin 2) ℝ).det)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) {w : ℂ} (hw : 0 < w.im) :
    w.im ^ 2 * Δ (χ ∘ mob γ) w = (mob γ w).im ^ 2 * Δ χ (mob γ w) := by
  rw [laplacian_comp_holomorphic (analyticAt_mob γ hw) hχ.contDiffAt, ← norm_deriv_mob_sq hγ hw]
  ring

/-! ## The group of Möbius maps of `Γ` -/

open HDec.LeafQCheck.HM.QMSplit (IsCocompactFuchsian IsFundDomain ellOrderOf Covers)

/-- `Γ` as a subgroup. -/
def subG {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ) : Subgroup (GL (Fin 2) ℝ) where
  carrier := Γ
  mul_mem' ha hb := hΓ.mul_mem _ ha _ hb
  one_mem' := hΓ.one_mem
  inv_mem' ha := hΓ.inv_mem _ ha

/-- The group of Möbius transformations of `H` (a subgroup of `Perm ℍ`). -/
def permG (H : Subgroup (GL (Fin 2) ℝ)) : Subgroup (Equiv.Perm UpperHalfPlane) :=
  H.map (MulAction.toPermHom (GL (Fin 2) ℝ) UpperHalfPlane)

theorem mem_permG {H : Subgroup (GL (Fin 2) ℝ)} {σ : Equiv.Perm UpperHalfPlane} :
    σ ∈ permG H ↔ ∃ γ ∈ H, ∀ z, σ z = γ • z := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩; exact ⟨γ, hγ, fun z => rfl⟩
  · rintro ⟨γ, hγ, h⟩; exact ⟨γ, hγ, Equiv.ext fun z => (h z).symm⟩

theorem smul_def {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) (z : UpperHalfPlane) :
    g • z = (g : Equiv.Perm UpperHalfPlane) z := rfl

/-- A representative matrix. -/
def rep {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) : GL (Fin 2) ℝ :=
  Classical.choose (mem_permG.1 g.2)

theorem rep_mem {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) : rep g ∈ H :=
  (Classical.choose_spec (mem_permG.1 g.2)).1

theorem rep_smul {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) (z : UpperHalfPlane) :
    g • z = rep g • z :=
  (Classical.choose_spec (mem_permG.1 g.2)).2 z

theorem smul_fun_eq {H : Subgroup (GL (Fin 2) ℝ)} (g : permG H) :
    (fun z : UpperHalfPlane => g • z) = fun z => rep g • z := funext (rep_smul g)

instance (H : Subgroup (GL (Fin 2) ℝ)) : MeasurableConstSMul (permG H) UpperHalfPlane :=
  ⟨fun g => by
    rw [smul_fun_eq g]
    exact (continuous_const_smul (rep g)).measurable⟩

instance (H : Subgroup (GL (Fin 2) ℝ)) :
    SMulInvariantMeasure (permG H) UpperHalfPlane volume :=
  ⟨fun g s hs => by
    rw [smul_fun_eq g]
    exact measure_preimage_smul (μ := (volume : Measure UpperHalfPlane)) (rep g) s⟩

theorem toPerm_mem {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ) {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ Γ) : MulAction.toPerm γ ∈ permG (subG hΓ) := ⟨γ, hγ, rfl⟩

variable {Γ : Set (GL (Fin 2) ℝ)} (hΓ : IsCocompactFuchsian Γ)

theorem rep_memΓ (g : permG (subG hΓ)) : rep g ∈ Γ := rep_mem g

theorem rep_det (g : permG (subG hΓ)) : 0 < (rep g : Matrix (Fin 2) (Fin 2) ℝ).det :=
  hΓ.det_pos _ (rep_mem g)

theorem finite_meet {K : Set UpperHalfPlane} (hK : IsCompact K) :
    {g : permG (subG hΓ) | ((fun z => g • z) '' K ∩ K).Nonempty}.Finite := by
  have h := hΓ.properlyDiscontinuous K hK
  refine (h.preimage (f := fun g : permG (subG hΓ) => fun z => g • z) ?_).subset ?_
  · intro g _ h _ e
    apply Subtype.ext; apply Equiv.ext; intro z
    exact congrFun e z
  · intro g hg
    exact ⟨rep g, rep_mem g, smul_fun_eq g, hg⟩

theorem countable_G : Countable (permG (subG hΓ)) := by
  set z0 : UpperHalfPlane := UpperHalfPlane.I
  have hU : (Set.univ : Set (permG (subG hΓ))) ⊆
      ⋃ n, {g | ((fun z => g • z) '' (compactCovering UpperHalfPlane n ∪ {z0}) ∩
        (compactCovering UpperHalfPlane n ∪ {z0})).Nonempty} := by
    intro g _
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ((iUnion_compactCovering UpperHalfPlane).symm ▸
      Set.mem_univ (g • z0))
    exact Set.mem_iUnion.2 ⟨n, ⟨g • z0, ⟨z0, Or.inr rfl, rfl⟩, Or.inl hn⟩⟩
  have : (Set.univ : Set (permG (subG hΓ))).Countable :=
    (Set.countable_iUnion fun n =>
      (finite_meet hΓ ((isCompact_compactCovering UpperHalfPlane n).union
        isCompact_singleton)).countable).mono hU
  exact Set.countable_univ_iff.1 this

theorem isFundamentalDomain {s : Set UpperHalfPlane} (hs : IsFundDomain Γ s) :
    IsFundamentalDomain (permG (subG hΓ)) s volume := by
  refine IsFundamentalDomain.mk'' hs.1.nullMeasurableSet ?_ ?_ ?_
  · refine Eventually.of_forall fun z => ?_
    obtain ⟨γ, hγ, hz⟩ := hs.2.1 z
    exact ⟨⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩, hz⟩
  · intro g hg
    have hg' : g⁻¹ ≠ 1 := inv_ne_one.2 hg
    have hne : (fun z : UpperHalfPlane => rep g⁻¹ • z) ≠ id := by
      intro h; apply hg'
      apply Subtype.ext; apply Equiv.ext; intro z
      simp only [← smul_def, rep_smul, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq]
      exact congrFun h z
    have h0 := hs.2.2 (rep g⁻¹) (rep_mem g⁻¹) hne
    rw [← smul_fun_eq] at h0
    have : g • s = (fun z => g⁻¹ • z) ⁻¹' s := by
      ext z; simp [Set.mem_smul_set_iff_inv_smul_mem]
    rw [AEDisjoint, this, Set.inter_comm]
    exact h0
  · intro g
    exact (measurePreserving_smul g volume).quasiMeasurePreserving

theorem card_stabilizer (t : UpperHalfPlane) :
    Nat.card (MulAction.stabilizer (permG (subG hΓ)) t) = ellOrderOf Γ t := by
  unfold ellOrderOf
  apply Nat.card_congr
  let φ : MulAction.stabilizer (permG (subG hΓ)) t →
      {f : UpperHalfPlane → UpperHalfPlane // ∃ γ ∈ Γ, γ • t = t ∧ f = fun z => γ • z} :=
    fun g => ⟨fun z => (g : permG (subG hΓ)) • z, rep (g : permG (subG hΓ)), rep_memΓ hΓ _,
      (rep_smul (g : permG (subG hΓ)) t).symm.trans (MulAction.mem_stabilizer_iff.1 g.2),
      smul_fun_eq _⟩
  refine Equiv.ofBijective φ ⟨?_, ?_⟩
  · intro g h e
    have e' : (fun z => (g : permG (subG hΓ)) • z) = fun z => (h : permG (subG hΓ)) • z :=
      congrArg Subtype.val e
    apply Subtype.ext; apply Subtype.ext; apply Equiv.ext; intro z
    exact congrFun e' z
  · rintro ⟨f, γ, hγ, ht, rfl⟩
    refine ⟨⟨⟨MulAction.toPerm γ, toPerm_mem hΓ hγ⟩, MulAction.mem_stabilizer_iff.2 ht⟩, rfl⟩

end ValenceCocompact
