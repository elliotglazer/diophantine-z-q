
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §5g. `s⁻¹𝔞 = (𝔞 : 𝔍_s)` with `𝔍_s = K ∩ s_f·Ô_O` (adelic, proved) -/

section Colon

variable {m : ℕ} [NeZero m]

/-- The order `O = ℤ + f𝓞_K`, as a `ℤ`-submodule of `K`. -/
def Osub (m f : ℕ) [NeZero m] [NeZero f] : Submodule ℤ (QNeg m) :=
  ((conductorOrder (QNeg m) f).toSubalgebra.toSubmodule).restrictScalars ℤ

theorem mem_Osub {f : ℕ} [NeZero f] {x : QNeg m} :
    x ∈ Osub m f ↔ x ∈ (conductorOrder (QNeg m) f).toSubalgebra := Iff.rfl

/-- **`𝔍_s = K ∩ s_f·Ô_O`**: the `O`-lattice of the idele `s` (`Ô_O` the closure of `O`). -/
def idealOf (m f : ℕ) [NeZero m] [NeZero f] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    Set (QNeg m) :=
  {j | finPart s⁻¹ * algebraMap (QNeg m) (AfK m) j ∈ latHat m (Osub m f : Set (QNeg m))}

/-- The colon lattice `(𝔞 : 𝔍) = {y : 𝔍y ⊆ 𝔞}`. -/
def colon (𝔞 𝔍 : Set (QNeg m)) : Set (QNeg m) := {y | ∀ j ∈ 𝔍, j * y ∈ 𝔞}

theorem finPart_inv_mul (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s⁻¹ * finPart s = 1 := by
  simp only [finPart]
  rw [← Prod.snd_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Prod.snd_one]

theorem finPart_mul_inv (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s * finPart s⁻¹ = 1 := by
  simp only [finPart]
  rw [← Prod.snd_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Prod.snd_one]

/-- `Ô_O·𝔞̂ ⊆ 𝔞̂` for an `O`-stable `𝔞`. -/
theorem latHat_O_mul {f : ℕ} [NeZero f] (𝔞 : Submodule ℤ (QNeg m))
    (h𝔞 : ∀ o ∈ Osub m f, ∀ y ∈ 𝔞, o * y ∈ 𝔞) {z w : AfK m}
    (hz : z ∈ latHat m (Osub m f : Set (QNeg m))) (hw : w ∈ latHat m (𝔞 : Set (QNeg m))) :
    z * w ∈ latHat m (𝔞 : Set (QNeg m)) := by
  refine map_mem_closure₂ continuous_mul hz hw ?_
  rintro _ ⟨o, ho, rfl⟩ _ ⟨y, hy, rfl⟩
  exact ⟨o * y, h𝔞 o ho y hy, map_mul _ _ _⟩

/-- `f·𝒪̂ ⊆ Ô_O`. -/
theorem fIntAd_sub_latHatO {f : ℕ} [NeZero f] {z : AfK m}
    (hz : algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z ∈
      FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)) :
    z ∈ latHat m (Osub m f : Set (QNeg m)) := by
  have hf0 : (f : QNeg m) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hcl := FiniteAdeleRing.closure_range_algebraMap (𝓞 (QNeg m)) (QNeg m)
  have hz' := (Set.ext_iff.1 hcl (algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z)).2 hz
  have hcont : Continuous fun w : AfK m => algebraMap (QNeg m) (AfK m) (f : QNeg m) * w :=
    continuous_const.mul continuous_id
  have h1 := image_closure_subset_closure_image hcont ⟨_, hz', rfl⟩
  have hzeq : algebraMap (QNeg m) (AfK m) (f : QNeg m) *
      (algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z) = z := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one, one_mul]
  beta_reduce at h1
  rw [hzeq] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  refine ⟨(f : QNeg m) * (r : QNeg m), ?_, ?_⟩
  · show (f : QNeg m) * (r : QNeg m) ∈ (conductorOrder (QNeg m) f).toSubalgebra
    rw [conductorOrder_toSubalgebra, mem_conductorOrderSubalgebra]
    exact ⟨0, r, by simp⟩
  · rw [map_mul] <;> rfl

/-- **Density**: `s_f` lies in the closure of `𝔍_s`. -/
theorem finPart_mem_closure_idealOf {f : ℕ} [NeZero f] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    finPart s ∈ closure (algebraMap (QNeg m) (AfK m) '' idealOf m f s) := by
  set W : Set (AfK m) := (fun z => algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) *
    (finPart s⁻¹ * z - 1)) ⁻¹' (FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) : Set (AfK m))
  have hWo : IsOpen W := (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
    (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const))
  have hsW : finPart s ∈ W := by
    show algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (finPart s⁻¹ * finPart s - 1) ∈
      FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)
    rw [finPart_inv_mul, sub_self, mul_zero]
    exact Subalgebra.zero_mem _
  have h1O : algebraMap (QNeg m) (AfK m) 1 ∈ latHat m (Osub m f : Set (QNeg m)) :=
    mem_latHat_of_mem (show (1 : QNeg m) ∈ (conductorOrder (QNeg m) f).toSubalgebra from
      Subalgebra.one_mem _)
  have hWsub : ∀ z ∈ W, finPart s⁻¹ * z ∈ latHat m (Osub m f : Set (QNeg m)) := by
    intro z hz
    have h2 := fIntAd_sub_latHatO (m := m) (f := f) hz
    have e : finPart s⁻¹ * z = (finPart s⁻¹ * z - 1) + algebraMap (QNeg m) (AfK m) 1 := by
      rw [map_one]; ring
    rw [e]
    exact latHat_add_mem _ h2 h1O
  rw [mem_closure_iff]
  intro U hU hsU
  obtain ⟨j, hj⟩ := (FiniteAdeleRing.denseRange_algebraMap (𝓞 (QNeg m)) (QNeg m)).exists_mem_open
    (hU.inter hWo) ⟨_, hsU, hsW⟩
  exact ⟨_, hj.1, j, hWsub _ hj.2, rfl⟩

/-- **`s⁻¹𝔞 = (𝔞 : 𝔍_s)`** for an `O`-stable `𝔞` with `K ∩ 𝔞̂ = 𝔞`. -/
theorem sInvLat_eq_colon {f : ℕ} [NeZero f] (𝔞 : Submodule ℤ (QNeg m))
    (h𝔞 : ∀ o ∈ Osub m f, ∀ y ∈ 𝔞, o * y ∈ 𝔞)
    (hInt : ∀ x : QNeg m, algebraMap (QNeg m) (AfK m) x ∈ latHat m (𝔞 : Set (QNeg m)) → x ∈ 𝔞)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    sInvLat m s (𝔞 : Set (QNeg m)) = colon (𝔞 : Set (QNeg m)) (idealOf m f s) := by
  ext y
  constructor
  · intro hy j hj
    apply hInt
    have e : algebraMap (QNeg m) (AfK m) (j * y) =
        (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) j) * (finPart s * algebraMap (QNeg m) (AfK m) y) := by
      rw [map_mul, show (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) j) *
          (finPart s * algebraMap (QNeg m) (AfK m) y) = (finPart s⁻¹ * finPart s) *
          (algebraMap (QNeg m) (AfK m) j * algebraMap (QNeg m) (AfK m) y) by ring,
        finPart_inv_mul, one_mul]
    rw [e]
    exact latHat_O_mul 𝔞 h𝔞 hj hy
  · intro hy
    have hcl := finPart_mem_closure_idealOf (m := m) (f := f) s
    have hmaps : Set.MapsTo (fun z : AfK m => z * algebraMap (QNeg m) (AfK m) y)
        (algebraMap (QNeg m) (AfK m) '' idealOf m f s)
        (algebraMap (QNeg m) (AfK m) '' (𝔞 : Set (QNeg m))) := by
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨j * y, hy j hj, map_mul _ _ _⟩
    exact map_mem_closure (f := fun z : AfK m => z * algebraMap (QNeg m) (AfK m) y)
      (continuous_id.mul continuous_const) hcl hmaps

end Colon

end T5Glue
