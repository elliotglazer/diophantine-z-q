import ZInQKernel.Contrib.TYZGenus.ShimuraModFn
import ZInQKernel.Contrib.TYZGenus.ShimuraMain

/-! Development copy: the T5Glue declarations `RingClassLattice` depends on (verbatim from
`scratch/t5-glue/T5Glue.lean`, origin/wip/t5-glue 39bb3cd2). -/

noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-- The finite adeles `𝔸_{K,f}` of `K = ℚ(√−m)`. -/
abbrev AfK (m : ℕ) [NeZero m] := FiniteAdeleRing (𝓞 (QNeg m)) (QNeg m)

/-- `𝔞̂ ⊂ 𝔸_{K,f}`: the closure of (the image of) a subset `𝔞 ⊂ K`; for a lattice `𝔞`,
`𝔞̂ = 𝔞 ⊗ ℤ̂`. -/
def latHat (m : ℕ) [NeZero m] (𝔞 : Set (QNeg m)) : Set (AfK m) :=
  closure (algebraMap (QNeg m) (AfK m) '' 𝔞)

/-- The finite component `s_f ∈ 𝔸_{K,f}` of an idele `s` of `K`. -/
def finPart {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : AfK m :=
  (s : AdeleRing (𝓞 (QNeg m)) (QNeg m)).2

/-- The idele class of an idele. -/
def icl {m : ℕ} [NeZero m] (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    IdeleClassGroup (𝓞 (QNeg m)) (QNeg m) :=
  QuotientGroup.mk s

section Copies

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

theorem finPart_inv_mul (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s⁻¹ * finPart s = 1 := by
  simp only [finPart]
  rw [← Prod.snd_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Prod.snd_one]

theorem finPart_mul_inv (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s * finPart s⁻¹ = 1 := by
  simp only [finPart]
  rw [← Prod.snd_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Prod.snd_one]

theorem latHat_eq_closure (M : Submodule ℤ (QNeg m)) :
    latHat m (M : Set (QNeg m)) =
      ((M.toAddSubgroup.map (algebraMap (QNeg m) (AfK m)).toAddMonoidHom).topologicalClosure :
        Set (AfK m)) := by
  rw [AddSubgroup.topologicalClosure_coe, latHat]
  rfl

theorem latHat_add_mem (M : Submodule ℤ (QNeg m)) {x y : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) (hy : y ∈ latHat m (M : Set (QNeg m))) :
    x + y ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx hy ⊢
  exact AddSubgroup.add_mem _ hx hy

theorem mem_latHat_of_mem {𝔞 : Set (QNeg m)} {x : QNeg m} (hx : x ∈ 𝔞) :
    algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞 :=
  subset_closure ⟨x, hx, rfl⟩

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

/-- **GLUE RING-CLASS-LATTICE (the idelic and the congruence descriptions of `Pic O` agree).** If
the ring class of the idele `s` (Tau Ceti's `ringClassIdeleQuotient`, defined through ray classes
modulo the conductor) is the class of `J ∩ O`, then the `O`-lattice `𝔍_s = K ∩ s_f·Ô_O` of `s` is
`k·(J ∩ O)` for some `k ∈ Kˣ`. (Standard: `Pic O ≅ 𝔸_K^×/Kˣ Ô_O^× K_∞^×`, `s ↦ [K ∩ s_f Ô_O]`;
Neukirch I §12 and VI §1, Cox §7 and §9; UNVERIFIED numbers. Proof: move `s` by a principal idele
into the congruence subgroup of the conductor `𝔣` (Tau Ceti
`exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup`); then `rayClassQuotient` is the ray class of
the ideal `I` of `s_f` (`rayClassQuotient_mk_of_mem`), `I = J·(βγ)` with `β ∈ O`, `γ ≡ 1 mod* 𝔣`
(`mem_ker_rayClassToPic`), and locally `s_f Ô_O = I_p` at `p ∤ f`, `= O_p` at `p ∣ f`, so
`𝔍_s = I ∩ O = βγ·(J ∩ O)`.) -/
def RingClassLattice : Prop :=
  ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J →
    ∃ k : QNeg m, k ≠ 0 ∧ idealOf m f s = (fun x => k * x) '' idealMeetOrder m f J

end Copies

end T5Glue
