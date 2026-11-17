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

/-! ## gt-ringclass: proof of `RingClassLattice` -/

section RCL

variable {m : ℕ} [NeZero m]

local notation "𝒪̂" => FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)

/-- The valuation of the `v`-component of a principal finite adele. -/
theorem val_algebraMap_apply (v : HeightOneSpectrum (𝓞 (QNeg m))) (x : QNeg m) :
    Valued.v ((algebraMap (QNeg m) (AfK m) x) v) = v.valuation (QNeg m) x := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

theorem mem_intAdeles_iff (z : AfK m) :
    z ∈ 𝒪̂ ↔ ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), Valued.v (z v) ≤ 1 := by
  rw [FiniteAdeleRing.mem_integralAdeles]
  rfl

theorem valuation_le_exp_of_mem_pow (v : HeightOneSpectrum (𝓞 (QNeg m))) {r : 𝓞 (QNeg m)} {n : ℕ}
    (hr : r ∈ v.asIdeal ^ n) : v.valuation (QNeg m) (r : QNeg m) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem r n).2 hr

theorem valuation_int_le_one (v : HeightOneSpectrum (𝓞 (QNeg m))) (r : 𝓞 (QNeg m)) :
    v.valuation (QNeg m) (r : QNeg m) ≤ 1 :=
  v.valuation_le_one r

theorem exp_neg_nat_le_one (n : ℕ) : WithZero.exp (-(n : ℤ)) ≤ 1 := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem af_add_apply (z w : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (z + w) v = z v + w v := rfl

theorem af_sub_apply (z w : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (z - w) v = z v - w v := rfl

theorem af_mul_apply (z w : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (z * w) v = z v * w v := rfl

theorem af_neg_apply (z : AfK m) (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (-z) v = -z v := rfl

theorem af_zero_apply (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (0 : AfK m) v = 0 := rfl

/-- The local bound `exp(-e_v)`, `e_v` the exponent of `v` in the conductor of `O = ℤ + f𝓞_K`. -/
abbrev cBound (m f : ℕ) [NeZero m] [NeZero f] (v : HeightOneSpectrum (𝓞 (QNeg m))) : WithZero (Multiplicative ℤ) :=
  WithZero.exp (-((conductorOrder (QNeg m) f).conductorModulus.exponent v : ℤ))

/-- `𝔣̂`: the finite adeles whose `v`-component lies in `𝔭_v^{e_v}` at every finite place
(`e_v = 0` off the conductor, so these adeles are integral). -/
def fHat (m f : ℕ) [NeZero m] [NeZero f] : AddSubgroup (AfK m) where
  carrier := {z | ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), Valued.v (z v) ≤ cBound m f v}
  zero_mem' := fun v => by
    show Valued.v ((0 : AfK m) v) ≤ _
    rw [af_zero_apply, map_zero]
    exact zero_le
  add_mem' := by
    intro z w hz hw v
    show Valued.v ((z + w) v) ≤ _
    rw [af_add_apply]
    exact Valuation.map_add_le _ (hz v) (hw v)
  neg_mem' := by
    intro z hz v
    show Valued.v ((-z) v) ≤ _
    rw [af_neg_apply, Valuation.map_neg]
    exact hz v

theorem mem_fHat {f : ℕ} [NeZero f] {z : AfK m} :
    z ∈ fHat m f ↔ ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), Valued.v (z v) ≤ cBound m f v :=
  Iff.rfl

theorem conductor_le_pow_exponent {f : ℕ} [NeZero f] (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    (conductorOrder (QNeg m) f).conductor ≤
      v.asIdeal ^ (conductorOrder (QNeg m) f).conductorModulus.exponent v := by
  have h := (conductorOrder (QNeg m) f).conductorModulus.pow_exponent_dvd_finitePart v
  rw [NumberFieldOrder.conductorModulus_finitePart] at h
  exact Ideal.le_of_dvd h

theorem valuation_le_cBound_of_mem_conductor {f : ℕ} [NeZero f]
    (v : HeightOneSpectrum (𝓞 (QNeg m))) {r : 𝓞 (QNeg m)}
    (hr : r ∈ (conductorOrder (QNeg m) f).conductor) :
    v.valuation (QNeg m) (r : QNeg m) ≤ cBound m f v :=
  valuation_le_exp_of_mem_pow v (conductor_le_pow_exponent v hr)

theorem algebraMap_mem_fHat_of_mem_conductor {f : ℕ} [NeZero f] {r : 𝓞 (QNeg m)}
    (hr : r ∈ (conductorOrder (QNeg m) f).conductor) :
    algebraMap (QNeg m) (AfK m) (r : QNeg m) ∈ fHat m f := fun v => by
  rw [val_algebraMap_apply]
  exact valuation_le_cBound_of_mem_conductor v hr

theorem exists_mem_conductor_of_algebraMap_mem_fHat {f : ℕ} [NeZero f] {x : QNeg m}
    (hx : algebraMap (QNeg m) (AfK m) x ∈ fHat m f) :
    ∃ r ∈ (conductorOrder (QNeg m) f).conductor, (r : QNeg m) = x := by
  have hx' : ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), v.valuation (QNeg m) x ≤ cBound m f v :=
    fun v => by rw [← val_algebraMap_apply]; exact hx v
  obtain ⟨r, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (QNeg m) x
    (fun v => (hx' v).trans (exp_neg_nat_le_one _))
  refine ⟨r, ?_, rfl⟩
  rw [← NumberFieldOrder.conductorModulus_finitePart]
  refine (conductorOrder (QNeg m) f).conductorModulus.mem_finitePart_of_forall_mem_pow_exponent
    (fun v _ => ?_)
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem,
    ← HeightOneSpectrum.valuation_of_algebraMap (K := QNeg m)]
  exact hx' v

theorem natCast_mem_conductor (f : ℕ) [NeZero f] :
    (f : 𝓞 (QNeg m)) ∈ (conductorOrder (QNeg m) f).conductor := by
  simpa using natCast_mul_mem_conductor (QNeg m) f 1

/-- `f·𝒪̂ ⊆ 𝔣̂`. -/
theorem mem_fHat_of_fIntAd {f : ℕ} [NeZero f] {z : AfK m}
    (hz : algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z ∈ 𝒪̂) : z ∈ fHat m f := by
  have hf0 : (f : QNeg m) ≠ 0 := by exact_mod_cast NeZero.ne f
  have hzeq : z = algebraMap (QNeg m) (AfK m) (f : QNeg m) *
      (algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf0, map_one, one_mul]
  intro v
  rw [hzeq, af_mul_apply, map_mul, val_algebraMap_apply]
  have h1 : v.valuation (QNeg m) (f : QNeg m) ≤ cBound m f v := by
    have := valuation_le_cBound_of_mem_conductor v (natCast_mem_conductor (m := m) f)
    simpa using this
  have h2 := (mem_intAdeles_iff _).1 hz v
  calc v.valuation (QNeg m) (f : QNeg m) *
        Valued.v ((algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z) v)
      ≤ cBound m f v * 1 := mul_le_mul' h1 h2
    _ = cBound m f v := mul_one _

theorem isOpen_fIntAd (f : ℕ) :
    IsOpen {z : AfK m | algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * z ∈ 𝒪̂} :=
  (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
    (continuous_const.mul continuous_id)

theorem fHat_mem_nhds_zero (f : ℕ) [NeZero f] : (fHat m f : Set (AfK m)) ∈ nhds 0 := by
  refine Filter.mem_of_superset ((isOpen_fIntAd (m := m) f).mem_nhds ?_)
    (fun z hz => mem_fHat_of_fIntAd hz)
  show algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * 0 ∈ 𝒪̂
  rw [mul_zero]
  exact Subalgebra.zero_mem _

/-- `ℤ + 𝔣̂`. -/
def oHat (m f : ℕ) [NeZero m] [NeZero f] : AddSubgroup (AfK m) where
  carrier := {z | ∃ a : ℤ, z - algebraMap (QNeg m) (AfK m) (a : QNeg m) ∈ fHat m f}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro z w ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    have e : z + w - algebraMap (QNeg m) (AfK m) ((a + b : ℤ) : QNeg m) =
        (z - algebraMap (QNeg m) (AfK m) (a : QNeg m)) +
          (w - algebraMap (QNeg m) (AfK m) (b : QNeg m)) := by
      rw [Int.cast_add, map_add]; abel
    rw [e]
    exact (fHat m f).add_mem ha hb
  neg_mem' := by
    rintro z ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    have e : -z - algebraMap (QNeg m) (AfK m) ((-a : ℤ) : QNeg m) =
        -(z - algebraMap (QNeg m) (AfK m) (a : QNeg m)) := by
      rw [Int.cast_neg, map_neg]; abel
    rw [e]
    exact (fHat m f).neg_mem ha

theorem isClosed_oHat (f : ℕ) [NeZero f] : IsClosed (oHat m f : Set (AfK m)) := by
  refine AddSubgroup.isClosed_of_isOpen _ (AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_)
  refine Filter.mem_of_superset (fHat_mem_nhds_zero (m := m) f) (fun z hz => ⟨0, ?_⟩)
  simpa using hz

/-- **`Ô_O = ℤ + 𝔣̂`** (`O = ℤ + 𝔣` for `O = ℤ + f𝓞_K` with conductor `𝔣`). -/
theorem mem_latHat_O_iff {f : ℕ} [NeZero f] (z : AfK m) :
    z ∈ latHat m (Osub m f : Set (QNeg m)) ↔
      ∃ a : ℤ, z - algebraMap (QNeg m) (AfK m) (a : QNeg m) ∈ fHat m f := by
  constructor
  · intro hz
    refine closure_minimal ?_ (isClosed_oHat (m := m) f) hz
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, y, rfl⟩ := (mem_conductorOrderSubalgebra (QNeg m)).1 hx
    refine ⟨a, ?_⟩
    have e : algebraMap (QNeg m) (AfK m) ((a : QNeg m) + (f : QNeg m) * (y : QNeg m)) -
        algebraMap (QNeg m) (AfK m) (a : QNeg m) =
        algebraMap (QNeg m) (AfK m) (((f : 𝓞 (QNeg m)) * y : 𝓞 (QNeg m)) : QNeg m) := by
      have e2 : (((f : 𝓞 (QNeg m)) * y : 𝓞 (QNeg m)) : QNeg m) = (f : QNeg m) * (y : QNeg m) := by
        simp
      rw [e2, ← map_sub, add_sub_cancel_left]
    rw [e]
    exact algebraMap_mem_fHat_of_mem_conductor (natCast_mul_mem_conductor (QNeg m) f y)
  · rintro ⟨a, ha⟩
    set w := z - algebraMap (QNeg m) (AfK m) (a : QNeg m)
    have hU : IsOpen {u : AfK m | algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (w - u) ∈ 𝒪̂} :=
      (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
        (continuous_const.mul (continuous_const.sub continuous_id))
    have hwU : w ∈ {u : AfK m | algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (w - u) ∈ 𝒪̂} := by
      show algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) * (w - w) ∈ 𝒪̂
      rw [sub_self, mul_zero]; exact Subalgebra.zero_mem _
    obtain ⟨x, hx⟩ :=
      (FiniteAdeleRing.denseRange_algebraMap (𝓞 (QNeg m)) (QNeg m)).exists_mem_open hU ⟨w, hwU⟩
    change algebraMap (QNeg m) (AfK m) ((f : QNeg m)⁻¹) *
      (w - algebraMap (QNeg m) (AfK m) x) ∈ 𝒪̂ at hx
    have hxF : algebraMap (QNeg m) (AfK m) x ∈ fHat m f := by
      have := (fHat m f).sub_mem ha (mem_fHat_of_fIntAd hx)
      simpa using this
    obtain ⟨r, hr, rfl⟩ := exists_mem_conductor_of_algebraMap_mem_fHat hxF
    have hrO : ((a : QNeg m) + (r : QNeg m)) ∈ (conductorOrder (QNeg m) f).toSubalgebra :=
      Subalgebra.add_mem _ (Subalgebra.intCast_mem _ a)
        ((conductorOrder (QNeg m) f).mem_toRingOfIntegers.1
          ((conductorOrder (QNeg m) f).conductor_le_toRingOfIntegers hr))
    have e : z = algebraMap (QNeg m) (AfK m) ((a : QNeg m) + (r : QNeg m)) +
        (w - algebraMap (QNeg m) (AfK m) (r : QNeg m)) := by
      rw [map_add]; simp only [w]; ring
    rw [e]
    exact latHat_add_mem _ (mem_latHat_of_mem hrO) (fIntAd_sub_latHatO hx)

theorem valued_mul_le {v : HeightOneSpectrum (𝓞 (QNeg m))} {x y : v.adicCompletion (QNeg m)}
    {E : WithZero (Multiplicative ℤ)} (hx : Valued.v x ≤ E) (hy : Valued.v y ≤ 1) :
    Valued.v (x * y) ≤ E := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ E * 1 := mul_le_mul' hx hy
    _ = E := mul_one E

theorem valuation_intCast_le_one (v : HeightOneSpectrum (𝓞 (QNeg m))) (a : ℤ) :
    v.valuation (QNeg m) (a : QNeg m) ≤ 1 := by
  simpa using valuation_int_le_one v (a : 𝓞 (QNeg m))

theorem cBound_le_one (f : ℕ) [NeZero f] (v : HeightOneSpectrum (𝓞 (QNeg m))) :
    cBound m f v ≤ 1 := exp_neg_nat_le_one _

theorem cBound_eq_one_of_not_dvd {f : ℕ} [NeZero f] {v : HeightOneSpectrum (𝓞 (QNeg m))}
    (hv : ¬ v.asIdeal ∣ (conductorOrder (QNeg m) f).conductorModulus.finitePart) :
    cBound m f v = 1 := by
  have h : (conductorOrder (QNeg m) f).conductorModulus.exponent v = 0 := by
    by_contra h
    exact hv (((conductorOrder (QNeg m) f).conductorModulus.mem_support_iff v).1
      (((conductorOrder (QNeg m) f).conductorModulus.mem_support_iff_exponent_ne_zero v).2 h))
  simp [cBound, h]

theorem mem_intAdeles_of_mem_oHat {f : ℕ} [NeZero f] {z : AfK m} {b : ℤ}
    (hb : z - algebraMap (QNeg m) (AfK m) (b : QNeg m) ∈ fHat m f) : z ∈ 𝒪̂ := by
  rw [mem_intAdeles_iff]
  intro v
  have e : z v = (z - algebraMap (QNeg m) (AfK m) (b : QNeg m)) v +
      (algebraMap (QNeg m) (AfK m) (b : QNeg m)) v := by
    rw [← af_add_apply, sub_add_cancel]
  rw [e]
  refine Valuation.map_add_le _ ((hb v).trans (cBound_le_one f v)) ?_
  rw [val_algebraMap_apply]
  exact valuation_intCast_le_one v b

/-- **The local computation.** Let `y ∈ 𝔸_{K,f}` with `K ∩ y⁻¹𝒪̂ = J` (`J` an ideal of `𝓞_K`),
`y_v ≡ a (mod 𝔭_v^{e_v})` at the primes of the conductor, and `a a' ≡ 1 (mod 𝔣)`. Then
`K ∩ y⁻¹Ô_O = J ∩ O`. -/
theorem setOf_mul_mem_latHat_eq {f : ℕ} [NeZero f] (y : AfK m) (J : Ideal (𝓞 (QNeg m)))
    (a a' : ℤ)
    (hD1 : ∀ j : QNeg m, y * algebraMap (QNeg m) (AfK m) j ∈ 𝒪̂ ↔ ∃ r ∈ J, (r : QNeg m) = j)
    (hD2 : ∀ v : HeightOneSpectrum (𝓞 (QNeg m)),
      v.asIdeal ∣ (conductorOrder (QNeg m) f).conductorModulus.finitePart →
      Valued.v ((y - algebraMap (QNeg m) (AfK m) (a : QNeg m)) v) ≤ cBound m f v)
    (hD3 : ((a * a' - 1 : ℤ) : 𝓞 (QNeg m)) ∈ (conductorOrder (QNeg m) f).conductor) :
    {j : QNeg m | y * algebraMap (QNeg m) (AfK m) j ∈ latHat m (Osub m f : Set (QNeg m))} =
      idealMeetOrder m f J := by
  ext j
  constructor
  · intro hj
    rw [Set.mem_setOf_eq, mem_latHat_O_iff] at hj
    obtain ⟨b, hb⟩ := hj
    obtain ⟨r, hrJ, rfl⟩ := (hD1 j).1 (mem_intAdeles_of_mem_oHat hb)
    refine ⟨?_, r, hrJ, rfl⟩
    have hF : algebraMap (QNeg m) (AfK m) ((r : QNeg m) - ((a' * b : ℤ) : QNeg m)) ∈ fHat m f := by
      intro v
      by_cases hv : v.asIdeal ∣ (conductorOrder (QNeg m) f).conductorModulus.finitePart
      · have e : algebraMap (QNeg m) (AfK m) ((r : QNeg m) - ((a' * b : ℤ) : QNeg m)) =
            -(algebraMap (QNeg m) (AfK m) (((a * a' - 1 : ℤ) : 𝓞 (QNeg m)) : QNeg m) *
                algebraMap (QNeg m) (AfK m) (r : QNeg m)) -
              algebraMap (QNeg m) (AfK m) (a' : QNeg m) *
                ((y - algebraMap (QNeg m) (AfK m) (a : QNeg m)) *
                  algebraMap (QNeg m) (AfK m) (r : QNeg m)) +
              algebraMap (QNeg m) (AfK m) (a' : QNeg m) *
                (y * algebraMap (QNeg m) (AfK m) (r : QNeg m) -
                  algebraMap (QNeg m) (AfK m) (b : QNeg m)) := by
          have e1 : (((a * a' - 1 : ℤ) : 𝓞 (QNeg m)) : QNeg m) = (a : QNeg m) * a' - 1 := by simp
          rw [e1]
          simp only [map_sub, map_mul, map_one, Int.cast_mul]
          ring
        rw [e, af_add_apply, af_sub_apply, af_neg_apply]
        have hr1 : Valued.v ((algebraMap (QNeg m) (AfK m) (r : QNeg m)) v) ≤ 1 := by
          rw [val_algebraMap_apply]; exact valuation_int_le_one v r
        have ha1 : Valued.v ((algebraMap (QNeg m) (AfK m) (a' : QNeg m)) v) ≤ 1 := by
          rw [val_algebraMap_apply]; exact valuation_intCast_le_one v a'
        refine Valuation.map_add_le _ (Valuation.map_sub_le _ ?_ ?_) ?_
        · rw [Valuation.map_neg, af_mul_apply]
          refine valued_mul_le ?_ hr1
          rw [val_algebraMap_apply]
          exact valuation_le_cBound_of_mem_conductor v hD3
        · rw [af_mul_apply, mul_comm, af_mul_apply]
          refine valued_mul_le ?_ ha1
          exact valued_mul_le (hD2 v hv) hr1
        · rw [af_mul_apply, mul_comm]
          exact valued_mul_le (hb v) ha1
      · rw [cBound_eq_one_of_not_dvd hv, val_algebraMap_apply]
        have e : (r : QNeg m) - ((a' * b : ℤ) : QNeg m) =
            ((r - ((a' * b : ℤ) : 𝓞 (QNeg m)) : 𝓞 (QNeg m)) : QNeg m) := by simp
        rw [e]
        exact valuation_int_le_one v _
    obtain ⟨c, hc, hce⟩ := exists_mem_conductor_of_algebraMap_mem_fHat hF
    have e : (r : QNeg m) = ((a' * b : ℤ) : QNeg m) + (c : QNeg m) := by rw [hce]; ring
    rw [e]
    exact Subalgebra.add_mem _ (Subalgebra.intCast_mem _ _)
      ((conductorOrder (QNeg m) f).mem_toRingOfIntegers.1
        ((conductorOrder (QNeg m) f).conductor_le_toRingOfIntegers hc))
  · rintro ⟨hjO, r, hrJ, hrj⟩
    obtain ⟨b, y0, hj⟩ := (mem_conductorOrderSubalgebra (QNeg m)).1 hjO
    have hint : y * algebraMap (QNeg m) (AfK m) j ∈ 𝒪̂ := (hD1 j).2 ⟨r, hrJ, hrj⟩
    rw [Set.mem_setOf_eq, mem_latHat_O_iff]
    refine ⟨a * b, fun v => ?_⟩
    by_cases hv : v.asIdeal ∣ (conductorOrder (QNeg m) f).conductorModulus.finitePart
    · have e : y * algebraMap (QNeg m) (AfK m) j - algebraMap (QNeg m) (AfK m) ((a * b : ℤ) : QNeg m) =
          (y - algebraMap (QNeg m) (AfK m) (a : QNeg m)) * algebraMap (QNeg m) (AfK m) j +
            algebraMap (QNeg m) (AfK m) (a : QNeg m) *
              algebraMap (QNeg m) (AfK m) ((((f : 𝓞 (QNeg m)) * y0 : 𝓞 (QNeg m))) : QNeg m) := by
        have e2 : (((f : 𝓞 (QNeg m)) * y0 : 𝓞 (QNeg m)) : QNeg m) = (f : QNeg m) * (y0 : QNeg m) := by
          simp
        rw [e2, hj]
        simp only [map_sub, map_mul, map_add, Int.cast_mul]
        ring
      rw [e, af_add_apply, af_mul_apply, af_mul_apply]
      refine Valuation.map_add_le _ ?_ ?_
      · refine valued_mul_le (hD2 v hv) ?_
        rw [val_algebraMap_apply, ← hrj]; exact valuation_int_le_one v r
      · rw [mul_comm]
        refine valued_mul_le ?_ ?_
        · rw [val_algebraMap_apply]
          exact valuation_le_cBound_of_mem_conductor v (natCast_mul_mem_conductor (QNeg m) f y0)
        · rw [val_algebraMap_apply]; exact valuation_intCast_le_one v a
    · rw [cBound_eq_one_of_not_dvd hv, af_sub_apply]
      refine Valuation.map_sub_le _ ((mem_intAdeles_iff _).1 hint v) ?_
      rw [val_algebraMap_apply]; exact valuation_intCast_le_one v _

/-! ### The ideal-theoretic side -/

open scoped nonZeroDivisors

theorem finPart_mul (s t : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    finPart (s * t) = finPart s * finPart t := rfl

theorem finPart_unitEmbedding (α : (QNeg m)ˣ) :
    finPart (IdeleGroup.unitEmbedding (𝓞 (QNeg m)) (QNeg m) α) =
      algebraMap (QNeg m) (AfK m) (α : QNeg m) := rfl

theorem coe_toFiniteIdele (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ((IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s : (AfK m)ˣ) : AfK m) = finPart s :=
  IdeleGroup.coe_toFiniteIdele _ _ s

/-- For an invertible fractional ideal `U`: `U⁻¹P ≤ 1 ↔ P ≤ U`. -/
theorem inv_mul_le_one_iff (U : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ)
    (P : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m)) :
    ((U⁻¹ : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ) : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m)) *
        P ≤ 1 ↔ P ≤ U := by
  constructor
  · intro h
    have h2 := mul_le_mul_right h (U : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))
    rwa [← mul_assoc, Units.mul_inv, one_mul, mul_one] at h2
  · intro h
    have h2 := mul_le_mul_right h
      ((U⁻¹ : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ) : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))
    rwa [Units.inv_mul] at h2

/-- From the ideal of a finite idele to the integrality condition `hD1`. -/
theorem mul_mem_intAdeles_iff (yU : (AfK m)ˣ) (J : Ideal (𝓞 (QNeg m)))
    (UJ : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ)
    (hUJ : (UJ : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m)) = J)
    (hy : FiniteAdeleRing.toFractionalIdeal yU = UJ⁻¹) (j : QNeg m) :
    (yU : AfK m) * algebraMap (QNeg m) (AfK m) j ∈ 𝒪̂ ↔ ∃ r ∈ J, (r : QNeg m) = j := by
  by_cases hj : j = 0
  · subst hj
    simp only [map_zero, mul_zero]
    exact ⟨fun _ => ⟨0, J.zero_mem, by simp⟩, fun _ => Subalgebra.zero_mem _⟩
  · set ju : (QNeg m)ˣ := Units.mk0 j hj
    have e : (yU : AfK m) * algebraMap (QNeg m) (AfK m) j =
        ((yU * FiniteAdeleRing.unitEmbedding (𝓞 (QNeg m)) (QNeg m) ju : (AfK m)ˣ) : AfK m) := by
      rw [Units.val_mul, FiniteAdeleRing.unitEmbedding_apply]
      rfl
    rw [e, ← FiniteAdeleRing.toFractionalIdeal_le_one_iff, map_mul,
      FiniteAdeleRing.toFractionalIdeal_unitEmbedding, hy, Units.val_mul, inv_mul_le_one_iff,
      coe_toPrincipalIdeal, hUJ, FractionalIdeal.spanSingleton_le_iff_mem,
      FractionalIdeal.mem_coeIdeal]
    rfl

/-- `a a' ≡ 1 (mod 𝔣)` for an integer `a` prime to `𝔣`. -/
theorem exists_int_inv_mod_conductor {f : ℕ} [NeZero f] (a : ℤ) (u w : 𝓞 (QNeg m))
    (hw : w ∈ (conductorOrder (QNeg m) f).conductor) (h : (a : 𝓞 (QNeg m)) * u + w = 1) :
    ∃ a' : ℤ, ((a * a' - 1 : ℤ) : 𝓞 (QNeg m)) ∈ (conductorOrder (QNeg m) f).conductor := by
  set 𝔣 := (conductorOrder (QNeg m) f).conductor
  have : Finite (𝓞 (QNeg m) ⧸ 𝔣) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (conductorOrder (QNeg m) f).conductor_ne_bot
  have hu : Ideal.Quotient.mk 𝔣 (a : 𝓞 (QNeg m)) * Ideal.Quotient.mk 𝔣 u = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔣), Ideal.Quotient.eq]
    have : (a : 𝓞 (QNeg m)) * u - 1 = -w := by rw [← h]; ring
    rw [this]
    exact 𝔣.neg_mem hw
  set U : (𝓞 (QNeg m) ⧸ 𝔣)ˣ := ⟨_, _, hu, by rw [mul_comm]; exact hu⟩
  have hn : 0 < orderOf U := orderOf_pos U
  refine ⟨a ^ (orderOf U - 1), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hU : (U : 𝓞 (QNeg m) ⧸ 𝔣) ^ orderOf U = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have e : ((a * a ^ (orderOf U - 1) - 1 : ℤ) : 𝓞 (QNeg m)) = (a : 𝓞 (QNeg m)) ^ orderOf U - 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hn]; push_cast; ring
  rw [e, map_sub, map_pow, map_one]
  exact sub_eq_zero.2 hU

/-- `t = α·s` has the same idele class as `s`. -/
theorem icl_unitEmbedding_mul (α : (QNeg m)ˣ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    icl (IdeleGroup.unitEmbedding (𝓞 (QNeg m)) (QNeg m) α * s) = icl s := by
  simp only [icl]
  rw [mul_comm, QuotientGroup.mk_mul_of_mem s (MonoidHom.mem_range.mpr ⟨α, rfl⟩)]

/-- **`RingClassLattice` (proved).** -/
theorem ringClassLattice : RingClassLattice := by
  intro m f _ _ _ J s hs
  -- 1. move `s` into the congruence subgroup of the conductor
  obtain ⟨α, hα⟩ := exists_unitEmbedding_mul_mem_ideleCongrOneSubgroup (conductorOrder (QNeg m) f).conductorModulus s
  set t := IdeleGroup.unitEmbedding (𝓞 (QNeg m)) (QNeg m) α * s with ht
  -- 2. its ray class is that of its fractional ideal
  set It : idealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus := ⟨FiniteAdeleRing.toFractionalIdeal
      (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) t),
    toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo hα⟩ with hIt
  have hray : rayClassQuotient (conductorOrder (QNeg m) f).conductorModulus (icl s) = rayClassMk (conductorOrder (QNeg m) f).conductorModulus It := by
    rw [← icl_unitEmbedding_mul α s]
    exact rayClassQuotient_mk_of_mem hα
  -- 3. the hypothesis: `rayClassMk It · [J]⁻¹` lies in the kernel of `rayClassToPic`
  have h2 : rayClassMk (conductorOrder (QNeg m) f).conductorModulus It * (idealClass (conductorOrder (QNeg m) f).conductorModulus J)⁻¹ ∈ (conductorOrder (QNeg m) f).rayClassToPic.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hray, ← ringClassIdeleQuotient_apply, hs,
      NumberFieldOrder.rayClassToPic_idealClass, mul_inv_cancel]
  obtain ⟨J', hJ'c, β, hβO, hJ'β⟩ := (conductorOrder (QNeg m) f).mem_ker_rayClassToPic.mp h2
  -- 4. `It = (γ)·(β)·J` with `γ ≡ 1 mod* 𝔣`
  set hom := TauCeti.NumberFieldArithmetic.integralIdealsAwayHom (QNeg m) (conductorOrder (QNeg m) f).conductorModulus.support
  have h3 : rayClassMk (conductorOrder (QNeg m) f).conductorModulus (It * (hom J' * hom J)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, ← idealClass_apply, ← idealClass_apply, hJ'c]
    group
  obtain ⟨γ, hγ, hγI⟩ := mem_ray_iff.mp (rayClassMk_eq_one_iff.mp h3)
  have hJ'ne : (J' : Ideal (𝓞 (QNeg m))) ≠ ⊥ :=
    (((conductorOrder (QNeg m) f).mem_integralIdealsPrimeTo_conductorModulus_iff).mp J'.2).1
  have hβ0 : (β : QNeg m) ≠ 0 := by
    intro h
    apply hJ'ne
    rw [hJ'β, Ideal.span_singleton_eq_bot]
    exact_mod_cast h
  set βu : (QNeg m)ˣ := Units.mk0 (β : QNeg m) hβ0
  have hβu : toPrincipalIdeal (𝓞 (QNeg m)) (QNeg m) βu =
      ((hom J' : TauCeti.NumberFieldArithmetic.idealsAway (QNeg m) (conductorOrder (QNeg m) f).conductorModulus.support) : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ) := by
    apply Units.ext
    rw [coe_toPrincipalIdeal, TauCeti.NumberFieldArithmetic.coe_integralIdealsAwayHom, hJ'β,
      FractionalIdeal.coeIdeal_span_singleton]
    rfl
  set UJ : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ :=
    ((hom J : TauCeti.NumberFieldArithmetic.idealsAway (QNeg m) (conductorOrder (QNeg m) f).conductorModulus.support) : (FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m))ˣ)
  have hUJ : (UJ : FractionalIdeal (𝓞 (QNeg m))⁰ (QNeg m)) = (J : Ideal (𝓞 (QNeg m))) :=
    TauCeti.NumberFieldArithmetic.coe_integralIdealsAwayHom (K := QNeg m) _ J
  have hγI' : toPrincipalIdeal (𝓞 (QNeg m)) (QNeg m) γ =
      FiniteAdeleRing.toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) t) *
        (toPrincipalIdeal (𝓞 (QNeg m)) (QNeg m) βu * UJ)⁻¹ := by
    rw [hγI, hβu]
    rfl
  -- 5. the element `k = α⁻¹γβ` and the finite idele `y = s_f⁻¹·k`
  set k : (QNeg m)ˣ := α⁻¹ * (γ * βu) with hk
  set yU : (AfK m)ˣ := IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s⁻¹ *
    FiniteAdeleRing.unitEmbedding (𝓞 (QNeg m)) (QNeg m) k with hyU
  have hyU_coe : (yU : AfK m) = finPart s⁻¹ * algebraMap (QNeg m) (AfK m) (k : QNeg m) := by
    rw [hyU, Units.val_mul, coe_toFiniteIdele, FiniteAdeleRing.unitEmbedding_apply]
  have hyU_ideal : FiniteAdeleRing.toFractionalIdeal yU = UJ⁻¹ := by
    have htf : IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) t =
        FiniteAdeleRing.unitEmbedding (𝓞 (QNeg m)) (QNeg m) α *
          IdeleGroup.toFiniteIdele (𝓞 (QNeg m)) (QNeg m) s := by
      rw [ht, map_mul, IdeleGroup.toFiniteIdele_unitEmbedding]
    rw [htf, map_mul, FiniteAdeleRing.toFractionalIdeal_unitEmbedding] at hγI'
    rw [hyU, hk]
    simp only [map_mul, map_inv, FiniteAdeleRing.toFractionalIdeal_unitEmbedding]
    rw [hγI']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  -- 6. `β = a + f y₁` and `a a' ≡ 1 mod 𝔣`
  have hβO' : (β : QNeg m) ∈ (conductorOrder (QNeg m) f).toSubalgebra := (conductorOrder (QNeg m) f).mem_toRingOfIntegers.1 hβO
  obtain ⟨a, y₁, hβa⟩ := (mem_conductorOrderSubalgebra (QNeg m)).1 hβO'
  have hβa' : β = (a : 𝓞 (QNeg m)) + (f : 𝓞 (QNeg m)) * y₁ := by
    apply RingOfIntegers.ext
    rw [hβa]
    simp
  have hD3 : ∃ a' : ℤ, ((a * a' - 1 : ℤ) : 𝓞 (QNeg m)) ∈ (conductorOrder (QNeg m) f).conductor := by
    have htop := (((conductorOrder (QNeg m) f).mem_integralIdealsPrimeTo_conductorModulus_iff).mp J'.2).2
    rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at htop
    obtain ⟨x, hx, w, hw, hxw⟩ := htop
    rw [hJ'β, Ideal.mem_span_singleton] at hx
    obtain ⟨u, rfl⟩ := hx
    refine exists_int_inv_mod_conductor a u ((f : 𝓞 (QNeg m)) * y₁ * u + w)
      ((conductorOrder (QNeg m) f).conductor.add_mem ((conductorOrder (QNeg m) f).conductor.mul_mem_right u (natCast_mul_mem_conductor (QNeg m) f y₁))
        hw) ?_
    rw [← hxw, hβa']
    ring
  obtain ⟨a', ha'⟩ := hD3
  -- 7. the local congruence at the primes of the conductor
  have hD2 : ∀ v : HeightOneSpectrum (𝓞 (QNeg m)), v.asIdeal ∣ (conductorOrder (QNeg m) f).conductorModulus.finitePart →
      Valued.v (((yU : AfK m) - algebraMap (QNeg m) (AfK m) (a : QNeg m)) v) ≤ cBound m f v := by
    intro v hv
    have hti : t⁻¹ ∈ ideleCongrOneSubgroup (conductorOrder (QNeg m) f).conductorModulus := (ideleCongrOneSubgroup (conductorOrder (QNeg m) f).conductorModulus).inv_mem hα
    have hc := (mem_ideleCongrOneSubgroup_iff.mp hti).1 v hv
    have hyt : (yU : AfK m) = finPart t⁻¹ * (algebraMap (QNeg m) (AfK m) (γ : QNeg m) *
        algebraMap (QNeg m) (AfK m) (β : QNeg m)) := by
      rw [hyU_coe, ht, mul_inv_rev, finPart_mul, ← map_inv, finPart_unitEmbedding, hk]
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, βu, Units.val_mk0]
      ring
    have e : (yU : AfK m) - algebraMap (QNeg m) (AfK m) (a : QNeg m) =
        (finPart t⁻¹ - 1) * (algebraMap (QNeg m) (AfK m) (γ : QNeg m) *
            algebraMap (QNeg m) (AfK m) (β : QNeg m)) +
          algebraMap (QNeg m) (AfK m) ((γ : QNeg m) - 1) * algebraMap (QNeg m) (AfK m) (β : QNeg m) +
          algebraMap (QNeg m) (AfK m) ((((f : 𝓞 (QNeg m)) * y₁ : 𝓞 (QNeg m))) : QNeg m) := by
      have e2 : (((f : 𝓞 (QNeg m)) * y₁ : 𝓞 (QNeg m)) : QNeg m) = (β : QNeg m) - a := by
        rw [hβa]; simp
      rw [hyt, e2]
      simp only [map_sub, map_one]
      ring
    have hβ1 : Valued.v ((algebraMap (QNeg m) (AfK m) (β : QNeg m)) v) ≤ 1 := by
      rw [val_algebraMap_apply]; exact valuation_int_le_one v β
    have hγ1 : Valued.v ((algebraMap (QNeg m) (AfK m) (γ : QNeg m)) v) = 1 := by
      rw [val_algebraMap_apply]; exact hγ.valuation_eq_one hv
    rw [e, af_add_apply, af_add_apply, af_mul_apply, af_mul_apply, af_mul_apply]
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · refine valued_mul_le ?_ (valued_mul_le hγ1.le hβ1)
      rw [af_sub_apply]
      have e3 : (finPart t⁻¹) v = (v.ideleFiniteCoord t⁻¹ : v.adicCompletion (QNeg m)) :=
        (HeightOneSpectrum.coe_ideleFiniteCoord v t⁻¹).symm
      rw [e3]
      exact hc
    · refine valued_mul_le ?_ hβ1
      rw [val_algebraMap_apply]
      exact hγ.valuation_sub_one_le hv
    · rw [val_algebraMap_apply]
      exact valuation_le_cBound_of_mem_conductor v (natCast_mul_mem_conductor (QNeg m) f y₁)
  -- 8. the local computation
  have hcore := setOf_mul_mem_latHat_eq (f := f) (yU : AfK m) (J : Ideal (𝓞 (QNeg m))) a a'
    (mul_mem_intAdeles_iff yU J UJ hUJ hyU_ideal) hD2 ha'
  refine ⟨(k : QNeg m), k.ne_zero, ?_⟩
  rw [← hcore]
  ext j
  constructor
  · intro hj
    refine ⟨(k : QNeg m)⁻¹ * j, ?_, by field_simp⟩
    show (yU : AfK m) * algebraMap (QNeg m) (AfK m) ((k : QNeg m)⁻¹ * j) ∈
      latHat m (Osub m f : Set (QNeg m))
    rw [hyU_coe, mul_assoc, ← map_mul, ← mul_assoc, mul_inv_cancel₀ k.ne_zero, one_mul]
    exact hj
  · rintro ⟨j', hj', rfl⟩
    show finPart s⁻¹ * algebraMap (QNeg m) (AfK m) ((k : QNeg m) * j') ∈
      latHat m (Osub m f : Set (QNeg m))
    rw [map_mul, ← mul_assoc, ← hyU_coe]
    exact hj'

end RCL

end T5Glue

#print axioms T5Glue.ringClassLattice
