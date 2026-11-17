import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Vendor.AnthropicFLT.BoxDefinitions
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.ScalarFiniteAdeles

/-!
Extracted from anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Submodule_finiteAdeleBox_ofFiniteIdele.lean, blob b160e600371172d07b3d0905b981ceef97617692.
Only shared coordinates/basis and algebraic reconstruction; no scalar proof construction,
generic FG, geometry, order vendor, or P2M build-time commands.
Apache-2.0; complete exact LICENSE/NOTICE/ATTRIBUTION.upstream.md alongside.
Compatibility: isolated namespace, existing box definitions, root scalar SA provider,
actual intersection lattice used at final call site rather than desired-result assumptions.
-/
open scoped TensorProduct Pointwise
open IsDedekindDomain NumberField
noncomputable section
namespace TYZSquareOddness.AdelicLattice.Reconstruction
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)
def s1_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem s1_mem_Zhat_iff (a : 𝔸f) : a ∈ s1_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

theorem s1_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem s1_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, s1_valued_algebraMap_apply]

theorem s1_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem s1_valuation_natCast_le_one (v : HOS) (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  have h := s1_valuation_intCast_le_one v (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem s1_algebraMap_intCast_mem_Zhat (m : ℤ) : algebraMap ℚ 𝔸f (m : ℚ) ∈ s1_Zhat := fun v =>
  (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m)

theorem s1_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm
section BoxGen

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_tmul_mem_finiteAdeleBox {Λ : Submodule ℤ K} {z : K} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : a ∈ s1_Zhat) : z ⊗ₜ[ℚ] a ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem s1_finiteAdeleBox_le_iff {Λ : Submodule ℤ K} {H : AddSubgroup (K ⊗[ℚ] 𝔸f)} :
    TYZSquareOddness.AdelicLattice.finiteAdeleBox Λ ≤ H ↔ ∀ z ∈ Λ, ∀ a : 𝔸f, a ∈ s1_Zhat → z ⊗ₜ[ℚ] a ∈ H := by
  unfold TYZSquareOddness.AdelicLattice.finiteAdeleBox
  rw [AddSubgroup.closure_le]
  constructor
  · intro h z hz a ha
    exact h ⟨z, hz, a, ha, rfl⟩
  · rintro h x ⟨z, hz, a, ha, rfl⟩
    exact h z hz a ha

end BoxGen
section Slice

variable {K : Type*} [Ring K] [Algebra ℚ K]

def s1_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] 𝔸f →ₗ[ℚ] 𝔸f :=
  TensorProduct.lift ((LinearMap.lsmul ℚ 𝔸f).comp (b.coord i))

theorem s1_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (a : 𝔸f) :
    s1_coord b i (z ⊗ₜ[ℚ] a) = (b.repr z i) • a := by
  unfold s1_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem s1_coord_mem_Zhat_of_mem_finiteAdeleBox {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι)
    {t : K ⊗[ℚ] 𝔸f} (ht : t ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox (Submodule.span ℤ (Set.range b))) :
    s1_coord b i t ∈ s1_Zhat := by
  have hle : TYZSquareOddness.AdelicLattice.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ≤ (s1_Zhat.toAddSubgroup).comap (s1_coord b i).toAddMonoidHom := by
    rw [s1_finiteAdeleBox_le_iff]
    intro z hz a ha
    rw [AddSubgroup.mem_comap]
    show s1_coord b i (z ⊗ₜ[ℚ] a) ∈ s1_Zhat
    rw [s1_coord_tmul]
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
    rw [← hm, Algebra.smul_def]
    refine mul_mem ?_ ha
    have : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
    rw [this]
    exact s1_algebraMap_intCast_mem_Zhat m
  exact hle ht

theorem s1_tmul_one_mem_finiteAdeleBox_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (z : K) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ↔ z ∈ Submodule.span ℤ (Set.range b) := by
  constructor
  · intro hz
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b z]
    intro i
    have hc := s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i hz
    rw [s1_coord_tmul, Algebra.smul_def, mul_one] at hc
    have hval : ∀ v : HOS, v.valuation ℚ (b.repr z i) ≤ 1 := fun v =>
      (s1_algebraMap_apply_mem_integers_iff _ v).mp (hc v)
    obtain ⟨m, hm⟩ := s1_exists_intCast_of_forall_valuation_le_one _ hval
    refine ⟨m, ?_⟩
    rw [hm, algebraMap_int_eq, Int.coe_castRingHom]
  · intro hz
    exact s1_tmul_mem_finiteAdeleBox hz (one_mem _)

end Slice
section LatticeBasis

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_exists_basis_of_isLattice (M : Submodule ℤ K) [Submodule.IsLattice ℚ M] :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = M := by
  classical
  haveI : Module.Finite ℤ ↥M := Submodule.IsLattice.finite ℚ _
  haveI : Module.Free ℤ ↥M := Submodule.IsLattice.free ℚ _
  let n := Module.finrank ℤ ↥M
  let bZ : Module.Basis (Fin n) ℤ ↥M := Module.finBasis ℤ ↥M
  refine ⟨n, bZ.extendOfIsLattice ℚ, ?_⟩
  have hrange : Set.range (bZ.extendOfIsLattice ℚ) = M.subtype '' Set.range bZ := by
    ext x
    simp only [Set.mem_range, Module.Basis.extendOfIsLattice_apply, Set.mem_image,
      Submodule.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨bZ k, ⟨k, rfl⟩, hk⟩, fun ⟨y, ⟨k, hk⟩, hy⟩ => ⟨k, by rw [hk]; exact hy⟩⟩
  rw [hrange, ← Submodule.map_span, bZ.span_eq, Submodule.map_top, Submodule.range_subtype]

end LatticeBasis
section Coord

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_sum_tmul_coord {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] 𝔸f) :
    ∑ i, (b i) ⊗ₜ[ℚ] (s1_coord b i t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, Finset.sum_const_zero]
  | tmul z a =>
      simp only [s1_coord_tmul]
      calc ∑ i, b i ⊗ₜ[ℚ] ((b.repr z) i • a)
          = ∑ i, ((b.repr z) i • b i) ⊗ₜ[ℚ] a := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.smul_tmul]
        _ = (∑ i, (b.repr z) i • b i) ⊗ₜ[ℚ] a := by rw [TensorProduct.sum_tmul]
        _ = z ⊗ₜ[ℚ] a := by rw [b.sum_repr]
  | add s t hs ht =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hs, ht]

theorem s3_mem_finiteAdeleBox_span_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] 𝔸f) :
    t ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox (Submodule.span ℤ (Set.range b)) ↔ ∀ i, s1_coord b i t ∈ s1_Zhat := by
  constructor
  · intro ht i
    exact s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i ht
  · intro h
    rw [← s3_sum_tmul_coord b t]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    exact s1_tmul_mem_finiteAdeleBox (Submodule.subset_span (Set.mem_range_self i)) (h i)

theorem s3_coord_tmul_one {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (x : K) :
    s1_coord b i (x ⊗ₜ[ℚ] (1 : 𝔸f)) = algebraMap ℚ 𝔸f (b.repr x i) := by
  rw [s1_coord_tmul, Algebra.smul_def, mul_one]

theorem s3_exists_sub_tmul_one_mem_finiteAdeleBox
    (hSA : ∀ a : 𝔸f, ∃ q : ℚ, a - algebraMap ℚ 𝔸f q ∈ s1_Zhat)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (t : K ⊗[ℚ] 𝔸f) :
    ∃ x : K, t - x ⊗ₜ[ℚ] (1 : 𝔸f) ∈ TYZSquareOddness.AdelicLattice.finiteAdeleBox (Submodule.span ℤ (Set.range b)) := by
  classical
  choose q hq using fun i => hSA (s1_coord b i t)
  refine ⟨∑ i, q i • b i, ?_⟩
  rw [s3_mem_finiteAdeleBox_span_iff]
  intro i
  rw [map_sub, s3_coord_tmul_one, b.repr_sum_self]
  exact hq i

end Coord
end TYZSquareOddness.AdelicLattice.Reconstruction
