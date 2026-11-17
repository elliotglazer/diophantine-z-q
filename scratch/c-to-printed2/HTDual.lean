import ZInQKernel.OneProof.H.TailT

/-! # c-to-printed2: the glue `HTDual` proved from Tate's two theorems

`HTDual` (modular-split, `scratch/modular-split/EigenHT.lean`, copied verbatim below with the contragredient
`dualGR` it is stated over) says: if `ρ|_{G_{ℚ_ℓ}}` is Hodge–Tate with weight multiset `S` (`card S = n`), then
`ρ^∨|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `−S`.

Proof (from the bundle leaves `TateTwistInvariants` and `AxSenTate` only), in hodge-split's coordinates
`Y_i(ρ) = {y ∈ ℂ_ℓⁿ | ρ(σ)ᵀ y = χ(σ)^i σ(y), σ ∈ G_E}` (`Ysp`, `E` finite Galois containing the entries):
1. (pairing) for `y ∈ Y_i(ρ)`, `z ∈ Y_j(ρ^∨)`, `σ(yᵀz) = χ(σ)^{−i−j} yᵀz`; so `yᵀz = 0` if `i + j ≠ 0`
   (Tate) and `yᵀz ∈ E` if `i + j = 0` (Ax–Sen–Tate);
2. hodge-split's `exists_basis_Ysp` gives a `ℂ_ℓ`-basis `b_k ∈ Y_{j_k}(ρ)` (Hodge–Tate means `Σ dim = n`);
3. the dual basis `c_m` (`b_kᵀ c_m = δ_{km}`) satisfies `c_m ∈ Y_{−j_m}(ρ^∨)` (apply `σ` to `b_kᵀ c_m = δ_{km}`);
4. by 1, every `z ∈ Y_i(ρ^∨)` is `Σ_m (b_mᵀ z) c_m` with `b_mᵀ z ∈ E`, zero unless `j_m = −i`; so
   `dim_E Y_i(ρ^∨) = #{m | j_m = −i}`, and symmetrically `dim_E Y_i(ρ) = #{m | j_m = i}`;
5. hodge-split's `htMult_eq_finrank_Ysp` turns this into `htMult(ρ^∨, w) = htMult(ρ, −w)`. -/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace CToPrinted2

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

/-! ## §1. The contragredient (modular-split's `EigenHT.lean` §Dual, verbatim) -/

section Dual

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem mat_mul_inv (ρ : GaloisRep ℓ n) (σ : GQ) :
    ρ.mat σ * ρ.mat σ⁻¹ = 1 := by
  rw [GaloisRep.mat, GaloisRep.mat, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem mat_inv_mul (ρ : GaloisRep ℓ n) (σ : GQ) :
    ρ.mat σ⁻¹ * ρ.mat σ = 1 := by
  rw [GaloisRep.mat, GaloisRep.mat, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

/-- The contragredient `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` as a homomorphism. -/
noncomputable def dualHom (ρ : GaloisRep ℓ n) : GQ →* GL (Fin n) (PadicAlgCl ℓ) where
  toFun σ := ⟨(ρ.mat σ⁻¹).transpose, (ρ.mat σ).transpose,
    by rw [← Matrix.transpose_mul, mat_mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, mat_inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp [GaloisRep.mat])
  map_mul' σ τ := Units.ext (by
    simp only [GaloisRep.mat, mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul])

/-- **The contragredient** `ρ^∨(σ) = ρ(σ⁻¹)ᵀ` of a continuous representation. -/
noncomputable def dualGR (ρ : GaloisRep ℓ n) : GaloisRep ℓ n where
  toHom := dualHom ρ
  continuous_toHom := by
    rw [Units.continuous_iff]
    constructor
    · change Continuous fun σ : GQ => (ρ.mat σ⁻¹).transpose
      exact ((Units.continuous_val.comp ρ.continuous_toHom).comp continuous_inv).matrix_transpose
    · change Continuous fun σ : GQ => (ρ.mat σ).transpose
      exact (Units.continuous_val.comp ρ.continuous_toHom).matrix_transpose

theorem dualGR_mat (ρ : GaloisRep ℓ n) (σ : GQ) : (dualGR ρ).mat σ = (ρ.mat σ⁻¹).transpose := rfl

end Dual

/-- **GLUE `HTDual` (modular-split, verbatim): Hodge–Tate weights of the contragredient.** If `ρ|_{G_{ℚ_ℓ}}` is
Hodge–Tate with weight multiset `S` (`card S = n`), then `ρ^∨|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `−S`.
Proved below (`htDual_proof`) from the bundle leaves `TateTwistInvariants` and `AxSenTate`. -/
def HTDual : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (ρ : GaloisRep ℓ n) (S : Multiset ℤ), S.card = n →
    ρ.HasHTWeightsAtSelf ℓ S → (dualGR ρ).HasHTWeightsAtSelf ℓ (S.map Neg.neg)

/-! ## §2. Pairing `Y_i(ρ)` with `Y_j(ρ^∨)` -/

section Pairing

variable (p : ℕ) [Fact p.Prime] {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}

/-- `ρ'` is the contragredient of `ρ`, read in `ℂ_p`: `ρ'(σ)ᵀ = ρ(σ⁻¹)`. -/
def IsDualPair (ρ ρ' : GQp p →* GL (Fin n) E) : Prop :=
  ∀ σ, (matC p (ρ' σ : Matrix (Fin n) (Fin n) E)).transpose = matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)

theorem IsDualPair.symm {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') : IsDualPair p ρ' ρ := by
  intro σ
  have h1 := h σ⁻¹
  rw [inv_inv] at h1
  rw [← h1, Matrix.transpose_transpose]

theorem cpAct_dot (σ : GQp p) (y z : Fin n → ℂ_[p]) :
    cpAct p σ (y ⬝ᵥ z) = vAct p σ y ⬝ᵥ vAct p σ z := by
  simp only [dotProduct, map_sum, map_mul, vAct]

/-- **Step 1: the twist of the pairing.** -/
theorem pair_twist {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {i j : ℤ}
    {y z : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i E) (hz : z ∈ Ysp p ρ' j E) {σ : GQp p}
    (hσ : σ ∈ E.fixingSubgroup) :
    cycPow p σ (i + j) • cpAct p σ (y ⬝ᵥ z) = y ⬝ᵥ z := by
  have h1 := hy σ hσ
  have h2 := hz σ hσ
  rw [h σ] at h2
  rw [cpAct_dot, cycPow_add, mul_smul, ← dotProduct_smul, ← smul_dotProduct, ← h1, ← h2,
    Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, matC_mul_inv,
    Matrix.one_mulVec]

theorem pair_eq_zero (hT : TateTwistInvariants) [FiniteDimensional ℚ_[p] E]
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {i j : ℤ} (hij : i + j ≠ 0)
    {y z : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i E) (hz : z ∈ Ysp p ρ' j E) : y ⬝ᵥ z = 0 :=
  hT p E (i + j) hij _ fun _ hσ => pair_twist p h hy hz hσ

theorem pair_mem (hA : AxSenTate) [FiniteDimensional ℚ_[p] E]
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {i j : ℤ} (hij : i + j = 0)
    {y z : Fin n → ℂ_[p]} (hy : y ∈ Ysp p ρ i E) (hz : z ∈ Ysp p ρ' j E) :
    ∃ e : E, y ⬝ᵥ z = algebraMap E ℂ_[p] e := by
  obtain ⟨e, he⟩ := hA p E (y ⬝ᵥ z) fun σ hσ => by
    have := pair_twist p h hy hz hσ
    rwa [hij, cycPow_zero, one_smul] at this
  exact ⟨e, by rw [he, eC_eq]⟩

end Pairing

/-! ## §3. The dual basis -/

section DualBasis

variable {K : Type*} [Field K] {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The vector `c_m` with `v ⬝ᵥ c_m = b.coord m v`. -/
def cvec (b : Module.Basis ι K (Fin n → K)) (m : ι) : Fin n → K := fun a => b.coord m (Pi.single a 1)

theorem coord_eq_dot (b : Module.Basis ι K (Fin n → K)) (m : ι) (v : Fin n → K) :
    b.coord m v = v ⬝ᵥ cvec b m := by
  have hv : v = ∑ a, v a • Pi.single a (1 : K) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct, cvec]

theorem dot_cvec (b : Module.Basis ι K (Fin n → K)) (k m : ι) :
    b k ⬝ᵥ cvec b m = if k = m then 1 else 0 := by
  rw [← coord_eq_dot, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

/-- A vector is determined by its pairings with a basis. -/
theorem eq_of_dot_basis (b : Module.Basis ι K (Fin n → K)) {x x' : Fin n → K}
    (h : ∀ k, b k ⬝ᵥ x = b k ⬝ᵥ x') : x = x' := by
  have h0 : ∀ v : Fin n → K, v ⬝ᵥ (x - x') = 0 := by
    intro v
    rw [← b.sum_repr v, sum_dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_dotProduct, dotProduct_sub, h k, sub_self, smul_zero]
  ext a
  have := h0 (Pi.single a 1)
  rw [single_dotProduct, one_mul, Pi.sub_apply, sub_eq_zero] at this
  exact this

/-- The dual expansion `z = Σ_m (b_m ⬝ᵥ z) c_m`. -/
theorem dual_expansion (b : Module.Basis ι K (Fin n → K)) (c : ι → Fin n → K)
    (hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0) (z : Fin n → K) :
    z = ∑ m, (b m ⬝ᵥ z) • c m := by
  refine eq_of_dot_basis b fun k => ?_
  rw [dotProduct_sum]
  simp only [dotProduct_smul, hbc, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]

theorem linearIndependent_of_dual (b : Module.Basis ι K (Fin n → K)) (c : ι → Fin n → K)
    (hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0) : LinearIndependent K c := by
  rw [Fintype.linearIndependent_iff]
  intro a ha k
  have := congrArg (fun v => b k ⬝ᵥ v) ha
  simp only [dotProduct_sum, dotProduct_smul, hbc, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, dotProduct_zero] at this
  exact this

end DualBasis

/-! ## §4. Dimensions of the `Y`'s from a dual pair of bases -/

section Dims

variable (p : ℕ) [Fact p.Prime] {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
  [FiniteDimensional ℚ_[p] E]

/-- **Step 3: the dual basis lies in the `Y`'s of the contragredient.** -/
theorem cvec_mem {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p])) (j : ι → ℤ)
    (hb : ∀ k, b k ∈ Ysp p ρ (j k) E) (m : ι) : cvec b m ∈ Ysp p ρ' (-j m) E := by
  intro σ hσ
  rw [h σ]
  -- `ρ(σ) σ(c_m) = χ(σ)^{j_m} c_m`, tested against the basis
  have key : (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).mulVec (vAct p σ (cvec b m)) =
      cycPow p σ (j m) • cvec b m := by
    refine eq_of_dot_basis b fun k => ?_
    have h1 : cpAct p σ (b k ⬝ᵥ cvec b m) = (if k = m then 1 else 0) := by
      rw [dot_cvec]; split_ifs <;> simp
    rw [cpAct_dot, vAct_of_mem p (hb k) hσ, smul_dotProduct, Matrix.mulVec_transpose,
      ← Matrix.dotProduct_mulVec] at h1
    rw [dotProduct_smul, dot_cvec]
    have h2 : b k ⬝ᵥ (matC p (ρ σ : Matrix (Fin n) (Fin n) E)).mulVec (vAct p σ (cvec b m)) =
        cycPow p σ (j k) • (if k = m then (1 : ℂ_[p]) else 0) := by
      rw [← h1, smul_smul, mul_comm, cycPow_neg_mul, one_smul]
    rw [h2]
    split_ifs with hkm
    · rw [hkm]
    · simp
  have e1 : vAct p σ (cvec b m) = cycPow p σ (j m) •
      (matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)).mulVec (cvec b m) := by
    have h3 := congrArg (matC p (ρ σ⁻¹ : Matrix (Fin n) (Fin n) E)).mulVec key
    rw [Matrix.mulVec_mulVec, matC_inv_mul, Matrix.one_mulVec, Matrix.mulVec_smul] at h3
    exact h3
  rw [e1, smul_smul, cycPow_neg_mul, one_smul]

/-- **Step 4: `dim_E Y_i(ρ') = #{m | j_m = −i}`.** -/
theorem finrank_Ysp_dual (hT : TateTwistInvariants) (hA : AxSenTate)
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p])) (j : ι → ℤ) (hb : ∀ k, b k ∈ Ysp p ρ (j k) E)
    (c : ι → Fin n → ℂ_[p]) (hc : ∀ m, c m ∈ Ysp p ρ' (-j m) E)
    (hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0) (i : ℤ) :
    Module.finrank E (Ysp p ρ' i E) = Fintype.card {m // j m = -i} := by
  classical
  let T := {m // j m = -i}
  have hcT : ∀ t : T, c t.1 ∈ Ysp p ρ' i E := fun t => by
    have := hc t.1; rwa [t.2, neg_neg] at this
  let F : (T → E) →ₗ[E] Ysp p ρ' i E :=
    { toFun := fun a => ∑ t, a t • ⟨c t.1, hcT t⟩
      map_add' := fun a a' => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hFval : ∀ a : T → E, ((F a : Ysp p ρ' i E) : Fin n → ℂ_[p]) =
      ∑ t, algebraMap E ℂ_[p] (a t) • c t.1 := by
    intro a
    change ((∑ t, a t • (⟨c t.1, hcT t⟩ : Ysp p ρ' i E) : Ysp p ρ' i E) : Fin n → ℂ_[p]) = _
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Submodule.coe_smul, algebraMap_smul]
  have hinj : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    funext t
    have h0 : ((F a : Ysp p ρ' i E) : Fin n → ℂ_[p]) = 0 := by rw [ha]; rfl
    rw [hFval] at h0
    have := congrArg (fun v => b t.1 ⬝ᵥ v) h0
    simp only [dotProduct_sum, dotProduct_smul, hbc, smul_eq_mul, mul_ite, mul_one, mul_zero,
      dotProduct_zero] at this
    rw [Finset.sum_eq_single t (fun t' _ ht' => by
      rw [if_neg (fun e => ht' (Subtype.ext e).symm)]) (by simp), if_pos rfl] at this
    rw [Pi.zero_apply]
    exact (algebraMap E ℂ_[p]).injective (this.trans (map_zero _).symm)
  have hsurj : Function.Surjective F := by
    rintro ⟨z, hz⟩
    have hcoef : ∀ m, ∃ e : E, b m ⬝ᵥ z = algebraMap E ℂ_[p] e ∧ (j m ≠ -i → e = 0) := by
      intro m
      by_cases hm : j m + i = 0
      · obtain ⟨e, he⟩ := pair_mem p hA h hm (hb m) hz
        exact ⟨e, he, fun hne => absurd (by omega) hne⟩
      · refine ⟨0, by rw [pair_eq_zero p hT h hm (hb m) hz, map_zero], fun _ => rfl⟩
    choose e he hez using hcoef
    refine ⟨fun t => e t.1, Subtype.ext ?_⟩
    rw [hFval]
    change ∑ t : T, algebraMap E ℂ_[p] (e t.1) • c t.1 = z
    conv_rhs => rw [dual_expansion b c hbc z]
    simp only [he]
    have hR : ∑ m, algebraMap E ℂ_[p] (e m) • c m =
        ∑ m ∈ Finset.univ.filter (fun m => j m = -i), algebraMap E ℂ_[p] (e m) • c m := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs with hm
      · rfl
      · rw [hez m hm, map_zero, zero_smul]
    rw [hR, Finset.sum_subtype (Finset.univ.filter (fun m => j m = -i)) (p := fun m => j m = -i)
      (fun m => by simp)]
  rw [← (LinearEquiv.ofBijective F ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- **Steps 2-4 together: `dim_E Y_i(ρ') = dim_E Y_{−i}(ρ)` for a dual pair, if `ρ` is Hodge–Tate.** -/
theorem finrank_Ysp_dual_eq (hT : TateTwistInvariants) (hA : AxSenTate)
    {ρ ρ' : GQp p →* GL (Fin n) E} (h : IsDualPair p ρ ρ') (J : Finset ℤ)
    (hsum : ∑ j ∈ J, Module.finrank E (Ysp p ρ j E) = n) (i : ℤ) :
    Module.finrank E (Ysp p ρ' i E) = Module.finrank E (Ysp p ρ (-i) E) := by
  classical
  obtain ⟨ι, _, b, j, hb⟩ := exists_basis_Ysp p hT hA E ρ J hsum
  let c := cvec b
  have hc : ∀ m, c m ∈ Ysp p ρ' (-j m) E := cvec_mem p h b j hb
  have hbc : ∀ k m, b k ⬝ᵥ c m = if k = m then 1 else 0 := dot_cvec b
  -- `c` is a basis, and `b` is dual to it
  have hcard : Fintype.card ι = Module.finrank ℂ_[p] (Fin n → ℂ_[p]) :=
    (Module.finrank_eq_card_basis b).symm
  let b' : Module.Basis ι ℂ_[p] (Fin n → ℂ_[p]) :=
    basisOfLinearIndependentOfCardEqFinrank' c (linearIndependent_of_dual b c hbc) hcard
  have hb'c : ∀ k, b' k = c k := fun k => by
    simp only [b', coe_basisOfLinearIndependentOfCardEqFinrank']
  have hb' : ∀ k, b' k ∈ Ysp p ρ' ((fun m => -j m) k) E := fun k => by rw [hb'c]; exact hc k
  have hcb : ∀ m, b m ∈ Ysp p ρ (-(fun m => -j m) m) E := fun m => by
    simp only [neg_neg]; exact hb m
  have hb'b : ∀ k m, b' k ⬝ᵥ b m = if k = m then 1 else 0 := fun k m => by
    rw [hb'c, dotProduct_comm, hbc]
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1
  rw [finrank_Ysp_dual p hT hA h b j hb c hc hbc i,
    finrank_Ysp_dual p hT hA h.symm b' (fun m => -j m) hb' b hcb hb'b (-i)]
  refine Fintype.card_congr (Equiv.subtypeEquivRight fun m => ?_)
  constructor <;> intro e <;> omega

end Dims

/-! ## §5. `HTDual` -/

section Main

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem dualGR_restrictLocal (ρ : GaloisRep ℓ n) (σ : GQp ℓ) :
    (((dualGR ρ).restrictLocal ℓ σ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) =
      ((ρ.restrictLocal ℓ σ⁻¹ : GL (Fin n) (PadicAlgCl ℓ)) : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)).transpose := by
  change (ρ.mat (decomp ℓ σ)⁻¹).transpose = _
  rw [← map_inv]
  rfl

end Main

/-- **`HTDual`, proved from Tate's two theorems** (the bundle leaves `tateTwistInvariants`, `axSenTate`). -/
theorem htDual_proof (hT : TateTwistInvariants) (hA : AxSenTate) : HTDual := by
  intro ℓ _ n ρ S hS hρ
  classical
  obtain ⟨E₁, hE₁, ρ₁, h₁, hw₁⟩ := hρ
  let E := IntermediateField.normalClosure ℚ_[ℓ] E₁ (PadicAlgCl ℓ)
  haveI : FiniteDimensional ℚ_[ℓ] E := inferInstance
  haveI : IsGalois ℚ_[ℓ] E := IsGalois.mk
  have hE₁E : E₁ ≤ E := IntermediateField.le_normalClosure E₁
  let ρL := ρ.restrictLocal ℓ
  let ρ'L := (dualGR ρ).restrictLocal ℓ
  have hent₁ : ∀ σ i j, (((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j : E₁) : PadicAlgCl ℓ) =
      (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j := by
    intro σ i j; rw [← h₁ σ]; rfl
  have hmem : ∀ σ i j, (ρL σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j ∈ E := by
    intro σ i j; rw [← hent₁]
    exact hE₁E ((ρ₁ σ : Matrix (Fin n) (Fin n) E₁) i j).2
  have hmem' : ∀ σ i j, (ρ'L σ : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) i j ∈ E := by
    intro σ i j
    rw [dualGR_restrictLocal ρ σ, Matrix.transpose_apply]
    exact hmem σ⁻¹ j i
  let ρE := liftGL E ρL hmem
  let ρ'E := liftGL E ρ'L hmem'
  have hwE : ∀ w, htMult ℓ ρE w = S.count w := fun w =>
    (htMult_eq_of_lifts ℓ ρL ρE ρ₁ (liftGL_map E ρL hmem) h₁ w).trans (hw₁ w)
  have hdual : IsDualPair ℓ ρE ρ'E := by
    intro σ
    ext a b
    simp only [matC, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
    apply Subtype.ext
    rw [liftGL_coe, liftGL_coe, dualGR_restrictLocal ρ σ, Matrix.transpose_apply]
  have hdY : ∀ i, Module.finrank E (Ysp ℓ ρE i E) = S.count (-i) := by
    intro i; rw [← hwE, htMult_eq_finrank_Ysp ℓ hT hA E ρE (-i), neg_neg]
  let J : Finset ℤ := (S.map fun w => -w).toFinset
  have hsum : ∑ j ∈ J, Module.finrank E (Ysp ℓ ρE j E) = n := by
    simp only [hdY]
    have hJ : J = S.toFinset.map ⟨fun w => -w, neg_injective⟩ := by
      ext j; simp [J]
    rw [hJ, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, neg_neg]
    rw [Multiset.toFinset_sum_count_eq, hS]
  refine ⟨E, inferInstance, ρ'E, liftGL_map E ρ'L hmem', fun w => ?_⟩
  rw [htMult_eq_finrank_Ysp ℓ hT hA E ρ'E w, finrank_Ysp_dual_eq ℓ hT hA hdual J hsum, neg_neg, hdY]
  have := Multiset.count_map_eq_count' (fun w : ℤ => -w) S neg_injective (-w)
  simp only [neg_neg] at this
  exact this.symm

end

end CToPrinted2

#print axioms CToPrinted2.htDual_proof
