import ZInQKernel.OneProof.H.TailZ15

/-! # c-to-printed2: the fields `eigenformHTNew`, `r17` and `t09SymmIsogenyExists` against their printed theorems

Single file (scratch files cannot import each other); it imports the top of the H assembly, `TailZ15`, so that
the bundle fields can be checked. Sections:
* §0 the three fields copied verbatim, each checked `rfl` against the bundle's constant;
* §1–§5 (= `HTDual.lean`) the glue `HTDual` proved from the bundle leaves `TateTwistInvariants`, `AxSenTate`;
* §6 `eigenformHTNew` from Kato's theorem at his realization (`KatoRealizationCoh`, cohomological
  normalization, or `KatoRealization`, Tate normalization), and the converse;
* §7 `r17` from Carayol's Théorème (A) at his realization (`CarayolRealization`), and the converse;
* §8 `t09SymmIsogenyExists`: no new leaf (missing definitions, see the report);
* §9 integration. -/

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

set_option synthInstance.maxHeartbeats 400000 in
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


/-! ## §6. `eigenformHTNew` from Kato's theorem at his realization

modular-split's leaves and proofs (`scratch/modular-split/EigenHT.lean`), copied verbatim into `CToPrinted2`;
new: `eigenformHTNew_of_printed` (the glue `HTDual` is now `htDual_proof`) and the converse
`katoRealization_of_field`. -/

namespace CToPrinted2

open ZInQ.Contrib.HodgeSplit ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module

noncomputable section

section DualIrr

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

/-- The contragredient of an irreducible (Burnside form) representation is irreducible. -/
theorem dualGR_isIrreducible (ρ : GaloisRep ℓ n) (h : ρ.IsIrreducible) : (dualGR ρ).IsIrreducible := by
  let A := Algebra.adjoin (PadicAlgCl ℓ) (Set.range (dualGR ρ).mat)
  let S : Subalgebra (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) :=
    { carrier := {M | M.transpose ∈ A}
      mul_mem' := by
        intro a b ha hb
        change (a * b).transpose ∈ A
        rw [Matrix.transpose_mul]; exact A.mul_mem hb ha
      add_mem' := by
        intro a b ha hb
        change (a + b).transpose ∈ A
        rw [Matrix.transpose_add]; exact A.add_mem ha hb
      algebraMap_mem' := by
        intro c
        change (algebraMap (PadicAlgCl ℓ) (Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)) c).transpose ∈ A
        rw [Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_one,
          ← Algebra.algebraMap_eq_smul_one]
        exact A.algebraMap_mem c }
  have hle : Algebra.adjoin (PadicAlgCl ℓ) (Set.range ρ.mat) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨σ, rfl⟩
    change (ρ.mat σ).transpose ∈ A
    have : (ρ.mat σ).transpose = (dualGR ρ).mat σ⁻¹ := by rw [dualGR_mat, inv_inv]
    rw [this]
    exact Algebra.subset_adjoin ⟨σ⁻¹, rfl⟩
  rw [h] at hle
  refine eq_top_iff.mpr fun M _ => ?_
  have : M.transpose ∈ S := hle Algebra.mem_top
  change M.transpose.transpose ∈ A at this
  rwa [Matrix.transpose_transpose] at this

end DualIrr

/-! ### The contragredient of a semisimple representation is semisimple (new)

`W^⊥ = {v | ∀ w ∈ W, w ⬝ᵥ v = 0}`; `W` is `ρ^∨`-stable iff `W^⊥` is `ρ`-stable; a `ρ`-stable complement `U` of
`W^⊥` gives the `ρ^∨`-stable complement `U^⊥` of `W`. Lets the realization leaf ask for a semisimple witness
instead of an irreducible one. -/

section DualSS

variable {K : Type*} [Field K] {n : ℕ}

/-- `v ↦ (w ↦ w ⬝ᵥ v)`, i.e. `(Pi.basisFun K (Fin n)).toDualEquiv`. -/
theorem toDual_eq_dot (v w : Fin n → K) : (Pi.basisFun K (Fin n)).toDual v w = w ⬝ᵥ v := by
  have hw : w = ∑ i, w i • Pi.basisFun K (Fin n) i := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, Module.Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]

/-- The orthogonal of `W` for the dot product. -/
def perp (W : Submodule K (Fin n → K)) : Submodule K (Fin n → K) :=
  W.dualAnnihilator.comap ((Pi.basisFun K (Fin n)).toDualEquiv : (Fin n → K) →ₗ[K] Module.Dual K (Fin n → K))

theorem mem_perp (W : Submodule K (Fin n → K)) (v : Fin n → K) : v ∈ perp W ↔ ∀ w ∈ W, w ⬝ᵥ v = 0 := by
  simp only [perp, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe,
    Module.Basis.toDualEquiv_apply, toDual_eq_dot]

theorem finrank_perp (W : Submodule K (Fin n → K)) : Module.finrank K (perp W) = n - Module.finrank K W := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have h2 : Module.finrank K (perp W) = Module.finrank K W.dualAnnihilator := by
    rw [perp, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  rw [Module.finrank_fin_fun] at h1
  omega

theorem eq_zero_of_dot (w : Fin n → K) (h : ∀ v, w ⬝ᵥ v = 0) : w = 0 := by
  ext i
  have := h (Pi.single i 1)
  rwa [dotProduct_single, mul_one] at this

end DualSS

section DualSSRep

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ}

theorem mulVec_mem_of_stable {M : Matrix (Fin n) (Fin n) (PadicAlgCl ℓ)}
    {W : Submodule (PadicAlgCl ℓ) (Fin n → PadicAlgCl ℓ)} (h : W.map (Matrix.toLin' M) ≤ W)
    {w : Fin n → PadicAlgCl ℓ} (hw : w ∈ W) : M.mulVec w ∈ W := by
  have := h (Submodule.mem_map_of_mem (f := Matrix.toLin' M) hw)
  rwa [Matrix.toLin'_apply] at this

/-- **The contragredient of a semisimple representation is semisimple.** -/
theorem dualGR_isSemisimple (ρ : GaloisRep ℓ n) (h : ρ.IsSemisimple) : (dualGR ρ).IsSemisimple := by
  intro W hW
  -- `W^⊥` is `ρ`-stable
  have hP : ∀ σ, (perp W).map (Matrix.toLin' (ρ.mat σ)) ≤ perp W := by
    rintro σ _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply, mem_perp]
    intro w hw
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : (ρ.mat σ).transpose = (dualGR ρ).mat σ⁻¹ := by rw [dualGR_mat, inv_inv]
    rw [this]
    exact (mem_perp W v).1 hv _ (mulVec_mem_of_stable (hW σ⁻¹) hw)
  obtain ⟨U, hcompl, hU⟩ := h (perp W) hP
  refine ⟨perp U, ?_, ?_⟩
  · rw [Submodule.isCompl_iff_disjoint]
    · rw [Submodule.disjoint_def]
      intro w hw hwU
      refine eq_zero_of_dot w fun v => ?_
      have hv : v ∈ perp W ⊔ U := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨a, ha, u, hu, rfl⟩ := Submodule.mem_sup.1 hv
      rw [dotProduct_add, (mem_perp W a).1 ha w hw, dotProduct_comm, (mem_perp U w).1 hwU u hu, zero_add]
    · have h1 := Submodule.finrank_add_eq_of_isCompl hcompl
      have h2 := finrank_perp W
      have h3 := finrank_perp U
      have hWle : Module.finrank (PadicAlgCl ℓ) W ≤ n := by
        have := Submodule.finrank_le W; rwa [Module.finrank_fin_fun] at this
      rw [Module.finrank_fin_fun] at h1 ⊢
      omega
  · rintro σ _ ⟨v, hv, rfl⟩
    rw [Matrix.toLin'_apply, mem_perp]
    intro u hu
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dualGR_mat, Matrix.transpose_transpose]
    exact (mem_perp U v).1 hv _ (mulVec_mem_of_stable (hU σ⁻¹) hu)

end DualSSRep

/-- **LEAF candidate (consequence, see the report): Kato's theorem at his realization, dualized.**
For a newform `f ∈ S_k(Γ₁(N))`, `k ≥ 2`, with nebentypus `χ`, a prime `ℓ` and embeddings `ιC`, `ιL`,
**there is** a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `f` (arithmetic Frobenius at
`p ∤ Nℓ` has trace `ιL ιC⁻¹ a_p(f)`) with Hodge–Tate weights `{0, 1 − k}` at `ℓ` (convention: the
cyclotomic character has weight `−1`).

Source: Kato, *p-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004),
§§9.2–9.4 and (9.2.2) (UNVERIFIED locators, hodge-split): `V_{F_λ}(f)` is de Rham at `ℓ` with Hodge–Tate
weights `0` and `k − 1` (cohomological normalization). The witness is the dual `V_{F_λ}(f)^∨` with
coefficients extended along `ιL ιC⁻¹` (dualizing turns geometric into arithmetic Frobenius and negates the
weights), irreducible by Ribet 1977 / 1985 (UNVERIFIED locators), hence semisimple. Not stronger than the
published statements: it asserts the conclusion for one realization only. -/
def KatoRealization : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧ ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

/-- **Row eigenformHTNew from `KatoRealization`.** -/
theorem eigenformHTNew_of_realization (hK : KatoRealization) : EigenformHTNew := by
  intro ℓ _ ιC ιL N k χ f ρ hN hk hf hss hatt
  obtain ⟨ρ0, hss0, hatt0, hHT0⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  have hconj : IsConj ρ0 ρ := by
    refine attachedConj_proof ℓ ρ0 ρ (N * ℓ).primeFactors hss0 hss fun p hp hpS => ?_
    have hpN : ¬ p ∣ N * ℓ := by
      intro h
      exact hpS (Nat.mem_primeFactors.mpr ⟨hp, h, Nat.mul_ne_zero (by omega)
        (Fact.out : ℓ.Prime).ne_zero⟩)
    obtain ⟨hu0, α0, hα0, htr0⟩ := hatt0 p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    have heq : α0 = α := by
      apply ιC.toRingHom.injective
      change ιC α0 = ιC α
      rw [hα0, hα]
    refine ⟨hu0, hu, fun v σ hv hσ => ?_⟩
    rw [htr0 v σ hv hσ, htr v σ hv hσ, heq]
  exact htConj_proof ℓ 2 ρ0 ρ _ hconj hHT0

/-- **LEAF candidate (consequence; closer to the printed form than `KatoRealization`): Kato's theorem at his
realization, in the cohomological normalization.** For a newform `f ∈ S_k(Γ₁(N))`, `k ≥ 2`, a prime `ℓ` and
embeddings `ιC`, `ιL`, **there is** an irreducible continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` such that for `p ∤ Nℓ`, `ρ` is
unramified at `p` and every **geometric** Frobenius `σ⁻¹` (`σ` arithmetic) has trace `ιL ιC⁻¹ a_p(f)`, and
`ρ|_{G_{ℚ_ℓ}}` is Hodge–Tate with weights `{0, k − 1}` (convention: the cyclotomic character has weight `−1`).

Sources: the witness is Kato's `V_{F_λ}(f)` (Astérisque 295 (2004), §§8.3, 9.2–9.4 and (9.2.2); UNVERIFIED locators)
with coefficients extended along `ιL ιC⁻¹`. Its geometric Frobenius traces are `a_p` (Eichler–Shimura–Deligne
normalization of `H¹_ét`). Kato's de Rham statement with Hodge–Tate weights `0, k − 1` is in the cohomological
normalization; its translation into this file's convention is UNVERIFIED (no source on this host). Irreducibility
is Ribet 1977 (`k = 2`) / Ribet 1985 (UNVERIFIED locators). The existential over `ρ` makes it a consequence, not
the printed statement, which is about the specific `V_{F_λ}(f)`. -/
def KatoRealizationCoh : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsIrreducible ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

/-- **`KatoRealization` from the cohomological form and the glue `HTDual`** (the contragredient is attached,
irreducible hence semisimple). -/
theorem katoRealization_of_coh (hK : KatoRealizationCoh) (hD : HTDual) : KatoRealization := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hirr, hatt, hHT⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  refine ⟨dualGR ρ, ?_, ?_, ?_⟩
  · have h := dualGR_isIrreducible ρ hirr
    exact C9Rhof.isSemisimple_of_isIrreducible (ℓ := ℓ) ⟨(dualGR ρ).toHom, (dualGR ρ).continuous_toHom⟩ h
  · intro p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    refine ⟨fun v hv σ hσ => ?_, α, hα, fun v σ hv hσ => ?_⟩
    · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
      apply Units.ext
      change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
      have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
      rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
    · rw [dualGR_mat, Matrix.trace_transpose, htr v σ hv hσ]
  · have h := hD ℓ 2 ρ {0, k - 1} (by simp) hHT
    have hS : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
    rwa [hS] at h

/-- **Row eigenformHTNew from the cohomological form of Kato's theorem and the glue `HTDual`.** -/
theorem eigenformHTNew_of_coh (hK : KatoRealizationCoh) (hD : HTDual) : EigenformHTNew :=
  eigenformHTNew_of_realization (katoRealization_of_coh hK hD)

/-- **Row eigenformHTNew from the realization leaf `KatoRealizationCoh` (Kato's normalization; Kato with
Eichler–Shimura–Deligne and Ribet at `V_{F_λ}(f)`)**, with the two bundle LEAF fields
`tateTwistInvariants`, `axSenTate` (Tate 1967 §3.3 Thms 1–2) closing modular-split's glue `HTDual`. -/
theorem eigenformHTNew_of_printed (hK : KatoRealizationCoh) (hT : TateTwistInvariants) (hA : AxSenTate) :
    EigenformHTNew :=
  eigenformHTNew_of_coh hK (htDual_proof hT hA)

/-- **LEAF candidate (consequence; the weakest form proposed here): Kato's theorem at his realization, cohomological
normalization, with a semisimple witness.** `KatoRealizationCoh` with `ρ.IsSemisimple` in place of
`ρ.IsIrreducible` (so `KatoRealizationCoh → KatoRealizationCohSS`, `katoRealizationCohSS_of_coh`). Witness: Kato's
`V_{F_λ}(f)` (Astérisque 295 (2004) §§8.3, 9.2–9.4; UNVERIFIED locators), semisimple by Ribet's irreducibility
(UNVERIFIED locators). Not stronger than the published statements: one realization only, and semisimplicity is
weaker than the published irreducibility. -/
def KatoRealizationCohSS : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

theorem katoRealizationCohSS_of_coh (hK : KatoRealizationCoh) : KatoRealizationCohSS := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hirr, hatt, hHT⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  exact ⟨ρ, C9Rhof.isSemisimple_of_isIrreducible (ℓ := ℓ) ⟨ρ.toHom, ρ.continuous_toHom⟩ hirr, hatt, hHT⟩

/-- **`KatoRealization` from the semisimple cohomological form and `HTDual`.** -/
theorem katoRealization_of_cohSS (hK : KatoRealizationCohSS) (hD : HTDual) : KatoRealization := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hss, hatt, hHT⟩ := hK ℓ ιC ιL N k χ f hN hk hf
  refine ⟨dualGR ρ, dualGR_isSemisimple ρ hss, ?_, ?_⟩
  · intro p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    refine ⟨fun v hv σ hσ => ?_, α, hα, fun v σ hv hσ => ?_⟩
    · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
      apply Units.ext
      change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
      have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
      rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
    · rw [dualGR_mat, Matrix.trace_transpose, htr v σ hv hσ]
  · have h := hD ℓ 2 ρ {0, k - 1} (by simp) hHT
    have hS : (({0, k - 1} : Multiset ℤ).map Neg.neg) = {0, 1 - k} := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
    rwa [hS] at h

/-- **Row eigenformHTNew from the weakest leaf `KatoRealizationCohSS`** and the bundle LEAF fields
`tateTwistInvariants`, `axSenTate`. -/
theorem eigenformHTNew_of_printedSS (hK : KatoRealizationCohSS) (hT : TateTwistInvariants) (hA : AxSenTate) :
    EigenformHTNew :=
  eigenformHTNew_of_realization (katoRealization_of_cohSS hK (htDual_proof hT hA))

/-- **Converse: the field gives back the existential leaf**, given the bundle LEAF fields `dsThm965`, `dsThm966`
(through hodge-split's `r14Det_of_printed`: a semisimple attached `ρ` exists for every normalized eigenform of
weight `≥ 1`). So `KatoRealization` is exactly as strong as the field `EigenformHTNew` over the bundle: the
existential substitute loses nothing. -/
theorem katoRealization_of_field (hD : DSThm965) (hDS : DSThm966) (h : EigenformHTNew) : KatoRealization := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hss, hatt⟩ :=
    eigenformRepExists_of_r14Det (r14Det_of_printed hD hDS) ℓ ιC ιL N k χ f hN (by omega) hf.1
  exact ⟨ρ, hss, hatt, h ℓ ιC ιL N k χ f ρ hN hk hf hss hatt⟩

/-- **Converse for the cohomological form**: over the bundle LEAF fields `dsThm965`, `dsThm966`, `tateTwistInvariants`,
`axSenTate`, the field gives back `KatoRealizationCohSS` (the contragredient of a semisimple attached `ρ`). -/
theorem katoRealizationCohSS_of_field (hD : DSThm965) (hDS : DSThm966) (hT : TateTwistInvariants)
    (hA : AxSenTate) (h : EigenformHTNew) : KatoRealizationCohSS := by
  intro ℓ _ ιC ιL N k χ f hN hk hf
  obtain ⟨ρ, hss, hatt, hHT⟩ := katoRealization_of_field hD hDS h ℓ ιC ιL N k χ f hN hk hf
  refine ⟨dualGR ρ, dualGR_isSemisimple ρ hss, ?_, ?_⟩
  · intro p hp hpN
    obtain ⟨hu, α, hα, htr⟩ := hatt p hp hpN
    refine ⟨fun v hv σ hσ => ?_, α, hα, fun v σ hv hσ => ?_⟩
    · have h1 := hu v hv σ⁻¹ ((v.inertiaSubgroup ℚ).inv_mem hσ)
      apply Units.ext
      change (ρ.mat ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹).transpose = 1
      have : ((σ⁻¹ : v.decompositionSubgroup ℚ) : GQ) = ((σ : v.decompositionSubgroup ℚ) : GQ)⁻¹ := rfl
      rw [GaloisRep.mat, ← this, h1, Units.val_one, Matrix.transpose_one]
    · rw [dualGR_mat, inv_inv, Matrix.trace_transpose, htr v σ hv hσ]
  · have h2 := htDual_proof hT hA ℓ 2 ρ {0, 1 - k} (by simp) hHT
    have hS : (({0, 1 - k} : Multiset ℤ).map Neg.neg) = {0, k - 1} := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, neg_zero, neg_sub]
    rwa [hS] at h2

/-- **The cohomological semisimple form is equivalent to the field over the bundle** (as is `KatoRealization`,
`katoRealization_iff_field`; the irreducible form `KatoRealizationCoh` only implies it). -/
theorem katoRealizationCohSS_iff_field (hD : DSThm965) (hDS : DSThm966) (hT : TateTwistInvariants)
    (hA : AxSenTate) : KatoRealizationCohSS ↔ EigenformHTNew :=
  ⟨fun hK => eigenformHTNew_of_printedSS hK hT hA, katoRealizationCohSS_of_field hD hDS hT hA⟩

theorem katoRealization_iff_field (hD : DSThm965) (hDS : DSThm966) : KatoRealization ↔ EigenformHTNew :=
  ⟨eigenformHTNew_of_realization, katoRealization_of_field hD hDS⟩

end

end CToPrinted2

/-! ## §7. `r17` from Carayol's Théorème (A) at his realization

modular-split's leaf and proof (`scratch/modular-split/R17.lean`), copied verbatim into `CToPrinted2.R17`;
new: the converse `carayolRealization_of_field`. -/

namespace CToPrinted2.R17

open LadicCond

section Conj

variable {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] {n : ℕ}

/-- `v ↦ P v` as a linear automorphism of `kⁿ`. -/
def glEquiv (P : GL (Fin n) k) : (Fin n → k) ≃ₗ[k] (Fin n → k) :=
  LinearEquiv.ofLinear (Matrix.toLin' (P : Matrix (Fin n) (Fin n) k))
    (Matrix.toLin' ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])

theorem glEquiv_apply (P : GL (Fin n) k) (v : Fin n → k) :
    glEquiv P v = (P : Matrix (Fin n) (Fin n) k).mulVec v := rfl

/-- Invariants of a conjugate: `V^S(PρP⁻¹) = P · V^S(ρ)`. -/
theorem invariants_conj (ρ ρ' : _root_.PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) (S : Set (_root_.PkgI4.GQp p)) :
    invariants ρ' S = (invariants ρ S).map (glEquiv P : (Fin n → k) →ₗ[k] (Fin n → k)) := by
  have hPinv : ∀ w : Fin n → k, (P : Matrix (Fin n) (Fin n) k).mulVec
      (((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPinv' : ∀ w : Fin n → k, ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec
      ((P : Matrix (Fin n) (Fin n) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hval : ∀ σ, (ρ' σ : Matrix (Fin n) (Fin n) k) = (P : Matrix (Fin n) (Fin n) k) *
      (ρ σ : Matrix (Fin n) (Fin n) k) * ((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    intro σ; rw [h σ]; rfl
  ext v
  constructor
  · intro hv
    refine ⟨((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v, ?_, ?_⟩
    · intro σ hσ
      have := hv σ hσ
      rw [hval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at this
      have h2 := congrArg (((P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec) this
      rwa [hPinv'] at h2
    · exact hPinv v
  · rintro ⟨w, hw, rfl⟩ σ hσ
    change (ρ' σ : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec w) =
      (P : Matrix (Fin n) (Fin n) k).mulVec w
    rw [hval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPinv', hw σ hσ]

theorem codimInv_conj (ρ ρ' : _root_.PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) (S : Set (_root_.PkgI4.GQp p)) : codimInv ρ' S = codimInv ρ S := by
  unfold codimInv
  rw [invariants_conj ρ ρ' P h S, LinearEquiv.finrank_map_eq]

theorem isAdapted_conj (ρ ρ' : _root_.PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) (L : Fld p) : IsAdapted L ρ' ↔ IsAdapted L ρ := by
  unfold IsAdapted
  have : ∀ σ, ρ' σ = 1 ↔ ρ σ = 1 := by
    intro σ; rw [h σ]
    constructor
    · intro h1
      have : ρ σ = P⁻¹ * (P * ρ σ * P⁻¹) * P := by group
      rw [this, h1]; group
    · intro h1; rw [h1]; group
  simp only [this]

theorem choose_congr {α : Sort*} {q r : α → Prop} (hqr : q = r) (hq : ∃ x, q x) (hr : ∃ x, r x) :
    hq.choose = hr.choose := by
  subst hqr; rfl

theorem swan_conj (ρ ρ' : _root_.PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) : swan ρ' = swan ρ := by
  have hsw : ∀ L, swanAt L ρ' = swanAt L ρ := by
    intro L; unfold swanAt; simp only [codimInv_conj ρ ρ' P h]
  have hpred : (fun L => IsAdapted L ρ') = (fun L => IsAdapted L ρ) :=
    funext fun L => propext (isAdapted_conj ρ ρ' P h L)
  unfold swan
  by_cases hex : ∃ L, IsAdapted L ρ
  · have hex' : ∃ L, IsAdapted L ρ' := by
      obtain ⟨L, hL⟩ := hex; exact ⟨L, (isAdapted_conj ρ ρ' P h L).mpr hL⟩
    rw [dif_pos hex, dif_pos hex', hsw, choose_congr hpred hex' hex]
  · have hex' : ¬ ∃ L, IsAdapted L ρ' := by
      rintro ⟨L, hL⟩; exact hex ⟨L, (isAdapted_conj ρ ρ' P h L).mp hL⟩
    rw [dif_neg hex, dif_neg hex']

/-- **GLUE, proved: the conductor exponent is invariant under conjugation.** -/
theorem condExp_conj (ρ ρ' : _root_.PkgI4.GQp p →* GL (Fin n) k) (P : GL (Fin n) k)
    (h : ∀ σ, ρ' σ = P * ρ σ * P⁻¹) : condExp ρ' = condExp ρ := by
  unfold condExp
  rw [codimInv_conj ρ ρ' P h, swan_conj ρ ρ' P h]

end Conj

/-- **LEAF candidate (consequence, see the report): Carayol's Théorème (A) at his realization.**
For a newform `f ∈ S₂(Γ₁(N))` with nebentypus `χ`, a prime `ℓ` and embeddings `ιC : ℚ̄ → ℂ`,
`ιL : ℚ̄ → ℚ̄_ℓ`, **there is** a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` attached to `f` (arithmetic
Frobenius at `p ∤ Nℓ` has trace `ιL ιC⁻¹ a_p(f)`) whose conductor exponent at every prime `p ≠ ℓ` is
`v_p(N)`.

Source: Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert*,
Ann. Sci. ÉNS (4) 19 (1986), Théorème (A), pp. 409–411, and §0.8 p. 411 (read by the locator audit,
`docs/research/locators.md` row R17: every finite `p` and every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`), at
`F = ℚ`, weight 2: `σ_λ(π_f)|_{G_{ℚ_p}}` corresponds to `π_{f,p}` under the local Langlands
correspondence, so its conductor is `a(π_{f,p})`; with Casselman 1973 (`a(π_{f,p}) = v_p(N)` for a
newform; UNVERIFIED locator) this gives `v_p(N)`. The witness is `σ_λ(π_f)` with coefficients extended to
`ℚ̄_ℓ` along `ιL ιC⁻¹` (or its contragredient, if Carayol's normalization uses geometric Frobenius: the
conductor is unchanged by duals, audit row R17), which is irreducible (Ribet 1977, UNVERIFIED locator), hence
semisimple. Not stronger than the published statements: it asserts the conclusion for one realization only. -/
def CarayolRealization : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : _root_.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : _root_.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : _root_.PkgI4.CF N 2), 0 < N → _root_.PkgI4.IsNewform f χ →
    ∃ ρ : _root_.PkgI4.GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f ∧
      ∀ (p : ℕ) [Fact p.Prime], p ≠ ℓ → condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

/-- **Row r17 (`LadicCond.CarayolR17'`) from `CarayolRealization`.** -/
theorem carayolR17'_of_realization (hC : CarayolRealization) : CarayolR17' := by
  intro ℓ _ ιC ιL N χ f ρ p _ hN hf hss hatt hpl
  obtain ⟨ρ0, hss0, hatt0, hcond0⟩ := hC ℓ ιC ιL N χ f hN hf
  let r0 : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2 := ⟨ρ0.toHom, ρ0.continuous_toHom⟩
  let r : ZInQ.Contrib.G9.PkgI4.GaloisRep ℓ 2 := ⟨ρ.toHom, ρ.continuous_toHom⟩
  have hconj : ZInQ.Contrib.HodgeSplit.IsConj r0 r := by
    refine ZInQ.Contrib.HodgeSplit.attachedConj_proof ℓ r0 r (N * ℓ).primeFactors hss0 hss
      fun q hq hqS => ?_
    have hqN : ¬ q ∣ N * ℓ := by
      intro h
      exact hqS (Nat.mem_primeFactors.mpr ⟨hq, h, Nat.mul_ne_zero (by omega)
        (Fact.out : ℓ.Prime).ne_zero⟩)
    obtain ⟨hu0, α0, hα0, htr0⟩ := hatt0 q hq hqN
    obtain ⟨hu, α, hα, htr⟩ := hatt q hq hqN
    have heq : α0 = α := by
      apply ιC.toRingHom.injective
      change ιC α0 = ιC α
      rw [hα0, hα]
    refine ⟨hu0, hu, fun v σ hv hσ => ?_⟩
    rw [show (r0.mat σ).trace = (ρ0.mat σ).trace from rfl, htr0 v σ hv hσ,
      show (r.mat σ).trace = (ρ.mat σ).trace from rfl, htr v σ hv hσ, heq]
  obtain ⟨P, hP⟩ := hconj
  rw [← hcond0 p hpl]
  exact (condExp_conj (ρ.restrictLocal p) (ρ0.restrictLocal p) P fun σ => hP _).symm

/-- **Converse: the field gives back the existential leaf**, given the bundle LEAF fields `dsThm965`, `dsThm966`
(a semisimple attached `ρ` exists, hodge-split's `r14Det_of_printed`). So `CarayolRealization` is exactly as
strong as the field `CarayolR17'` over the bundle. -/
theorem carayolRealization_of_field (hD : ZInQ.Contrib.HodgeSplit.DSThm965)
    (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) (h : CarayolR17') : CarayolRealization := by
  intro ℓ _ ιC ιL N χ f hN hf
  obtain ⟨ρ, hss, hatt⟩ := ZInQ.Contrib.HodgeSplit.eigenformRepExists_of_r14Det
    (ZInQ.Contrib.HodgeSplit.r14Det_of_printed hD hDS) ℓ ιC ιL N 2 χ f hN (by norm_num) hf.1
  let r : _root_.PkgI4.GaloisRep ℓ 2 := ⟨ρ.toHom, ρ.continuous_toHom⟩
  exact ⟨r, hss, hatt, fun p _ hpl => h ℓ ιC ιL N χ f r p hN hf hss hatt hpl⟩

theorem carayolRealization_iff_field (hD : ZInQ.Contrib.HodgeSplit.DSThm965)
    (hDS : ZInQ.Contrib.HodgeSplit.DSThm966) : CarayolRealization ↔ CarayolR17' :=
  ⟨carayolR17'_of_realization, carayolRealization_of_field hD hDS⟩

end CToPrinted2.R17

/-! ## §0. The three fields, verbatim, checked against the bundle -/

namespace CToPrinted2.Verbatim

open LadicCond _root_.PkgI4 in
/-- `LadicCond.CarayolR17'` (`ZInQKernel/HDecomp/Conductor/LadicCond.lean`), verbatim. -/
def CarayolR17' : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2) (ρ : GaloisRep ℓ 2) (p : ℕ) [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
      condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)

example : CarayolR17' = _root_.LadicCond.CarayolR17' := rfl

open ZInQ.Contrib.G9.PkgI4 (GaloisRep GaloisChar) in
/-- `ZInQ.Contrib.HodgeSplit.EigenformHTNew` (`ZInQKernel/OneProof/H/TailS.lean` §10), verbatim. -/
def EigenformHTNew : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : ZInQ.Contrib.G9.PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : ZInQ.Contrib.G9.PkgI4.CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → ZInQ.Contrib.G9.PkgI4.IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

example : EigenformHTNew = _root_.ZInQ.Contrib.HodgeSplit.EigenformHTNew := rfl

open HDec HDec.WeilPairing PkgI3 in
/-- `WeilPairing.T09_SymmIsogenyExists` (`ZInQKernel/OneProof/H/TailB.lean` §4), verbatim. -/
def T09_SymmIsogenyExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K), Nonempty (SymmIsogeny A)

example : T09_SymmIsogenyExists = HDec.WeilPairing.T09_SymmIsogenyExists := rfl

/-- The bundle fields have exactly these types. -/
example (r : HDec.HSyn.OpenResearchLeaves10) : CarayolR17' := r.r17
example (r : HDec.HSyn.OpenResearchLeaves10) : EigenformHTNew := r.eigenformHTNew
example (l : HDec.HSyn.OpenAddedLeaves9) : T09_SymmIsogenyExists := l.t09SymmIsogenyExists

end CToPrinted2.Verbatim

/-! ## §9. Integration -/

namespace CToPrinted2

/-- **The two fields `eigenformHTNew` and `r17` of the single proof from the realization leaves**, with the
bundle's own LEAF fields `tateTwistInvariants`, `axSenTate` (in `OpenAddedLeaves9`). -/
theorem fields_of_printed (hK : KatoRealizationCohSS) (hC : R17.CarayolRealization)
    (l : HDec.HSyn.OpenAddedLeaves9) :
    ZInQ.Contrib.HodgeSplit.EigenformHTNew ∧ LadicCond.CarayolR17' :=
  ⟨eigenformHTNew_of_printedSS hK l.tateTwistInvariants l.axSenTate, R17.carayolR17'_of_realization hC⟩

end CToPrinted2

#print axioms CToPrinted2.htDual_proof
#print axioms CToPrinted2.eigenformHTNew_of_printed
#print axioms CToPrinted2.eigenformHTNew_of_realization
#print axioms CToPrinted2.eigenformHTNew_of_printedSS
#print axioms CToPrinted2.dualGR_isSemisimple
#print axioms CToPrinted2.katoRealization_iff_field
#print axioms CToPrinted2.katoRealizationCohSS_iff_field
#print axioms CToPrinted2.R17.carayolR17'_of_realization
#print axioms CToPrinted2.R17.carayolRealization_iff_field
#print axioms CToPrinted2.fields_of_printed
