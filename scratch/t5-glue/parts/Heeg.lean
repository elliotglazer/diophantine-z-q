
noncomputable section

set_option maxRecDepth 20000

namespace T5Glue

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise

/-! ## §5b. `IdeleLatticeHeegner` split: the lattice computation and strong approximation -/

/-- **GLUE IDELE-SCALE (the lattice computation, shimura-modfn §1).** Under the hypotheses of
`IdeleLatticeHeegner`: `κ(s⁻¹𝔞) = c'·⟨1, τ_{Q'}⟩` and `κ(s⁻¹𝔞_N) = c'·⟨1/N, τ_{Q'}⟩` for one
`c' ≠ 0`, where `𝔞 = κ⁻¹⟨1, τ_Q⟩`, `𝔞_N = κ⁻¹⟨1/N, τ_Q⟩`. (`s = k·s_J·w`, `k ∈ Kˣ`, `w ∈ Ô^×ℂˣ`;
both lattices are `κ(O)`-stable (`⟨1, τ_Q⟩` has multiplier ring `O`, `Q` being primitive of
discriminant `disc O`; `⟨1/N, τ_Q⟩ = N⁻¹⟨1, Nτ_Q⟩` comes from `[A/N, B, CN]`, possibly imprimitive,
with multiplier ring `⊇ O`; kernel `kappa_mul_mem_lat`, `kappa_mul_mem_latN_gen`), so `w` fixes their
closures and `s⁻¹(𝔞, 𝔞_N) = k⁻¹(J ∩ O)⁻¹(𝔞, 𝔞_N)`; localizing `κ(J ∩ O)·L' = c·L` (at `p ∤ f`,
`(J ∩ O)_p = J_p = s_{J,p}𝒪_p`; at `p ∣ f`, `(J ∩ O)_p = O_p`) gives `κ((J ∩ O)⁻¹𝔞) = c⁻¹⟨1, τ_{Q'}⟩`,
and likewise for `𝔞_N` with the same `c`. Needs the identity
`ker(ringClassIdeleQuotient) = Kˣ·Ô^×·ℂˣ`, which Tau Ceti states through ray classes only.) -/
def IdeleLatticeScale : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (m f : ℕ) [NeZero m] [NeZero f], Squarefree m →
  ∀ (J : integralIdealsPrimeTo (conductorOrder (QNeg m) f).conductorModulus)
    (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)),
    ringClassIdeleQuotient (conductorOrder (QNeg m) f) (icl s) =
      (conductorOrder (QNeg m) f).picClass J →
  ∀ (D : ℤ), D = discOf m f → ∀ (Q Q' : HeegnerForm N D) (c : ℂ),
    idealLat m f J * Q'.lat = Q.lat.map (LinearMap.mulLeft ℤ c) →
    idealLat m f J * Q'.latN = Q.latN.map (LinearMap.mulLeft ℤ c) →
    ∃ c' : ℂ, c' ≠ 0 ∧
      kappa m '' sInvLat m s (kappa m ⁻¹' (Q.lat : Set ℂ)) = c' • (Q'.lat : Set ℂ) ∧
      kappa m '' sInvLat m s (kappa m ⁻¹' (Q.latN : Set ℂ)) = c' • (Q'.latN : Set ℂ)

/-- **STRONG-APPROX (adelic; proved in §5d, `strongApprox`, from Tau Ceti's strong approximation).**
For the lattice `𝔞 = κ⁻¹⟨1, τ_Q⟩` of a Heegner form and an idele `s`, every `u ∈ K` has an
`s⁻¹u ∈ K/s⁻¹𝔞`: some `v ∈ K` with `s_f v − u ∈ 𝔞̂`. -/
def StrongApprox : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m → ∀ (f : ℕ) [NeZero f] (D : ℤ), D = discOf m f →
    ∀ (N : ℕ) (Q : HeegnerForm N D) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (u : QNeg m),
    ∃ v : QNeg m, finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈
      latHat m (kappa m ⁻¹' (Q.lat : Set ℂ))

section Aux

variable {m : ℕ} [NeZero m]

theorem latHat_eq_closure (M : Submodule ℤ (QNeg m)) :
    latHat m (M : Set (QNeg m)) =
      ((M.toAddSubgroup.map (algebraMap (QNeg m) (AfK m)).toAddMonoidHom).topologicalClosure :
        Set (AfK m)) := by
  rw [AddSubgroup.topologicalClosure_coe, latHat]
  rfl

theorem latHat_sub_mem (M : Submodule ℤ (QNeg m)) {x y : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) (hy : y ∈ latHat m (M : Set (QNeg m))) :
    x - y ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx hy ⊢
  exact AddSubgroup.sub_mem _ hx hy

theorem latHat_add_mem (M : Submodule ℤ (QNeg m)) {x y : AfK m}
    (hx : x ∈ latHat m (M : Set (QNeg m))) (hy : y ∈ latHat m (M : Set (QNeg m))) :
    x + y ∈ latHat m (M : Set (QNeg m)) := by
  rw [latHat_eq_closure] at hx hy ⊢
  exact AddSubgroup.add_mem _ hx hy

theorem mem_latHat_of_mem {𝔞 : Set (QNeg m)} {x : QNeg m} (hx : x ∈ 𝔞) :
    algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞 :=
  subset_closure ⟨x, hx, rfl⟩

theorem latHat_mono {𝔞 𝔟 : Set (QNeg m)} (h : 𝔞 ⊆ 𝔟) : latHat m 𝔞 ⊆ latHat m 𝔟 :=
  closure_mono (Set.image_mono h)

/-- `κ⁻¹(L)` for a `ℤ`-submodule `L ⊂ ℂ`, as a submodule of `K`. -/
def kappaComap (L : Submodule ℤ ℂ) : Submodule ℤ (QNeg m) := L.comap (kappaLin m)

theorem coe_kappaComap (L : Submodule ℤ ℂ) :
    ((kappaComap (m := m) L : Submodule ℤ (QNeg m)) : Set (QNeg m)) = kappa m ⁻¹' (L : Set ℂ) := by
  ext x; simp [kappaComap, kappaLin_apply]

theorem kappa_sub (a b : QNeg m) : kappa m (a - b) = kappa m a - kappa m b := by
  simp only [← kappaAlg_apply, map_sub]

theorem lat_le_latN {N : ℕ} {D : ℤ} (Q : HeegnerForm N D) (hN : 0 < N) : Q.lat ≤ Q.latN := by
  rw [HeegnerForm.lat, Submodule.span_le]
  intro x hx
  rcases hx with rfl | rfl
  · have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have : (1 : ℂ) = (N : ℤ) • (1 / (N : ℂ)) := by rw [zsmul_eq_mul]; push_cast; field_simp
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · exact Submodule.subset_span (by simp)

theorem mem_smul_set_sub {c : ℂ} {L : Submodule ℤ ℂ} {x y : ℂ} (hx : x ∈ c • (L : Set ℂ))
    (hy : y ∈ c • (L : Set ℂ)) : x - y ∈ c • (L : Set ℂ) := by
  obtain ⟨a, ha, rfl⟩ := Set.mem_smul_set.1 hx
  obtain ⟨b, hb, rfl⟩ := Set.mem_smul_set.1 hy
  exact Set.mem_smul_set.2 ⟨a - b, L.sub_mem ha hb, by simp [smul_eq_mul, mul_sub]⟩

/-- `(k − k')/N ∈ ⟨1, τ⟩` with `k, k' < N − 1` forces `k = k'`. -/
theorem eq_of_sub_div_mem (τ : UpperHalfPlane) {N k k' : ℕ} (hk : k < N - 1) (hk' : k' < N - 1)
    (h : (((k : ℂ) + 1) / N - ((k' : ℂ) + 1) / N) ∈ (pp τ).lattice) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := div_nat_not_mem τ (a := k' - k) (N := N) (by omega) (by omega)
    apply this
    have e : (((k' - k : ℕ) : ℂ) / N) = -((((k : ℂ) + 1) / N - ((k' : ℂ) + 1) / N)) := by
      rw [Nat.cast_sub hlt.le]; ring
    rw [e]; exact (pp τ).lattice.neg_mem h
  · have := div_nat_not_mem τ (a := k - k') (N := N) (by omega) (by omega)
    apply this
    have e : (((k - k' : ℕ) : ℂ) / N) = (((k : ℂ) + 1) / N - ((k' : ℂ) + 1) / N) := by
      rw [Nat.cast_sub hlt.le]; ring
    rw [e]; exact h

theorem linIndep_one_t {D : ℤ} {N : ℕ} (Q : HeegnerForm N D) {t : QNeg m}
    (ht : kappa m t = Q.tau) : LinearIndependent ℚ ![(1 : QNeg m), t] := by
  have him : t.im ≠ 0 := by
    intro h0
    have hQ : (Q.tau).im = 0 := by
      rw [← ht]; simp [kappa, h0]
    have := Q.tauH.im_pos
    exact absurd hQ (ne_of_gt this)
  rw [LinearIndependent.pair_iff]
  intro p q hpq
  have h2 := congrArg QuadraticAlgebra.im hpq
  simp at h2
  rcases h2 with h2 | h2
  · subst h2
    have := congrArg QuadraticAlgebra.re hpq
    simp at this
    exact ⟨this, rfl⟩
  · exact absurd h2 him

end Aux

/-- **`IdeleLatticeHeegner` from the lattice computation, strong approximation and `LatHatInter`.**
The permutation `π` of the nonzero points of `⟨1/N⟩` is built in Lean. -/
theorem ideleLatticeHeegner_of (hS : IdeleLatticeScale) (hSA : StrongApprox) (hI : LatHatInter) :
    IdeleLatticeHeegner := by
  intro N hN m f _ _ hsq J s hcl D hD Q Q' c hLc hLN
  obtain ⟨c', hc', h1, h2⟩ := hS N hN m f hsq J s hcl D hD Q Q' c hLc hLN
  refine ⟨c', hc', h1, ?_⟩
  obtain ⟨t, ht⟩ := exists_kappa_tau (m := m) hD Q
  set 𝔞 : Set (QNeg m) := kappa m ⁻¹' (Q.lat : Set ℂ) with h𝔞
  have h𝔞span : 𝔞 = (Submodule.span ℤ {(1 : QNeg m), t} : Set (QNeg m)) :=
    preimage_lat_eq_span hD Q ht
  have h𝔞M : 𝔞 = ((kappaComap (m := m) Q.lat : Submodule ℤ (QNeg m)) : Set (QNeg m)) :=
    (coe_kappaComap Q.lat).symm
  have h𝔞NM : kappa m ⁻¹' (Q.latN : Set ℂ) =
      ((kappaComap (m := m) Q.latN : Submodule ℤ (QNeg m)) : Set (QNeg m)) :=
    (coe_kappaComap Q.latN).symm
  -- `K ∩ 𝔞̂ = 𝔞`
  have hInt : ∀ x : QNeg m, algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔞 → x ∈ 𝔞 := by
    intro x hx
    have := hI m hsq f D hD N Q
    exact (Set.ext_iff.1 this x).1 hx
  set u : Fin (N - 1) → QNeg m := fun k => algebraMap ℚ (QNeg m) (((k : ℕ) + 1 : ℚ) / N) with hu
  have hku : ∀ k : Fin (N - 1), kappa m (u k) = (((k : ℕ) : ℂ) + 1) / N := by
    intro k; simp only [hu]; rw [kappa_rat]; push_cast; rfl
  have hv : ∀ k : Fin (N - 1), ∃ v : QNeg m,
      finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) (u k) ∈ latHat m 𝔞 := by
    intro k
    exact hSA m hsq f D hD N Q s (u k)
  choose v hv using hv
  -- `v k ∈ s⁻¹𝔞_N`
  have hvN : ∀ k, v k ∈ sInvLat m s (kappa m ⁻¹' (Q.latN : Set ℂ)) := by
    intro k
    show finPart s * algebraMap (QNeg m) (AfK m) (v k) ∈ latHat m (kappa m ⁻¹' (Q.latN : Set ℂ))
    have e : finPart s * algebraMap (QNeg m) (AfK m) (v k) =
        (finPart s * algebraMap (QNeg m) (AfK m) (v k) - algebraMap (QNeg m) (AfK m) (u k)) +
          algebraMap (QNeg m) (AfK m) (u k) := by ring
    rw [e, h𝔞NM]
    apply latHat_add_mem
    · rw [← h𝔞NM]
      exact latHat_mono (fun x hx => lat_le_latN Q hN hx) (hv k)
    · apply mem_latHat_of_mem
      rw [← h𝔞NM]
      show kappa m (u k) ∈ Q.latN
      rw [hku k]
      have hk1 : ((((k : ℕ) : ℂ) + 1) / N) = ((k : ℕ) + 1 : ℤ) • (1 / (N : ℂ)) := by
        rw [zsmul_eq_mul]; push_cast; ring
      rw [hk1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  -- `v k ∉ s⁻¹𝔞`
  have hvnot : ∀ k, v k ∉ sInvLat m s 𝔞 := by
    intro k hk
    have : algebraMap (QNeg m) (AfK m) (u k) ∈ latHat m 𝔞 := by
      have e : algebraMap (QNeg m) (AfK m) (u k) = finPart s * algebraMap (QNeg m) (AfK m) (v k) -
          (finPart s * algebraMap (QNeg m) (AfK m) (v k) - algebraMap (QNeg m) (AfK m) (u k)) := by ring
      rw [e, h𝔞M]
      apply latHat_sub_mem
      · rw [← h𝔞M]; exact hk
      · rw [← h𝔞M]; exact hv k
    have hu𝔞 := hInt _ this
    have : kappa m (u k) ∈ Q.lat := hu𝔞
    rw [hku k] at this
    exact div_nat_not_mem Q.tauH (a := (k : ℕ) + 1) (N := N) (by omega) (by omega)
      (by push_cast; exact this)
  -- the index `π k`
  have hj : ∀ k : Fin (N - 1), ∃ j : Fin (N - 1),
      kappa m (v k) - c' * ((((j : ℕ) : ℂ) + 1) / N) ∈ c' • (Q'.lat : Set ℂ) := by
    intro k
    have hmem : kappa m (v k) ∈ c' • (Q'.latN : Set ℂ) := by
      rw [← h2]; exact ⟨v k, hvN k, rfl⟩
    obtain ⟨y, hy, hyv⟩ := Set.mem_smul_set.1 hmem
    rw [SetLike.mem_coe, HeegnerForm.latN, Submodule.mem_span_pair] at hy
    obtain ⟨a, b, rfl⟩ := hy
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hNi : (0 : ℤ) < N := by exact_mod_cast hN
    set r := a % (N : ℤ) with hr
    set q := a / (N : ℤ) with hq
    have har : a = r + N * q := by
      rw [hr, hq]; have := Int.emod_add_ediv_mul a N; linarith
    have hr0 : 0 ≤ r := Int.emod_nonneg a (by omega)
    have hrN : r < N := Int.emod_lt_of_pos a hNi
    have key : kappa m (v k) - c' * (r / N) = c' * ((q : ℂ) * 1 + (b : ℂ) * Q'.tau) := by
      rw [← hyv, smul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, har]; push_cast; field_simp; ring
    have hkeymem : kappa m (v k) - c' * (r / N) ∈ c' • (Q'.lat : Set ℂ) := by
      rw [key]
      refine Set.mem_smul_set.2 ⟨(q : ℂ) * 1 + (b : ℂ) * Q'.tau, ?_, rfl⟩
      rw [SetLike.mem_coe, HeegnerForm.lat, Submodule.mem_span_pair]
      exact ⟨q, b, by simp [zsmul_eq_mul]⟩
    have hr1 : r ≠ 0 := by
      intro hr0'
      rw [hr0'] at hkeymem
      simp only [Int.cast_zero, zero_div, mul_zero, sub_zero] at hkeymem
      rw [← h1] at hkeymem
      obtain ⟨w, hw, hwv⟩ := hkeymem
      have := kappa_injective hwv
      rw [this] at hw
      exact hvnot k hw
    refine ⟨⟨r.toNat - 1, by omega⟩, ?_⟩
    have hrc : ((((r.toNat - 1 : ℕ) : ℂ) + 1)) = (r : ℂ) := by
      have : ((r.toNat - 1 : ℕ) : ℤ) + 1 = r := by omega
      exact_mod_cast this
    rw [hrc]
    exact hkeymem
  choose π0 hπ0 using hj
  have hinj : Function.Injective π0 := by
    intro k k' hkk
    have hd : kappa m (v k) - kappa m (v k') ∈ c' • (Q'.lat : Set ℂ) := by
      have := mem_smul_set_sub (hπ0 k) (hπ0 k')
      rw [hkk] at this
      convert this using 1; ring
    rw [← kappa_sub, ← h1] at hd
    obtain ⟨w, hw, hwv⟩ := hd
    have hw' := kappa_injective hwv
    rw [hw'] at hw
    have hdiff : algebraMap (QNeg m) (AfK m) (u k - u k') ∈ latHat m 𝔞 := by
      have e : algebraMap (QNeg m) (AfK m) (u k - u k') =
          finPart s * algebraMap (QNeg m) (AfK m) (v k - v k') -
            (finPart s * algebraMap (QNeg m) (AfK m) (v k) - algebraMap (QNeg m) (AfK m) (u k)) +
            (finPart s * algebraMap (QNeg m) (AfK m) (v k') - algebraMap (QNeg m) (AfK m) (u k')) := by
        simp only [map_sub]; ring
      rw [e, h𝔞M]
      refine latHat_add_mem _ (latHat_sub_mem _ ?_ ?_) ?_
      · rw [← h𝔞M]; exact hw
      · rw [← h𝔞M]; exact hv k
      · rw [← h𝔞M]; exact hv k'
    have h3 : kappa m (u k - u k') ∈ Q.lat := hInt _ hdiff
    rw [kappa_sub, hku, hku] at h3
    exact Fin.ext (eq_of_sub_div_mem Q.tauH k.2 k'.2 h3)
  exact ⟨Equiv.ofBijective π0 (Finite.injective_iff_bijective.1 hinj), fun k => ⟨v k, hv k, hπ0 k⟩⟩

end T5Glue
