import Mathlib

open IsLocalRing
open scoped Pointwise
set_option linter.style.haveILetI false

namespace GTSHPair

section Count

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

attribute [local instance] Ideal.Quotient.field in
/-- `|D_P| = |I_P| · |Aut(κ(P)/κ(p))|` with no separability hypothesis. -/
theorem card_stabilizer_eq_card_inertia_mul_card_gal (p : Ideal R) [p.IsMaximal]
    (P : Ideal S) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) =
      Nat.card (P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) := by
  have : Subgroup.index _ = _ := Nat.card_congr
    (Ideal.Quotient.stabilizerQuotientInertiaEquiv G p P).toEquiv
  rw [← this, ← ((P.inertia G).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

theorem card_stabilizer_eq_ram_mul_inertiaDeg [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G
  have h2 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)
  rw [Nat.card_prod, Nat.card_coe_set_eq, Algebra.IsInvariant.orbit_eq_primesOver R S G p P] at h2
  have h0 : (p.primesOver S).ncard ≠ 0 := by
    intro h; rw [h, zero_mul] at h1; exact (Nat.card_pos (α := G)).ne' h1.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0) (h2.trans h1.symm)


attribute [local instance] Ideal.Quotient.field in
/-- `|I_P| · |Aut(κ(P)/κ(p))| = e · f` with no separability hypothesis. -/
theorem card_inertia_mul_card_gal [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (p : Ideal R) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (P.inertia G) * Nat.card ((S ⧸ P) ≃ₐ[R ⧸ p] (S ⧸ P)) =
      p.ramificationIdxIn S * p.inertiaDegIn S := by
  rw [← card_stabilizer_eq_card_inertia_mul_card_gal p P, card_stabilizer_eq_ram_mul_inertiaDeg p P]

end Count

/-- For a normal extension, the number of automorphisms is the separable degree. -/
theorem card_aut_eq_finSepDegree (F E : Type*) [Field F] [Field E] [Algebra F E] [Normal F E] :
    Nat.card (E ≃ₐ[F] E) = Field.finSepDegree F E :=
  (Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)).symm

/-- **Separable-degree count.** `F ⊆ E ⊆ L`, `L/F` finite and normal, `L/E` normal. If
`e · [E : F] · |Aut(L/E)| = |Aut(L/F)|` then `e = 1` and `E/F` is separable. -/
theorem eq_one_and_isSeparable_of_card {F E L : Type*} [Field F] [Field E] [Field L] [Algebra F E]
    [Algebra E L] [Algebra F L] [IsScalarTower F E L] [FiniteDimensional F L] [Normal F L]
    [Normal E L] (e : ℕ)
    (h : e * Module.finrank F E * Nat.card (L ≃ₐ[E] L) = Nat.card (L ≃ₐ[F] L)) :
    e = 1 ∧ Algebra.IsSeparable F E := by
  haveI : FiniteDimensional F E := FiniteDimensional.left F E L
  haveI : FiniteDimensional E L := FiniteDimensional.right F E L
  rw [card_aut_eq_finSepDegree, card_aut_eq_finSepDegree,
    ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic F E L] at h
  have hs2 : 0 < Field.finSepDegree E L := Nat.pos_of_ne_zero (NeZero.ne _)
  have h' : e * Module.finrank F E = Field.finSepDegree F E := Nat.eq_of_mul_eq_mul_right hs2 h
  have hle := Field.finSepDegree_le_finrank F E
  have hpos : 0 < Module.finrank F E := Module.finrank_pos
  have hspos : 0 < Field.finSepDegree F E := Nat.pos_of_ne_zero (NeZero.ne _)
  have he : e = 1 := by
    rcases Nat.lt_or_ge e 1 with he | he
    · interval_cases e; omega
    · by_contra hne
      have : 2 * Module.finrank F E ≤ e * Module.finrank F E := Nat.mul_le_mul_right _ (by omega)
      omega
  refine ⟨he, ?_⟩
  rw [he, one_mul] at h'
  exact (Field.finSepDegree_eq_finrank_iff F E).mp h'.symm

attribute [local instance] Ideal.Quotient.field in
/-- **The inertia ring is unramified with separable residue extension** (no separability
hypothesis on residue fields). `A ⊆ R ⊆ S`, `S/A` Galois with group `G`, `S/R` Galois with group the
inertia group `H` of a maximal `P ⊆ S` over `p`. Then `𝔮 = P ∩ R` has ramification index `1` over
`p` and `R/𝔮` is separable over `A/p`. -/
theorem inertia_unram {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [IsDomain A]
    [IsDomain R] [IsDomain S] [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G A S]
    [Module.Finite A S] [Module.Finite R S] [Module.Flat A S] [Module.Flat R S]
    (p : Ideal A) [p.IsMaximal] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [IsGaloisGroup (P.inertia G) R S] [(P.under R).IsMaximal] [(P.under R).LiesOver p] :
    (P.under R).ramificationIdx A = 1 ∧ Algebra.IsSeparable (A ⧸ p) (R ⧸ P.under R) := by
  set 𝔮 := P.under R
  set H := P.inertia G
  haveI : IsScalarTower (A ⧸ p) (R ⧸ 𝔮) (S ⧸ P) := IsScalarTower.of_algebraMap_eq (fun x => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply])
  have hc1 := card_inertia_mul_card_gal (G := G) p P
  have hc3 := card_inertia_mul_card_gal (G := H) 𝔮 P
  have e4 : Nat.card (P.inertia H) = Nat.card H :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (fun h => fun s => h.2 s))
  rw [e4] at hc3
  have hHpos : 0 < Nat.card H := Nat.card_pos
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G, Ideal.inertiaDegIn_eq_inertiaDeg p P G,
    Ideal.ramificationIdx_tower (R := A) 𝔮 P, Ideal.inertiaDeg_tower (R := A) 𝔮 P] at hc1
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔮 P H, Ideal.inertiaDegIn_eq_inertiaDeg 𝔮 P H]
    at hc3
  haveI : Normal (A ⧸ p) (S ⧸ P) := Ideal.Quotient.normal G p P
  haveI : Normal (R ⧸ 𝔮) (S ⧸ P) := Ideal.Quotient.normal H 𝔮 P
  haveI : FiniteDimensional (A ⧸ p) (S ⧸ P) := inferInstance
  refine eq_one_and_isSeparable_of_card (L := S ⧸ P) _ ?_
  rw [← Ideal.inertiaDeg_eq_of_isMaximal p 𝔮]
  have h5 : Nat.card H * Nat.card ((S ⧸ P) ≃ₐ[A ⧸ p] (S ⧸ P)) =
      Nat.card H * (𝔮.ramificationIdx A * 𝔮.inertiaDeg A *
        Nat.card ((S ⧸ P) ≃ₐ[R ⧸ 𝔮] (S ⧸ P))) := by
    rw [hc1]
    calc _ = 𝔮.ramificationIdx A * 𝔮.inertiaDeg A * (P.ramificationIdx R * P.inertiaDeg R) := by ring
      _ = _ := by rw [← hc3]; ring
  exact (Nat.eq_of_mul_eq_mul_left hHpos h5).symm

end GTSHPair
