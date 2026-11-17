/-! # shimura-glue: Baba–Granath and Elkies leaves without the `j`-normalization; Möbius glue -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

open scoped Classical
open ShimuraGlue.Mob (gl2 gl2_apply gl2_smul_some gl2_smul_infty)

/-- **A Möbius transformation over `ℚ` sends three distinct points of `P¹(ℚ)` to `0, ∞, 1`.** -/
theorem exists_mobius01 (a b c : OnePoint ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℚ, g • a = ((0 : ℚ) : OnePoint ℚ) ∧ g • b = OnePoint.infty ∧
      g • c = ((1 : ℚ) : OnePoint ℚ) := by
  induction a using OnePoint.rec with
  | infty =>
    induction b using OnePoint.rec with
    | infty => exact absurd rfl hab
    | coe b =>
      induction c using OnePoint.rec with
      | infty => exact absurd rfl hac
      | coe c =>
        have hcb : c - b ≠ 0 := sub_ne_zero.2 fun e => hbc (by rw [e])
        refine ⟨gl2 0 (c - b) 1 (-b) (by intro e; apply hcb; linear_combination -e), ?_, ?_, ?_⟩
        · rw [gl2_smul_infty]; simp
        · rw [gl2_smul_some]; simp
        · rw [gl2_smul_some, if_neg (by intro e; apply hcb; linear_combination e)]
          congr 1
          rw [div_eq_one_iff_eq (by intro e; apply hcb; linear_combination e)]; ring
  | coe a =>
    induction b using OnePoint.rec with
    | infty =>
      induction c using OnePoint.rec with
      | infty => exact absurd rfl hbc
      | coe c =>
        have hca : c - a ≠ 0 := sub_ne_zero.2 fun e => hac (by rw [e])
        refine ⟨gl2 (1 / (c - a)) (-a / (c - a)) 0 1 (by simpa using hca), ?_, ?_, ?_⟩
        · rw [gl2_smul_some, if_neg (by simp)]
          congr 1; field_simp; ring
        · rw [gl2_smul_infty]; simp
        · rw [gl2_smul_some, if_neg (by simp)]
          congr 1; field_simp; try ring
    | coe b =>
      have hab' : a - b ≠ 0 := sub_ne_zero.2 fun e => hab (by rw [e])
      induction c using OnePoint.rec with
      | infty =>
        refine ⟨gl2 1 (-a) 1 (-b) (by intro e; apply hab'; linear_combination e), ?_, ?_, ?_⟩
        · rw [gl2_smul_some, if_neg (by intro e; apply hab'; linear_combination e)]; simp
        · rw [gl2_smul_some]; simp
        · rw [gl2_smul_infty]; simp
      | coe c =>
        have hca : c - a ≠ 0 := sub_ne_zero.2 fun e => hac (by rw [e])
        have hcb : c - b ≠ 0 := sub_ne_zero.2 fun e => hbc (by rw [e])
        set k := (c - b) / (c - a) with hkdef
        have hk : k ≠ 0 := div_ne_zero hcb hca
        have hkc : k * (c - a) = c - b := by rw [hkdef]; field_simp
        refine ⟨gl2 k (-k * a) 1 (-b) (by
          intro e; apply mul_ne_zero hk hab'; linear_combination e), ?_, ?_, ?_⟩
        · rw [gl2_smul_some, if_neg (by intro e; apply hab'; linear_combination e)]
          congr 1; rw [div_eq_zero_iff]; left; ring
        · rw [gl2_smul_some]; simp
        · rw [gl2_smul_some, if_neg (by intro e; apply hcb; linear_combination e)]
          congr 1
          rw [div_eq_one_iff_eq (by intro e; apply hcb; linear_combination e)]
          linear_combination hkc

/-- Three distinct points of `P¹(ℚ)` go to `0, ∞, −16/27`. -/
theorem exists_mobiusBG (a b c : OnePoint ℚ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ g : GL (Fin 2) ℚ, g • a = ((0 : ℚ) : OnePoint ℚ) ∧ g • b = OnePoint.infty ∧
      g • c = ((-16 / 27 : ℚ) : OnePoint ℚ) := by
  obtain ⟨g, h0, h1, h2⟩ := exists_mobius01 a b c hab hac hbc
  let s := gl2 (-16 / 27) 0 0 1 (by norm_num)
  refine ⟨s * g, ?_, ?_, ?_⟩
  · rw [mul_smul, h0, gl2_smul_some]; simp
  · rw [mul_smul, h1, gl2_smul_infty]; simp
  · rw [mul_smul, h2, gl2_smul_some]; simp

/-- The value transfer: `G·s = (g·t)` over `ℚ̄` iff `s = t`, for `G` the image of `g`. -/
theorem smul_map_iff (g : GL (Fin 2) ℚ) (t : OnePoint ℚ) (s : OnePoint Qbar) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) g • s = (g • t).map (algebraMap ℚ Qbar) ↔
      s = t.map (algebraMap ℚ Qbar) := by
  rw [OnePoint.map_smul]
  exact (MulAction.injective _).eq_iff

/-- **LEAF (Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 (p. 737) and Lemma 3.1 (pp. 739–740),
read by the locator audit: YES; with the CM assignment read from the §3.1 elliptic-order table, p. 740),
without the `j`-normalization.** Some coarse witness of the moduli clause lists carries `π : X₆ → P¹` with
* the fibre clause (Thm 2.1: the polarized moduli space is `V/W`; two `ℚ̄`-points have the same value
  iff their QM pairs are `Aut(𝒪)`-twists, i.e. `W`-conjugate), and
* three distinct points `t₄, t₃, t₂₄ ∈ P¹(ℚ)` (Lemma 3.1: `V/W ≅ P¹_ℚ` and the three distinguished images
  are rational) such that the CM points of discriminants `−4, −3, −24` are exactly the fibres over them.
The last clause (each of `CM(−4)`, `CM(−3)`, `CM(−24)` is one `W`-orbit, over a distinguished point) is read
from the §3.1 elliptic-order table; locators.md grades that table's row NO for a different claim (the
ramification indices), and this reading is UNVERIFIED. Unlike `BabaGranathX6'` the leaf does not fix the
coordinate's values `0, ∞, −16/27` (the normalization the audit did not locate in Thm 2.1/Lemma 3.1); that
is the Möbius computation `babaGranathX6'_of_rational`. It is implied by `BabaGranathX6'` (take
`t = 0, ∞, −16/27`). -/
def BabaGranathRational : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π : ToP1 X.left)
    (t₄ t₃ t₂₄ : OnePoint ℚ),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ t₄ ≠ t₃ ∧ t₄ ≠ t₂₄ ∧ t₃ ≠ t₂₄ ∧
    ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (π.val (K := Qbar) x.left = π.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM4 P.q ↔ π.val (K := Qbar) x.left = t₄.map (algebraMap ℚ Qbar)) ∧
        (HasCM3 P.q ↔ π.val (K := Qbar) x.left = t₃.map (algebraMap ℚ Qbar)) ∧
        (HasCM24 P.q ↔ π.val (K := Qbar) x.left = t₂₄.map (algebraMap ℚ Qbar))

/-- **`BabaGranathX6'` from `BabaGranathRational` and the Möbius glue**: the coordinate sending the
three CM values to `0, ∞, −16/27` (`exists_mobiusBG`). -/
theorem babaGranathX6'_of_rational (h : BabaGranathRational) (hM : MobiusCompose) :
    BabaGranathX6' := by
  obtain ⟨Y, Φ, X, Ψ, fY, π, t₄, t₃, t₂₄, h1, h6, d1, d2, d3, hcl⟩ := h
  obtain ⟨g, hg4, hg3, hg24⟩ := exists_mobiusBG t₄ t₃ t₂₄ d1 d2 d3
  obtain ⟨π', hπ'⟩ := hM X π g
  refine ⟨Y, Φ, X, Ψ, fY, h1, h6, π', fun x x' P Q hP hQ => ?_⟩
  obtain ⟨hf, h4, h3, h24⟩ := hcl x x' P Q hP hQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hπ', hπ', (MulAction.injective _).eq_iff]; exact hf
  · rw [h4, hπ', show (OnePoint.some (0 : Qbar)) = (g • t₄).map (algebraMap ℚ Qbar) by
      rw [hg4]; simp, smul_map_iff]
  · rw [h3, hπ', show (OnePoint.infty : OnePoint Qbar) = (g • t₃).map (algebraMap ℚ Qbar) by
      rw [hg3]; simp, smul_map_iff]
  · rw [h24, hπ', show (OnePoint.some (-16 / 27 : Qbar)) = (g • t₂₄).map (algebraMap ℚ Qbar) by
      rw [hg24]; simp, smul_map_iff]

/-- The conic model in Elkies' coordinate `t = −X²/Z²` (`t = ∞` at the points at infinity). -/
def ConicModelT (X : Over (Spec (CommRingCat.of ℚ))) (t : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ X6Kummer.ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = X6Kummer.conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      t.val (K := Qbar) x.left = OnePoint.some (-(p.1.1 ^ 2))) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → t.val (K := Qbar) x.left = OnePoint.infty)

/-- **LEAF (Elkies, ANTS-III, LNCS 1423 (1998), §3, in his coordinate; locators UNVERIFIED).** Some
witness of the moduli clause lists carries Elkies' coordinate `t : X₆ → X*(6) = X₆/W ≅ P¹` with
* the fibre clause (`t` is a coordinate on `X₆/W`: equal values iff `W`-conjugate),
* `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`, and
* the Kummer description `X₆ = X*(6)(√−t, √(3(t − 1)))` on `ℚ̄`-points, written in the Kummer coordinates
  `X/Z = √−t`, `Y/Z = √(3(t − 1))` (so `Y² + 3X² + 3Z² = 0` and `t = −X²/Z²`): `ConicModelT`.
Reading (SPECULATIVE): Elkies' statement is about function fields; this is its form on the points of the
smooth projective model. Residue fields pin `t = 1 ↔ D = −4` (the fibre over `t = 1` has residue field
`ℚ(i)`); the assignment of `0, ∞` to `D = −24, −3` rests on Elkies' text (UNVERIFIED, no network). It does not use Baba–Granath's `j` (the relation `j = 16(t − 1)/27` is the
Möbius computation in `elkiesConicX6_of_t`). -/
def ElkiesConicT : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    ConicModelT X t

/-- `j = 16(t − 1)/27`. -/
noncomputable def gJ : GL (Fin 2) ℚ := gl2 (16 / 27) (-16 / 27) 0 1 (by norm_num)

theorem gJ_smul (s : OnePoint Qbar) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) gJ • s =
      s.map (fun z : Qbar => 16 * (z - 1) / 27) := by
  induction s using OnePoint.rec with
  | infty => rw [OnePoint.smul_infty_eq_ite]; simp [Matrix.GeneralLinearGroup.map_apply, gJ, gl2_apply]
  | coe z =>
    rw [OnePoint.smul_some_eq_ite]
    simp [Matrix.GeneralLinearGroup.map_apply, gJ, gl2_apply]
    ring

/-- **`ElkiesConicX6` from Elkies' statement in his coordinate and the Möbius glue** (`j = 16(t−1)/27`
sends `0, 1, ∞` to `−16/27, 0, ∞` and `−X²/Z²` to `−16(X² + Z²)/(27Z²)`). -/
theorem elkiesConicX6_of_t (h : ElkiesConicT) (hM : MobiusCompose) : ElkiesConicX6 := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, e, he, hp, hi⟩ := h
  obtain ⟨π', hπ'⟩ := hM X t gJ
  refine ⟨Y, Φ, X, Ψ, fY, π', h1, h6, fun x x' P Q hP hQ => ?_, e, he, fun x p hx => ?_,
    fun x b hx => ?_⟩
  · obtain ⟨hf, h24, h4, h3⟩ := hcl x x' P Q hP hQ
    refine ⟨?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
    · rw [hπ', hπ', (MulAction.injective _).eq_iff]; exact hf
    · rw [hπ', gJ_smul, h4 c]; simp
    · rw [hπ', gJ_smul, h3 c]; rfl
    · rw [hπ', gJ_smul, h24 c]; simp; try ring
  · rw [hπ', gJ_smul, hp x p hx]; simp; try ring
  · rw [hπ', gJ_smul, hi x b hx]; rfl

/-! ### Converses: the new leaves follow from the old ones (so they are not stronger) -/

/-- `BabaGranathRational` from `BabaGranathX6'` (take `t = 0, ∞, −16/27`). -/
theorem babaGranathRational_of (h : BabaGranathX6') : BabaGranathRational := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6, π₆, h2⟩ := h
  refine ⟨Y, Φ, X, Ψ, fY, π₆, ((0 : ℚ) : OnePoint ℚ), OnePoint.infty, ((-16 / 27 : ℚ) : OnePoint ℚ),
    h1, h6, OnePoint.coe_ne_infty _, ?_, (OnePoint.coe_ne_infty _).symm, fun x x' P Q hP hQ => ?_⟩
  · intro e; have := OnePoint.coe_injective e; norm_num at this
  · obtain ⟨hf, h4, h3, h24⟩ := h2 x x' P Q hP hQ
    refine ⟨hf, ?_, ?_, ?_⟩
    · rw [h4]; simp
    · rw [h3]; rfl
    · rw [h24]; simp

/-- `t = 27 j/16 + 1`. -/
noncomputable def gT : GL (Fin 2) ℚ := gl2 (27 / 16) 1 0 1 (by norm_num)

theorem gT_smul (s : OnePoint Qbar) :
    Matrix.GeneralLinearGroup.map (algebraMap ℚ Qbar) gT • s =
      s.map (fun z : Qbar => 27 * z / 16 + 1) := by
  induction s using OnePoint.rec with
  | infty => rw [OnePoint.smul_infty_eq_ite]; simp [Matrix.GeneralLinearGroup.map_apply, gT, gl2_apply]
  | coe z =>
    rw [OnePoint.smul_some_eq_ite]
    simp [Matrix.GeneralLinearGroup.map_apply, gT, gl2_apply]
    ring

/-- `ElkiesConicT` from `ElkiesConicX6` (`t = 27 j/16 + 1`). -/
theorem elkiesConicT_of (h : ElkiesConicX6) : ElkiesConicT := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, h6, h2, e, he, hp, hi⟩ := h
  obtain ⟨t, ht⟩ := mobiusCompose X π₆ gT
  refine ⟨Y, Φ, X, Ψ, fY, t, h1, h6, fun x x' P Q hP hQ => ?_, e, he, fun x p hx => ?_,
    fun x b hx => ?_⟩
  · obtain ⟨hf, h4, h3, h24⟩ := h2 x x' P Q hP hQ
    refine ⟨?_, fun c => ?_, fun c => ?_, fun c => ?_⟩
    · rw [ht, ht, (MulAction.injective _).eq_iff]; exact hf
    · rw [ht, gT_smul, h24 c]; simp; try ring
    · rw [ht, gT_smul, h4 c]; simp
    · rw [ht, gT_smul, h3 c]; rfl
  · rw [ht, gT_smul, hp x p hx]; simp; try ring
  · rw [ht, gT_smul, hi x b hx]; rfl

/-- **`BabaGranathX6'` from `BabaGranathRational` alone** (the Möbius glue is proved:
`mobiusCompose`). -/
theorem babaGranathX6'_of_rational' (h : BabaGranathRational) : BabaGranathX6' :=
  babaGranathX6'_of_rational h mobiusCompose

/-- **`ElkiesConicX6` from `ElkiesConicT` alone.** -/
theorem elkiesConicX6_of_t' (h : ElkiesConicT) : ElkiesConicX6 :=
  elkiesConicX6_of_t h mobiusCompose

/-- **The bundle with the printed Deligne leaves, Baba–Granath without the `j`-normalization and
Elkies in his coordinate.** -/
structure ShimuraGlueLeaves2 : Prop where
  deligneX6P : ShimuraGlue.DeligneComponentsX6Printed
  geomConn : GeomConnOfAlgClosure
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  reciprocity : ReciprocityCanonical
  gonzalezRotger : GonzalezRotgerX6
  gonzalezRotgerCount : ShimuraSplit.GonzalezRotgerCountX6
  deligneY3P : ShimuraGlue.DeligneComponentsY3Printed
  elkiesT : ElkiesConicT

theorem shimuraGlueLeaves_of_2 (L : ShimuraGlueLeaves2) : ShimuraGlueLeaves :=
  ⟨L.deligneX6P, L.geomConn, L.t5, babaGranathX6'_of_rational' L.babaGranathR, L.reciprocity,
    L.gonzalezRotger, L.gonzalezRotgerCount, L.deligneY3P, elkiesConicX6_of_t' L.elkiesT⟩

/-- **Rows `r1r2`, `r1rec`, `r5`, `r5count`, `y3Connected`, `x6ConicModel` from `ShimuraGlueLeaves2`.** -/
theorem rows_of_shimuraGlueLeaves2 (L : ShimuraGlueLeaves2) :
    LeafAdopt.R1R2fpRep ∧ LeafQM.AV.R1rec ∧ LeafQM.AV.R5fp ∧ LeafQM.AV.R5fpCount ∧
      TSHecke.Y3Connected ∧ X6Kummer.X6ConicModel :=
  rows_of_shimuraGlueLeaves (shimuraGlueLeaves_of_2 L)

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.babaGranathX6'_of_rational'
#print axioms HDec.QMSplit.Moduli.elkiesConicX6_of_t'
#print axioms HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves2
#print axioms HDec.QMSplit.Moduli.babaGranathRational_of
#print axioms HDec.QMSplit.Moduli.elkiesConicT_of

example : HDec.QMSplit.Moduli.ShimuraGlueLeaves2 →
    HDec.LeafAdopt.R1R2fpRep ∧ _root_.LeafQM.AV.R1rec ∧ _root_.LeafQM.AV.R5fp ∧
      _root_.LeafQM.AV.R5fpCount ∧ HDec.TSHecke.Y3Connected ∧ HDec.X6Kummer.X6ConicModel :=
  HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves2

#print axioms HDec.QMSplit.Moduli.babaGranathX6'_of_rational
#print axioms HDec.QMSplit.Moduli.elkiesConicX6_of_t
