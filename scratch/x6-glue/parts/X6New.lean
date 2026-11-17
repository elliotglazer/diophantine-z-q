/-! # x6-glue Part 4: Elkies' leaf in printed (equations) form; `r1r2` and `x6ConicModel` from published-form
leaves -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF (Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), §3 (the curve `X*(6)`);
locators and the exact display UNVERIFIED, from memory, no network).** Some witness of the moduli clause
lists (the canonical `Y₃`, `X₆ = X₀(6,1)` with its moduli bijection `Ψ`) carries Elkies' coordinate
`t : X₆ → X*(6) = X₆/W ≅ P¹` with:
* the fibre clause: `t` is a coordinate on `X₆/W` (equal values iff the QM pairs are `Aut(𝒪)`-twists;
  `W ≅ Aut(𝒪) ≅ (ℤ/2)²` acting by twists is the moduli meaning of the Atkin–Lehner group, as in
  Baba–Granath Thm 2.1);
* `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3` (Elkies' normalization; the assignment of
  `0` and `∞` is UNVERIFIED, residue fields pin `t = 1 ↔ D = −4`);
* **Elkies' equations** `X₆ = X*(6)(√−t, √(3(t − 1)))`, as the curve over the `t`-line:
  `ElkiesCharts X t` says that over `t ≠ ∞` the curve is `s² = −t, r² = 3(t − 1)` and over `t ≠ 0` it is
  `a² = −1/t, b² = 3(1/t − 1)` with `a = 1/s, b = r/s` (both opens affine with exactly these coordinate
  rings).
*Form*: Elkies prints the function field `ℚ(X₆) = ℚ(t)(√−t, √(3(t−1)))`; `ElkiesCharts` is the smooth
projective model of that function field (the affine curve `s² = −t, r² = 3(t − 1)` is smooth, since it is
`r² + 3s² + 3 = 0` with `t = −s²`, so it is the normalization of the `t`-line in that field; Hartshorne
I.6, II.6.7). The model statement replaces shimura-glue's points form `ConicModelT`, which
`X6Glue.conicModelT_of_charts` now derives. The fibre and CM clauses are those of `ElkiesConicT`
verbatim. -/
def ElkiesEquationsX6 : Prop :=
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
    X6Glue.ElkiesCharts X t

/-- **shimura-glue's `ElkiesConicT` from Elkies' equations** (`conicModelT_of_charts`). -/
theorem elkiesConicT_of_equations (h : ElkiesEquationsX6) : ElkiesConicT := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, hc⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, X6Glue.conicModelT_of_charts hc⟩

/-- **shimura-split's `ElkiesConicX6` from Elkies' equations** (with the proved Möbius glue,
`j = 16(t − 1)/27`). -/
theorem elkiesConicX6_of_equations (h : ElkiesEquationsX6) : ElkiesConicX6 :=
  elkiesConicX6_of_t' (elkiesConicT_of_equations h)

/-- **The row `r1r2` from published-form leaves** (and one consequence, `RayClassCM`):
* `DeligneComponentsX6Printed`: Deligne's `π₀` display at level `𝒪̂^×` (printed form; the double coset
  `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` is computed in Lean, `ShimuraGlue.pi0_Kfull_eq_one`);
* `GeomConnOfAlgClosure`: EGA IV 4.5 / Stacks 0389, weakened (textbook);
* T5 (`PkgI2.TorsionStructure`, `A(k̄)[n] ≅ (ℤ/n)^{2g}`, textbook; Mumford §4);
* `BabaGranathRational`: Baba–Granath Thm 2.1 and Lemma 3.1 (printed; the CM assignment read from the §3.1
  table, UNVERIFIED);
* `RayClassCM`: Shimura reciprocity at CM points in ray-class form (**consequence**);
* `GonzalezRotgerX6`: González–Rotger 2006 Thm 5.12 (printed, on the canonical model). -/
theorem r1r2_of_published (hD : ShimuraGlue.DeligneComponentsX6Printed) (hE : GeomConnOfAlgClosure)
    (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational) (hR : ShimuraGlue.Ray.RayClassCM)
    (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of_printed_t5 (ShimuraGlue.deligneComponentsX6_of_printed hD) hE hT
    (babaGranathX6'_of_rational' hB) (ShimuraGlue.Ray.reciprocityCanonical_of_rayClass hR) hG

/-- **The row `x6ConicModel` from published-form leaves**: those of `r1r2_of_published` and Elkies'
equations `ElkiesEquationsX6`. -/
theorem x6ConicModel_of_published (hD : ShimuraGlue.DeligneComponentsX6Printed)
    (hE : GeomConnOfAlgClosure) (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) (hC : ElkiesEquationsX6) :
    X6Kummer.X6ConicModel :=
  x6ConicModel_of_elkies_t5 (r1r2_of_published hD hE hT hB hR hG) (elkiesConicX6_of_equations hC) hT

/-- **The leaves of the two `X₆` fields** `r1r2` and `x6ConicModel`. -/
structure X6Leaves : Prop where
  deligneX6P : ShimuraGlue.DeligneComponentsX6Printed
  geomConn : GeomConnOfAlgClosure
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  rayClass : ShimuraGlue.Ray.RayClassCM
  gonzalezRotger : GonzalezRotgerX6
  elkiesEq : ElkiesEquationsX6

theorem x6Rows_of_leaves (L : X6Leaves) : LeafAdopt.R1R2fpRep ∧ X6Kummer.X6ConicModel :=
  ⟨r1r2_of_published L.deligneX6P L.geomConn L.t5 L.babaGranathR L.rayClass L.gonzalezRotger,
    x6ConicModel_of_published L.deligneX6P L.geomConn L.t5 L.babaGranathR L.rayClass L.gonzalezRotger
      L.elkiesEq⟩

/-- **The bundle `ShimuraGlueLeaves3` with Elkies' equations in place of `ElkiesConicT`.** -/
structure ShimuraGlueLeaves4 : Prop where
  deligneX6P : ShimuraGlue.DeligneComponentsX6Printed
  geomConn : GeomConnOfAlgClosure
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  rayClass : ShimuraGlue.Ray.RayClassCM
  gonzalezRotger : GonzalezRotgerX6
  gonzalezRotgerCount : ShimuraSplit.GonzalezRotgerCountX6
  deligneY3P : ShimuraGlue.DeligneComponentsY3Printed
  elkiesEq : ElkiesEquationsX6

theorem rows_of_shimuraGlueLeaves4 (L : ShimuraGlueLeaves4) :
    LeafAdopt.R1R2fpRep ∧ LeafQM.AV.R1rec ∧ LeafQM.AV.R5fp ∧ LeafQM.AV.R5fpCount ∧
      TSHecke.Y3Connected ∧ X6Kummer.X6ConicModel :=
  rows_of_shimuraGlueLeaves3 ⟨L.deligneX6P, L.geomConn, L.t5, L.babaGranathR, L.rayClass,
    L.gonzalezRotger, L.gonzalezRotgerCount, L.deligneY3P, elkiesConicT_of_equations L.elkiesEq⟩

end HDec.QMSplit.Moduli

#print axioms X6Glue.ev_injective
#print axioms X6Glue.ev_surjective
#print axioms X6Glue.conicModelT_of_charts
#print axioms HDec.QMSplit.Moduli.elkiesConicT_of_equations
#print axioms HDec.QMSplit.Moduli.elkiesConicX6_of_equations
#print axioms HDec.QMSplit.Moduli.r1r2_of_published
#print axioms HDec.QMSplit.Moduli.x6ConicModel_of_published
#print axioms HDec.QMSplit.Moduli.x6Rows_of_leaves
#print axioms HDec.QMSplit.Moduli.rows_of_shimuraGlueLeaves4

/-- The fully qualified statements (the row types as the bundle states them). -/
example : HDec.QMSplit.Moduli.X6Leaves → HDec.LeafAdopt.R1R2fpRep ∧ HDec.X6Kummer.X6ConicModel :=
  HDec.QMSplit.Moduli.x6Rows_of_leaves
