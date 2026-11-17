"""Generate ZInQKernel/OneProof/H/TailZ22.lean: the abelian-scheme forms of x6-glue's five moduli leaves, the bundles
OpenResearchLeaves13 / OpenAddedLeaves12, the conversions and sixContactMin_of_open16."""
D = 'scratch/x6-fold/'
R = open(D + 'R12.txt').read().rstrip('\n'); A = open(D + 'A11.txt').read().rstrip('\n')
Rf = [f for f in open(D + 'R12_fields.txt').read().split() if f != 'r1r2Ab']
Af = [f for f in open(D + 'A11_fields.txt').read().split() if f != 'x6ConicModel']
S = r'''import ZInQKernel.OneProof.H.TailZ21

/-! # OneProof H, x6-fold (3/3): the bundles `OpenResearchLeaves13`, `OpenAddedLeaves12` and `sixContactMin_of_open16`

x6-glue (docs/research/x6-glue.md; `TailZ20`, `TailZ21`) proves the two fields
* `r1r2Ab : LeafAdopt.R1R2fpRepAb` (research; through route-a-fold's `r1R2fpRep_iff_ab`) and
* `x6ConicModel : X6Kummer.X6ConicModel` (added)
from seven leaves: Deligne's `π₀` at level `𝒪̂^×` in printed form (`ShimuraGlue.DeligneComponentsX6Printed`), the
textbook criterion `GeomConnOfAlgClosure` (EGA IV 4.5, Stacks 0389, weakened), T5 (`PkgI2.TorsionStructure`, already
proved in the chain from the textbook field `mumfordTorsionAlgClosed`, `AvSplit.torsionStructure_of_mumford`),
Baba–Granath (`BabaGranathRational`), González–Rotger Thm 5.12 (`GonzalezRotgerX6`), Elkies' equations as charts over
the `t`-line (`ElkiesEquationsX6`), and Shimura reciprocity in ray-class form (`ShimuraGlue.Ray.RayClassCM`, a
consequence of a printed theorem).

As route-a-fold did for the other moduli leaves (`TailZ17`), the five leaves stated on a witness with the kernel's
`R1fpProps` enter the bundles in their abelian-scheme form (`R1fpPropsAb`, the objects of the published fine-moduli
problem): each `LAb` below is the text of `L` with `R1fpProps` replaced by `R1fpPropsAb`, in `L`'s namespace with `L`'s
`open`s, and `L_iff_ab` (under Mumford's rigidity, from the field `mumfordRigidityCore`) closes by rewriting
`R1fpProps = R1fpPropsAb` (`r1fpProps_eq_ab'`), which checks that the two texts elaborate to the same term up to that
one constant. docs/research/x6-fold.md lists the fields. -/

/-! ## The abelian-scheme forms of the five moduli leaves -/

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
attribute [local instance 2000] instAlgebraAdicCompletion

/-- **Abelian-scheme form of `ShimuraGlue.DeligneComponentsX6Printed`** (Deligne's `π₀` display at level `𝒪̂^×` on
the canonical `X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def DeligneComponentsX6PrintedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull

end ShimuraGlue

namespace ShimuraGlue.Ray

open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields NumberField IsDedekindDomain
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `ShimuraGlue.Ray.RayClassCM`** (Shimura reciprocity at CM points in ray-class form, a
consequence): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def RayClassCMAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      (HasCM4 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K4))) ∧
      (HasCM3 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K3))) ∧
      (HasCM24 P.q → Nonempty (residueImage (X := Y.left) y.left →+* rayClassField (mod3 K24)))

end ShimuraGlue.Ray

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.GonzalezRotgerX6`** (González–Rotger 2006 Thm 5.12 on the canonical
`X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb`. -/
def GonzalezRotgerX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ElkiesEquationsX6`** (Elkies, ANTS-III (1998) §3: `X₆` over the
`t`-line as the charts `s² = −t, r² = 3(t − 1)`, with the fibre and CM clauses): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ElkiesEquationsX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (t : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM24 P.q → t.val (K := Qbar) x.left = OnePoint.some 0) ∧
        (HasCM4 P.q → t.val (K := Qbar) x.left = OnePoint.some 1) ∧
        (HasCM3 P.q → t.val (K := Qbar) x.left = OnePoint.infty)) ∧
    X6Glue.ElkiesCharts X t

section
open scoped Classical

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.BabaGranathRational`** (Baba–Granath 2008 Thm 2.1 and Lemma 3.1
on the canonical `X₆`): its text with `R1fpProps` replaced by `R1fpPropsAb` (stated, like the original, under
`open scoped Classical`). -/
def BabaGranathRationalAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π : ToP1 X.left)
    (t₄ t₃ t₂₄ : OnePoint ℚ),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ t₄ ≠ t₃ ∧ t₄ ≠ t₂₄ ∧ t₃ ≠ t₂₄ ∧
    ∀ (x x' : fieldPt Qbar ⟶ X) (P Q : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ x' = Quotient.mk _ Q →
        (π.val (K := Qbar) x.left = π.val (K := Qbar) x'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM4 P.q ↔ π.val (K := Qbar) x.left = t₄.map (algebraMap ℚ Qbar)) ∧
        (HasCM3 P.q ↔ π.val (K := Qbar) x.left = t₃.map (algebraMap ℚ Qbar)) ∧
        (HasCM24 P.q ↔ π.val (K := Qbar) x.left = t₂₄.map (algebraMap ℚ Qbar))

end

end HDec.QMSplit.Moduli

/-! ## Each leaf from its abelian-scheme form, under rigidity -/

namespace LeafQM.AV.R1UnivRigid

theorem deligneComponentsX6Printed_iff_ab (hR : MumfordRigidity) :
    ShimuraGlue.DeligneComponentsX6Printed ↔ ShimuraGlue.DeligneComponentsX6PrintedAb := by
  unfold ShimuraGlue.DeligneComponentsX6Printed ShimuraGlue.DeligneComponentsX6PrintedAb
  rw [r1fpProps_eq_ab' hR]

theorem rayClassCM_iff_ab (hR : MumfordRigidity) :
    ShimuraGlue.Ray.RayClassCM ↔ ShimuraGlue.Ray.RayClassCMAb := by
  unfold ShimuraGlue.Ray.RayClassCM ShimuraGlue.Ray.RayClassCMAb
  rw [r1fpProps_eq_ab' hR]

theorem gonzalezRotgerX6_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.GonzalezRotgerX6 ↔ HDec.QMSplit.Moduli.GonzalezRotgerX6Ab := by
  unfold HDec.QMSplit.Moduli.GonzalezRotgerX6 HDec.QMSplit.Moduli.GonzalezRotgerX6Ab
  rw [r1fpProps_eq_ab' hR]

theorem elkiesEquationsX6_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.ElkiesEquationsX6 ↔ HDec.QMSplit.Moduli.ElkiesEquationsX6Ab := by
  unfold HDec.QMSplit.Moduli.ElkiesEquationsX6 HDec.QMSplit.Moduli.ElkiesEquationsX6Ab
  rw [r1fpProps_eq_ab' hR]

theorem babaGranathRational_iff_ab (hR : MumfordRigidity) :
    HDec.QMSplit.Moduli.BabaGranathRational ↔ HDec.QMSplit.Moduli.BabaGranathRationalAb := by
  unfold HDec.QMSplit.Moduli.BabaGranathRational HDec.QMSplit.Moduli.BabaGranathRationalAb
  rw [r1fpProps_eq_ab' hR]

end LeafQM.AV.R1UnivRigid

namespace HDec

namespace HSyn

/-! ## The bundles -/

/-- **The research leaves still open** (x6-fold): leaf-fold12's `OpenResearchLeaves12` without `r1r2Ab` (proved by
x6-glue's `r1r2_of_published`, through `r1R2fpRep_iff_ab`), with four of its leaves added in abelian-scheme form.
35 fields. -/
structure OpenResearchLeaves13 : Prop where
@@R@@
  /-- x6-glue, printed form (on abelian schemes): Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and Lemma 3.1
  (read by the locator audit), on one canonical coarse witness `X₆`: a coordinate `π : X₆ → P¹` whose fibres are the
  `Aut(𝒪)`-twist classes, with three distinct rational values at the CM points of discriminants `−4, −3, −24` (the
  CM assignment read from the §3.1 table, UNVERIFIED). -/
  babaGranathRationalAb : QMSplit.Moduli.BabaGranathRationalAb
  /-- x6-glue, printed form (on abelian schemes): González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (read by
  the locator audit), residue fields of CM points, on one canonical coarse witness `X₆`. -/
  gonzalezRotgerX6Ab : QMSplit.Moduli.GonzalezRotgerX6Ab
  /-- x6-glue, printed form (on abelian schemes): Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998),
  §3 (display, section number and the `0`/`∞` orientation UNVERIFIED): `X₆` over the `t`-line is
  `s² = −t, r² = 3(t − 1)` (`X6Glue.ElkiesCharts`), with `t` a coordinate on `X₆/W` and `t = 0, 1, ∞` at the CM
  points of discriminants `−24, −4, −3`. -/
  elkiesEquationsX6Ab : QMSplit.Moduli.ElkiesEquationsX6Ab
  /-- x6-glue, **consequence** (on abelian schemes): Shimura reciprocity at CM points of the canonical model
  (Shimura, Ann. of Math. 85 (1967) Main Thm I; Deligne 1971 §3; locators UNVERIFIED) in ray-class form: the
  residue field of a CM point by `ℚ(i)`, `ℚ(ζ₃)`, `ℚ(√−6)` embeds into the ray class field of conductor `3`. -/
  rayClassCMAb : _root_.ShimuraGlue.Ray.RayClassCMAb

/-- **The added leaves still open** (x6-fold): leaf-fold12's `OpenAddedLeaves11` without `x6ConicModel` (proved by
x6-glue's `x6ConicModel_of_published`), with two of its leaves added. 14 fields. -/
structure OpenAddedLeaves12 : Prop where
@@A@@
  /-- x6-glue (shimura-glue), printed form (on abelian schemes): Deligne's theorem on the connected components of a
  Shimura variety (Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3; locators UNVERIFIED) for
  `G = B^×` at level `𝒪̂^×` on one canonical coarse witness `X₆` (the double coset is computed in Lean). -/
  deligneComponentsX6PrintedAb : _root_.ShimuraGlue.DeligneComponentsX6PrintedAb
  /-- x6-glue (shimura-split), textbook, weakened: for a proper `X → Spec k`, `char k = 0`, connectedness of
  `X ×_k k̄` gives geometric connectedness (EGA IV 4.5; Stacks 0389; locators UNVERIFIED). -/
  geomConnOfAlgClosure : QMSplit.Moduli.GeomConnOfAlgClosure

/-! ## From the new bundles to leaf-fold12's -/

/-- **The two `X₆` rows from the new bundles** (x6-glue's `x6Rows_of_leaves`): each leaf from its abelian-scheme form
under Mumford's rigidity (`mumfordRigidityCore`), and T5 from the textbook field `mumfordTorsionAlgClosed`. -/
theorem x6Rows_of_open13 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    LeafAdopt.R1R2fpRep ∧ X6Kummer.X6ConicModel :=
  have hR := _root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore
  QMSplit.Moduli.x6Rows_of_leaves
    { deligneX6P := (_root_.LeafQM.AV.R1UnivRigid.deligneComponentsX6Printed_iff_ab hR).mpr
        l.deligneComponentsX6PrintedAb
      geomConn := l.geomConnOfAlgClosure
      t5 := _root_.AvSplit.torsionStructure_of_mumford t.mumfordTorsionAlgClosed
      babaGranathR := (_root_.LeafQM.AV.R1UnivRigid.babaGranathRational_iff_ab hR).mpr r.babaGranathRationalAb
      rayClass := (_root_.LeafQM.AV.R1UnivRigid.rayClassCM_iff_ab hR).mpr r.rayClassCMAb
      gonzalezRotger := (_root_.LeafQM.AV.R1UnivRigid.gonzalezRotgerX6_iff_ab hR).mpr r.gonzalezRotgerX6Ab
      elkiesEq := (_root_.LeafQM.AV.R1UnivRigid.elkiesEquationsX6_iff_ab hR).mpr r.elkiesEquationsX6Ab }

/-- leaf-fold12's research bundle from x6-fold's: `r1r2Ab` from x6-glue's `r1r2_of_published` and route-a-fold's
`r1R2fpRep_iff_ab`. -/
theorem researchLeaves12_of_open13 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    OpenResearchLeaves12 where
  r1r2Ab := (_root_.LeafQM.AV.R1UnivRigid.r1R2fpRep_iff_ab
    (_root_.LeafQM.AV.R1UnivRigid.mumfordRigidity_of_core r.mumfordRigidityCore)).mp (x6Rows_of_open13 r t l).1
@@RF@@

/-- leaf-fold12's added-leaf bundle from x6-fold's: `x6ConicModel` from x6-glue's `x6ConicModel_of_published`. -/
theorem addedLeaves11_of_open12 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12) :
    OpenAddedLeaves11 where
@@AF@@
  x6ConicModel := (x6Rows_of_open13 r t l).2

/-- **G0 with only the open leaves and the open glue** (x6-fold; no `sorry`, standard axioms).
`ZInQ.SixContactMin` from `OpenResearchLeaves13` (35), `OpenTextbookLeaves10` (15), `OpenAddedLeaves12` (14) and
`OpenGlue7` (1). -/
theorem sixContactMin_of_open16 (r : OpenResearchLeaves13) (t : OpenTextbookLeaves10) (l : OpenAddedLeaves12)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open15 (researchLeaves12_of_open13 r t l) t (addedLeaves11_of_open12 r t l) g

end HSyn

end HDec

#print axioms HDec.QMSplit.Moduli.r1r2_of_published
#print axioms HDec.QMSplit.Moduli.x6ConicModel_of_published
#print axioms HDec.HSyn.x6Rows_of_open13
#print axioms HDec.HSyn.researchLeaves12_of_open13
#print axioms HDec.HSyn.addedLeaves11_of_open12
#print axioms HDec.HSyn.sixContactMin_of_open16
'''
S = S.replace('@@R@@', R).replace('@@A@@', A)
S = S.replace('@@RF@@', '\n'.join(f'  {f} := r.{f}' for f in Rf))
S = S.replace('@@AF@@', '\n'.join(f'  {f} := l.{f}' for f in Af))
open('ZInQKernel/OneProof/H/TailZ22.lean', 'w').write(S)
print(len(S.encode()), len(Rf) + 4, len(Af) + 2)
