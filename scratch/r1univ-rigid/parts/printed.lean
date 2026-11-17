
/-! ## §10 The abelian-scheme (printed) forms of the leaves on `R1fpProps`

For each leaf `L` below, `LAb` is the text of `L` with `R1fpProps` replaced by `R1fpPropsAb` (the form in
which the published fine-moduli theorems are stated), placed in `L`'s namespace with `L`'s `open`s; the
theorem `L_iff_ab` (§11) closes by rewriting `R1fpProps = R1fpPropsAb` and `Iff.rfl`, which checks that
the two texts elaborate to the same term up to that replacement. -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.GonzalezRotgerX6`** (row H-142): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def GonzalezRotgerX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ

end HDec.QMSplit.Moduli

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `ShimuraSplit.GonzalezRotgerCountX6`** (row H-145): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def GonzalezRotgerCountX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
      Module.finrank ℚ k = 2 →
      ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
        (∃ P : QMPair Qbar, Nonempty (com P.q ≃+* R)) →
          Nat.card {x : fieldPt Qbar ⟶ X //
              ∃ P : QMPair Qbar, Ψ x = Quotient.mk _ P ∧ Nonempty (com P.q ≃+* R)} =
            2 ^ inertCount6 k * Nat.card (CommRing.Pic R)

end ShimuraSplit

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.DeligneComponentsX6`** (row H-149): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def DeligneComponentsX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ ConnectedSpace (ShimuraSplit.baseQbar X)

end HDec.QMSplit.Moduli

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.BabaGranathX6'`** (row H-151): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def BabaGranathX6'Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ ∃ π₆ : ToP1 X.left, LeafAdopt.R2X6PropsIff X Ψ π₆

end HDec.QMSplit.Moduli

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ReciprocityCanonical`** (row H-152): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ReciprocityCanonicalAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ R1recProps Y Φ

end HDec.QMSplit.Moduli

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ElkiesConicX6`** (row H-153): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ElkiesConicX6Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧ X6Kummer.ConicModel X π₆

end HDec.QMSplit.Moduli

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ShimuraHolFamily`** (row H-154): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ShimuraHolFamilyAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

end HDec.QMSplit.Moduli

namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `ShimuraSplit.DeligneComponentsY3`** (row H-155): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def DeligneComponentsY3Ab : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∃ c : _root_.ConnectedComponents (baseQbar Y) ≃ (ZMod 3)ˣ,
      ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (z : _root_.ConnectedComponents (baseQbar Y)),
        c (galActπ₀ Y σ z) = chi3 σ * c z

end ShimuraSplit

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
attribute [local instance 2000] instAlgebraAdicCompletion

/-- **Abelian-scheme form of `ShimuraGlue.DeligneComponentsY3Printed`** (row shimura-glue): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def DeligneComponentsY3PrintedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ DelignePi0 Y K3

end ShimuraGlue

namespace ShimuraGlue

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum
attribute [local instance 2000] instAlgebraAdicCompletion

/-- **Abelian-scheme form of `ShimuraGlue.DeligneComponentsX6Printed`** (row shimura-glue): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def DeligneComponentsX6PrintedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧ DelignePi0 X Kfull

end ShimuraGlue

namespace HDec.LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.LeafAdopt.R1R2fpRep`** (row H-1 r1r2): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def R1R2fpRepAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ ∧ R1pi0Props X

end HDec.LeafAdopt

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.CanonicalModelY3`** (row CanonicalModelY3): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def CanonicalModelY3Ab : Prop := ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ

end HDec.QMSplit.Moduli

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ShimuraFamily`** (row shimuraFamily H-139): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def ShimuraFamilyAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧
    ∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π

end HDec.QMSplit.Moduli

namespace HDec.TSHecke

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue PkgI3
open MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Abelian-scheme form of `HDec.TSHecke.Y3Connected`** (row y3Connected H-59): its text with `R1fpProps` replaced by
`R1fpPropsAb`. -/
def Y3ConnectedAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ ConnectedSpace Y.left

end HDec.TSHecke

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

open scoped Classical

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.BabaGranathRational`** (row shimura-glue, replaces H-151): its text with `R1fpProps`
replaced by `R1fpPropsAb`. -/
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

end HDec.QMSplit.Moduli

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

open scoped Classical

/-- **Abelian-scheme form of `HDec.QMSplit.Moduli.ElkiesConicT`** (row shimura-glue, replaces H-153): its text with `R1fpProps`
replaced by `R1fpPropsAb`. -/
def ElkiesConicTAb : Prop :=
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
    ConicModelT X t

end HDec.QMSplit.Moduli
