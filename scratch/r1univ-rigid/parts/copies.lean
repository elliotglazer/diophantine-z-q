/-! ## §8 The eight frontier leaves (r5 §4.11) and their abelian-scheme forms

Verbatim copies of the leaves that live only in scratch files (scratch files cannot import each other):
`GonzalezRotgerX6` (scratch/qm-glue/ModuliCompare.lean), `BabaGranathX6'`, `ReciprocityCanonical`,
`ElkiesConicX6` (scratch/shimura-split/Rows.lean), `ShimuraHolFamily` with `ShimuraSplit.ptC`,
`ShimuraSplit.regVal`, `ShimuraSplit.IsHolFamily`, `IsShimuraHolFamily`
(scratch/shimura-split/ShimuraFam.lean), each in its original namespace with its original `open`s. The
others (`DeligneComponentsX6`, `DeligneComponentsY3`, the two `…Printed` forms, `GonzalezRotgerCountX6`,
`CanonicalModelY3`, `Y3Connected`, `ShimuraFamily`, `R1R2fpRep`) are imported from `ZInQKernel/OneProof/H`. -/


namespace ShimuraSplit

open CategoryTheory AlgebraicGeometry Limits Filter Topology
open LeafQM.AV

variable {X : Scheme.{0}}

/-- The point of `X` under a `ℂ`-point. -/
abbrev ptC (y : Spec (CommRingCat.of ℂ) ⟶ X) : X := (Scheme.SpecToEquivOfField ℂ X y).1

open Classical in
/-- The value `f(y) ∈ ℂ` of a regular function `f ∈ Γ(X, U)` at a `ℂ`-point `y` whose point lies in `U`
(the image of `f(x) ∈ κ(x)` under the embedding `κ(x) → ℂ` of `y`), and `0` otherwise. -/
def regVal (U : X.Opens) (f : Γ(X, U)) (y : Spec (CommRingCat.of ℂ) ⟶ X) : ℂ :=
  if h : ptC y ∈ U then (Scheme.SpecToEquivOfField ℂ X y).2 (X.evaluation U _ h f) else 0

/-- **A holomorphic map `ℍ → X(ℂ)`**, written with the regular functions of `X`: the preimage of every
Zariski open is open, and every regular function on a Zariski open `U` pulls back to a function holomorphic
(analytic) on the preimage of `U`. For a variety this is the usual notion (an affine open embeds in `ℂ^n`
by finitely many regular functions, and the analytic topology is the one induced from `ℂ^n`). -/
def IsHolFamily (φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)) : Prop :=
  (∀ U : X.Opens, IsOpen {τ | ptC (φ τ) ∈ U}) ∧
  ∀ (U : X.Opens) (f : Γ(X, U)) (τ : UpperHalfPlane), ptC (φ τ) ∈ U →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, regVal U f (φ ⟨z, hz⟩) = g z

end ShimuraSplit

namespace HDec

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight cDom cEvalAt)

open Complex

/-- **Shimura's holomorphic family on a witness** (the moduli clause of `IsR1bFamily`, copied verbatim, and
holomorphy of `τ ↦ y_τ` in the sense of `ShimuraSplit.IsHolFamily`; no map to `P¹` involved). -/
def IsShimuraHolFamily (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y)) : Prop :=
  (∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (yτ τ) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      IotaCompatible P Φu) ∧
  ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (yτ τ).left)

end FibreQM

end G0Split

end HSyn

end HDec

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF-form (González–Rotger on the canonical `X₆`).** Some coarse witness satisfies `R5ptProps`
(residue fields of CM points). González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12; locators
UNVERIFIED. -/
def GonzalezRotgerX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R5ptProps X Ψ

/-- **LEAF-form (Baba–Granath on the canonical `X₆`), without the surjectivity clause.** Some coarse
witness carries `π₆ : X₆ → P¹` with the fibre clause (two `ℚ̄`-points have the same value iff their QM pairs
are `Aut(𝒪)`-twists, i.e. `W`-conjugate) and the CM clauses (`π₆ = 0, ∞, −16/27` exactly at CM by `ℤ[i]`,
`ℤ[ζ₃]`, `ℤ[√−6]`) of `R2X6PropsIff`. Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 (`X₆/W ≅ P¹_ℚ`,
the polarized moduli space is `X₆/W`), Lemma 3.1 and the §3.1 table (each of `CM(−4)`, `CM(−3)`, `CM(−24)`
is one `W`-orbit); read by the audit (YES); the coordinate is Baba–Granath's `j` (values `0, ∞, −16/27`). -/
def BabaGranathX6' : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ ∃ π₆ : ToP1 X.left, LeafAdopt.R2X6PropsIff X Ψ π₆

/-- **LEAF-form (Shimura reciprocity at the three elliptic CM points, on the points of the canonical
`Y₃`).** Some fine witness `(Y, Φ)` satisfies `R1recProps`: a `ℚ̄`-point whose object has CM by `ℤ[i]`,
`ℤ[ζ₃]` or `ℤ[√−6]` has residue field unramified at every `p ≥ 5`.
*Published statement*: Shimura reciprocity for CM points on the canonical model (Shimura, Ann. of Math. 85
(1967), Main Thm II; Deligne, Sém. Bourbaki 389 (1971), §§3.7-3.13, Thm 4.19, read by the audit as
"consequence with qualifications"; locators otherwise UNVERIFIED): for `y` with CM by the maximal order of
`k`, `k(y)` lies in the ray class field of `k` of conductor 3, which is unramified outside `3·disc(k) | 72`.
*Form*: a **consequence** of one theorem (the unramifiedness conclusion, not the printed reciprocity law);
it is the point form of leaf-qm-fp's `R1recProps`, and equivalent to `R1rec` given a fine witness
(`ShimuraSplit.r1rec_of_point`, `point_of_r1rec`). Lemma QP as for `R1fp`. -/
def ReciprocityCanonical : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ R1recProps Y Φ

/-- **LEAF-form (Kurihara, Elkies: the conic model of the canonical `X₆` with its Hauptmodul).** Some witness
`(Y, Φ, X, Ψ, fY)` of the moduli clause lists `R1fpProps`, `X6Props` carries `π₆ : X₆ → P¹` with the fibre and
CM clauses `R2X6Props` and the conic model `X6Kummer.ConicModel X π₆` (`X₆(ℚ̄) ≃ C(ℚ̄)` for
`C : Y² + 3X² + 3Z² = 0`, `Aut(ℚ̄/ℚ)`-equivariantly, with `π₆ = −16(X² + Z²)/(27Z²)`). Published: Kurihara,
J. Fac. Sci. Univ. Tokyo 25 (1979) (`X₀(6,1) : x² + y² + 3 = 0`); Elkies, ANTS-III, LNCS 1423 (1998), §3
(`X*(6) = X₆/W` with coordinate `t`, `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`, and
`X₆ = X*(6)(√−t, √(3(t − 1)))`; `j = 16(t − 1)/27`); locators UNVERIFIED. Unlike qm-glue's `ConicCanonical`
(which is the row `X6ConicModel` itself), it does not contain the clauses `R1heckeProps`, `CMExists`,
`R1recProps`, `X6Surj`, `R5ptProps` of the row's witness: those come from `r1r2`. -/
def ElkiesConicX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6Props X Ψ π₆ ∧ X6Kummer.ConicModel X π₆

/-- **LEAF (Shimura's complex uniformization of the canonical model, Main Theorem I).**

*Published statement* (Shimura, Ann. of Math. 85 (1967), Main Theorem I; Deligne, Sém. Bourbaki 389 (1971),
§4.15; locators UNVERIFIED, no network): the canonical model `V` of `Γ\ℍ` carries a holomorphic map
`φ : ℍ → V(ℂ)` whose value at `τ` is the moduli point of `ℂ²/ι(𝒪)(τ, 1)ᵀ` (with its `ι` and level
structure).

*Lean form*: some fine witness `(Y, Φ)` (the canonical model `Y₃`) has `τ ↦ y_τ ∈ Y(ℂ)` with the object at
`y_τ` equal (by an `ι`-compatible analytic uniformization with kernel `Λ_τ = ι(𝒪)(τ,1)ᵀ`) to `ℂ²/Λ_τ`, and
`τ ↦ y_τ` holomorphic (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens are open and regular
functions pull back to holomorphic functions, the standard notion for maps into the complex points of a
variety).

*Form*: a **consequence** of Main Thm I (one holomorphic `φ`, as here), not its printed form: Shimura's
`V` for the level-3 group is one geometric component, defined over `ℚ(ζ₃)`, while `Y₃` over `ℚ` has two; the
moduli clause on `Y₃` comes through Deligne's adelic reformulation (§4) with R1 and Lemma QP (independent
review, shimura-split §3.4). The row's "for every `π : Y → P¹`" is derived (`isR1bFamily_of_hol`), so the
flagged GAGA-level composition step is no longer part of the leaf. -/
def ShimuraHolFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∃ yτ : UpperHalfPlane → (fieldPt ℂ ⟶ Y), HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ yτ

end HDec.QMSplit.Moduli

/-! Verbatim from scratch/shimura-glue/parts/MobiusNew.lean (shimura-glue): `BabaGranathRational`,
`ConicModelT`, `ElkiesConicT`. -/

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

open scoped Classical

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

end HDec.QMSplit.Moduli
