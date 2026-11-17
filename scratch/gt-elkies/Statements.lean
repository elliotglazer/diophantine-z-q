-- Verbatim copy (gt-elkies) of the target Prop and the chart clause it uses, from ZInQKernel/OneProof/H/TailZ22.lean L68-83 and
-- ZInQKernel/OneProof/H/TailZ21.lean (ElkiesCharts), at a454ad64. Reference only: not compiled (the originals are in the build;
-- ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean uses them directly). Other dependencies: X6Props, QMPair, pairSetoid, QMIso,
-- QMStr.twist, HasCM*, ToP1 in ZInQKernel/HDecomp/QM/{Structures,Pairs,Leaves}.lean; R1fpPropsAb in TailZ16.lean L145.

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV


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

end HDec.QMSplit.Moduli

namespace X6Glue

theorem elkiesLift_T {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K) h1 h2 :
    elkiesLift t s r h1 h2 eT = t := by simp [elkiesLift]
theorem elkiesLift_S {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K) h1 h2 :
    elkiesLift t s r h1 h2 eS = s := by simp [elkiesLift]
theorem elkiesLift_R {K : Type*} [CommRing K] [Algebra ℚ K] (t s r : K) h1 h2 :
    elkiesLift t s r h1 h2 eR = r := by simp [elkiesLift]

/-- **Elkies' equations as charts of `X` over the `t`-line.** For a `ℚ`-scheme `X` with `t : X → P¹`
(the kernel's charts `t.U = {t ≠ ∞}`, `t.V = {t ≠ 0}`, `t.f = t`, `t.g = 1/t`):
* `t.U` and `t.V` are affine;
* `Γ(t.U) ≅ ℚ[t, s, r]/(s² + t, r² − 3(t − 1))` with `t ↦ t.f` (that is, over `t ≠ ∞`, `X` is the
  curve `s² = −t`, `r² = 3(t − 1)`);
* `Γ(t.V) ≅ ℚ[u, a, b]/(a² + u, b² − 3(u − 1))` with `u ↦ t.g = 1/t` (over `t ≠ 0`, with
  `a = 1/s`, `b = r/s`: `a² = −1/t`, `b² = 3(t − 1)/(−t) = 3(1/t − 1)`);
* on `t.U ∩ t.V`: `s·a = 1` and `r·a = b` (the gluing).
This is the curve `X*(6)(√−t, √(3(t − 1)))` over the `t`-line, written in the two standard charts. -/
def ElkiesCharts (X : Over (Spec (CommRingCat.of ℚ))) (t : ToP1 X.left) : Prop :=
  IsAffineOpen t.U ∧ IsAffineOpen t.V ∧
  ∃ (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V)),
    φU eT = t.f ∧ φV eT = t.g ∧
    X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eS) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) = 1 ∧
    X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eR) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) =
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eR)

end X6Glue

/-! # x6-glue part: parts/ConicProof.lean -/
/-! # x6-glue Part 3: `ConicModelT` from `ElkiesCharts` -/

end X6Glue
