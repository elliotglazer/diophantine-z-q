/-! dev copy of `HDec.X6Kummer.ConicPt`, `conicGal` (TailE, verbatim) and shimura-glue's `ConicModelT` -/
namespace HDec.X6Kummer
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
abbrev ConicPt : Type :=
  {p : Qbar × Qbar // p.2 ^ 2 + 3 * p.1 ^ 2 + 3 = 0} ⊕ {b : Qbar // b ^ 2 = -3}
def conicGal (σ : Qbar ≃ₐ[ℚ] Qbar) : ConicPt → ConicPt
  | Sum.inl p => Sum.inl ⟨(σ p.1.1, σ p.1.2), by
      have h := congrArg σ p.2
      simp only [map_add, map_mul, map_pow, map_ofNat, map_zero] at h
      exact h⟩
  | Sum.inr b => Sum.inr ⟨σ b.1, by
      have h := congrArg σ b.2
      simp only [map_pow, map_neg, map_ofNat] at h
      exact h⟩
end HDec.X6Kummer
namespace HDec.QMSplit.Moduli
open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
def ConicModelT (X : Over (Spec (CommRingCat.of ℚ))) (t : ToP1 X.left) : Prop :=
  ∃ e : (fieldPt Qbar ⟶ X) ≃ HDec.X6Kummer.ConicPt,
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X),
      e (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = HDec.X6Kummer.conicGal σ (e x)) ∧
    (∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      t.val (K := Qbar) x.left = OnePoint.some (-(p.1.1 ^ 2))) ∧
    (∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → t.val (K := Qbar) x.left = OnePoint.infty)
end HDec.QMSplit.Moduli
