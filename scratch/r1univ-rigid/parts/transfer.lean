
/-! ## §9 The transfer: every statement on `R1fpProps` is equivalent, under rigidity, to the same
statement on `R1fpPropsAb` -/

namespace LeafQM.AV.R1UnivRigid

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **Under `MumfordRigidity`, `R1fpProps = R1fpPropsAb`** (as predicates on `(Y, Φ)`): any leaf
or glue Prop stated on `R1fpProps`, in any position, is equivalent to the same text with
`R1fpPropsAb` (rewrite with this equation). -/
theorem r1fpProps_eq_ab (hR : MumfordRigidity) :
    (R1fpProps : (Y : Over (Spec (CommRingCat.of ℚ))) → PtEquiv Y → Prop) = R1fpPropsAb :=
  funext fun Y => funext fun Φ => propext (r1fpProps_iff_ab hR Y Φ)

/-- An existential leaf on `R1fpPropsAb` gives the same leaf on `R1fpProps` (the direction used
by a fold; it needs only the `R1univProps` half of rigidity). -/
theorem exists_r1fp_of_ab (hR : MumfordRigidity)
    {C : (Y : Over (Spec (CommRingCat.of ℚ))) → PtEquiv Y → Prop}
    (h : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAb Y Φ ∧ C Y Φ) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧ C Y Φ := by
  obtain ⟨Y, Φ, h1, h2⟩ := h
  exact ⟨Y, Φ, (r1fpProps_iff_ab hR Y Φ).2 h1, h2⟩

/-- A universal statement on `R1fpProps` follows from the same statement on `R1fpPropsAb`
(through `r1fpProps_iff_ab`; the `R1famProps` half uses rigidity). -/
theorem forall_r1fp_of_ab {C : (Y : Over (Spec (CommRingCat.of ℚ))) → PtEquiv Y → Prop}
    (h : ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpPropsAb Y Φ → C Y Φ)
    (hR : MumfordRigidity) :
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → C Y Φ :=
  fun Y Φ h1 => h Y Φ ((r1fpProps_iff_ab hR Y Φ).1 h1)

end LeafQM.AV.R1UnivRigid
