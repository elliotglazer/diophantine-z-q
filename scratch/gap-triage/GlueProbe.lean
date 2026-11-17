import ZInQKernel.OneProof.H.TailZ13
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates

/-!
gap-triage probe for the glue field `quotientP1Coordinate` (mcr-quot's inputs).

1. `CoverModelOfHeckeN` enters mcr-quot only through `modelYIrreducible_of_coverModelN`, i.e. only to give
   `ModelYIrreducible`. The body of `ModelYIrreducible` (copied verbatim from
   `scratch/mcr-quot/MCRQuot.lean` L7336, as `ModelYIrreducibleCopy`) is the body of the chain's
   `HeckeIrreducible`, and the chain already proves it from the field `deligneComponentsY3Printed`.
2. `P1SchemeQ`: the CloudW07 projective-line API.
-/

open CategoryTheory AlgebraicGeometry LeafQM LeafQM.AV

namespace GapTriage

/-- `MCRQuot.ModelYIrreducible`, verbatim body. -/
def ModelYIrreducibleCopy : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π → IrreducibleSpace Y.left

/-- The chain's `HeckeIrreducible` is `ModelYIrreducible` (definitional). -/
example : HDec.PropTSGlue.HeckeIrreducible = ModelYIrreducibleCopy := rfl

/-- `ModelYIrreducible` from the bundle field `deligneComponentsY3Printed`: no `CoverModelOfHeckeN`,
no Lemma NV. -/
theorem modelYIrreducible_of_open9 (l : HDec.HSyn.OpenAddedLeaves9) : ModelYIrreducibleCopy :=
  HDec.TSHecke.heckeIrreducible_of_connected
    (_root_.ShimuraSplit.y3Connected_of_deligne
      (_root_.ShimuraGlue.deligneComponentsY3_of_printed l.deligneComponentsY3Printed))

end GapTriage

#print axioms GapTriage.modelYIrreducible_of_open9

-- P1SchemeQ toolkit (CloudW07, frenzymath/Jacobian-Challenge)
#check @AlgebraicGeometry.projectiveLineOver
#check @AlgebraicGeometry.ProjectiveLine.isProper_toSpec
#check @AlgebraicGeometry.ProjectiveLine.smoothOfRelativeDimension_toSpec
#check @AlgebraicGeometry.ProjectiveLine.chartSpecIso
#check @AlgebraicGeometry.ProjectiveLine.isAffineOpen_chart
#check @AlgebraicGeometry.ProjectiveLine.polyEquivChart
#check @AlgebraicGeometry.ProjectiveSpace.homOfSections
#check @AlgebraicGeometry.ProjectiveSpace.homOfSections_preimage_standardOpen
#check @AlgebraicGeometry.ProjectiveSpace.hom_ext
#check @AlgebraicGeometry.ProjectiveSpace.instIsProper
#check @AlgebraicGeometry.ProjectiveLine.normalized
#check @AlgebraicGeometry.ProjectiveLine.normalized_eq_of_mul_eq_one
#check @AlgebraicGeometry.ProjectiveLine.relativeChartCoordinate_mul
#check @AlgebraicGeometry.Scheme.Cover.glueMorphisms
