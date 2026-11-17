import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Embedding
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ClearDenominators
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.ImmersionAffine
open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}} {N : Type} {S : Scheme.{0}} (i : X ⟶ ℙ(N; S))
example : i ⁻¹ᵁ (⊤ : ℙ(N; S).Opens) = ⊤ := rfl
#check @Scheme.Modules.basicOpen_coeff_eq
#check @Scheme.Modules.IsFreeGenerator.coeff_smul
#check @Scheme.Modules.IsFreeGenerator.smul_left_injective
#check @Scheme.Modules.map_smul
#check @Scheme.basicOpen_res
#check @Scheme.preimage_basicOpen
#check @Scheme.Modules.unitSectionsEquiv
#check @Proj.ratio
example (K : Type) [Field K] (N : Type) : IsSeparated (ℙ(N; Spec (CommRingCat.of K)) ↘ Spec (CommRingCat.of K)) := inferInstance
