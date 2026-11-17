import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Embedding
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Relative
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ClearDenominators
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.GlobalSection
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.ImmersionAffine
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Group
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.ZeroLocusFunctorial

noncomputable section
open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite

namespace T09Pic

attribute [local instance] MvPolynomial.gradedAlgebra

/-- copy of Pic.lean's `IsAmple` -/
def IsAmple (X : Scheme.{0}) (L : X.Pic) : Prop :=
  CompactSpace X ∧ ∀ x : X, ∃ (n : ℕ) (_ : 0 < n)
    (s : 𝟙_ X.Modules ⟶ ((fromSkeleton X.Modules).obj L.val).tensorPow n),
    x ∈ (Scheme.Modules.Hom.zeroLocus s).support.compl ∧
      IsAffineOpen (Scheme.Modules.Hom.zeroLocus s).support.compl

/-- An invertible `E` with sections `σ_k` whose nonvanishing loci are affine and cover `X` is
ample (`n = 1`). -/
theorem isAmple_mk_of_sections {X : Scheme.{0}} [CompactSpace X] (E : X.Modules) [E.IsInvertible]
    {I : Type} (σ : I → (𝟙_ X.Modules ⟶ E))
    (haff : ∀ k, IsAffineOpen (Scheme.Modules.Hom.zeroLocus (σ k)).support.compl)
    (hcov : ∀ x, ∃ k, x ∈ (Scheme.Modules.Hom.zeroLocus (σ k)).support.compl) :
    IsAmple X (Scheme.Pic.mk E) := by
  let F := (fromSkeleton X.Modules).obj (Scheme.Pic.mk E).val
  let e : E ≅ F.tensorPow 1 := (Scheme.Pic.mkIso E).symm ≪≫ (ρ_ F).symm
  refine ⟨inferInstance, fun x => ?_⟩
  obtain ⟨k, hk⟩ := hcov x
  have hz : Scheme.Modules.Hom.zeroLocus (σ k ≫ e.hom) = Scheme.Modules.Hom.zeroLocus (σ k) :=
    Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso (σ k ≫ e.hom) (σ k)
      (Arrow.isoMk (Iso.refl _) e.symm (by simp))
  exact ⟨1, one_pos, σ k ≫ e.hom, by rw [hz]; exact hk, by rw [hz]; exact haff k⟩

variable {X : Scheme.{0}} {N : Type} {S : Scheme.{0}}

/-- the pulled-back coordinate section `i^*Xₖ` of `i^*𝒪(1)` -/
def coordSection (i : X ⟶ ℙ(N; S)) (k : N) :
    𝟙_ X.Modules ⟶ (Scheme.Modules.pullback i).obj (ProjectiveSpace.twist N S 1) :=
  Scheme.Modules.homOfGlobalSection _
    (Scheme.Modules.pullbackSection i (ProjectiveSpace.twistOneSection N S k))

/-- **`X_{i^*Xₖ} = i⁻¹ D₊(Xₖ)`.** -/
theorem compl_support_zeroLocus_coordSection (i : X ⟶ ℙ(N; S)) (k : N) :
    (Scheme.Modules.Hom.zeroLocus (coordSection i k)).support.compl =
      i ⁻¹ᵁ ProjectiveSpace.standardOpen N S k := by
  ext x
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((ProjectiveSpace.iSup_standardOpen N S).ge (Set.mem_univ (i x)))
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := x)
    (U := i ⁻¹ᵁ ProjectiveSpace.standardOpen N S j) hj
  let E := (Scheme.Modules.pullback i).obj (ProjectiveSpace.twist N S 1)
  have heV := ProjectiveSpace.isFreeGenerator_pullbackSection_twistOneSection i j
  have heU := heV.map hWV
  have hform := ProjectiveSpace.pullbackSection_twistOneSection_map_eq_smul i k j
  have key := Scheme.Modules.basicOpen_coeff_eq (coordSection i k) ⟨W, hW⟩ heU
  let c : Γ(X, i ⁻¹ᵁ ProjectiveSpace.standardOpen N S j) :=
    i.app (ProjectiveSpace.standardOpen N S j) ((ProjectiveSpace.toIntegralModel N S).app
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ)) (MvPolynomial.X j))
      (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{0} ℤ) j k)))
  have h1 : (coordSection i k).app W (Scheme.Modules.unitSectionsEquiv W 1) =
      E.presheaf.map (homOfLE hWV).op (E.presheaf.map (homOfLE (i.preimage_mono le_top)).op
        (Scheme.Modules.pullbackSection i (ProjectiveSpace.twistOneSection N S k))) := by
    refine (Scheme.Modules.homOfGlobalSection_app_one _ _ W).trans ?_
    exact (Scheme.Modules.presheaf_map_map_apply _ _ _).symm
  have hσ : (coordSection i k).app W (Scheme.Modules.unitSectionsEquiv W 1) =
      X.presheaf.map (homOfLE hWV).op c • E.presheaf.map (homOfLE hWV).op
        (E.presheaf.map (homOfLE (i.preimage_mono le_top)).op
          (Scheme.Modules.pullbackSection i (ProjectiveSpace.twistOneSection N S j))) := by
    rw [h1]
    erw [hform]
    exact Scheme.Modules.map_smul _ _ _ _
  have hcoeff : heU.coeff ((coordSection i k).app W (Scheme.Modules.unitSectionsEquiv W 1)) =
      X.presheaf.map (homOfLE hWV).op c :=
    heU.smul_left_injective (by
      show heU.coeff _ • _ = _ • _
      rw [heU.coeff_smul]
      exact hσ)
  rw [hcoeff] at key
  erw [Scheme.basicOpen_res] at key
  have hX (m : N) : MvPolynomial.X m ∈ MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ) 1 :=
    MvPolynomial.X_mem_homogeneousSubmodule_one _ m
  have hr : (Proj (MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ))).basicOpen
      (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{0} ℤ) j k)) =
      Proj.basicOpen _ (MvPolynomial.X j) ⊓ Proj.basicOpen _ (MvPolynomial.X k) :=
    Proj.basicOpen_ratio (MvPolynomial.homogeneousSubmodule N (ULift.{0} ℤ)) one_pos (hX j) (hX k)
  have hc : X.basicOpen c = i ⁻¹ᵁ (ProjectiveSpace.toIntegralModel N S ⁻¹ᵁ
      (Proj.basicOpen _ (MvPolynomial.X j) ⊓ Proj.basicOpen _ (MvPolynomial.X k))) := by
    rw [← hr, Scheme.preimage_basicOpen, Scheme.preimage_basicOpen]
    rfl
  rw [hc] at key
  constructor
  · intro h
    have hm : x ∈ W ⊓ (Scheme.Modules.Hom.zeroLocus (coordSection i k)).support.compl := ⟨hxW, h⟩
    rw [← key] at hm
    exact hm.2.2
  · intro h
    have hm : x ∈ W ⊓ i ⁻¹ᵁ (ProjectiveSpace.toIntegralModel N S ⁻¹ᵁ
        (Proj.basicOpen _ (MvPolynomial.X j) ⊓ Proj.basicOpen _ (MvPolynomial.X k))) := ⟨hxW, hj, h⟩
    rw [key] at hm
    exact hm.2

/-- **The pull-back of `𝒪(1)` along an immersion with closed image is ample** (proved): the sections
`i^*Xₖ` have nonvanishing loci `i⁻¹ D₊(Xₖ)`, affine since `D₊(Xₖ)` is affine and `i` is a closed
immersion onto its image, and they cover. -/
theorem isAmple_of_isImmersion [CompactSpace X] [Finite N] [IsAffine S] (i : X ⟶ ℙ(N; S))
    [IsImmersion i] (hcl : IsClosed (Set.range i)) :
    IsAmple X (Scheme.Pic.map i (Scheme.Pic.mk (ProjectiveSpace.twist N S 1))) := by
  rw [Scheme.Pic.map_mk]
  refine isAmple_mk_of_sections _ (coordSection i) (fun k => ?_) (fun x => ?_)
  · rw [compl_support_zeroLocus_coordSection]
    refine i.isAffineOpen_preimage_of_le_coborderRange
      (ProjectiveSpace.isAffineOpen_standardOpen N S k) ?_
    intro y _
    change y ∈ coborder (Set.range i)
    rw [coborder_eq_univ_iff.mpr hcl]
    trivial
  · obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((ProjectiveSpace.iSup_standardOpen N S).ge (Set.mem_univ (i x)))
    exact ⟨k, by rw [compl_support_zeroLocus_coordSection]; exact hk⟩

end T09Pic
