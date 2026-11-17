import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Normalization.ResidualUnit
import ZInQKernel.Contrib.OneProof.TYZSquareOddness.Reconstruction.ActualBox

/-!
# Closed factorization on the literal Mathlib Hamilton finite-adèle carrier

New upstream application of the frozen nineteen-file coarse route. The rational witness is a
WHOLE `Quaternion ℚ`, not a central rational scalar. Both coefficient clauses are written out
on every actual height-one prime; the inverse is the actual inverse of `Units (Quaternion AF)`.
Internal reconstruction, finite generation, full span and principality are proved in this cone,
not supplied by the caller. The old frozen-source/R3 receipts do not approve this changed route.
Canonical W28 PR130 and A/B PR135 sources remain separately owned source dependencies.
This component does not assert Local2/Hfx, global normalization, hP23, R1, QSol or full H10.
-/

open scoped Quaternion
open TYZSquareOddness.ScalarFiniteAdeles
set_option autoImplicit false

namespace TYZSquareOddness.Normalization

/-- Closed stabilization together with actual element and unit-inverse memberships. -/
theorem actual_residual_stabilizes (g : ℍ[AQ]ˣ) :
    ∃ gamma : ℍ[ℚ], ∃ hgamma : gamma ≠ 0,
      gamma ∈ hurwitzIntersection g ∧
        hurwitzHatAddSubgroup.map
          (AddMonoidHom.mulLeft (residualUnit g gamma hgamma : ℍ[AQ])) =
            hurwitzHatAddSubgroup ∧
        (residualUnit g gamma hgamma : ℍ[AQ]) ∈ hurwitzHatAddSubgroup ∧
        (((residualUnit g gamma hgamma)⁻¹ : ℍ[AQ]ˣ) : ℍ[AQ]) ∈ hurwitzHatAddSubgroup := by
  obtain ⟨gamma, hmem, hne, hbox⟩ := actual_principal_box g
  have htranslate := (hamiltonBox_hurwitzIntersection g).symm.trans hbox
  have hstab := residual_stabilizes_of_translate_eq g gamma hne htranslate
  have hboth := both_mem_of_stabilizes (residualUnit g gamma hne) hstab
  exact ⟨gamma, hne, hmem, hstab, hboth.1, hboth.2⟩

/-- Fully literal closed headline: all actual units; nonzero whole rational Hamilton witness;
actual residual unit; ordered factor equation; and both five-integral-coefficient clauses. -/
theorem actual_rational_gamma_factorization :
    ∀ g : (Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))ˣ,
      ∃ gamma : Quaternion ℚ, gamma ≠ 0 ∧
        ∃ u : (Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))ˣ,
          (g : Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
            (⟨algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) gamma.re,
              algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) gamma.imI,
              algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) gamma.imJ,
              algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) gamma.imK⟩ :
              Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) *
            (u : Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) ∧
          (∃ a b c d e : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ,
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), b v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), d v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), e v ∈ v.adicCompletionIntegers ℚ) ∧
            (u : Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
              ⟨a - e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
                b + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
                c + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
                d + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2)⟩) ∧
          (∃ a b c d e : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ,
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), b v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), d v ∈ v.adicCompletionIntegers ℚ) ∧
            (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), e v ∈ v.adicCompletionIntegers ℚ) ∧
            ((u⁻¹ : (Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))ˣ) :
              Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
              ⟨a - e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
                b + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
                c + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
                d + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2)⟩) := by
  intro g
  obtain ⟨gamma, hgamma, u, hfactor, hu, huinv⟩ :=
    factorization_of_actual_reconstruction g (hamiltonBox_hurwitzIntersection g)
  refine ⟨gamma, hgamma, u, ?_, hu, huinv⟩
  simpa only [qι_apply] using hfactor

/-- The whole rational Hamilton witness as a genuine unit; the same literal two clauses. -/
theorem actual_rational_unit_factorization
    (g : (Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))ˣ) :
    ∃ gamma : (Quaternion ℚ)ˣ,
      ∃ u : (Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))ˣ,
        (g : Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
          (⟨algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (gamma : Quaternion ℚ).re,
            algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (gamma : Quaternion ℚ).imI,
            algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (gamma : Quaternion ℚ).imJ,
            algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (gamma : Quaternion ℚ).imK⟩ :
            Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) *
          (u : Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) ∧
        (∃ a b c d e : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), b v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), d v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), e v ∈ v.adicCompletionIntegers ℚ) ∧
          (u : Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
            ⟨a - e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
              b + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
              c + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
              d + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2)⟩) ∧
        (∃ a b c d e : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ,
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), b v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), d v ∈ v.adicCompletionIntegers ℚ) ∧
          (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), e v ∈ v.adicCompletionIntegers ℚ) ∧
          ((u⁻¹ : (Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))ˣ) :
            Quaternion (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) =
            ⟨a - e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
              b + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
              c + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2),
              d + e * algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) (1 / 2)⟩) := by
  obtain ⟨gamma, hne, u, hfactor, hu, huinv⟩ := actual_rational_gamma_factorization g
  exact ⟨rationalGeneratorUnit gamma hne, u, hfactor, hu, huinv⟩

end TYZSquareOddness.Normalization
