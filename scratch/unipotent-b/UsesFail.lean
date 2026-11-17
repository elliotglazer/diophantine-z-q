import ZInQKernel.OneProof.H.TailZ14

/-! # unipotent-b: do the uses of `semistableUnipotent` survive the added instances?

`SemistableUnipotent0` below is `UnipotentB.SemistableUnipotent0` (the field with `[CharZero K]` and
`[PerfectField k(s)]`), restated here because scratch files cannot import each other.
`fail_r6` replays `ReductSplit.raynaudCriterion_of_leaves` (the r6 proof) with it: it must fail,
since `PkgI2.RaynaudCriterion` quantifies over every field. `raynaudCriterion0_of_leaves` proves
the row restricted to the same instances. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open PkgI2 (IsAbelianVariety IsInertia)
open ReductSplit

set_option linter.style.haveILetI false

namespace UnipotentBUses

def SemistableUnipotent0 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [PerfectField (IsLocalRing.ResidueField O)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K, HasSemistableReduction A O →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) → ∀ σ : Ω ≃ₐ[K] Ω, IsInertia w σ →
      ∀ t : TΩ A Ω ℓ, galTΩ A ℓ σ (galTΩ A ℓ σ t) - 2 • galTΩ A ℓ σ t + t = 0

/-- Expected to FAIL (kept as a record): the r6 proof with the restricted field. -/
theorem fail_r6 (hR : RaynaudSemistable) (hU : SemistableUnipotent0)
    (hN : NeronSchemeModelExistsDVR) (hT : PkgI2.TorsionStructure.{0})
    (hF : FixedTorsionRational) : PkgI2.RaynaudCriterion.{0} := by
  intro K _ O _ w hw A _ m hm hmO hrat σ hσ ℓ hℓ hℓO n x hx
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  let B := ObjBridge.ofGrp A
  have hss : SemistableNeronModels B O :=
    hR K O B m hm hmO (hF K B m (natCast_ne_zero_of_isUnit O hmO) (fun σ x hx => hrat σ x hx))
  obtain ⟨t, ht⟩ := exists_tate_lift A hT ℓ (natCast_ne_zero_of_isUnit O hℓO) n x hx
  exact unipSq_of_tate B ℓ σ t n x ht
    (hU K O (AlgebraicClosure K) w hw B (hasSemistableReduction_of hN O B hss) ℓ hℓO σ hσ t)

end UnipotentBUses
