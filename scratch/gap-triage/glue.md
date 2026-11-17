# gap-triage: the glue field `quotientP1Coordinate` (my own reading; probe GlueProbe.lean)

Field `quotientP1Coordinate : MCRGlue.QuotientP1Coordinate` (OpenGlue7, TailX.lean L191), project glue.
Consumer: TailX.lean L282 `modelCoordinateResidue := MCRGlue.modelCoordinateResidue_of_quotient' g.quotientP1Coordinate`
(VERIFIED grep). Use: (b) one object: the smooth model 𝒴 over ℤ_(p) of the canonical triple (Y₃, Φ, π) at each
prime p > 324, with the coordinate π normalized at the three CM values 0, ∞, −16/27.

mcr-quot (scratch/mcr-quot/MCRQuot.lean, compiled there; not in the chain) proves
`modelCoordinateResidue_final9 (hAF hQE hTS hP1 hFix hCyc) (hT : TorsionStructure) (hC : CurveBijIso)
 (hCov : CoverModelOfHeckeN) (hP : P1SchemeQ) (hO : CMStabObj) : ModelCoordinateResidue`.

## CoverModelOfHeckeN is not needed (no Lemma NV)

VERIFIED by reading MCRQuot.lean: `hCov` is used only through
`modelYIrreducible_of_coverModelN (hT) (hCov) : ModelYIrreducible` (L7609; every later composite passes
`modelYIrreducible_of_coverModelN hT hCov` into the `hYI : ModelYIrreducible` slot).
VERIFIED by reading: the body of `MCRQuot.ModelYIrreducible` (L7336) is token-for-token the body of the chain's
`HDec.PropTSGlue.HeckeIrreducible` (TailG.lean L3919), and the chain proves
`HDec.TSHecke.heckeIrreducible_of_connected (hC : Y3Connected) : HeckeIrreducible` (TailG L8380), with
`Y3Connected` filled from the field `deligneComponentsY3Printed` in `addedLeaves8_of_open9` (TailZ13 L55).
So `ModelYIrreducible` follows from a field already in the bundles; `CoverModelOfHeckeN` (and with it
`HeckeNoVertRam` = Lemma NV) leaves the route. Probe `GlueProbe.lean` compiles this (see log).

## P1SchemeQ (foundations)

`∃ P τ, IsProper P.hom ∧ SmoothOfRelativeDimension 1 P.hom ∧ IsP1CoordinateQ P τ ∧ ∀ Z σ, ∃ m eU eV, …`
(MCRQuot.lean L8549). CloudW07 (frenzymath Jacobian-Challenge) provides (VERIFIED read; #check in probe):
`projectiveLine k := Proj k[X₀,X₁]`, `isProper_toSpec`, `smoothOfRelativeDimension_toSpec`, `chartSpecIso`,
`isAffineOpen_chart`, `polyEquivChart`; the relative line `ℙ(ULift (Fin 2); S)` with `homOfSections`
(maps from global sections generating the unit ideal), `homOfSections_preimage_standardOpen`, `hom_ext`,
`instIsProper`, `normalized`, `normalized_eq_of_mul_eq_one` (the two normalized maps agree where fg = 1).
Mathlib: `Scheme.OpenCover.glueMorphisms`. Missing: (1) the two charts of `projectiveLine ℚ` (or of the
relative line) as a `ToP1` with `IsP1CoordinateQ` (affine + bijective ℚ[X] → Γ); (2) for σ : ToP1 Z, glue
`normalized … 0 f` on U and `normalized … 1 g` on V (agreement on U ⊓ V by `normalized_eq_of_mul_eq_one`),
(3) the preimage equalities m⁻¹U_τ = U_σ, m⁻¹V_τ = V_σ (from `homOfSections_preimage_standardOpen` and
`basicOpen_f/g` of ToP1) and the two pullback equalities of f, g. If the relative line is used, smoothness
must be transported (charts ≅ 𝔸¹) or taken from `projectiveLine` via an iso. Tier T1 (one agent task),
risk: universe/`Over` plumbing and eqToHom transport in the last clause.

## CMStabObj (QM objects with CM)

`∀ P : QML3 Qbar, (HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q) → ∃ α u, T fixes [P] ∧ T∘T = id ∧ T ≠ id`
with `T = M3.twist α ∘ M3.rightMul u` (MCRQuot.lean L7648). Needs, per CM type, an automorphism or normalizer
element of `(A, ι)` acting on `A[3]` as a unit u of 𝒪 mod 3 (the ℤ[i] case: α = id, u a lift of the action of
i; ℤ[ζ₃] and ℤ[√−6]: an Atkin–Lehner-type twist from the normalizer of ι(𝒪) in End A), plus an object whose
class T moves. The bundle field `qmCentralizerCMC` (End_𝒪(A) is ℤ or an optimal order) and the kernel's
`Level3.torsor`, `exists_unit_congr` are the available inputs. Tier T2 (QM endomorphism computations at CM
points; SPECULATIVE), strategy: prove directly from `qmCentralizerCMC` + T5; split by CM type.
