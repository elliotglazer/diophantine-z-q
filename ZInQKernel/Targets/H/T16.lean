import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# H target T16: Local Kronecker–Weber; local reciprocity with upper numbering

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T16` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T16_holds` in module `ZInQKernel.Contrib.H.T16`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI6.LocalKroneckerWeber` (reference lines 3610-3619); `PkgI6.LocalReciprocityUpper` (reference
lines 3785-3797). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 389-389:

| T16 | Local Kronecker–Weber for `ℚ_p`; local reciprocity at a finite abelian level with the upper numbering theorem | Neukirch V (1.10); Serre XIII §4, XV §2 | E | yes, `PkgI6.LocalKroneckerWeber`, `PkgI6.LocalReciprocityUpper` | not located |

Conventions and caveats:
* Two parts, proposed as one target `T16 = T16a ∧ T16b`. Part (a) is the reference's `∀ (p : ℕ)
  [Fact p.Prime], PkgI6.LocalKroneckerWeber p` (as bundled in `HSyn.TextbookLeaves.t16a`).
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open CategoryTheory IsLocalRing
open PkgI6

-- As in the baseline's `section LocalLeaves` (`ZInQKernel/HDecomp/Conductor/I6Base.lean`).
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace ZInQ.Targets.H

/-- **Part T16(a).**

**Leaf I6.3 (local Kronecker–Weber for `ℚ_p`).** Every finite abelian extension of `ℚ_p`
inside `\bar ℚ_p` lies in `ℚ_p(μ_n)` for some `n ≥ 1`.  (Serre, *Local class field theory*, in
Cassels–Fröhlich, §3.? ; Neukirch, *ANT* V (1.10); Lang, *ANT* (UNVERIFIED locators).)  In B2 it
replaces "local reciprocity" in the square-root criterion: a finite-order character of `G_{ℚ_p}`
has a character square root iff it is trivial on the element acting by `ζ ↦ ζ⁻¹` on `p`-power
roots of unity and trivially on prime-to-`p` roots of unity (GLUE).

Reference declaration `PkgI6.LocalKroneckerWeber`; edits: bound `p` as in
`HSyn.TextbookLeaves.t16a`. -/
def T16a : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    ∀ L : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] L →
      IsAbelianGalois ℚ_[p] L →
        ∃ n : ℕ, 0 < n ∧ L ≤ IntermediateField.adjoin ℚ_[p] {x : PadicAlgCl p | x ^ n = 1}

/-- Cross-check: `T16a` is, by definition, the baseline's `∀ (p : ℕ) [Fact p.Prime],
PkgI6.LocalKroneckerWeber p`. -/
theorem T16a_iff_baseline : T16a ↔ ∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p := Iff.rfl

/-- **Part T16(b).**

(no docstring in the reference)

Reference declaration `PkgI6.LocalReciprocityUpper`, body verbatim. -/
def T16b : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [Finite (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    (∀ σ τ : B ≃ₐ[A] B, σ * τ = τ * σ) →
    ∃ θ : (FractionRing A)ˣ →* (B ≃ₐ[A] B), Function.Surjective θ ∧
      (∀ x, θ x = 1 ↔ ∃ y : FractionRing B,
          Algebra.norm (FractionRing A) y = (x : FractionRing A)) ∧
      (∀ (π : A), Irreducible π → ∀ hπ : IsUnit (algebraMap A (FractionRing A) π),
          ∀ b : B, θ hπ.unit b - b ^ Nat.card (ResidueField A) ∈ maximalIdeal B) ∧
      (∀ v : ℝ, 0 ≤ v → θ '' unitFiltration A ⌈v⌉₊ = (upperRam A B v : Set (B ≃ₐ[A] B)))

/-- Cross-check: `T16b` is, by definition, the baseline's `PkgI6.LocalReciprocityUpper`. -/
theorem T16b_iff_baseline : T16b ↔ PkgI6.LocalReciprocityUpper := Iff.rfl

/-- **Target T16**: all parts of the leaf, as a conjunction (`T16a`, `T16b`). -/
def T16 : Prop :=
  T16a ∧ T16b

end ZInQ.Targets.H
