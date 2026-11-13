import ZInQKernel.HDecomp.Objects

/-!
# H target R9: Faltings 1983: semisimplicity and the Tate conjecture

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.R9` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.R9_holds` in module `ZInQKernel.Contrib.H.R9`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI3.FaltingsSemisimple` (reference lines 1613-1617); `PkgI3.FaltingsTate` (reference lines
1619-1625). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 291-298:

**R9. Faltings 1983.** (a) `V_ℓ(A)` is a semisimple `G_F`-representation; (b)
`Hom_F(A,B) ⊗ ℤ_ℓ → Hom(T_ℓA, T_ℓB)` is injective with image the `G_F`-equivariant maps. Ref:
Invent. Math. 73 (1983), Satz 3, Satz 4, Korollar 1, pp. 360-361 (read by a model); erratum 75
(1984). E. Objects: abelian varieties, `Hom`, `T_ℓ`, `V_ℓ` with Galois action, all defined by
pkg-I3 on Mathlib's group schemes (`PkgI3.AbVar`, `AbVar.T`, `AbVar.galRep`). Lean: **yes**,
`PkgI3.FaltingsSemisimple`, `PkgI3.FaltingsTate` (the easy inclusion of (b) is proved,
`PkgI3.range_tateHomZl_subset`, so the leaf asserts exactly the published content). Steps C2, C10,
E1.

Conventions and caveats:
* Two parts (Satz 3; Satz 4 with Korollar 1), proposed as one target `R9 = R9a ∧ R9b`. The easy
  inclusion of (b) is already proved in the baseline (`PkgI3.range_tateHomZl_subset`), so (b)
  asserts exactly the published content.
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar Polynomial
open scoped Quaternion TensorProduct

namespace ZInQ.Targets.H

/-- **Part R9(a).**

**I3.F1 — Faltings 1983, Satz 3 (semisimplicity).** For an abelian variety `A` over a number
field `K` and a prime `ℓ`, the representation of `G_K` on `V_ℓ(A)` is semisimple.

Reference declaration `PkgI3.FaltingsSemisimple`, body verbatim. -/
def R9a : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    (A.galRep ℓ).IsSemisimpleRepresentation

/-- Cross-check: `R9a` is, by definition, the baseline's `PkgI3.FaltingsSemisimple`. -/
theorem R9a_iff_baseline : R9a ↔ PkgI3.FaltingsSemisimple := Iff.rfl

/-- **Part R9(b).**

**I3.F2 — Faltings 1983, Satz 4 (`A = B`) and Korollar 1 (Tate's conjecture).** For abelian
varieties `A, B` over a number field `K` and a prime `ℓ`, the natural map
`Hom_K(A, B) ⊗ ℤ_ℓ → Hom_{ℤ_ℓ}(T_ℓ A, T_ℓ B)` is injective with image the `G_K`-equivariant maps.

Reference declaration `PkgI3.FaltingsTate`, body verbatim. -/
def R9b : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    Function.Injective (tateHomZl ℓ A B) ∧
      Set.range (tateHomZl ℓ A B) = {φ | IsGalEquivariant φ}

/-- Cross-check: `R9b` is, by definition, the baseline's `PkgI3.FaltingsTate`. -/
theorem R9b_iff_baseline : R9b ↔ PkgI3.FaltingsTate := Iff.rfl

/-- **Target R9**: all parts of the leaf, as a conjunction (`R9a`, `R9b`). -/
def R9 : Prop :=
  R9a ∧ R9b

end ZInQ.Targets.H
