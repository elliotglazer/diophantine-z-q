import ZInQKernel.HDecomp.Objects

/-!
# H target T5: Structure of `A(K̄)[n]`

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T5` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T5_holds` in module `ZInQKernel.Contrib.H.T5`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI2.TorsionStructure` (reference lines 1038-1047). Statement bodies are copied verbatim except
for the edits listed on each part.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 375-375:

| T5 | `A(K̄)[n] ≅ (ℤ/n)^{2g}`, `n` invertible | Mumford §4, §6 | E | yes, `PkgI2.TorsionStructure` | none |

Conventions and caveats:
* Dimension is the topological Krull dimension of the underlying space.
* universe specialization: the reference statement quantifies over `Type u`; the proposed target
  fixes `u = 0` (`Type`), the instance H uses (the reference bundles it as `.{0}`).
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj
open PkgI2

namespace ZInQ.Targets.H

/-- **Target T5.**

**Leaf I2-Tors (structure of `A[n]`; boundary with I3).** Mumford, *Abelian varieties*
(1970), §4, Application 2 / §6 (locator UNVERIFIED): for an abelian variety of dimension `g` over
`K` and `n ≥ 1` invertible in `K`, `A(K̄)[n] ≅ (ℤ/n)^{2g}` as groups. The dimension is the
topological Krull dimension of the underlying space.

Reference declaration `PkgI2.TorsionStructure`; edits: `Type u` → `Type` (universe 0). -/
def T5 : Prop :=
  ∀ (K : Type) [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A] (g n : ℕ),
    topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : K) ≠ 0 →
      ∃ e : torsion A (AlgebraicClosure K) n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A (AlgebraicClosure K) n,
          ∀ h : x.1 * y.1 ∈ torsion A (AlgebraicClosure K) n, e ⟨x.1 * y.1, h⟩ = e x + e y

/-- Cross-check: `T5` is, by definition, the baseline's `PkgI2.TorsionStructure.{0}`. -/
theorem T5_iff_baseline : T5 ↔ PkgI2.TorsionStructure.{0} := Iff.rfl

end ZInQ.Targets.H
