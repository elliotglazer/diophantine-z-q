import ZInQKernel.HDecomp.Objects

/-!
# H target T1: Zariski–Nagata purity of the branch locus, ring form

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T1` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T1_holds` in module `ZInQKernel.Contrib.H.T1`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI2.PurityBranchLocus` (reference lines 811-827). Statement bodies are copied verbatim except for
the edits listed on each part.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 370-370:

| T1 | Zariski–Nagata purity, ring form | SGA 1 X 3.4; Stacks 0BMB | E | yes, `PkgI2.PurityBranchLocus` | Stacks formalization `etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne` (unreviewed); Tau Ceti dim ≤ 2 |

Conventions and caveats:
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

/-- **Target T1.**

**Leaf I2-P (Zariski–Nagata purity of the branch locus).**
Ring form of Stacks Tag 0BMB (SGA 1, Exp. X, Thm 3.4, numbering UNVERIFIED):
let `R → S` be of finite type with `R` Noetherian, `q` a prime of `S` over `p`, with `R_p` regular,
`S_q` a normal domain, `S` quasi-finite at `q`, `dim S_q = dim R_p ≥ 1`, and `R → S` unramified at
every prime `q' ⊆ q` of height one. Then `R → S` is étale at `q`.

Reference declaration `PkgI2.PurityBranchLocus`; edits: `Type u` → `Type` (universe 0). -/
def T1 : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime],
    IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap R S))) →
    IsDomain (Localization.AtPrime q) →
    IsIntegrallyClosed (Localization.AtPrime q) →
    Algebra.QuasiFiniteAt R q →
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime (q.comap (algebraMap R S))) →
    1 ≤ ringKrullDim (Localization.AtPrime q) →
    (∀ (q' : Ideal S) [q'.IsPrime], q' ≤ q → q'.height = 1 → Algebra.IsUnramifiedAt R q') →
    Algebra.IsEtaleAt R q

/-- Cross-check: `T1` is, by definition, the baseline's `PkgI2.PurityBranchLocus.{0}`. -/
theorem T1_iff_baseline : T1 ↔ PkgI2.PurityBranchLocus.{0} := Iff.rfl

end ZInQ.Targets.H
