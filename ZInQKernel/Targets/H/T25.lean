import ZInQKernel.Targets.H.Defs.PkgI4

/-!
# H target T25: Newforms: each eigensystem away from the level is that of a newform

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T25` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T25_holds` in module `ZInQKernel.Contrib.H.T25`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI4.NewformOfEigenform` (reference lines 3254-3262). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 405-405:

| T25 | Newforms: each eigensystem away from the level is that of a newform of level dividing it | Li 1975 Thm 5; Miyake 4.6.19 | C | yes, `PkgI4.NewformOfEigenform` (newforms through the old space) | Tau Ceti (newform bookkeeping) |

Conventions and caveats:
* Consequence (C); newforms are defined through the old space (no Petersson product).
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open scoped MatrixGroups ModularForm
open PkgI4

namespace ZInQ.Targets.H

/-- **Target T25.**

**I4-L5. Newform attached to an eigensystem** (Li, Math. Ann. 212 (1975), Thm 5 (strong
multiplicity one) with the decomposition `S_k = S_k^new ⊕ S_k^old`; Miyake Thm 4.6.19; locators
UNVERIFIED). Every normalized eigenform of level `M` has the Hecke eigenvalues away from `M` of a
newform of level dividing `M`. Consequence form.

Reference declaration `PkgI4.NewformOfEigenform`, body verbatim. -/
def T25 : Prop :=
  ∀ (M : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ M) (g : CF M k),
    0 < M → IsNormalizedEigenform g χ →
    ∃ (N : ℕ) (χ' : DirichletCharacter ℂ N) (f : CF N k), 0 < N ∧ N ∣ M ∧ IsNewform f χ' ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M → coeff f p = coeff g p

end ZInQ.Targets.H
