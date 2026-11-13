import ZInQKernel.Targets.H.Defs.HSyn

/-!
# H target T19: Brauer–Nesbitt (characteristic 0, trace form)

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T19` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T19_holds` in module `ZInQKernel.Contrib.H.T19`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged): `HSyn.BrauerNesbitt`
(reference lines 9016-9029). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 392-392:

| T19 | Brauer–Nesbitt (char 0, trace form) | Curtis–Reiner §30; Lang XVII 3.8 | E | yes, `HSyn.BrauerNesbitt` (also `PkgI6.BrauerNesbittChar0`) | none found |

Conventions and caveats:
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open scoped MatrixGroups ModularForm
open HSyn

namespace ZInQ.Targets.H

/-- **Target T19.**

**L19. Brauer–Nesbitt** (Curtis–Reiner §30). Semisimple representations of a group over a
field of characteristic 0 with equal traces are isomorphic. Exact.

Reference declaration `HSyn.BrauerNesbitt`, body verbatim. -/
def T19 : Prop :=
  ∀ (G : Type) [Group G] (E : Type) [Field E] [CharZero E] (n : ℕ)
    (ρ₁ ρ₂ : G →* GL (Fin n) E),
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₁ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ W : Submodule E (Fin n → E),
      (∀ g, W.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W) →
      ∃ W', IsCompl W W' ∧ ∀ g, W'.map (Matrix.toLin' (ρ₂ g : Matrix (Fin n) (Fin n) E)) ≤ W') →
    (∀ g, Matrix.trace (ρ₁ g : Matrix (Fin n) (Fin n) E) =
      Matrix.trace (ρ₂ g : Matrix (Fin n) (Fin n) E)) →
    ∃ P : GL (Fin n) E, ∀ g, ρ₂ g = P * ρ₁ g * P⁻¹

end ZInQ.Targets.H
