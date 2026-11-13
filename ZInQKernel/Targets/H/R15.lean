import ZInQKernel.Targets.H.Defs.HSyn

/-!
# H target R15: Deligne–Serre: weight one gives finite image

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.R15` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.R15_holds` in module `ZInQKernel.Contrib.H.R15`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`HSyn.DeligneSerreConseq` (reference lines 9040-9047). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 333-335:

**R15. Deligne–Serre, finite image.** A semisimple `ρ` attached to a weight-1 eigenform has finite
image. Ref: Ann. Sci. ÉNS 7 (1974), Thm 4.1 (with T18, T19 for "every semisimple `ρ` with these
traces"). C. Lean: **yes**, `HSyn.DeligneSerreConseq`. Step C8.

Conventions and caveats:
* Consequence (C): Deligne–Serre Thm 4.1 together with T18 and T19 ("every semisimple `ρ` with these
  traces").
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open scoped MatrixGroups ModularForm
open HSyn

namespace ZInQ.Targets.H

/-- **Target R15.**

**L27(b). Deligne–Serre, in the form used** (Ann. Sci. ÉNS 7 (1974), Thm 4.1, with L18 and
L19). A semisimple representation attached to a weight-one eigenform has finite image.
Consequence.

Reference declaration `HSyn.DeligneSerreConseq`, body verbatim. -/
def R15 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (ρ : GaloisRep ℓ 2) (N : ℕ) (χ : DirichletCharacter ℂ N) (g : CF N 1),
    0 < N → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    (Set.range ρ.toHom).Finite

end ZInQ.Targets.H
