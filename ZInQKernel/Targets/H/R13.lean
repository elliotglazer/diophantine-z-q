import ZInQKernel.Targets.H.Defs.PkgI4

/-!
# H target R13: Hodge–Tate weights of eigenform representations, every level

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.R13` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.R13_holds` in module `ZInQKernel.Contrib.H.R13`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged): `PkgI4.EigenformHT`
(reference lines 3223-3234). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 321-325:

**R13. Hodge–Tate weights of eigenforms, every level.** `ρ_{g,ι}` for a weight-`k ≥ 2` eigenform
of any level is HT at `ℓ` with weights `{0, 1−k}` (Tate normalization). Ref: Saito, Invent. Math.
129 (1997); or Kato, Astérisque 295 (2004), §9.4; or Faltings 1987. C (normalization; rv-h-c8 R1).
Lean: **yes**, `PkgI4.EigenformHT` (Hodge–Tate multiplicities by Tate–Sen, `PkgI4.HasHTWeights`,
cyclotomic weight −1). Step C8.

Conventions and caveats:
* Tate normalization: weights `{0, 1 − k}` with cyclotomic weight −1 (note §6 R2, rv-h-c8 R1).
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open scoped MatrixGroups ModularForm
open PkgI4

namespace ZInQ.Targets.H

/-- **Target R13.**

**I4-L2. Hodge–Tate weights of eigenform representations, every level** (Faltings, Math.
Ann. 278 (1987) for `k ≥ 2` (level `ℓ ∣ N` UNVERIFIED there); Saito, Invent. Math. 129 (1997)
(pst at `ℓ`, every level); Kato, Astérisque 295 (2004) §9.4 (de Rham, every level); Scholl 1990
with Scholze 2013 and Fontaine's closure). A semisimple `ρ` attached to a normalized eigenform of
weight `k ≥ 2` and any level `N` (including `ℓ ∣ N`) is Hodge–Tate at `ℓ` with weights
`{0, 1 − k}` in the Tate normalization (cyclotomic weight `−1`; h-trust C8). Consequence form
(the published theorems give de Rham or pst, which imply Hodge–Tate with the same weights).

Reference declaration `PkgI4.EigenformHT`, body verbatim. -/
def R13 : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

end ZInQ.Targets.H
