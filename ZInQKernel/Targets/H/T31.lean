import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# H target T31: Unramified classes of `H²(G_{ℚ_p}, ±1)` vanish

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T31` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T31_holds` in module `ZInQKernel.Contrib.H.T31`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`GlueDescent.B2Q.LeafUnramified` (reference lines 7025-7032). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 395-395:

| T31 | Unramified classes of `H²(G_{ℚ_p}, ±1)` vanish (`cd ℤ̂ = 1`) | Serre, *Galois cohomology* II §3 | C | yes, `GlueDescent.B2Q.LeafUnramified` | none |

Conventions and caveats:
* Consequence (C) (`cd ℤ̂ = 1`).
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open GlueDescent.B2 GlueDescent.B2Q NumberField

namespace ZInQ.Targets.H

/-- **Target T31.**

**Leaf L-B2d** (unramified classes vanish locally). If `ε` is inflated from `Gal(L/ℚ)` for
a finite Galois `L` unramified at `p`, its restriction to `G_{ℚ_p}` is a coboundary.
Consequence of: the restriction is inflated from `Gal(ℚ_p^{ur}/ℚ_p) ≅ ℤ̂`, and
`H²(ℤ̂, ℤ/2) = 0` (`cd ℤ̂ = 1`).

Reference declaration `GlueDescent.B2Q.LeafUnramified`, body verbatim. -/
def T31 : Prop :=
  ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ), IsSignCocycle ε → InflatedFrom L ε →
    ∀ p : Nat.Primes, UnramifiedAt L p → SignCob (pull (resp p) ε)

/-- Cross-check: `T31` is, by definition, the baseline's `GlueDescent.B2Q.LeafUnramified`. -/
theorem T31_iff_baseline : T31 ↔ GlueDescent.B2Q.LeafUnramified := Iff.rfl

end ZInQ.Targets.H
