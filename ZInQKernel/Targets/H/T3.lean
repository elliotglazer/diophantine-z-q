import ZInQKernel.HDecomp.Objects

/-!
# H target T3: Néron mapping property, abelian-scheme case

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T3` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T3_holds` in module `ZInQKernel.Contrib.H.T3`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI2.NeronMappingAbelianScheme` (reference lines 981-990). Statement bodies are copied verbatim
except for the edits listed on each part.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 373-373:

| T3 | Néron mapping property, abelian-scheme case | BLR §1.2 Prop. 8 | C | yes, `PkgI2.NeronMappingAbelianScheme` | Anthropic FLT (Néron models, special case) |

Conventions and caveats:
* Consequence (C) of BLR §1.2 Def. 1, Prop. 8.
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

/-- **Target T3.**

**Leaf I2-NMP (Néron mapping property, abelian-scheme case).** Consequence of
Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2, Def. 1 and Prop. 8 (an abelian scheme
over a DVR is the Néron model of its generic fibre; numbers UNVERIFIED): for abelian schemes
`𝒜, ℬ` over the DVR `O ⊆ K`, restriction to the generic fibre is a bijection
`Hom_O(𝒜, ℬ) → Hom_K(𝒜_K, ℬ_K)` (morphisms of schemes over the base).

Reference declaration `PkgI2.NeronMappingAbelianScheme`; edits: `Type u` → `Type` (universe 0). -/
def T3 : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (𝒜 ℬ : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] [IsAbelianScheme ℬ],
    Function.Bijective (fun f : 𝒜.X ⟶ ℬ.X =>
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).map f)

/-- Cross-check: `T3` is, by definition, the baseline's `PkgI2.NeronMappingAbelianScheme.{0}`. -/
theorem T3_iff_baseline : T3 ↔ PkgI2.NeronMappingAbelianScheme.{0} := Iff.rfl

end ZInQ.Targets.H
