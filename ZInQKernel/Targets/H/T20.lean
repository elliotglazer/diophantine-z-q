import ZInQKernel.HDecomp.Conductor.Breaks

/-!
# H target T20: Hilbert's different formula

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T20` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T20_holds` in module `ZInQKernel.Contrib.H.T20`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`GlueConductor.HilbertDifferentFormula` (reference lines 4188-4196). Statement bodies are copied
verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 398-398:

| T20 | Hilbert's different formula | Serre, *Corps locaux* IV §1 Prop. 4 | E | yes, `GlueConductor.HilbertDifferentFormula` (also `PkgI6.HilbertDifferentFormula`) | Tau Ceti |

Conventions and caveats:
* The reference counts glue-conductor's form (`GlueConductor.HilbertDifferentFormula`), not the
  baseline's `PkgI6.HilbertDifferentFormula`.
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open Finset NumberField
open GlueConductor

namespace ZInQ.Targets.H

/-- **Target T20.**

**Leaf (Hilbert's different formula; Serre, *Corps locaux*, IV §1, Prop. 4, with `G_i = 1`
for large `i`, IV §1; UNVERIFIED numbering).** For a Galois number field `L` and a nonzero prime
`P` of `𝓞 L`, some `G_n` is trivial and the exact power of `P` in the different of `𝓞 L/ℤ` is
`∑_{i<n} (|G_i| - 1)`.

Reference declaration `GlueConductor.HilbertDifferentFormula`, body verbatim. -/
def T20 : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

/-- Cross-check: `T20` is, by definition, the baseline's `GlueConductor.HilbertDifferentFormula`. -/
theorem T20_iff_baseline : T20 ↔ GlueConductor.HilbertDifferentFormula := Iff.rfl

end ZInQ.Targets.H
