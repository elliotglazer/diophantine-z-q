import ZInQKernel.Targets.H.Defs.PkgI4
import ZInQKernel.HDecomp.Objects

/-!
# H target R10: de Rham comparison for abelian varieties, with Hodge–Tate weights

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.R10` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.R10_holds` in module `ZInQKernel.Contrib.H.R10`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI4.DeRhamComparison` (reference lines 3198-3211). Statement bodies are copied verbatim except
for the edits listed on each part.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 300-306:

**R10. de Rham comparison.** For `F/ℚ_ℓ` finite and `A/F`, `H¹_et(A_F̄, ℚ_ℓ)` is de Rham with
`D_dR ≅ H¹_dR(A/F)`; `V_ℓ(A)` has HT weights `0, −1`, each with multiplicity `dim A`. Ref: Scholze,
Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum; or Faltings 1989, Tsuji 1999. E
(first clause); the Tate-module form stated in Lean is a consequence with T10. Lean: **yes**,
`PkgI4.DeRhamComparison`, over pkg-I3's Tate modules (copied as `PkgI4.I3`) and pkg-I4's de Rham
predicate (`G_F`-action on Mathlib's `BDeRham 𝓞_ℂ_p`, `D_dR`, `IsDeRhamOver`) and Hodge–Tate
weights. Step C3.

Conventions and caveats:
* The reference states this over `PkgI4.I3.AbVar`, a verbatim renamed copy of package I3; the target
  uses the baseline's identical `PkgI3.AbVar` (`ZInQKernel/HDecomp/Objects.lean`). The published
  first clause is about `H¹_et`; the Tate-module form here is a consequence with T10 (`V_ℓ(A) ≅
  H¹_et(A, ℚ_ℓ)^∨`, an opaque, unregistered leaf). Hodge–Tate weights in the Tate normalization
  (cyclotomic weight −1); `IsDeRhamOver`/`htMultOver` have no proved non-vacuity check yet (pkg-I4
  §3.4).
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open scoped MatrixGroups ModularForm
open PkgI4

namespace ZInQ.Targets.H

/-- **Target R10.**

**I4-L0. de Rham comparison for abelian varieties, with Hodge–Tate weights** (C3; Fontaine,
LNM 1016 (1983) and Fontaine–Messing (1987) for abelian varieties; Faltings 1989; Tsuji 1999 with
de Jong; Scholze 2013 Cor. 1.8 with Thms 9.1, 9.3 and the 2016 corrigendum; with
`V_p(A) ≅ H¹_et(A_F̄, ℚ_p)^∨`, Mumford §§19-20 / Milne 1986 Thm 15.1(a); numbers UNVERIFIED except
Scholze's wording, VERIFIED by h-leaves §3.1). For an abelian variety `A` of dimension `g` over a
finite extension `F` of `ℚ_p`, `V_p(A)` (pkg-I3's `galRep`) is de Rham as a
`G_F`-representation, with Hodge–Tate weight `0` and `−1` each of multiplicity `g`. Consequence
form. Statable now over genuine definitions: pkg-I3's abelian varieties and Tate modules, and
§1b's `IsDeRhamOver`, `htMultOver`.

Reference declaration `PkgI4.DeRhamComparison`; edits: `PkgI4.I3.AbVar` → baseline `PkgI3.AbVar`
(identical copy). -/
def R10 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
      htMultOver p (A.galRep p) (-1) = g

end ZInQ.Targets.H
