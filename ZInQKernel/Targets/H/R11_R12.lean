import ZInQKernel.Targets.H.Defs.PkgI4

/-!
# H target R11 + R12: Berger + Pan, jointly: Pan's theorem with "de Rham at p" (`PanBerger`)

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.R11_R12` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned
as `ZInQ.Contrib.H.R11_R12_holds` in module `ZInQKernel.Contrib.H.R11_R12`; **that provider is not
declared anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged): `PkgI4.PanBerger`
(reference lines 3302-3309); `PkgI4.PanFor` (reference lines 3284-3300), `PkgI4.LocalPred`.
Statement bodies are copied verbatim except for the edits listed on each part.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 308-310:

**R11. Berger.** de Rham ⇒ potentially semistable. Ref: Invent. Math. 148 (2002), Thm 0.7 (read
by a model; arXiv v3 Thm 0.6 VERIFIED by rv-h-a011). E. Lean: alone, **new defs** (`B_st`;
very large; template `PkgI4.BergerDR IsPst`); jointly with R12, **yes** (below). Step C4.

Note lines 312-319:

**R12. Pan.** `p` odd, `ρ : G_ℚ → GL₂(ℚ̄_p)` continuous irreducible, finitely ramified,
potentially semistable at `p`, odd, distinct HT weights (residual clause at `p = 3`) ⇒ there are a
normalized eigenform `g` and a continuous character `ψ` with `tr ρ(Frob_v) = ψ(Frob_v)·ι(a_v(g))`
for almost all `v`. Ref: JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by h-a011). C
(the trace reading; every reading in the literature implies it; §6 R2). Lean: alone, template
`PkgI4.PanFor IsPst` (missing only `IsPst`); jointly with R11, **yes**: `PkgI4.PanBerger`, Pan's
theorem with "de Rham at `p`" in place of "potentially semistable at `p`", the form N5 uses
(a consequence of R11 + R12, not a merged leaf: both are counted). Step C7.

Conventions and caveats:
* **One target for two leaves.** R11 (Berger 2002, Thm 0.7: de Rham ⇒ potentially semistable) and
  R12 (Pan 2022, Thm 1.0.4) are stated in the reference only through their joint consequence
  `PkgI4.PanBerger = PanFor LocalIsDeRham`; separately they need `B_st` (not defined). No separate
  Berger or Pan statement is proposed. Coverage: 35 leaves, 34 independent targets. The body is
  `PanFor` with `IsPst := LocalIsDeRham` beta-reduced. Restricted to `p ≥ 5` (drops Pan's residual
  clause at `p = 3`); trace reading of "comes from an eigenform up to twist", which every reading
  implies (note §6 R2).
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open scoped MatrixGroups ModularForm
open PkgI4

namespace ZInQ.Targets.H

/-- **Target R11_R12.**

**I4-L7′. Pan∘Berger — statable now, over genuine definitions.** Pan's Theorem 1.0.4
(`PanFor`, `p ≥ 5`) with "de Rham at `p`" (`LocalIsDeRham`, built in §1b on Mathlib's `BDeRham`)
in place of "potentially semistable at `p`". It is a consequence of Pan 2022 Thm 1.0.4 together
with Berger 2002 Thm 0.7 (de Rham ⇒ pst), and it is the form N5 uses (N5 L734-741 proves de Rham
and then applies Berger). Needs no `B_st`.

Reference declaration `PkgI4.PanBerger`; edits: `PanFor` unfolded with `IsPst := LocalIsDeRham`
(beta-reduced `PkgI4.PanBerger`). -/
def R11_R12 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ρ : GaloisRep p 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → LocalIsDeRham p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    ρ.DistinctHTWeights p →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar p) (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl p) (S : Finset ℕ),
        ρ.AttachedUpToTwist ψ ιC ιL g S

end ZInQ.Targets.H
