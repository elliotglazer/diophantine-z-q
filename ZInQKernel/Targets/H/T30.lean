import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# H target T30: Local square-root criterion for Dirichlet characters

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T30` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T30_holds` in module `ZInQKernel.Contrib.H.T30`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`GlueDescent.B2Q.LeafSqrtCrit` (reference lines 6999-7011). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 394-394:

| T30 | Local square-root criterion: `χ\|G_{ℚ_p}` has a continuous square root iff `χ(u) = 1` for `u ≡ −1 mod p^k`, `≡ 1` prime to `p` | consequence of local CFT for `ℚ_p` (Serre, *Local fields*) | C | yes, `GlueDescent.B2Q.LeafSqrtCrit` | none |

Conventions and caveats:
* Consequence (C) of local class field theory for `ℚ_p`.
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open GlueDescent.B2 GlueDescent.B2Q NumberField

namespace ZInQ.Targets.H

/-- **Target T30.**

**Leaf L-B2c** (explicit local square-root criterion for Dirichlet characters). For a
Dirichlet character `χ` mod `N` and a prime `p` with `N = p^k N'`, `p ∤ N'`, let `u ∈ (ℤ/N)^×`
be `≡ -1 mod p^k` and `≡ 1 mod N'`. Then `χ|_{G_{ℚ_p}}` has a continuous square-root
character iff `χ(u) = 1`. Consequence of local class field theory for `ℚ_p` with its explicit
(Lubin–Tate / cyclotomic) reciprocity law — the local Artin map sends `-1 ∈ ℤ_p^×` to an element
acting on `μ_N` through `u^{±1} = u` — together with the structure of `ℚ_p^×` (N5 L683-689: a
finite-order character of `ℚ_p^×` has a square root iff its value at `-1` is `1`).

Reference declaration `GlueDescent.B2Q.LeafSqrtCrit`, body verbatim. -/
def T30 : Prop :=
  ∀ (p : Nat.Primes) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (u : (ZMod N)ˣ),
    ((u : ZMod N).cast : ZMod ((p : ℕ) ^ N.factorization p)) = -1 →
    ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1 →
    ((∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧ ∀ x, φ x ^ 2 = galChar χ (resp p x)) ↔
      χ.toUnitHom u = 1)

/-- Cross-check: `T30` is, by definition, the baseline's `GlueDescent.B2Q.LeafSqrtCrit`. -/
theorem T30_iff_baseline : T30 ↔ GlueDescent.B2Q.LeafSqrtCrit := Iff.rfl

end ZInQ.Targets.H
