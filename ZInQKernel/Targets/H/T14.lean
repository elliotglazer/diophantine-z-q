import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# H target T14: ABHN and reciprocity for `H²(G_ℚ, ℤ/2)`

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T14` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T14_holds` in module `ZInQKernel.Contrib.H.T14`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged): `PkgI6.BrauerHasse2`
(reference lines 3434-3442); `PkgI6.BrauerReciprocity2` (reference lines 3445-3453). Statement
bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 387-387:

| T14 | ABHN and reciprocity for `H²(G_ℚ, ℤ/2)`: injective into `∏_v H²(G_{ℚ_v}, ℤ/2)`, finite even support | Milne ADT I; Tate in C–F VII §11 | C | yes, `PkgI6.BrauerHasse2`, `PkgI6.BrauerReciprocity2`; the finite-places cochain form used by glue-descent, `GlueDescent.B2Q.LeafHasse`, is a consequence (with T15 at `∞`); algebra form `HSyn.HasseBrauerQ` also compiles | Tau Ceti (Br forms `brLocalization_injective`, `sumLocalInv_brLocalization_eq_zero`); the `H²` bridge not located |

Conventions and caveats:
* Two parts (injectivity; finite even support), proposed as one target `T14 = T14a ∧ T14b`.
  Glue-descent's finite-place cochain forms are consequences (with T15 at ∞), not registered.
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open CategoryTheory IsLocalRing
open PkgI6

namespace ZInQ.Targets.H

/-- **Part T14(a).**

**Leaf I6.2a (Albert–Brauer–Hasse–Noether, 2-torsion, Galois-cohomology form).**
`H²(G_ℚ, ℤ/2) → ∏_v H²(G_{ℚ_v}, ℤ/2)` is injective: `Ш²(ℚ, ℤ/2) = 0` over all places.
This is the injectivity of `Br ℚ → ⊕_v Br ℚ_v` (Milne, ADT, Ch. I, Thm 4.? / Neukirch–Schmidt–
Wingberg (8.1.17); Tate in Cassels–Fröhlich VII §11.2: UNVERIFIED locators) composed with the
Kummer isomorphism `H²(G_K, μ₂) ≅ Br(K)[2]` (Hilbert 90; Serre, *Corps locaux* X §4–5), which is
natural in `K`.

Reference declaration `PkgI6.BrauerHasse2`, body verbatim. -/
def T14a : Prop :=
  ∀ x : continuousCohomology 2 (Z2 ℚ),
    locInf.hom x = 0 → (∀ (p : ℕ) [Fact p.Prime], (locP p).hom x = 0) → x = 0

/-- Cross-check: `T14a` is, by definition, the baseline's `PkgI6.BrauerHasse2`. -/
theorem T14a_iff_baseline : T14a ↔ PkgI6.BrauerHasse2 := Iff.rfl

open Classical in
/-- **Part T14(b).**

**Leaf I6.2b (reciprocity, 2-torsion form).** For `x ∈ H²(G_ℚ, ℤ/2)` the set of places where
`x` is locally nonzero is finite and has even cardinality.  This is `∑_v inv_v = 0` together with
`inv_v(x) ∈ {0, 1/2}` and `inv_v` injective (Milne ADT Ch. I; Serre, *Corps locaux* XIII §3 for
`Br ℚ_p ≅ ℚ/ℤ`; UNVERIFIED locators).

Reference declaration `PkgI6.BrauerReciprocity2`, body verbatim. -/
def T14b : Prop :=
  ∀ x : continuousCohomology 2 (Z2 ℚ),
    {p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom x ≠ 0}.Finite ∧
    Even ({p : Nat.Primes | haveI : Fact (p : ℕ).Prime := ⟨p.2⟩; (locP (p : ℕ)).hom x ≠ 0}.ncard
      + if locInf.hom x = 0 then 0 else 1)

/-- Cross-check: `T14b` is, by definition, the baseline's `PkgI6.BrauerReciprocity2`. -/
theorem T14b_iff_baseline : T14b ↔ PkgI6.BrauerReciprocity2 := Iff.rfl

/-- **Target T14**: all parts of the leaf, as a conjunction (`T14a`, `T14b`). -/
def T14 : Prop :=
  T14a ∧ T14b

end ZInQ.Targets.H
