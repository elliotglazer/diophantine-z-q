import ZInQKernel.HDecomp.Objects

/-!
# H target T27: QM dichotomy

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T27` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T27_holds` in module `ZInQKernel.Contrib.H.T27`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged): `PkgI3.QMDichotomy`
(reference lines 1661-1671). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 384-384:

| T27 | QM dichotomy: a quaternion division algebra in `End⁰` of an abelian surface over `k = k̄`, char 0, forces `End⁰ ≅ B` or `M₂(ℚ(√d))`, `d < 0` | Mumford §§19, 21-22 (Albert); Shimura 1963 | C | yes, `PkgI3.QMDichotomy` | none |

Conventions and caveats:
* Consequence (C) assembled from Mumford §§19, 21-22; a refereed locator is an open check (note §6
  R1).
* The objects (abelian varieties, Tate modules, Galois cohomology, ramification groups, …) are the
  PR36 baseline's (`ZInQKernel/HDecomp`), which are textually identical to the reference's apart
  from docstring line breaks; each part is checked against the baseline's own leaf definition by
  `Iff.rfl` (`…_iff_baseline`).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar Polynomial
open scoped Quaternion TensorProduct

namespace ZInQ.Targets.H

/-- **Target T27.**

**I3.Q — the QM dichotomy (step A9).** Over an algebraically closed field of characteristic
`0`, if a quaternion division algebra `B = (a, b)_ℚ` embeds in `End⁰(A)` for an abelian surface
`A`, then `End⁰(A) ≅ B` or `End⁰(A) ≅ M₂(ℚ(√d))` with `d < 0`. (Consequence of Mumford §19
Thm 1, Cor. 2, §21 (Albert, `[D:ℚ] ∣ 2g` in characteristic `0`) and §22; see the note.)

Reference declaration `PkgI3.QMDichotomy`, body verbatim. -/
def T27 : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
      Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
        Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
          ∃ d : ℚ, d < 0 ∧
            Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))

/-- Cross-check: `T27` is, by definition, the baseline's `PkgI3.QMDichotomy`. -/
theorem T27_iff_baseline : T27 ↔ PkgI3.QMDichotomy := Iff.rfl

end ZInQ.Targets.H
