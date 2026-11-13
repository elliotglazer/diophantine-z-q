import ZInQKernel.Targets.H.Defs.PkgI1
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# H target T28: Clebsch–Bolza–Igusa separation of binary sextics

Draft engineering statement extraction (not a proof, not an acceptance). Proposed target
`ZInQ.Targets.H.T28` (closed `Prop`, no universe parameters). Its proof provider is pre-assigned as
`ZInQ.Contrib.H.T28_holds` in module `ZInQKernel.Contrib.H.T28`; **that provider is not declared
anywhere in this change** (no `axiom`, no `sorry`, no placeholder). Registration in
`KERNEL_CONTRACT.json` is only *proposed* (`docs/h-targets/registration-proposal.json`) and needs
maintainer statement review.

Source: the reference `scratch/h-decomposition/Leaves.lean` (fork `diophantine-z-q`, base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, unchanged):
`PkgI1.IgusaClebschSeparation` (reference lines 741-754). Statement bodies are copied verbatim.

Leaf entry of the reference note `docs/research/h-decomposition.md` (611 lines, SHA-256
`5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`), §2 (theorem numbers UNVERIFIED
unless marked there):

Note lines 406-406:

| T28 | Clebsch–Bolza–Igusa: Igusa invariants separate `GL₂`-orbits of binary sextics with nonzero discriminant | Igusa, Ann. of Math. 72 (1960) | E | yes, `PkgI1.IgusaClebschSeparation` | none |

Conventions and caveats:
* The objects are the definition-only modules `ZInQKernel/Targets/H/Defs/*` (verbatim reference
  definitions, unreviewed; note §6 R4).
* A placeholder-free statement over genuine definitions is still only as faithful as those
  definitions; locators are UNVERIFIED unless the note marks them VERIFIED (note §6 R1).
-/

open Complex Matrix
open PkgI1

namespace ZInQ.Targets.H

/-- **Target T28.**

**LEAF (Clebsch 1872, Bolza 1888, Igusa 1960).** Over an algebraically closed field of
characteristic 0, two binary sextics with nonzero discriminant are equivalent under
`GL₂ × 𝔾_m` iff their Igusa invariants agree in weighted projective space `P(1,2,3,5)`.
(Equivalently: two genus-2 curves are isomorphic iff `[J₂:J₄:J₆:J₁₀]` agree.) The `⇒`
direction is the transformation law `J_{2k}(e·f|M) = (e·det³M)^{2k} J_{2k}(f)` (checked in
`igusa_poly.py`); the content is `⇐`. Igusa, *Arithmetic variety of moduli for genus two*,
Ann. of Math. 72 (1960) (§§1-2, UNVERIFIED locator); Mestre, *Construction de courbes de genre 2
à partir de leurs modules*, Progr. Math. 94 (1991) (UNVERIFIED locator).

Reference declaration `PkgI1.IgusaClebschSeparation`, body verbatim. -/
def T28 : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharZero L] (f g : Fin 7 → L),
    J10 f ≠ 0 → J10 g ≠ 0 →
    ((∃ M : Matrix (Fin 2) (Fin 2) L, M.det ≠ 0 ∧ ∃ e : L, e ≠ 0 ∧ g = sexticAct f M e) ↔
      ∃ r : L, r ≠ 0 ∧ J2 g = r * J2 f ∧ J4 g = r ^ 2 * J4 f ∧ J6 g = r ^ 3 * J6 f ∧
        J10 g = r ^ 5 * J10 f)

end ZInQ.Targets.H
