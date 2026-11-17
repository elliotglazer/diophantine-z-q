# gt-shpair: summary

**Verdict.** `ReductGlue.StrictHenselizationPair` (GLUE, composite) now rests on one printed-form leaf. Its
commutative-algebra half is proved in Lean for every characteristic and every residue field.

**The leaf.** `GapSHPair.NeronBaseChangeStrictHenselization` is BLR, *Néron models*, §1.2 Prop. 2: Néron models
commute with strict henselization (locator UNVERIFIED). It is stated for unramified strictly henselian extensions
with `K₁/K` separable and separable residue extension (`IsSHSep`). In every characteristic these conditions pin
`O₁ ≅ O^sh` (report §2), so the leaf is the printed theorem up to isomorphism of bases. It is also a specialization of
the chain's `ReductGlue.NeronBaseChangeUnramifiedDVR` (checked in Lean).

**What compiles.**
- The deliverable is `ZInQKernel/Contrib/OneProof/StrictHenselizationPair.lean` (namespace `GapSHPair`, 81 KB). It
  imports `TailZ14` and `Mathlib`, not `Main`. Its build succeeds.
- `#discharges` reports `strictHenselizationPair` discharged by:
  - `strictHenselizationPair_of_neron` (still assumes the new leaf);
  - `strictHenselizationPair_of_unramified` (still assumes `NeronBaseChangeUnramifiedDVR`).
- Axioms are `[propext, Classical.choice, Quot.sound]`. There is no `sorry`.
- `GapSHPair.shPair` (the commutative algebra) has no hypotheses.

**What is new mathematically.** Task sh-route covered only characteristic 0 with a perfect residue field. This task
extends it:
- **Inertia ring without separable residue fields.** Mathlib's `card_inertia_eq_ramificationIdxIn` needs separable
  residue fields. It is replaced by `|I|·|Aut(κP/κp)| = e·f` (from Mathlib's fundamental identity and
  `Stab/I ≃ Aut`) plus a separable-degree count. This gives `e = 1` and a separable residue extension for the
  inertia ring.
- **Separable simple roots** in characteristic `p`.
- **The nesting `E_{K'} ⊆ E_K(K')`** in characteristic `p`, by a `p`-power argument.

**What remains.**
- The Néron leaf. Néron models are not in Mathlib.
- The BLR and EGA IV₄ 18.8 locators are UNVERIFIED (no network).
- The general (all-characteristic) forms of `StrictHenselizationNeron` and `StrictHenselizationInside` would follow
  from the same file but are not open fields, so they are not done.

Report: `docs/research/gt-shpair.md`. Log: `scratch/gt-shpair/log.md`.
