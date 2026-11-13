# H-decomposition: claimable target task list (DRAFT)

**Status: DRAFT task list. No new proof providers. No headline assumption discharged.**
`ZInQ.SixContactMin` (H) remains a premise of the headline. This is not an official research record,
not Astra acceptance, and not a human approval of any statement. Target and provider names are the
code child's **proposed** names (early mapping, 2026-11-12 20:19 PST); none is registered or accepted.
Prepared 2026-11-12 from the frozen reference fork (see §9 for exactly what was checked).

**Reference used.** `diophantine-z-q/docs/research/h-decomposition.md` (611 lines, base
`48b5f075`) and the unmodified `scratch/h-decomposition/Leaves.lean` (9,321 lines, SHA-256
`99c4fa05…a05d3`), plus the PR #36 head `9bf9ad8a` (`ZInQKernel/HDecomp/`, docs) for reusable names.

## 0. Counts at a glance

| Quantity | Number | Note |
|---|---|---|
| Leaves of H in the reference (R1-R22 research, T1-T32 textbook) | 54 | 22 + 32 |
| Leaves with genuine Lean statements in the reference `Leaves.lean` | **35** | 10 research (R11 + R12 jointly) + 25 textbook |
| Genuine Props (bundle fields of `HSyn.ResearchLeaves` / `HSyn.TextbookLeaves`) | **39** | R7, R9, T14, T16, T22 have two parts each |
| **Locked targets proposed (one per leaf group)** | **34** | 33 single leaves + 1 joint target `R11_R12` covering two leaves |
| Multi-part targets (conjunction of two Props) | 5 | R7, R9, T14, T16, T22 |
| Opaque placeholder leaves (definition/API projects, **not** targets) | **19** | R1-R3, R5, R8, R16-R22; T9-T12, T23, T29, T32 |

How the counts were established: the reference bundles have 23 + 35 = 58 fields. Of these, 19 are the 19 `opaque` placeholders (the file's only `opaque` declarations), and the remaining 39 are genuine Props whose definitions were kernel-checked here (§9). Those 39 Props cover 35 distinct leaves. **34** is the code child's proposed grouping (conjunctions for R7, R9, T14, T16, T22, and one joint R11_R12). It is a proposal, not a registration.

Why 34 and not 35: Berger (R11) and Pan (R12) are stated **only** through their joint consequence
`PkgI4.PanBerger` (Pan's theorem with "de Rham at p" for "potentially semistable at p"). There is
no Lean definition of potentially semistable (`B_st`), so R11 and R12 cannot be separate targets.
Do not invent an `IsPst` definition, and do not open separate Pan or Berger targets. Proving
`R11_R12` covers both leaves in the count; it is one piece of work.

Potential further joint count (explicit). With the five two-part leaves split into separate Props,
the same coverage would be **39 Prop-level targets**. The code child bundles them as conjunctions
(**34**). No other merge is justified by the reference. Merging distinct publications was
rejected (reference §6, "Leaf count").

### Discrepancy with the PR #36 branch's own note (must be stated wherever this list is copied)

PR #36 (`h-targets/docs/research/h-decomposition.md`, 958 lines, revised by hsyn-fix, hsyn-fold
and a 2026-11-12 locator audit) claims **40 of 54 leaves, 46 Props**. The extra five (R8 in
monodromy form, T9, T23, T29a/b, T32a/b) come from a later `Leaves.lean` revision ("leaf-push").
That file is **not** in the PR #36 checkout (`docs/lean-contributions.md` says so) or in the
reference fork. This list uses the locked reference count: **35 leaves, 39 Props, 34 targets**.
Promoting the other five is a separate statement-review decision (§3, D-R8 etc.). The PR #36 note
also corrects R2, R3 and R5 and adds locator readings, which are folded into the caveats below. It
reports more proved glue (A6, C10, D1-local, D3, D4), which is listed separately in §4.

## 1. Legend

- **Kind**: `literature` (a published theorem to prove), `literature (joint)`, `port` (a
  formalization exists elsewhere: Tau Ceti, Stacks project; port provenance and attribution
  check pending), `def/API` (§3), `glue` (§4-§5).
- **Four separate statuses per target.** They must not be merged: compiling is not review.
  1. **Encoding** (faithful encoding of the source, per column `Encoding`). Every statement was
     encoded by AI-model tasks from the notes. Its fidelity to the published text is **not
     established**.
     - `Enc`: the Lean form is meant to be the printed statement (E in the reference).
     - `Enc-C`: the Lean form is a **consequence** of the printed statement. The derivation
       (Protocol_D: available result, needed assertion, exact derivation) must be written before
       a proof is accepted as closing the leaf.
     - `Enc-D`: another non-equivalent form of the same leaf exists, and that other form is the one
       the proved glue consumes. A bridge is needed (§5). Register only the bundle form.
     Theorem numbers are UNVERIFIED unless a note read them.
  2. **Statement kernel verification**: `K-def` means that the **reference** statement (the 39
     Props of the unmodified `Leaves.lean`) was audited here: it elaborates against the prebuilt
     `Leaves.olean`, and its axioms are exactly `propext, Classical.choice, Quot.sound` (§9). The
     new target files (`ZInQKernel.Targets.H.<ID>`) also passed a focused local build and draft
     kernel replay: all 34 are closed Props with no universe parameters, all providers absent,
     and only the three allowed axioms. This is not the full required CI audit. Neither check
     establishes fidelity to a published mathematical statement.
  3. **Reviewed mathematical statement**: `R0` (none) for all 34. No human review. AI-model
     reviews (rv-leaves-a/b, the locator audit) exist only in the PR #36 notes and do not count.
     The supporting definitions are unreviewed (API-01 … API-07).
  4. **Proved provider / integration**: `I0` (no provider) and `N0-proposed` (name proposed by the
     code child, not registered, not accepted) for all 34.
  All four statuses appear as explicit columns in the master table (§2.0).
- **Difficulty (SPECULATIVE)**: S < 1 week, M weeks, L months, XL a large multi-person project,
  XXL research-scale or decades of formalization. These are guesses, not estimates.
- **Lane**: see §7.
- `G1`-`G20` are the reference's glue steps (§3 there); A1-F4 are h-trust's steps.

## 2. Registered-target candidates (34 targets, 39 Props)

Common to every row: canonical target `ZInQ.Targets.H.<ID>` in module
`ZInQKernel.Targets.H.<ID>`; preregistered provider `ZInQ.Contrib.H.<ID>_holds` in module
`ZInQKernel.Contrib.H.<ID>`. The status of every target is stated row by row in the master table
(§2.0). The area tables below add per-Prop detail and source caveats.
`PkgI2.*` statements are universe-polymorphic in the reference; the bundle uses `.{0}`, and the
targets must be closed Props at universe 0. `T16` part (a) is closed as
`∀ (p : ℕ) [Fact p.Prime], PkgI6.LocalKroneckerWeber p` (the bundle field `t16a`).

Source caveats per area follow each table. They are taken from the notes and were not re-checked
against publications in this task-list audit.

### 2.0 Master allocation table (one row per proposed target; 34 rows)

Statuses as of this draft. Implementation: no provider exists. Statement kernel verification: the
reference Props are audited; all 34 new target files passed focused local kernel replay.
Full required CI and mathematical statement review are not supplied here.
Proved provider: none. Integration: names proposed by the code child, not registered or accepted.
The parent will update these columns after the code check.

| # | Target ID | Target / provider (proposed) | Props: reference source | Kind | Prereq IDs | Unlocks | Reuse | Difficulty (spec.) | Faithful encoding | Implementation | Statement kernel verification | Math review | Proved provider | Integration |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | **R4** | `ZInQ.Targets.H.R4` / `ZInQ.Contrib.H.R4_holds` | R4: `PkgI1.ThetaModularity` | literature | API-06 | G19; proved consumer(s) in §4 | reference `PkgI1` only (definition-only extraction) | L | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 2 | **R6** | `ZInQ.Targets.H.R6` / `ZInQ.Contrib.H.R6_holds` | R6: `PkgI2.RaynaudCriterion.{0}` | literature | API-02 | G3, G15; proved consumer(s) in §4 | PR36 `HDecomp/Objects.lean` def (text-identical) | XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 3 | **R7 (conj. of 2)** | `ZInQ.Targets.H.R7` / `ZInQ.Contrib.H.R7_holds` | R7a: `PkgI2.NeronOggShafarevich.{0}`; R7b: `PkgI2.SerreTatePotentialGood.{0}` | literature | API-02 | G3, G4, G11; proved consumer(s) in §4 | PR36 `Objects.lean` defs (text-identical); `ObjBridge.neronOggShafarevich_iff` | XL | Enc (meant as printed) | none | reference Props audited (K-def, 2 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 4 | **R9 (conj. of 2)** | `ZInQ.Targets.H.R9` / `ZInQ.Contrib.H.R9_holds` | R9a: `PkgI3.FaltingsSemisimple`; R9b: `PkgI3.FaltingsTate` | literature | API-02 | G8, G14, G17; proved consumer(s) in §4 | PR36 `Objects.lean` defs; easy inclusion proved (`PkgI3.range_tateHomZl_subset`) | XXL | Enc (meant as printed) | none | reference Props audited (K-def, 2 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 5 | **R10** | `ZInQ.Targets.H.R10` / `ZInQ.Contrib.H.R10_holds` | R10: `PkgI4.DeRhamComparison` | literature | API-02, API-03 | G9; no proved consumer | reference `PkgI4` only (over `PkgI4.I3` copy) | XXL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 6 | **R11_R12 (joint, 2 leaves)** | `ZInQ.Targets.H.R11_R12` / `ZInQ.Contrib.H.R11_R12_holds` | R11R12: `PkgI4.PanBerger` | literature (joint) | API-01, API-03 | G12; no proved consumer | reference `PkgI4.PanBerger` only; no separate Pan/Berger | XXL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 7 | **R13** | `ZInQ.Targets.H.R13` / `ZInQ.Contrib.H.R13_holds` | R13: `PkgI4.EigenformHT` | literature | API-01, API-03 | G12; no proved consumer | reference `PkgI4` only | XXL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 8 | **R14** | `ZInQ.Targets.H.R14` / `ZInQ.Contrib.H.R14_holds` | R14: `HSyn.EigenformRepExists` | literature | API-01 | G12, G14; no proved consumer | reference `HSyn`; `PkgI4.EigenformRepExists` not rfl-equal: do not register | XXL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 9 | **R15** | `ZInQ.Targets.H.R15` / `ZInQ.Contrib.H.R15_holds` | R15: `HSyn.DeligneSerreConseq` | literature | API-01 | G12; no proved consumer | reference `HSyn`; `PkgI4.DeligneSerreFinite` not rfl-equal: do not register | XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 10 | **T1** | `ZInQ.Targets.H.T1` / `ZInQ.Contrib.H.T1_holds` | T1: `PkgI2.PurityBranchLocus.{0}` | port | — | G2; no proved consumer | PR36 `Objects.lean`; Stacks formalization (unreviewed) | M–L | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 11 | **T2** | `ZInQ.Targets.H.T2` / `ZInQ.Contrib.H.T2_holds` | T2: `PkgI2.AbhyankarDVR.{0}` | port | — | G2; no proved consumer | PR36 `Objects.lean`; Stacks 0EYG (unreviewed) | M–L | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 12 | **T3** | `ZInQ.Targets.H.T3` / `ZInQ.Contrib.H.T3_holds` | T3: `PkgI2.NeronMappingAbelianScheme.{0}` | literature | API-02 | G3, G14; no proved consumer | PR36 `Objects.lean` | L–XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 13 | **T4** | `ZInQ.Targets.H.T4` / `ZInQ.Contrib.H.T4_holds` | T4: `PkgI2.ReductionTorsionBijective.{0}` | literature | API-02 | G14; no proved consumer | PR36 `Objects.lean` | XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 14 | **T5** | `ZInQ.Targets.H.T5` / `ZInQ.Contrib.H.T5_holds` | T5: `PkgI2.TorsionStructure.{0}` | literature | API-02 | G3; proved consumer(s) in §4 | PR36 `Objects.lean` | XL | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 15 | **T6** | `ZInQ.Targets.H.T6` / `ZInQ.Contrib.H.T6_holds` | T6: `PkgI3.HomFreeFinite` | literature | API-02 | G4, G8; proved consumer(s) in §4 | PR36 `Objects.lean`; `PkgI2.HomRankBound` is a proved consequence: do not register | XL | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 16 | **T7** | `ZInQ.Targets.H.T7` / `ZInQ.Contrib.H.T7_holds` | T7: `PkgI3.CharPolyIndepOfEll` | literature | API-02 | G14; proved consumer(s) in §4 | PR36 `Objects.lean`; `PkgI2.CharpolyIndependentOfEll` not rfl-equal: do not register | XL | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 17 | **T8** | `ZInQ.Targets.H.T8` / `ZInQ.Contrib.H.T8_holds` | T8: `PkgI3.PoincareReducibility` | literature | API-02 | G17; no proved consumer | PR36 `Objects.lean` | XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 18 | **T13** | `ZInQ.Targets.H.T13` / `ZInQ.Contrib.H.T13_holds` | T13: `HSyn.SkolemNoether` | port | — | G7; proved consumer(s) in §4 | `PkgI6.SkolemNoether` rfl-equal (PR36 `I6Base.lean`); Tau Ceti `skolemNoether` | S–M | Enc-D (bridge to consumed form needed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 19 | **T14 (conj. of 2)** | `ZInQ.Targets.H.T14` / `ZInQ.Contrib.H.T14_holds` | T14a: `PkgI6.BrauerHasse2`; T14b: `PkgI6.BrauerReciprocity2` | port | API-05 | G7; proved consumer(s) in §4 | PR36 `I6Base.lean`; cochain forms `…2C` not rfl-equal: do not register both | L | Enc-D (bridge to consumed form needed) | none | reference Props audited (K-def, 2 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 20 | **T15** | `ZInQ.Targets.H.T15` / `ZInQ.Contrib.H.T15_holds` | T15: `PkgI6.LocalH2Card` | port | API-05 | G7; proved consumer(s) in §4 | PR36 `I6Base.lean`; `LocalH2CardC` not rfl-equal; Tau Ceti (compatibility unknown) | L | Enc-D (bridge to consumed form needed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 21 | **T16 (conj. of 2)** | `ZInQ.Targets.H.T16` / `ZInQ.Contrib.H.T16_holds` | T16a: `PkgI6.LocalKroneckerWeber`; T16b: `PkgI6.LocalReciprocityUpper` | literature | API-04 | G7, G15; no proved consumer | PR36 `I6Base.lean` | XL | Enc (meant as printed) | none | reference Props audited (K-def, 2 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 22 | **T17** | `ZInQ.Targets.H.T17` / `ZInQ.Contrib.H.T17_holds` | T17: `HSyn.KroneckerWeber` | port | — | G12; no proved consumer | reference `HSyn` only; Tau Ceti `kroneckerWeber` | M | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 23 | **T18** | `ZInQ.Targets.H.T18` / `ZInQ.Contrib.H.T18_holds` | T18: `HSyn.FrobeniusDense` | port | API-01 | G12, G14; no proved consumer | reference `HSyn`; `PkgI6.ChebotarevExists` not rfl-equal; Tau Ceti density | M–L | Enc-D (bridge to consumed form needed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 24 | **T19** | `ZInQ.Targets.H.T19` / `ZInQ.Contrib.H.T19_holds` | T19: `HSyn.BrauerNesbitt` | literature | — | G12, G14; no proved consumer | reference `HSyn`; `PkgI6.BrauerNesbittChar0` not rfl-equal | M | Enc-D (bridge to consumed form needed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 25 | **T20** | `ZInQ.Targets.H.T20` / `ZInQ.Contrib.H.T20_holds` | T20: `GlueConductor.HilbertDifferentFormula` | port | API-04 | G15; proved consumer(s) in §4 | PR36 `Breaks.lean`; local `PkgI6` form not rfl-equal; Tau Ceti | M–L | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 26 | **T21** | `ZInQ.Targets.H.T21` / `ZInQ.Contrib.H.T21_holds` | T21: `GlueConductor.SerreDifferentBound` | literature | API-04 | G15; proved consumer(s) in §4 | PR36 `Breaks.lean`; local `PkgI6.DifferentBound` not rfl-equal | M | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 27 | **T22 (conj. of 2)** | `ZInQ.Targets.H.T22` / `ZInQ.Contrib.H.T22_holds` | T22a: `PkgI6.HerbrandQuotient`; T22b: `PkgI6.HerbrandTransitivity` | port | API-04 | G15; no proved consumer | PR36 `I6Base.lean`; Tau Ceti upper-numbering quotient | M–L | Enc (meant as printed) | none | reference Props audited (K-def, 2 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 28 | **T24** | `ZInQ.Targets.H.T24` / `ZInQ.Contrib.H.T24_holds` | T24: `HSyn.EigenformTwist` | literature | API-01 | G13; no proved consumer | reference `HSyn`; `PkgI4.EigenformTwist` rfl-equal (same target) | L | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 29 | **T25** | `ZInQ.Targets.H.T25` / `ZInQ.Contrib.H.T25_holds` | T25: `PkgI4.NewformOfEigenform` | literature | API-01 | G13; no proved consumer | reference `PkgI4` only; Tau Ceti newform bookkeeping | XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 30 | **T26** | `ZInQ.Targets.H.T26` / `ZInQ.Contrib.H.T26_holds` | T26: `PkgI3.TateModuleFree` | literature | API-02 | G8, G17; proved consumer(s) in §4 | PR36 `Objects.lean` | XL | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 31 | **T27** | `ZInQ.Targets.H.T27` / `ZInQ.Contrib.H.T27_holds` | T27: `PkgI3.QMDichotomy` | literature | API-02 | G5; no proved consumer | PR36 `Objects.lean` | XL | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 32 | **T28** | `ZInQ.Targets.H.T28` / `ZInQ.Contrib.H.T28_holds` | T28: `PkgI1.IgusaClebschSeparation` | literature | API-06 | G4; proved consumer(s) in §4 | reference `PkgI1` only | L–XL | Enc (meant as printed) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 33 | **T30** | `ZInQ.Targets.H.T30` / `ZInQ.Contrib.H.T30_holds` | T30: `GlueDescent.B2Q.LeafSqrtCrit` | literature | API-05, API-07 | G7; proved consumer(s) in §4 | PR36 `Descent/B2Glue.lean` | L | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |
| 34 | **T31** | `ZInQ.Targets.H.T31` / `ZInQ.Contrib.H.T31_holds` | T31: `GlueDescent.B2Q.LeafUnramified` | literature | API-05, API-07 | G7; proved consumer(s) in §4 | PR36 `Descent/B2Glue.lean` | M–L | Enc-C (consequence; derivation to record) | none | reference Prop audited (K-def, 1 of 39); new target file: local kernel replay PASSED; closed Prop, no provider | none (no human review) | none | proposed name; not registered, not accepted |

Row totals: 34 targets, 39 Props, 35 leaves (R11_R12 covers two leaves with one Prop; R7, R9, T14,
T16 and T22 are conjunctions of two Props). The 19 opaque leaves are not rows (§3.2).

### 2.1 Theta and invariants (2 targets, 2 Props)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **R4** | `ZInQ.Targets.H.R4` / `ZInQ.Contrib.H.R4_holds` | R4: `PkgI1.ThetaModularity` (`r4`) | Igusa: Σθ⁸, Πθ² modular of weights 4, 10 under Sp₄(ℤ) (transformation-law form) | literature | API-06 | G19 (F1): `PkgI1.thetaRatio_invariant` | only in Leaves (`PkgI1`); not in PR36 | L | Enc-C | L2 |
| **T28** | `ZInQ.Targets.H.T28` / `ZInQ.Contrib.H.T28_holds` | T28: `PkgI1.IgusaClebschSeparation` (`t28`) | Clebsch–Bolza–Igusa separation of binary sextics | literature | API-06 | G4 (A7): `PkgI1.equiv_of_lyVec` | only in Leaves (`PkgI1`) | L–XL | Enc | L2 |

- R4: Igusa, Amer. J. Math. 89 (1967) pp. 833-834, 848; 84 (1962): UNVERIFIED. The Lean form is
  the transformation law (signs and weights checked numerically by pkg-I1), **not** Igusa's
  identity. The conventions linking ψ₄, χ₁₀ to J₂..J₁₀ enter only through the proved glue
  `PkgI1.f1_algebra`.
- T28: Igusa, Ann. of Math. 72 (1960): UNVERIFIED.

### 2.2 Reduction theory and étale covers (7 targets, 8 Props)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **R6** | `ZInQ.Targets.H.R6` / `ZInQ.Contrib.H.R6_holds` | R6: `PkgI2.RaynaudCriterion.{0}` (`r6`) | Raynaud criterion, Galois form: A[m] rational, m ≥ 3 ⇒ (σ−1)² = 0 on A[ℓⁿ] | literature | API-02 | G3 (A6), G15 (D2): `PkgI2.D2_fixed_of_raynaud`; A6 (PR36 `GlueA6Alg.goodReduction_of_QM_rational3`) | PR36 `PkgI2.RaynaudCriterion` (text-identical) | XL | Enc-C | L4 |
| **R7** (conj. of 2) | `ZInQ.Targets.H.R7` / `ZInQ.Contrib.H.R7_holds` | R7a: `PkgI2.NeronOggShafarevich.{0}` (`r7a`) | Néron–Ogg–Shafarevich (finite-level, both "all m" and "infinitely many m") | literature | API-02 | G3 (A6), G4, G11: `PkgI2.inertiaTrivial_of_goodReduction`; A6 | PR36 `PkgI2.NeronOggShafarevich`; `ObjBridge.neronOggShafarevich_iff` | XL | Enc | L4 |
| ↳ | ″ | R7b: `PkgI2.SerreTatePotentialGood.{0}` (`r7b`) | Serre–Tate potential good reduction (one finite K′ for all n) | literature | API-02 | G3 only on h-b1 route (not used by the proved Raynaud-route A6) | PR36 `PkgI2.SerreTatePotentialGood` | XL | Enc | L4 |
| **T1** | `ZInQ.Targets.H.T1` / `ZInQ.Contrib.H.T1_holds` | T1: `PkgI2.PurityBranchLocus.{0}` (`t1`) | Zariski–Nagata purity, ring form | port | — | G2 (Prop. TS) | PR36 `PkgI2.PurityBranchLocus`; Stacks formalization (unreviewed) | M–L | Enc | L1 |
| **T2** | `ZInQ.Targets.H.T2` / `ZInQ.Contrib.H.T2_holds` | T2: `PkgI2.AbhyankarDVR.{0}` (`t2`) | Abhyankar's lemma, DVR form | port | — | G2 (Prop. TS) | PR36 `PkgI2.AbhyankarDVR`; Stacks 0EYG (unreviewed) | M–L | Enc | L1 |
| **T3** | `ZInQ.Targets.H.T3` / `ZInQ.Contrib.H.T3_holds` | T3: `PkgI2.NeronMappingAbelianScheme.{0}` (`t3`) | Néron mapping property, abelian-scheme case | literature | API-02 | G3 (h-b1 route), G14 | PR36 `PkgI2.NeronMappingAbelianScheme` | L–XL | Enc-C | L3 |
| **T4** | `ZInQ.Targets.H.T4` / `ZInQ.Contrib.H.T4_holds` | T4: `PkgI2.ReductionTorsionBijective.{0}` (`t4`) | Reduction of prime-to-p torsion is bijective | literature | API-02 | G14 | PR36 `PkgI2.ReductionTorsionBijective` | XL | Enc-C | L3 |
| **T5** | `ZInQ.Targets.H.T5` / `ZInQ.Contrib.H.T5_holds` | T5: `PkgI2.TorsionStructure.{0}` (`t5`) | A(K̄)[n] ≅ (ℤ/n)^{2g}, n invertible | literature | API-02 | G3 (A6, with R6, R7a): PR36 `GlueA6Alg.goodReduction_of_QM_rational3` | PR36 `PkgI2.TorsionStructure` | XL | Enc | L3 |

- R6: SGA 7 I, Exp. IX, Prop. 4.7 with Prop. 3.5; Silverberg–Zarhin Thm 3.5 (read by a model).
  Galois consequence. The PR #36 locator audit could not confirm that the printed bound includes
  `m = 3`, which is the case A6 uses.
- R7: Serre–Tate, Ann. of Math. 88 (1968), Thms 1, 2: UNVERIFIED. These are finite-level forms. In
  (b) the Lean form fixes one finite `K′` before `n` (one common open subgroup), as the audit requires.
- T1, T2: SGA 1 X 3.4, 3.6 (UNVERIFIED). The Stacks and Tau Ceti formalizations named in the
  reference are unreviewed and need a statement-compatibility proof.
- T3, T4: BLR §1.2 Prop. 8; Serre–Tate §1. Consequence forms (pkg-I2 derivations to be recorded).
- R7(b) and T3 are used only by h-b1's route for A6. The proved A6 (Raynaud route) uses R6, R7(a)
  and T5. They stay targets because the reference counts them, but they are low priority.

### 2.3 Abelian varieties: Faltings and Mumford (6 targets, 7 Props)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **R9** (conj. of 2) | `ZInQ.Targets.H.R9` / `ZInQ.Contrib.H.R9_holds` | R9a: `PkgI3.FaltingsSemisimple` (`r9a`) | Faltings: V_ℓ(A) semisimple | literature | API-02 | G8 (C2), G14, G17 (E1); no proved consumer in Leaves | PR36 `PkgI3.FaltingsSemisimple` | XXL | Enc | L4 |
| ↳ | ″ | R9b: `PkgI3.FaltingsTate` (`r9b`) | Faltings: Hom ⊗ ℤ_ℓ ≅ equivariant Hom(T_ℓA, T_ℓB) (injective, image = equivariant) | literature | API-02 | G8, G17: `PkgI3.exists_hom_ne_zero_of_equivariant`, `PkgI3.finrank_equivEnd` | PR36 `PkgI3.FaltingsTate`; easy inclusion proved `PkgI3.range_tateHomZl_subset` | XXL | Enc | L4 |
| **T6** | `ZInQ.Targets.H.T6` / `ZInQ.Contrib.H.T6_holds` | T6: `PkgI3.HomFreeFinite` (`t6`) | Hom(A,B) free finite, injective into Hom(T_ℓA, T_ℓB) | literature | API-02 | G4 (A8), G8: `PkgI3.finrank_equivEnd`; PR36 `ObjBridge.pkgI2_homRankBound_of_pkgI3_homFreeFinite` | PR36 `PkgI3.HomFreeFinite`; `PkgI2.HomRankBound` is a CONSEQUENCE (proved in PR36), do not register | XL | Enc | L3 |
| **T7** | `ZInQ.Targets.H.T7` / `ZInQ.Contrib.H.T7_holds` | T7: `PkgI3.CharPolyIndepOfEll` (`t7`) | Char. polynomials integral, independent of ℓ | literature | API-02 | G14 (C10): PR36 `PkgI3.trace_indep_of_ell` | PR36 `PkgI3.CharPolyIndepOfEll`; `PkgI2.CharpolyIndependentOfEll` NOT rfl-equal (do not register) | XL | Enc | L3 |
| **T8** | `ZInQ.Targets.H.T8` / `ZInQ.Contrib.H.T8_holds` | T8: `PkgI3.PoincareReducibility` (`t8`) | Poincaré reducibility (form used at E1) | literature | API-02 | G17 (E1 assembly) | PR36 `PkgI3.PoincareReducibility` | XL | Enc-C | L3 |
| **T26** | `ZInQ.Targets.H.T26` / `ZInQ.Contrib.H.T26_holds` | T26: `PkgI3.TateModuleFree` (`t26`) | T_ℓ(A) free of rank 2 dim A | literature | API-02 | G8, G17: `PkgI3.exists_hom_ne_zero_of_equivariant`, `PkgI3.finrank_equivEnd` | PR36 `PkgI3.TateModuleFree` | XL | Enc | L3 |
| **T27** | `ZInQ.Targets.H.T27` / `ZInQ.Contrib.H.T27_holds` | T27: `PkgI3.QMDichotomy` (`t27`) | QM dichotomy for abelian surfaces | literature | API-02 | G5 | PR36 `PkgI3.QMDichotomy` | XL | Enc-C | L3 |

- R9: Faltings, Invent. Math. 73 (1983), Satz 3, Satz 4 (read by a model; the original was not
  opened by the PR #36 audit, only the erratum). Keep the **integral** form `Hom ⊗ ℤ_ℓ`.
- T8: the form used is over any `k` of characteristic 0 (Milne 1986 Prop. 12.1, per rv-leaves-b;
  Mumford §19 is over `k̄`).
- T27: there is no single locator in the reference. The PR #36 audit names Chia-Fu Yu, J. Pure
  Appl. Algebra (2013), Thm 1.1, with "indefinite" kept.
- Every abelian-variety target quantifies over `PkgI2.IsAbelianVariety` / `PkgI3.AbVar`. The
  reference's statement "Mathlib cannot construct a nonzero abelian variety" (pkg-I3 §7) is about
  Mathlib alone and is out of date as a project-wide obstacle. The verified opt-in bridge
  (`scratch/axiom-bridge/`, local branch `wip/axiom-bridge`; all 9 theorems audited at the three
  standard axioms) proves `AxiomBridge.exists_pkgI2_jacobian`: a curve with a rational degree-one
  divisor has a PkgI2 Jacobian of dimension equal to its genus. It also proves
  `AxiomBridge.jacobian_isAbelianVariety` and `AxiomBridge.abelianVariety_iff` (equivalence with
  Mordell's `AlgebraicGeometry.IsAbelianVariety`). So a nonzero PkgI2 abelian variety follows,
  conditionally, from any positive-genus instance. **Do not assign rebuilding this bridge.** What
  remains is the `PkgI3`/`PkgI4.I3` side (via PR #36 `ObjBridge`) and a concrete positive-genus
  instance. The bridge is not in PR #36 and needs the Mordell/Stacks dependency builds.

### 2.4 p-adic Hodge theory (3 targets, 3 Props; covers 4 leaves)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **R10** | `ZInQ.Targets.H.R10` / `ZInQ.Contrib.H.R10_holds` | R10: `PkgI4.DeRhamComparison` (`r10`) | de Rham comparison: V_p(A) de Rham, HT weights 0, −1 each mult. g | literature | API-02, API-03 | G9 (C3, appendix lemma) | only in Leaves (`PkgI4`, over `PkgI4.I3` copy of AbVar) | XXL | Enc-C | L4 |
| **R11_R12** (joint: 2 leaves, 1 Prop) | `ZInQ.Targets.H.R11_R12` / `ZInQ.Contrib.H.R11_R12_holds` | R11R12: `PkgI4.PanBerger` (`r11r12`) | JOINT Pan∘Berger (p ≥ 5): irreducible, finitely ramified, de Rham at p, odd, distinct HT ⇒ eigenform up to twist (trace form) | literature (joint) | API-01, API-03 | G12 (C7) | only in Leaves (`PkgI4.PanBerger` = `PanFor` at `LocalIsDeRham`) | XXL | Enc-C | L4 |
| **R13** | `ZInQ.Targets.H.R13` / `ZInQ.Contrib.H.R13_holds` | R13: `PkgI4.EigenformHT` (`r13`) | HT weights {0, 1−k} of eigenform reps, every level, k ≥ 2 | literature | API-01, API-03 | G12 (C8) | only in Leaves (`PkgI4`) | XXL | Enc-C | L4 |

- R10: Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, Thms 9.1, 9.3 + corrigendum. The Tate-module
  form is a consequence with T10 (an opaque leaf), so that derivation is part of the caveat.
- R11_R12: Pan, JAMS 35 (2022), Thm 1.0.4 (arXiv v2 statement VERIFIED by h-a011; JAMS numbering
  UNVERIFIED) and Berger, Invent. Math. 148 (2002), Thm 0.7 (arXiv v3 Thm 0.6). The Lean form is
  restricted to `p ≥ 5` (no `p = 3` residual clause; C7 uses `p = 5`). The conclusion is in trace
  form, a consequence under every reading (reference §6 R2). The PR #36 audit adds that Pan uses
  geometric Frobenius, so the arithmetic trace form needs dualization and a twist adjustment.
- R13: Saito 1997 / Kato 2004 §9.4 / Faltings 1987. The PR #36 audit names Kato as the all-level
  supplier. Mind the normalization (Tate weights `{0, 1−k}`).

### 2.5 Modular forms (4 targets, 4 Props)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **R14** | `ZInQ.Targets.H.R14` / `ZInQ.Contrib.H.R14_holds` | R14: `HSyn.EigenformRepExists` (`r14`) | Galois reps of normalized cuspidal eigenforms, weight ≥ 1 (semisimple, attached) | literature | API-01 | G12 (C8), G14 (C10) | only in Leaves; duplicate `PkgI4.EigenformRepExists` (NOT rfl-equal) | XXL | Enc-C | L4 |
| **R15** | `ZInQ.Targets.H.R15` / `ZInQ.Contrib.H.R15_holds` | R15: `HSyn.DeligneSerreConseq` (`r15`) | Deligne–Serre: semisimple attached rep of weight-1 eigenform has finite image | literature | API-01 | G12 (C8) | only in Leaves; duplicate `PkgI4.DeligneSerreFinite` (NOT rfl-equal) | XL | Enc-C | L4 |
| **T24** | `ZInQ.Targets.H.T24` / `ZInQ.Contrib.H.T24_holds` | T24: `HSyn.EigenformTwist` (`t24`) | Twist of a normalized eigenform by a Dirichlet character | literature | API-01 | G13 | only in Leaves; `PkgI4.EigenformTwist` IS rfl-equal (same target) | L | Enc-C | L2 |
| **T25** | `ZInQ.Targets.H.T25` / `ZInQ.Contrib.H.T25_holds` | T25: `PkgI4.NewformOfEigenform` (`t25`) | Eigensystem of an eigenform is that of a newform of level dividing it | literature | API-01 | G13; R15 transfer (PR36 note) | only in Leaves (`PkgI4`); Tau Ceti newform bookkeeping | XL | Enc-C | L3 |

- R14: Shimura 1971 Thm 7.14; Deligne, Sém. Bourbaki 355; Deligne–Serre 1974. The Lean form is
  over Mathlib `CuspForm` on Γ₁(N) (so Eisenstein series are excluded). It is a consequence: it
  needs eigen-isotypic extraction, semisimplification and an explicit Frobenius convention.
- R15: Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1, with T18, T19 (and possibly T25) for "every
  semisimple ρ with these traces". Semisimplicity cannot be dropped.
- T24: Shimura 1971 Prop. 3.64; Atkin–Li 1978. T25: Li 1975 Thm 5; Miyake 4.6.19. Consequences
  ("newform through the old space").
- `IsNormalizedEigenform` is defined through the coefficient recursion. Its equivalence with the
  Hecke definition is unproved (WP1 sanity lemma).

### 2.6 Arithmetic of ℚ and Galois cohomology (9 targets, 11 Props)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **T13** | `ZInQ.Targets.H.T13` / `ZInQ.Contrib.H.T13_holds` | T13: `HSyn.SkolemNoether` (`t13`) | Skolem–Noether | port | — | G7 (B1) via `PkgI6.skolemNoether_aut` → `GlueDescent.LeafSkolemNoether` (bridge not proved) | `PkgI6.SkolemNoether` is rfl-equal (same target); PR36 `PkgI6.SkolemNoether`; Tau Ceti `skolemNoether` | S–M | Enc-D | L1 |
| **T14** (conj. of 2) | `ZInQ.Targets.H.T14` / `ZInQ.Contrib.H.T14_holds` | T14a: `PkgI6.BrauerHasse2` (`t14a`) | Hasse principle: H²(G_ℚ, ℤ/2) → ∏_v H²(G_ℚv, ℤ/2) injective | port | API-05 | G7 (B2): `PkgI6.eq_of_same_finite_support`; bridge to `GlueDescent.B2Q.LeafHasse` open (WP3) | PR36 `PkgI6.BrauerHasse2`; cochain form `PkgI6.BrauerHasse2C` NOT rfl-equal | L | Enc-D | L3 |
| ↳ | ″ | T14b: `PkgI6.BrauerReciprocity2` (`t14b`) | Reciprocity: finite even support for H²(G_ℚ, ℤ/2) | port | API-05 | G7 (B2): `PkgI6.eq_of_same_finite_support` | PR36 `PkgI6.BrauerReciprocity2`; cochain form `BrauerReciprocity2C` | L | Enc-D | L3 |
| **T15** | `ZInQ.Targets.H.T15` / `ZInQ.Contrib.H.T15_holds` | T15: `PkgI6.LocalH2Card` (`t15`) | Local H²(G_ℚv, ℤ/2) ≅ ℤ/2 | port | API-05 | G7 (B2): `PkgI6.eq_of_same_finite_support`; bridge to `LeafLocalTwo` open | PR36 `PkgI6.LocalH2Card`; cochain form `LocalH2CardC` NOT rfl-equal; Tau Ceti `h2MuEquivZMod` (compatibility unknown) | L | Enc-D | L3 |
| **T16** (conj. of 2) | `ZInQ.Targets.H.T16` / `ZInQ.Contrib.H.T16_holds` | T16a: `PkgI6.LocalKroneckerWeber` (`t16a`) | Local Kronecker–Weber for ℚ_p (closed form: ∀ p [Fact p.Prime], …) | literature | API-04 | G7 (B2 local, pkg-I6 route SPECULATIVE) | PR36 `PkgI6.LocalKroneckerWeber` (parametric in p) | L–XL | Enc | L3 |
| ↳ | ″ | T16b: `PkgI6.LocalReciprocityUpper` (`t16b`) | Local reciprocity at finite abelian level with upper numbering | literature | API-04 | G7 (B2), G15 | PR36 `PkgI6.LocalReciprocityUpper` | XL | Enc | L3 |
| **T17** | `ZInQ.Targets.H.T17` / `ZInQ.Contrib.H.T17_holds` | T17: `HSyn.KroneckerWeber` (`t17`) | Kronecker–Weber | port | — | G12 (twist is Dirichlet) | only in Leaves (`HSyn`); Tau Ceti `kroneckerWeber` | M | Enc | L1 |
| **T18** | `ZInQ.Targets.H.T18` / `ZInQ.Contrib.H.T18_holds` | T18: `HSyn.FrobeniusDense` (`t18`) | Chebotarev: Frobenius elements dense in G_ℚ | port | API-01 | G12–G14; C10 consumes `ChebotarevExists` (bridge open) | only in Leaves (`HSyn`); finite form `PkgI6.ChebotarevExists` NOT rfl-equal; Tau Ceti density | M–L | Enc-D | L1 |
| **T19** | `ZInQ.Targets.H.T19` / `ZInQ.Contrib.H.T19_holds` | T19: `HSyn.BrauerNesbitt` (`t19`) | Brauer–Nesbitt, char 0, trace form | literature | — | G12–G14; C10 consumes `BrauerNesbittChar0` (bridge open) | only in Leaves (`HSyn`); `PkgI6.BrauerNesbittChar0` NOT rfl-equal | M | Enc-D | L2 |
| **T30** | `ZInQ.Targets.H.T30` / `ZInQ.Contrib.H.T30_holds` | T30: `GlueDescent.B2Q.LeafSqrtCrit` (`t30`) | Local square-root criterion for χ restricted to G_ℚp | literature | API-05, API-07 | G7 (B2–B3): `GlueDescent.B2Q.b2_of_leaves`, `GlueDescent.B3Q.b3_degree_le_QM` | PR36 `GlueDescent.B2Q.LeafSqrtCrit` | L | Enc-C | L2 |
| **T31** | `ZInQ.Targets.H.T31` / `ZInQ.Contrib.H.T31_holds` | T31: `GlueDescent.B2Q.LeafUnramified` (`t31`) | Unramified classes of H²(G_ℚp, ±1) vanish | literature | API-05, API-07 | G7 (B2–B3): `b2_of_leaves`, `b3_degree_le_QM` | PR36 `GlueDescent.B2Q.LeafUnramified` | M–L | Enc-C | L2 |

- T14, T15: the bundle forms are over Mathlib `continuousCohomology`. The B2-B3 glue consumes the
  cochain forms `LeafHasse`, `LeafLocalTwo`, and the derivation is unproved (WP3). The pkg-I6
  cochain forms `BrauerHasse2C` etc. are **not** rfl-equal to the bundle forms (§9). Decide once,
  at statement review, which form is locked. Do not register both.
- T13 (`HSyn.SkolemNoether`) is rfl-equal to `PkgI6.SkolemNoether` (§9): one target.
- T30, T31: these are consequences of local class field theory and of `cd ℤ̂ = 1`. They are stated
  directly in glue-descent's form, which is the form B2-B3 consumes.
- T16(a) on the pkg-I6 route is SPECULATIVE until written (reference §6).

### 2.7 Ramification (3 targets, 4 Props)

| Target ID | Locked target / provider (proposed) | Prop part: Leaves.lean source (bundle field) | Leaf (form used) | Kind | Prereqs | Unlocks (glue step: consumer) | Reuse / do-not-duplicate | Diff. (spec.) | Encoding | Lane |
|---|---|---|---|---|---|---|---|---|---|---|
| **T20** | `ZInQ.Targets.H.T20` / `ZInQ.Contrib.H.T20_holds` | T20: `GlueConductor.HilbertDifferentFormula` (`t20`) | Hilbert's different formula (global form) | port | API-04 | G15 (D1): `GlueConductor.D1_genuine`; PR36 `GlueD1Local.D1_krasner'` | PR36 `GlueConductor.HilbertDifferentFormula`; local `PkgI6.HilbertDifferentFormula` NOT rfl-equal | M–L | Enc-C | L1 |
| **T21** | `ZInQ.Targets.H.T21` / `ZInQ.Contrib.H.T21_holds` | T21: `GlueConductor.SerreDifferentBound` (`t21`) | Different bound v(𝔇) ≤ e − 1 + v(e) (global form) | literature | API-04 | G15 (D1): `GlueConductor.D1_genuine` | PR36 `GlueConductor.SerreDifferentBound`; local `PkgI6.DifferentBound` NOT rfl-equal | M | Enc-C | L2 |
| **T22** (conj. of 2) | `ZInQ.Targets.H.T22` / `ZInQ.Contrib.H.T22_holds` | T22a: `PkgI6.HerbrandQuotient` (`t22a`) | Herbrand: (G/H)^v = G^vH/H | port | API-04 | G15 (D3/D4) | PR36 `PkgI6.HerbrandQuotient`; Tau Ceti `map_restrictNormalHom_upperRamificationGroup` | M–L | Enc | L1 |
| ↳ | ″ | T22b: `PkgI6.HerbrandTransitivity` (`t22b`) | Transitivity of Herbrand φ | port | API-04 | G15 | PR36 `PkgI6.HerbrandTransitivity` | M–L | Enc | L1 |

- T20, T21 are global forms. They need a cited localization of the different and of `G_i`
  (Serre III §4, I §7; rv-leaves-b). The local pkg-I6 forms are not rfl-equal. Register only the
  global ones, which `D1_genuine` consumes.

## 3. Definition/API projects (NOT registered targets)

### 3.1 Layer reviews and unifications (prerequisites named in §2)

| ID | Project | Current declarations | Why it gates targets | Lane |
|---|---|---|---|---|
| API-01 | Review the Galois-representation and eigenform layer; merge the `HSyn` and `PkgI4` copies | `HSyn.GaloisRep`, `FrobTrace`, `IsArithFrob`, `AttachedTo`, `IsOdd`, `IsIrreducible`, `IsSemisimple`, `CF`, `IsNormalizedEigenform`; `PkgI4.*` duplicates, `PkgI4.IsNewform`, `AttachedUpToTwist` | `FrobTrace` is meaningful only at unramified primes; check the eigenform recursion against the Hecke definition; `HSyn` and `PkgI4` forms of R14 and R15 are not rfl-equal (§9) | L0 |
| API-02 | Review and unify the abelian-variety layer: `PkgI2.IsAbelianVariety` on `Grp (Over (Spec K))`, `PkgI3.AbVar`, the renamed copy `PkgI4.I3`; non-vacuity | PR #36 `ZInQKernel/HDecomp/Objects.lean` (`ObjBridge.*`, bijection and `*_iff` restatements, proved) | a wrong or empty definition makes a leaf vacuous; R10 is stated over the `PkgI4.I3` copy, so it needs the bridge. Non-vacuity for the PkgI2 layer is supported, conditionally, by the already verified `AxiomBridge.exists_pkgI2_jacobian` (positive genus ⇒ nonzero; opt-in, not in PR #36; reuse it, do not rebuild it) | L0 |
| API-03 | Review the p-adic Hodge layer | `PkgI4.IsDeRham`, `LocalIsDeRham`, `IsDeRhamOver`, `HasHTWeights`, `htMultOver`; sanity `PkgI4.isDeRham_trivial`, `htMult_cycRep_eq_zero` | non-vacuity of `B_dR` action and HT multiplicities (`ℚ_p(1)` weight −1) | L0 |
| API-04 | Review the local-field and ramification layer | `PkgI6.lowerRam`, `upperRam`, `artinConductor`; `GlueConductor.ramGroup`, `phi`; Mathlib `differentIdeal` | T16, T20-T22 | L0 |
| API-05 | Review the Galois-cohomology layer | `PkgI6.Z2`, `locP`, Mathlib `continuousCohomology`; cochain forms `IsCocycle2`, `IsCoboundary2` | Mathlib has no comparison of `continuousCohomology` with inhomogeneous cochains (rv-leaves-b) | L0 |
| API-06 | Review the theta and Igusa layer | `PkgI1.thetaConst`, `SiegelH2`, `spAct`, `J2`..`J10` | period matrix and characteristic conventions were checked numerically only | L0 |
| API-07 | Review the descent character layer | `GlueDescent.B2Q.GQ`, `galChar`, `UnramifiedAt`, `InflatedFrom` | T30, T31 | L0 |

### 3.2 The 19 opaque leaves (`HSyn.*` placeholders: `opaque … : Prop`, no content)

A placeholder must never be registered or offered as a target. Any theorem that has one as a
hypothesis says nothing until the placeholder is replaced.

| ID | Leaf | Reference placeholder | Missing definitions (tier, reference §4) | Notes | Blocks glue |
|---|---|---|---|---|---|
| D-R1 | Shimura–Deligne, level-3 QM curve | `HSyn.R01_ShimuraDeligne` | QM PEL moduli, canonical model, CM points (very large) | must also **produce** the surface `A` as a Lean object; PR #36 audit: a qualified consequence | G1-G6, G19 |
| D-R2 | Baba–Granath | `HSyn.R02_BabaGranath` | via D-R1 (very large) | **statement corrected in PR #36 note**: ramification index 2 at each branch value; 4, 6, 2 are orbifold orders. The reference docstring is outdated | G2, G4 (A2, A5, A7) |
| D-R3 | Lin–Yang | `HSyn.R03_LinYang` | QM locus (very large) | locator corrected to arXiv v1 **Example 29** (not 30) | G4, G19 |
| D-R5 | González–Rotger | `HSyn.R05_GonzalezRotger` | via D-R1 (very large) | **count corrected**: `2^{#{p∣D(R)N(R)}}·h(R)`, not `h(R)`; its use in NoCM is under separate review | G6 |
| D-R8 | Grothendieck semistable reduction | `HSyn.R08_SemistableReduction` | Néron models (large) | the Galois consequence `PkgI2.GrothendieckMonodromy` is a genuine def in the reference (not in the bundle; also in PR #36 `Objects.lean`). No proved step needs R8. Promoting it is a statement decision | G3 (h-b1 route only) |
| D-R16 | Eichler–Shimura in J₁(N) | `HSyn.R16_EichlerShimuraJ1` | X₁(N), J₁(N) over ℚ (very large) | must produce `J₁(N)`; realization bridge incompletely sourced (PR #36 audit) | G13, G14, G17 |
| D-R17 | Carayol | `HSyn.R17_Carayol` | ℓ-adic conductor at infinite level (medium) | templates `PkgI4.CarayolFor`, unramified case `PkgI4.CarayolUnramified` (genuine, not a leaf). D5 needs `p ∣ N`. def-ladic-cond (PR #36 note) is in neither checkout | G15-G16 |
| D-R18 | Javanpeykar | `HSyn.R18_Javanpeykar` | stable Faltings height, J₁(N), Belyi (very large) | | G18 |
| D-R19 | Gaudron–Rémond | `HSyn.R19_GaudronRemond` | Faltings height (very large) | | G18 |
| D-R20 | Faltings height lemma | `HSyn.R20_FaltingsHeightLemma` | Faltings height | | G18 |
| D-R21 | Bost | `HSyn.R21_Bost` | Faltings height | Bost's constant UNVERIFIED from Bost | G18 |
| D-R22 | Pazuki | `HSyn.R22_Pazuki` | Faltings height, theta height | Deligne-metric shift: the reference glue uses `hA + log π`; the PR #36 note hardens it to `h_F + 3` | G19 |
| D-T9 | Weil pairing | `HSyn.T09_WeilPairing` | polarizations (medium) | leaf-push form exists only in a revision not in either checkout | G12 |
| D-T10 | `V_ℓ ≅ H¹_et^∨` | `HSyn.T10_TateDuality` | ℓ-adic étale cohomology (large) | | G9 (R10's Tate-module form) |
| D-T11 | Riemann/GAGA | `HSyn.T11_RiemannGAGA` | analytification (large) | | G10 |
| D-T12 | Artin comparison | `HSyn.T12_ArtinComparison` | as D-T11 | | G10 |
| D-T23 | Fontaine closure | `HSyn.T23_FontaineClosure` | `B_dR` filtration, closure (medium/large) | leaf-push form absent from both checkouts | G9 |
| D-T29 | Local quaternion normalizers | `HSyn.T29_LocalNormalizers` | cheap | glue-vigneras (PR #36 note) proves N5's case; absent from both checkouts | G1 (A3) |
| D-T32 | Tame quadratic characters | `HSyn.T32_TameQuadratic` | inertia subgroups of G_ℚ (cheap) | glue-b3-unram forms and a new leaf `LeafConj` absent from both checkouts | G7 (L′ unramified) |

Further new-object projects (reference §4): API-08 the **actual** objects the glue needs, namely
the QM surface `A` (from D-R1) and `J₁(N)` (from D-R16). This is not "some nonzero abelian
variety": that is conditionally available through the verified axiom bridge (§2.3 note). The
`PkgI3` transfer of the bridge's Jacobians and a positive-genus instance are open; API-09 Weil restriction (G4, route K); API-10 `B_st` (**not needed**:
`R11_R12` avoids it, so do not start it for H).

## 4. Already proved conditional glue (do not redo)

"Proved" below means a sorry-free Lean theorem with axioms `propext, Classical.choice,
Quot.sound`, **with its stated hypotheses**. No row proves a whole glue step G1-G20 unless it says
so. The "Assumes" column lists the leaf Props taken as explicit hypotheses. Other hypotheses
(numerical inputs, properties of the actual `A`) are summarized. Rows marked **R** were audited
here by `#check` and `#print axioms` against the reference `Leaves.olean`. Rows marked **P** exist
in PR #36 `ZInQKernel/HDecomp/` and are listed in its `scripts/print_axioms.lean`. Their check is
recorded by hdec-adopt (179 axiom lists) and was not re-run here.

| Step | Lean name(s) | Src | Component proved | Assumes (explicit) | Still open in this step |
|---|---|---|---|---|---|
| G18-G20 | `HSyn.sixContactMin_of_glueOutputs`; `GlueAssembly.sixContactMinAt_of_glueOutputs`, `jHeightBound_of_glueOutputs` | R, P | `GlueOutputs Mult.S_mul → ZInQ.SixContactMin` | `GlueAssembly.GlueOutputs` (a numerical contract, **not a leaf**, never a target) | producing `GlueOutputs` = G0's `sorry` |
| G20 | `ZInQ.JHeight.sixContactMin_of_jHeightBound`; `HSyn.jHeightBound_copy_iff` (Iff.rfl) | repo, R | `JHeightBound → SixContactMin` | — | — (fully proved) |
| G18 | `GlueAssembly.transfer_of_level`, `GlueAssembly.index_Gamma1_le` | R | the arithmetic `h_F(A) ≤ Q¹⁷M²⁴` from the real-number inequalities; `[SL₂(ℤ):Γ₁(N)] ≤ N²` | inequalities as real hypotheses | supplying them from R18-R21 on actual varieties |
| G19 | `GlueAssembly.logHeight_Phi_le`, `GlueAssembly.pazuki_numerics`, `PkgI1.f1_algebra`, `PkgI1.thetaRatio_invariant` | R, P (first) | F2 on Mathlib Weil heights; F3 numerics; F1 algebra; theta-ratio invariance | `thetaRatio_invariant`: R4 (`PkgI1.ThetaModularity`); `pazuki_numerics`: Pazuki's bound with `hA + log π` | that the theta point of the actual `A` satisfies F1 (needs D-R1-D-R3, R4) |
| G16 | `GlueConductor.level_le` | R, P | `N ≤ heightQ R · contactSupport²` | exponent bounds as hypotheses | the exponents (G15, D-R17) |
| G15 (D1) | `GlueConductor.D1_genuine`; `GlueD1Local.D1_local'`, `D1_krasner'`; `PkgI6.ramificationIdx_le_factorial` | R; P | `φ(b) ≤ 4a²` (global, and local via the decomposition group) | T20, T21 (+ `e ≤ a!` or local degree hypotheses) | Krasner / `D_P ≅ Gal(L_P/ℚ_p)` transport (STANDARD, not in Lean) |
| G15 (D2-D4) | `PkgI2.D2_fixed_of_raynaud`, `GlueConductor.upper_break_le`, `swan_le`, `artin_le`, `fourth_pow_mem`, `exists_sq_eq_one_add`, `HSyn.sq_principalUnits_proved` | R, P | wild inertia fixed (from R6), break/Swan/Artin arithmetic, `(U^{e+1})⁴ ⊆ U^{3e+1}`, square roots of principal units | `D2_fixed_of_raynaud`: R6 | assembly at infinite level (ℓ-adic conductors, D-R17); instantiation on `r_ℓ` |
| G15 (D4) | `PkgI6.artinConductor_le_of_upper` | **P only** | `f(V) ≤ dim V·(1+U)` | — | **in the reference it is `sorryAx`** (audited); proved only in PR #36 `Conductor/ArtinUpper.lean` |
| G15 (D3) | `PkgI6.sq_principalUnits` | **P only** | square roots in principal units | — | **`sorryAx` in the reference**; there use `HSyn.sq_principalUnits_proved` (same statement, R) |
| G7 (B2-B3) | `GlueDescent.B2Q.b2_of_leaves`, `GlueDescent.B3Q.b3_of_leaves`, `GlueDescent.B3Q.b3_degree_le_QM`, `GlueDescent.exists_chi` | R, P | χ, β with `β² = χ`, `∂β = ε`, `L′` Galois, `[L′:ℚ] ≤ Q·M` | `LeafHasse`, `LeafLocalTwo` (cochain forms of T14, T15), T30, T31; ε a sign cocycle inflated from `L` | T14/T15 → `LeafHasse`/`LeafLocalTwo` bridge (WP3); `L′` unramified (D-T32); instantiation on `A` |
| G7 (B2 Brauer) | `PkgI6.eq_of_same_finite_support` / `cob_of_same_finite_support` | R, P | classes with the same finite support are equal | T14a, T14b, T15 (bundle forms) / their cochain forms | as above |
| G7 (B1) | `GlueDescent.cocycle_of_projective`, `sign_normalization`, `B6_inner`, `B6_isSimpleRing`; `PkgI6.skolemNoether_aut` | R, P | cocycle, sign normalization, `B` central simple, automorphisms inner | `B6_inner`: `GlueDescent.LeafSkolemNoether`; `skolemNoether_aut`: `PkgI6.SkolemNoether` (= T13) | `LeafSkolemNoether` from T13 (small bridge, not rfl, §9) |
| G7 caution | `GlueDescent.twist_kills_inertia` | R | proved, but **do not build on it** | — | the PR #36 note says its hypothesis is undischargeable (corrected in glue-b3-unram, absent here) |
| G8 (C1, C2 part) | `GlueDescent.rho_map_mul`, `GlueDescent.MatrixUnits2.splitEquiv_intertwines`; `PkgI3.finrank_equivEnd` | R, P | `ρ ≅ r ⊕ r` by matrix units; `finrank` of equivariant endomorphisms | `finrank_equivEnd`: R9b, T26, T6 | C2 absolute irreducibility (glue-I3-linalg, `SemisimpleBaseChange`: in neither checkout); instantiation |
| G11 | `PkgI2.inertiaTrivial_of_goodReduction` | R, P | inertia acts trivially at good reduction | R7a | instantiation (G3) |
| G3 (A6) | `GlueA6Alg.goodReduction_of_QM_rational3`, `goodReduction_of_QM_rational3'`, `quatUnipotentTrivial` | **P only** | good reduction away from 3 | R7a, R6, T5 + QM data on `A` (dim 2, `I`, `J` relations, `A[3]` rational, 3 a unit) | **reference `PkgI2.goodReduction_of_QM_rational3` is `sorryAx`** (audited); producing `A` (D-R1) and its conjugates |
| G3 aux | `GlueRepo.TorsionFree.padic_subgroup_trivial`, `card_le_three_pow` | R, P | `1 + 3M_r(ℤ₃)` torsion-free | — | — |
| G12 | `HSyn.weight_match`, `GlueAssembly.weight_match`, `weight_match_coh`, `PkgI4.weight_match(_coh)`, `GlueAssembly.twist_finite` | R | weight arithmetic (both normalizations); determinant argument | — | the C7/C8 assembly with R11_R12, R13-R15, T9, T17-T19 |
| G14 (C10) | `GlueC10.c10`, `GlueC10.iso_three_of_five`, `GlueC10.frobLift`, `PkgI3.trace_indep_of_ell` | **P only** | `r₃ ≅ ρ_{f,3}` from the 5-adic identification and trace data | `ChebotarevExists`, `BrauerNesbittChar0` (not the bundle T18/T19 forms), trace identities and semisimplicity as hypotheses; `trace_indep_of_ell`: T7 | supplying the trace identities (T3, T4, D-R16, C2): none statable today |
| G17 (E1 part) | `PkgI3.exists_hom_ne_zero_of_equivariant`, `GlueAssembly.invariants_ne_bot_of_baseChange` | R, P (first via `ObjBridge.exists_hom_ne_one_of_equivariant`) | nonzero equivariant map ⇒ nonzero homomorphism | R9b, T26 | assembly with T8; the `J₁(N)` object (D-R16) |
| G1 | `GlueRepo.A1.*` (e.g. `card_units_mod3` = 72, `trd_mul_ros_pos`, `det_gram_E`), `PkgI1.gram_det` | R, P | order of discriminant 6, Gram det 1, Rosati positivity, `#(𝒪/3𝒪)^* = 72` | — | the quotient `Y₃ → P¹_j` (D-R1); normalizer index (D-T29) |
| G2 | `GlueRepo.PR.inertia_orders_eq_one_iff`, `PkgI1.G6_sub_F2`, `PkgI1.Ju_ne_branch`, `GlueRepo.Numerics.splitting_degree_le` | R, P | valuation case analysis of Lemma PR(i), `[K:ℚ] ≤ 324!` | — | Prop. TS (from T1, T2), Lemma NV |
| G4 | `PkgI1.equiv_of_lyVec`, `GlueRepo.Numerics.a8_degree`, `a8_field`; `ObjBridge.pkgI2_homRankBound_of_pkgI3_homFreeFinite` | R; P | A7's algebraic step; Minkowski bound arithmetic; I2-Rank from T6 | `equiv_of_lyVec`: T28; the last: T6 | Weil restriction (API-09), the Hom field |
| G6 | `PkgI1.elkies_t`, `GlueRepo.PR.fibre_free` | R, P | Elkies identities; free `W`-orbit, complex conjugation as `w₃` | — | the count with D-R5 (corrected count, separate review) |
| G0 | `HSyn.sixContactMin_of_leaves` | R | **not proved**: `sorryAx` through `HSyn.glueOutputs_of_leaves` | `ResearchLeaves`, `TextbookLeaves` (19 fields are placeholders) | everything in §5 |

## 5. Glue backlog (projects, not literature targets; Lane L6)

| ID | Work | Inputs | Notes |
|---|---|---|---|
| GLUE-01 | T14a/b, T15 (bundle) ⇒ `GlueDescent.B2Q.LeafHasse`, `LeafLocalTwo` | API-05 | WP3; needs the cohomology-cochain comparison |
| GLUE-02 | T13 ⇒ `GlueDescent.LeafSkolemNoether` | `PkgI6.skolemNoether_aut` | small |
| GLUE-03 | T18 `HSyn.FrobeniusDense` ⇒ `ChebotarevExists`; T19 `HSyn.BrauerNesbitt` ⇒ `BrauerNesbittChar0` (the forms C10 consumes) | API-01 | not rfl-equal (§9) |
| GLUE-04 | Port PR #36-only proofs into whatever replaces the reference: A6, D3, D4, C10, D1-local | PR #36 `HDecomp/` | they exist; do not re-prove |
| GLUE-05 | Prop. TS from T1, T2 over `RatFunc ℚ`; Lemma NV | T1, T2 | G2 |
| GLUE-06 | C2 absolute irreducibility, `SemisimpleBaseChange` (glue-I3-linalg) | R9, T6, T26 | in neither checkout |
| GLUE-07 | `L′` unramified outside `T` | D-T32 | glue-b3-unram, absent |
| GLUE-08 | Glazer's appendix lemma G9; oddness G10; C7/C8 assembly G12; G13 | R10, R11_R12, R13-R15, T17-T19, T23-T25, D-T9-D-T12 | medium each |
| GLUE-09 | Full G15 at infinite level | D-R17, API-04 | "the new mathematics most worth checking early" (WP5) |
| GLUE-10 | G0: `HSyn.glueOutputs_of_leaves` | everything | needs the actual `A` and `J₁(N)` (API-08, D-R1, D-R16), not merely some nonzero abelian variety |

## 6. Contributor workflow (after the initial maintainer PR lands)

1. Pick an unclaimed target ID from a lane in §7. Coordinate through the project's tracker before
   starting so two people do not duplicate a proof (`docs/lean-contributions.md`).
2. The statement is **locked**: `ZInQ.Targets.H.<ID>` is a closed `Prop` (universe 0, no
   parameters, no section variables), with definitions from the baseline. Do not edit it. A
   statement change is a separate statement-review PR with its reason.
3. Add **one new file** `ZInQKernel/Contrib/H/<ID>.lean` (module `ZInQKernel.Contrib.H.<ID>`)
   containing `theorem ZInQ.Contrib.H.<ID>_holds : ZInQ.Targets.H.<ID>`, with exactly that type and
   no extra explicit, implicit or typeclass hypotheses. `P → P` or `[Fact P]` does not close `P`.
   Import the specific modules you need, not an umbrella. Helper lemmas go in your own new files
   under `ZInQKernel/Contrib/`. CI builds tracked contribution modules even if no root imports them.
4. **Edit no shared file**: not the targets, definitions, manifests, `lakefile.toml`, CI, root
   imports or other contributors' files. Do not update the Lean or Mathlib pins.
5. CI checks: the full elaborated type of the provider, kernel replay, axioms ⊆ `propext,
   Classical.choice, Quot.sound`, and no `sorry`/`unsafe`/`partial` provider. A green status is
   **not** acceptance. Acceptance needs the independent Astra review of the exact revision under
   Protocol_D (statement fidelity, provenance, dependency use, objections).
6. For `Enc-C` targets, include the written derivation from the published statement to the locked
   Lean form, and name the source and conventions (Frobenius, Hodge–Tate normalization).
7. A proved target closes only that leaf. It does not discharge H. The headline changes only
   with a checked discharge theorem after the glue (§5) is done.

**Initial maintainer registration (before proof-only contributions are accepted).** Land the
needed definition-only modules, locked target statements and pre-assigned provider names through
statement/infrastructure review. Registration may be done all at once or by area; a contributor
needs only the relevant target and its prerequisites registered at a trusted base.

**Per-area registry/manifest sharding is optional.** It can reduce shared-file conflicts between
parallel PRs that add new targets or change definitions. It is **not** required for parallel proofs
of already-registered targets: those PRs add only their own `Contrib/H` files and edit no shared
manifest. The following areas are an optional review/allocation grouping, not a sharding mandate:

| Area manifest | Targets | Props | Definition sources |
|---|---|---|---|
| `Theta` | R4, T28 | 2 | `PkgI1` (definition-only extraction) |
| `Reduction` | R6, R7, T1, T2, T3, T4, T5 | 8 | PR #36 `Objects.lean` (`PkgI2`) |
| `AbVar` | R9, T6, T7, T8, T26, T27 | 7 | PR #36 `Objects.lean` (`PkgI3`) |
| `PAdicHodge` | R10, R11_R12, R13 | 3 (4 leaves) | `PkgI4` (incl. `PkgI4.I3` copy, until API-02) |
| `Modular` | R14, R15, T24, T25 | 4 | `HSyn` §0-§1, `PkgI4` |
| `GaloisQ` | T13, T14, T15, T16, T17, T18, T19, T30, T31 | 11 | PR #36 `Conductor/I6Base.lean`, `Descent/B2Glue.lean`; `HSyn` |
| `Ramification` | T20, T21, T22 | 4 | PR #36 `Conductor/Breaks.lean`, `I6Base.lean` |
| **Total** | **34** | **39 (35 leaves)** | |

The optional manifest/shard names are the maintainers' choice. No manifest was edited, and
registration awaits human review. The existing single-manifest layout already supports
independent proof-only PRs once the relevant statements and provider names are registered.

## 7. Allocation lanes

| Lane | Meaning | Targets / projects |
|---|---|---|
| L0 | Prerequisite: definition review (start now; gates trust in every proof) | API-01 … API-07 |
| L1 | Ready, port from an existing library (provenance/attribution and statement-compatibility check first) | T1, T2, T13, T17, T18, T20, T22 |
| L2 | Ready, self-contained classical proof | T19, T21, T24, T28, T30, T31, R4 |
| L3 | Ready statement, infrastructure-heavy textbook proof (abelian varieties, local CFT, cohomology, newforms) | T3, T4, T5, T6, T7, T8, T14, T15, T16, T25, T26, T27 |
| L4 | Research-scale literature (long term) | R6, R7, R9, R10, R11_R12, R13, R14, R15 |
| L5 | New definitions before any statement (never registered as is) | the 19 opaque leaves of §3.2, API-08 … API-10 |
| L6 | Glue | §5 |

Every target is claimable now in the sense that its statement is genuine. Lanes L1-L3 are the
realistic first claims. All proofs remain subject to L0's definition review: a proof over a wrong
definition can be vacuous.

## 8. Not done / needs a human

- Human statement approval of all 34 targets (not given; not claimed).
- The choice between bundle and cochain forms for T14/T15, and whether to promote R8's monodromy
  form or PR #36's leaf-push statements (each changes the count).
- Port provenance and attribution check before any port (Tau Ceti, Stacks); pending, not assessed here.
- Final IDs and provider names were checked against the 34-entry registration proposal.
  The proposal remains unapplied: none is registered or accepted.

## 9. Validation performed and its limits

- Read in full: the reference `h-decomposition.md` (611 lines). Of `Leaves.lean`, read the header
  and the `HSyn` bundle/placeholder section (lines 1-53, 8887-9321) and the leaf definitions used
  above. All 757 declarations were extracted by a script (`h-task-list-notes/extract_names.py`).
  The 39 bundle fields were matched to their definitions (asserted in `target_map.py`).
- One Lean process at a time, private `ELAN_HOME`, `lake env lean` from the reference root against
  the prebuilt `Leaves.olean`. No build was run and no repository file was written. `git status`
  of the reference was identical before and after.
  - `AuditGlue.lean`: `#check` and `#print axioms` for all 382 public theorems and 363
    definitions. Exit 0, 6 s wall time, 7.2 GB max RSS. The results: 745 axiom lists; only 5
    contain `sorryAx` (`PkgI2.goodReduction_of_QM_rational3`, `PkgI6.artinConductor_le_of_upper`,
    `PkgI6.sq_principalUnits`, `HSyn.glueOutputs_of_leaves`, `HSyn.sixContactMin_of_leaves`). All
    others are subsets of `propext, Classical.choice, Quot.sound`. All 39 target definitions:
    exactly those three.
  - `AuditDuplicates.lean`: `Iff.rfl` succeeds for `HSyn.SkolemNoether ↔ PkgI6.SkolemNoether`
    and `HSyn.EigenformTwist ↔ PkgI4.EigenformTwist`. It fails (that is, not shown equal by rfl,
    which does not mean inequivalent) for the R14, R15, T6, T7, T14, T15, T18, T19, T20, T21 pairs
    named in §2 and for `HSyn.SkolemNoether ↔ GlueDescent.LeafSkolemNoether`.
- PR #36: read only, never built here. Leaf definitions in `HDecomp/Objects.lean`,
  `Conductor/I6Base.lean`, `Breaks.lean`, `Descent/B2Glue.lean` are whitespace-normalized
  text-identical to the reference (`compare_defs.py`). Rows marked **P** in §4 rely on PR #36's
  `print_axioms.lean` list and hdec-adopt's recorded check. PR #36's own body says full CI and
  final protected acceptance are pending.
- The "Unlocks" and "Assumes" columns come from the elaborated types (regex on audited `#check`
  output) and from the notes. A consumer that reaches a leaf through another bridge can be missed.
- Not verified: any published source or theorem number (every locator comes from the
  notes). Difficulty is SPECULATIVE. Definitions are unreviewed (WP1). Target and provider
  names were matched to the 34-entry proposal; registration remains unapplied.

Working files (scripts, logs, JSON target map `targets.json`): `h-task-list-notes/`.
