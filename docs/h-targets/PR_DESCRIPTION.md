# Draft: H literature leaves as named closed-`Prop` kernel targets (statement review requested)

**Type:** statement extraction for maintainer statement/infrastructure review. **Not** a proof,
**not** an assembled-proof acceptance, **not** an Astra acceptance, **no** manuscript change.
`KERNEL_CONTRACT.json`, the checker (`scripts/check_kernel_contract.py`), the audit
(`scripts/audit_kernel.lean`), CI and every baseline source are unchanged. No proof provider is
declared (no `axiom`, no `sorry`, no placeholder).

Base: PR36 head `9bf9ad8aa99168060cd0f770a007a30ff2c31aca` (branch `wip/h-leaf-targets`).

## Summary

The H decomposition (`docs/research/h-decomposition.md`) reduces hypothesis H to 54 literature
leaves plus glue. Its Lean companion (the fork's `scratch/h-decomposition/Leaves.lean`, SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, 9321 lines, base
`48b5f075…`; not in this checkout and unchanged) states **35 leaves as 39 Props** over genuine
definitions; **19 leaves are `opaque` placeholders** and are **not registered**.

This PR turns the 35 genuine leaves into **34 named targets** `ZInQ.Targets.H.<ID> : Prop`, one file
each, with a reserved, distinct, undeclared provider `ZInQ.Contrib.H.<ID>_holds` in
`ZInQKernel.Contrib.H.<ID>`:

* Research (9 targets, 10 leaves, 11 Props): R4, R6, R7 (a∧b), R9 (a∧b), R10, **R11_R12**, R13, R14, R15.
* Textbook (25 targets, 25 leaves, 28 Props): T1-T8, T13, T14 (a∧b), T15, T16 (a∧b), T17-T21,
  T22 (a∧b), T24-T28, T30, T31.
* **R11 + R12 = one target.** Berger and Pan exist in the source only as their joint consequence
  `PkgI4.PanBerger` (Pan with "de Rham at p"); separately they need `B_st`, which is not defined.
  `ZInQ.Targets.H.R11_R12` covers both leaves; no separate Berger/Pan statement or provider is
  invented. Hence 35 leaves → 34 independent targets.
* Every part of a multi-part leaf is kept (`<ID>a`, `<ID>b`; the target is their conjunction).
* Not registered (opaque, no content): R1-R3, R5, R8, R16-R22, T9-T12, T23, T29, T32.

Full mapping table: `docs/h-targets/README.md`.

## New files (nothing modified)

* `ZInQKernel/Targets/H/<ID>.lean` × 34 — the proposed statement, its source declaration and line range,
  the leaf's note entry (locators UNVERIFIED unless marked), convention caveats; for parts over
  baseline objects an `Iff.rfl` cross-check `<part>_iff_baseline` against the baseline's own leaf
  definition.
* `ZInQKernel/Targets/H/Defs/{PkgI1,PkgI4,HSyn}.lean` — definition-only modules: the reference's
  genuine definitions the baseline lacks (genus-2 theta constants and Igusa invariants;
  `G_{ℚ_p}` on `ℂ_p` and Mathlib's `B_dR`, de Rham predicate, Hodge–Tate multiplicities, cusp forms,
  eigenforms, newforms; the `HSyn` Galois/eigenform layer), verbatim bodies in their original
  namespaces, pruned by a kernel-level reachability report to what the statements use (plus two
  proved non-vacuity checks of the de Rham/HT definitions). Narrow Mathlib imports (`#min_imports`).
  No leaf statement, `opaque`, `axiom`, `sorry`, or glue in them.
* `ZInQKernel/Targets/H.lean` — umbrella import (not imported by the root `ZInQKernel`).
* `docs/h-targets/README.md`, `docs/h-targets/registration-proposal.json`, and
  `docs/h-targets/validation/` (commands, audit report, fidelity checks, build summary, checker
  simulation).

Statements over abelian varieties, Galois cohomology and ramification groups reuse the PR36 baseline
object layer `ZInQKernel/HDecomp/{Objects, Conductor/I6Base, Conductor/Dyadic, Conductor/Breaks,
Descent/B2Glue}` (already pinned; verified textually identical to the reference apart from docstring
line breaks and glue proofs) instead of adding a fourth copy of the abelian-variety layer. Name
collisions with the baseline were checked: the new namespaces (`PkgI1`, `PkgI4`, `HSyn`,
`ZInQ.Targets.H`) do not occur there.

Textual edits to source statements (all listed in each docstring): `Type u` → `Type` (universe 0,
as the reference bundles the leaves); `PkgI4.I3.AbVar` → baseline `PkgI3.AbVar` (the reference's
renamed verbatim copy); `PanFor LocalIsDeRham` beta-reduced for R11_R12; T16(a) binds `p` exactly as
the reference's leaf bundle.

## What reviewers are asked to do

1. **Statement review** of each target (fidelity to the cited theorem, convention caveats, whether a
   "consequence" form is never stronger than the published statement), and of the `Defs`
   definitions (note §6 R4: unreviewed; a definitional slip could make a statement vacuous; the
   reference keeps two Galois-representation layers, `HSyn` and `PkgI4`, which this PR preserves
   rather than merging, since merging would change statements).
2. If accepted, **apply the registration** in a maintainer-owned statement/infrastructure PR:
   `docs/h-targets/registration-proposal.json` → `manifest_additions` (38 file pins + 34 target
   entries; headline, exports, existing pins/targets and `baseline_commit` untouched unless the
   maintainer decides otherwise). The proposal is marked `PROPOSAL_NOT_APPLIED`,
   `acceptance: false`.
3. Optionally register **area by area** (`per_area_split`: theta/Igusa; reduction; Faltings–Mumford;
   p-adic Hodge; eigenform Galois; local arithmetic). Each area PR adds that area's files with their
   manifest entries; the umbrella goes with the last area.

**Why this permits parallel proof-only PRs.** Once a target is registered at a trusted base, a
proof is a single new file `ZInQKernel/Contrib/H/<ID>.lean` declaring
`theorem ZInQ.Contrib.H.<ID>_holds : ZInQ.Targets.H.<ID>`. Such a PR changes no locked file, so the
trusted checker routes it to `proof_only_astra_review`, and contributors can work on different
leaves independently. Each provider name is distinct and pre-assigned, so proofs cannot collide on
the manifest.

## Current state of this branch under the unchanged checker (by design)

Until the maintainer applies the proposal, the new `ZInQKernel/` sources are unregistered, so
`scripts/check_kernel_contract.py` **rejects** the committed branch ("Unregistered baseline source")
and `check_kernel.py` would stop there. That is the intended, honest state: this PR asks for
statement review; it does not self-register or relax the lock.

## Validation (local, devvm; Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`)

* **Build:** `lake build ZInQKernel.Targets.H` (3 Defs + 34 targets + umbrella, plus the 5 baseline
  HDecomp dependencies) — exit 0, ≤ 2 compiler processes (FIFO-gated, `LEAN_NUM_THREADS=1`), from
  the public Mathlib cache: first build of the baseline dependencies + Defs 49 s wall, each later
  rebuild of all new modules ≤ 67 s wall; peak process-group RSS ≈ 15 GB.
* **Draft kernel audit** (copy of `scripts/audit_kernel.lean` without headline/exports, with
  provider absence enforced; modules = 38 new modules + the 5 baseline HDecomp modules, external base
  = Mathlib): passed; 1040 owned declarations replayed through the kernel; axioms used `propext`,
  `Classical.choice`, `Quot.sound` only; 0 owned `opaque`, 0 owned `axiom`, 0 unsafe/partial; all 34
  targets closed `Prop` without universe parameters; all 34 status `open` (no provider declared).
  This is not the CI gate (the CI audit also needs the full root build and the headline).
* **Exact preservation of the reference encoding** (not fidelity to the published mathematics,
  which is unreviewed): (a) every kept `Defs` declaration is byte-identical (modulo trailing whitespace) to
  the reference (14 + 112 + 13 declarations); (b) 44 `Iff.rfl` checks: each Defs-backed target equal
  to the reference statement re-declared verbatim, each baseline-backed part equal to the reference
  bundle's universe-0 form, each multi-part target equal to the conjunction of its parts; a negative
  control (deliberately mismatched pairs) fails as expected; (c) the 26 in-file `_iff_baseline`
  checks compile.
* **Checker simulation** (throw-away clone; the PR36 checker byte-identical to base): candidate as
  committed → rejected "Unregistered baseline source" (expected); proposal applied → valid candidate
  contract (979 files, 39 targets), route `statement_or_infrastructure_review`, lock changed
  `KERNEL_CONTRACT.json`; then a `Contrib/H`-only change on that base → route
  `proof_only_astra_review`.
* Reference `Leaves.lean` SHA-256 re-checked after the work: unchanged.

## Scope gaps / known limitations

* Statement fidelity is to the reference encoding; the mathematical statements are **not reviewed**
  (several are "consequence" forms; Pan's trace reading; R13's normalization; locators UNVERIFIED;
  note §6 R1-R2, R4).
* PR36's own `docs/research/h-decomposition.md` (958 lines) describes a later 40-leaf/46-Prop
  `Leaves.lean` (adds R8, T9, T23, T29, T32 and R17 elsewhere) that is not available; this draft
  follows the locked 35/39 reference. The existing contribution doc's sentence that the scratch leaf
  file is not in this checkout remains true; it is not edited.
* Registering the targets does not change the headline: H is still a premise until the glue
  (note §3, mostly unformalized) and a checked discharge theorem exist.
* The full CI path (`check_kernel.py`: root build of all ~940 modules + headline audit) was not run
  for the proposal-applied tree; only the contract-checker simulation and the draft audit above.
