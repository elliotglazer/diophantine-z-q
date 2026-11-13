# Validation evidence for the proposed H targets (draft; not a CI gate, not an acceptance)

Everything here concerns the 38 new Lean sources whose SHA-256 values are in
[`sources.sha256`](sources.sha256) (identical to `manifest_additions.files` of
[`../registration-proposal.json`](../registration-proposal.json)). Build, audit and fidelity checks
were run on exactly these file states. Paths are relative to the repository root.

## Environment

* Lean `leanprover/lean4:v4.35.0`; Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` from the public
  cache (`lake exe cache get`); dependency checkouts at the revisions of `lake-manifest.json`.
* At most 2 concurrent Lean compiler processes (FIFO slot gate around `lean`, each with
  `LEAN_NUM_THREADS=1`); standalone checks with `LEAN_NUM_THREADS=1`.

## Commands and results

| Check | Command | Result |
|---|---|---|
| Build | `lake build ZInQKernel.Targets.H` (gated to 2 compilers) | exit 0; 38 new modules compiled, all exit 0; 61.7 s wall; peak process-group RSS 10.6 GiB ([`build-summary.json`](build-summary.json), which also lists the first compilation of the 5 baseline HDecomp dependencies in this worktree) |
| Draft kernel audit | `lake env lean --run docs/h-targets/validation/audit_h_targets.lean docs/h-targets/validation/audit-spec.json OUT.json` | passed ([`audit-report.json`](audit-report.json)): 43 owned modules (38 new + `ZInQKernel.HDecomp.{Objects, Conductor.Dyadic, Conductor.I6Base, Conductor.Breaks, Descent.B2Glue}`), external base = Mathlib only; 1040 owned declarations replayed through the kernel; axioms in the closure of all owned bodies: `propext`, `Classical.choice`, `Quot.sound`; owned `opaque` 0, owned `axiom` 0, unsafe/partial 0; all 34 targets closed `Prop` without universe parameters; all 34 `open` (no provider declared — the audit fails if one exists) |
| Exact preservation of the reference encoding (Lean) | `lake env lean docs/h-targets/validation/fidelity_check.lean` | exit 0: 44 `Iff.rfl` checks — each Defs-backed target equals the reference statement re-declared verbatim in the file; each baseline-backed part equals the reference bundle's universe-0 form; each multi-part target equals the conjunction of its parts |
| Negative control | `lake env lean docs/h-targets/validation/fidelity_negative.lean` | fails as required (2 errors: deliberately mismatched pairs) |
| Exact preservation (text) | `fidelity.py` (scratch tool; needs the reference file, not in this checkout) | [`fidelity-textual.json`](fidelity-textual.json): every kept `Defs` declaration byte-identical (modulo trailing whitespace) to the reference: PkgI1 14/14, PkgI4 112/112, HSyn 13/13 |
| In-file baseline cross-checks | part of the build | the 26 `<part>_iff_baseline : <part> ↔ <baseline leaf> := Iff.rfl` theorems compile |
| Registration simulation | `bash docs/h-targets/validation/simulate_registration.sh` (throw-away `git clone --shared` in `$TMPDIR`) | [`simulation-results.json`](simulation-results.json): candidate with the manifest unchanged → rejected "Unregistered baseline source" (intended); proposal applied → `valid_candidate_contract`, 979 files, 39 targets, route `statement_or_infrastructure_review`, lock changed `KERNEL_CONTRACT.json`; then a `ZInQKernel/Contrib/H`-only change → `proof_only_astra_review`. The checker used is the base commit's, byte-identical |

The reference `scratch/h-decomposition/Leaves.lean` of the fork (base
`48b5f075e5509678c84685f0d1ec53febd10b1e5`) had SHA-256
`99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3` before and after the work.

## Scope of this evidence

* `audit_h_targets.lean` is a copy of `scripts/audit_kernel.lean` with the headline/exports checks
  removed (the H targets are not headline premises) and provider absence enforced; its header
  lists the differences. It is **not** the CI gate: CI builds the whole root (about 940 modules) and
  audits the headline, which was not run for the proposal-applied tree.
* "Kernel-checked statement" and "exact preservation of the reference encoding" do **not** mean the
  statements are faithful to the published theorems. That mathematical review has not happened
  (note §6 R1, R2, R4), and no provider is proved.
* The 5 baseline HDecomp modules were compiled and replayed here only as dependencies; their glue
  theorems were not separately reviewed.
