# H literature leaves as named kernel targets (draft, not registered)

Status: **draft engineering statement extraction** for maintainer statement review. Nothing here is a
proof, an assembled-proof acceptance, an Astra acceptance or a manuscript change. No proof provider
is declared. `KERNEL_CONTRACT.json` is **unchanged**; the exact entries a maintainer would add are in
[`registration-proposal.json`](registration-proposal.json) (`"status": "PROPOSAL_NOT_APPLIED"`).

## What this adds

* `ZInQKernel/Targets/H/<ID>.lean`: one file per genuine leaf, defining the closed proposition
  `ZInQ.Targets.H.<ID> : Prop` (no universe parameters; universe 0 where the source is
  universe-polymorphic). Each file's docstring records the source declaration and lines, the leaf's
  entry in the reference note (locators UNVERIFIED unless marked there), and convention caveats.
  Leaves with parts keep every part (`<ID>a`, `<ID>b` in the same file; the target is their
  conjunction).
* `ZInQKernel/Targets/H/Defs/{PkgI1,PkgI4,HSyn}.lean`: definition-only modules with the reference's
  definitions (verbatim bodies, original namespaces) that the PR36 baseline lacks, pruned to what
  the statements use plus two proved non-vacuity checks of the de Rham / Hodge–Tate definitions. No
  leaf statement, `opaque`, `axiom` or `sorry` in them.
* `ZInQKernel/Targets/H.lean`: umbrella import of the 34 targets (not imported by the root).
* Statements over abelian varieties, Galois cohomology and ramification groups use the PR36 baseline
  object layer (`ZInQKernel/HDecomp/{Objects,Conductor/I6Base,Conductor/Breaks,Descent/B2Glue}`),
  which is textually identical to the reference's; each such part is proved `Iff.rfl`-equal to the
  baseline's own leaf definition (`<part>_iff_baseline`). No baseline file is modified.

Source: the unchanged reference `scratch/h-decomposition/Leaves.lean` of the fork `diophantine-z-q`
(base `48b5f075e5509678c84685f0d1ec53febd10b1e5`, SHA-256 `99c4fa0535874e6fc737dafe52b82687bc29bc3d592d4bc38a02065f489a05d3`, 9321 lines) and its note
`docs/research/h-decomposition.md` (611 lines, SHA-256 `5f46224b5c53fc660bc477b51c79b7ec6ebaafe8cf16124fc3692346d850101e`). The reference file is not in
this checkout and is not imported (it has a `sorry` glue theorem and imports project modules).
PR36's own `docs/research/h-decomposition.md` (958 lines) describes a later 40-leaf/46-Prop
version of that file which is not available; this draft follows the locked 35/39 reference.

## Coverage

54 leaves (22 research, 32 textbook). The reference states **35 leaves as 39 Props** over genuine
definitions; the other **19** are `opaque` placeholders with no content and are **not registered**:
R1, R2, R3, R5, R8, R16, R17, R18, R19, R20, R21, R22, T9, T10, T11, T12, T23, T29, T32.

The 35 genuine leaves give **34 targets**: R11 (Berger) and R12 (Pan) exist only through their joint
consequence `PkgI4.PanBerger` (Pan's theorem with "de Rham at p" for "potentially semistable at
p"); separately they need `B_st`, which is not defined. `ZInQ.Targets.H.R11_R12` covers both
leaves; no separate Berger or Pan statement or provider is invented. Multi-part targets: R7, R9
(research), T14, T16, T22 (textbook). Research: 9 targets, 10 leaves, 11 Props. Textbook: 25
targets, 25 leaves, 28 Props.

| ID | Leaves | Props | Target | Provider (reserved, not declared) | Reference declaration(s) | Area |
|---|---|---|---|---|---|---|
| R4 | R4 | 1 | `ZInQ.Targets.H.R4` | `ZInQ.Contrib.H.R4_holds` | `PkgI1.ThetaModularity` | h-theta-igusa |
| T28 | T28 | 1 | `ZInQ.Targets.H.T28` | `ZInQ.Contrib.H.T28_holds` | `PkgI1.IgusaClebschSeparation` | h-theta-igusa |
| R6 | R6 | 1 | `ZInQ.Targets.H.R6` | `ZInQ.Contrib.H.R6_holds` | `PkgI2.RaynaudCriterion` | h-reduction |
| R7 | R7 | 2 | `ZInQ.Targets.H.R7` | `ZInQ.Contrib.H.R7_holds` | `PkgI2.NeronOggShafarevich`, `PkgI2.SerreTatePotentialGood` | h-reduction |
| T1 | T1 | 1 | `ZInQ.Targets.H.T1` | `ZInQ.Contrib.H.T1_holds` | `PkgI2.PurityBranchLocus` | h-reduction |
| T2 | T2 | 1 | `ZInQ.Targets.H.T2` | `ZInQ.Contrib.H.T2_holds` | `PkgI2.AbhyankarDVR` | h-reduction |
| T3 | T3 | 1 | `ZInQ.Targets.H.T3` | `ZInQ.Contrib.H.T3_holds` | `PkgI2.NeronMappingAbelianScheme` | h-reduction |
| T4 | T4 | 1 | `ZInQ.Targets.H.T4` | `ZInQ.Contrib.H.T4_holds` | `PkgI2.ReductionTorsionBijective` | h-reduction |
| T5 | T5 | 1 | `ZInQ.Targets.H.T5` | `ZInQ.Contrib.H.T5_holds` | `PkgI2.TorsionStructure` | h-reduction |
| R9 | R9 | 2 | `ZInQ.Targets.H.R9` | `ZInQ.Contrib.H.R9_holds` | `PkgI3.FaltingsSemisimple`, `PkgI3.FaltingsTate` | h-faltings-mumford |
| T6 | T6 | 1 | `ZInQ.Targets.H.T6` | `ZInQ.Contrib.H.T6_holds` | `PkgI3.HomFreeFinite` | h-faltings-mumford |
| T7 | T7 | 1 | `ZInQ.Targets.H.T7` | `ZInQ.Contrib.H.T7_holds` | `PkgI3.CharPolyIndepOfEll` | h-faltings-mumford |
| T8 | T8 | 1 | `ZInQ.Targets.H.T8` | `ZInQ.Contrib.H.T8_holds` | `PkgI3.PoincareReducibility` | h-faltings-mumford |
| T26 | T26 | 1 | `ZInQ.Targets.H.T26` | `ZInQ.Contrib.H.T26_holds` | `PkgI3.TateModuleFree` | h-faltings-mumford |
| T27 | T27 | 1 | `ZInQ.Targets.H.T27` | `ZInQ.Contrib.H.T27_holds` | `PkgI3.QMDichotomy` | h-faltings-mumford |
| R10 | R10 | 1 | `ZInQ.Targets.H.R10` | `ZInQ.Contrib.H.R10_holds` | `PkgI4.DeRhamComparison` | h-padic-hodge |
| R11_R12 | R11, R12 | 1 | `ZInQ.Targets.H.R11_R12` | `ZInQ.Contrib.H.R11_R12_holds` | `PkgI4.PanBerger` (= `PanFor LocalIsDeRham`) | h-padic-hodge |
| R13 | R13 | 1 | `ZInQ.Targets.H.R13` | `ZInQ.Contrib.H.R13_holds` | `PkgI4.EigenformHT` | h-padic-hodge |
| T25 | T25 | 1 | `ZInQ.Targets.H.T25` | `ZInQ.Contrib.H.T25_holds` | `PkgI4.NewformOfEigenform` | h-padic-hodge |
| R14 | R14 | 1 | `ZInQ.Targets.H.R14` | `ZInQ.Contrib.H.R14_holds` | `HSyn.EigenformRepExists` | h-eigenform-galois |
| R15 | R15 | 1 | `ZInQ.Targets.H.R15` | `ZInQ.Contrib.H.R15_holds` | `HSyn.DeligneSerreConseq` | h-eigenform-galois |
| T13 | T13 | 1 | `ZInQ.Targets.H.T13` | `ZInQ.Contrib.H.T13_holds` | `HSyn.SkolemNoether` | h-eigenform-galois |
| T17 | T17 | 1 | `ZInQ.Targets.H.T17` | `ZInQ.Contrib.H.T17_holds` | `HSyn.KroneckerWeber` | h-eigenform-galois |
| T18 | T18 | 1 | `ZInQ.Targets.H.T18` | `ZInQ.Contrib.H.T18_holds` | `HSyn.FrobeniusDense` | h-eigenform-galois |
| T19 | T19 | 1 | `ZInQ.Targets.H.T19` | `ZInQ.Contrib.H.T19_holds` | `HSyn.BrauerNesbitt` | h-eigenform-galois |
| T24 | T24 | 1 | `ZInQ.Targets.H.T24` | `ZInQ.Contrib.H.T24_holds` | `HSyn.EigenformTwist` | h-eigenform-galois |
| T14 | T14 | 2 | `ZInQ.Targets.H.T14` | `ZInQ.Contrib.H.T14_holds` | `PkgI6.BrauerHasse2`, `PkgI6.BrauerReciprocity2` | h-local-arithmetic |
| T15 | T15 | 1 | `ZInQ.Targets.H.T15` | `ZInQ.Contrib.H.T15_holds` | `PkgI6.LocalH2Card` | h-local-arithmetic |
| T16 | T16 | 2 | `ZInQ.Targets.H.T16` | `ZInQ.Contrib.H.T16_holds` | `PkgI6.LocalKroneckerWeber`, `PkgI6.LocalReciprocityUpper` | h-local-arithmetic |
| T20 | T20 | 1 | `ZInQ.Targets.H.T20` | `ZInQ.Contrib.H.T20_holds` | `GlueConductor.HilbertDifferentFormula` | h-local-arithmetic |
| T21 | T21 | 1 | `ZInQ.Targets.H.T21` | `ZInQ.Contrib.H.T21_holds` | `GlueConductor.SerreDifferentBound` | h-local-arithmetic |
| T22 | T22 | 2 | `ZInQ.Targets.H.T22` | `ZInQ.Contrib.H.T22_holds` | `PkgI6.HerbrandQuotient`, `PkgI6.HerbrandTransitivity` | h-local-arithmetic |
| T30 | T30 | 1 | `ZInQ.Targets.H.T30` | `ZInQ.Contrib.H.T30_holds` | `GlueDescent.B2Q.LeafSqrtCrit` | h-local-arithmetic |
| T31 | T31 | 1 | `ZInQ.Targets.H.T31` | `ZInQ.Contrib.H.T31_holds` | `GlueDescent.B2Q.LeafUnramified` | h-local-arithmetic |

## Status vocabulary (keep these separate)

| Property | State in this draft |
|---|---|
| Exact preservation of the reference encoding | Yes (this is **not** fidelity to the published mathematics): bodies verbatim from the reference (listed edits only: `Type u`→`Type`, `PkgI4.I3.AbVar`→baseline `PkgI3.AbVar`, `PanFor LocalIsDeRham` beta-reduced, T16(a) binds `p` as the reference bundle does); every target/part is `Iff.rfl`-equal to the reference statement re-declared verbatim, or to the baseline's identical leaf. |
| Kernel-checked statement | Yes, by a local draft audit (copy of `scripts/audit_kernel.lean` without headline/exports; owned modules = the 38 new modules + 5 baseline HDecomp modules, external base = Mathlib; evidence in [`validation/`](validation/)): all 34 targets are closed `Prop` definitions with no universe parameters; kernel replay against Mathlib; axioms `propext`, `Classical.choice`, `Quot.sound` only; no `opaque`, no `axiom`, no `sorry`. Not the CI gate. |
| Reviewed mathematical statement (fidelity to the published theorem) | **No.** Needs maintainer statement review (and Astra review where required). Definitions are unreviewed (note §6 R4); two Galois-representation layers (`HSyn`, `PkgI4`) are kept as in the reference. |
| Registered in `KERNEL_CONTRACT.json` | **No** (proposal only). Until registered, the existing checker rejects these new `ZInQKernel/` sources as unregistered baseline sources, by design. |
| Proved provider | **No** (all open; no provider declared). |

## Review routes

A maintainer applies the proposal's `manifest_additions` (all at once, or area by area using
`per_area_split`) in a statement/infrastructure review PR: it changes the lock, so the trusted
checker routes it to `statement_or_infrastructure_review`. Once an area is registered at a trusted
base, a PR that only adds `ZInQKernel/Contrib/H/<ID>.lean` is classified
`proof_only_astra_review`, so proofs of different leaves can be done in parallel proof-only PRs.

## Contributing a proof (after registration)

Create `ZInQKernel/Contrib/H/<ID>.lean` importing `ZInQKernel.Targets.H.<ID>` (and the narrow
modules the proof uses) and close the target with exactly this shape:

```lean
import ZInQKernel.Targets.H.T17

namespace ZInQ.Contrib.H

/-- Kronecker–Weber (Washington, Thm 14.1). -/
theorem T17_holds : ZInQ.Targets.H.T17 := by
  -- a complete proof; no `sorry`, no new `axiom`, no extra hypotheses or instance arguments
  ...

end ZInQ.Contrib.H
```

The type must be exactly the registered target (CI compares full elaborated types; `P → P` or a
`[Fact P]` argument does not count). Do not edit target, `Defs` or baseline files in a proof PR;
statement changes go through statement review. A proved leaf is not removed from any headline
until a checked discharge theorem exists; H itself still needs the unformalized glue
(`docs/research/h-decomposition.md` §3).
