# reduct-b results log

- RBBase.lean = scratch/reduct-glue/ReductGlue.lean minus `#print axioms` lines (Base = kernel TailZ7, Body = kernel
  TailZ14 modulo imports/header, VERIFIED by diff 11-14 17:55).
- t.sh: compiles a test file against /tmp/rblib/RBBase.olean (built by `lake env lean -R scratch/reduct-b
  scratch/reduct-b/RBBase.lean -o /tmp/rblib/RBBase.olean`, 50 s, 7.6 GB).
- K1 (11-14) VERIFIED compiled: `ReductB.semistableReductionDVR_of_raynaud (hR : RaynaudSemistable)
  (hM : AvSplit.MumfordTorsionAlgClosed) (hE : AvSplit.T4.MulEtaleAbelianScheme) : SemistableReductionDVR`,
  axioms [propext, Classical.choice, Quot.sound]. New lemmas: `mem_of_isSeparable_of_fixed_inter`,
  `exists_rational_of_fixed_etale_inter` (Galois descent to an intermediate field F ⊆ K̄ for points of étale
  K-schemes), `fixedTorsionRational_inter`, `exists_three_le_isUnit` (3 or 4 is a unit in a local ring, 4-3=1).
  The AlgebraicClosure K' vs K̄ transfer: κ' := IsAlgClosed.lift : K̄ →ₐ[K'] (K')‾ (a K'-embedding, so
  κ'∘val = ofId), needs explicit `Module.IsTorsionFree K' _` instances (else typeclass timeout).
- K1.lean renamed Body.lean (namespace ReductB, imports RBBase).
- Route B (11-14) VERIFIED compiled, standard axioms:
  `strictHenselizationNeron_of_pair : StrictHenselizationPair → StrictHenselizationNeron` (instance K'=K, O'=O,
  `comap_algebraMap_self`); `raynaudSemistable_of_SH_pair : RaynaudSemistableSH → StrictHenselizationPair →
  MulEtale → RaynaudSemistable`; `semistablePersistsDVR_of_SH_pair : SemistablePersistsSH → Pair →
  SemistablePersistsDVR`; `semistableReductionDVR_of_SH_pair` (K1 ∘ Route B); `three_fields_of_printed`.
- Route B-CP VERIFIED compiled: defs `RaynaudSemistableSHcp`, `SemistablePersistsSHcp` ([CharZero K]
  [PerfectField κ(O)] on the SH forms), `RaynaudSemistableCP`, `SemistablePersistsDVRcp`, `SemistablePersistsDVRnf`;
  `cp_of_general` (the cp SH leaves are specializations of the DVR forms); `raynaudSemistableCP_of_SH`,
  `semistablePersistsDVRcp_of_SH` (CharZero E from injectivity, PerfectField κ(P) by
  `Algebra.IsAlgebraic.perfectField` from IsSHNeronExt's algebraic residue extension);
  `perfectField_residue_nf` (κ(O) finite for a DVR of a number field: 𝓞/𝔭 finite, `resIso`);
  `persistsNF_of_cp`; `semistablePersists_of_leaves_nf` (SS3 from the nf form, reduct-split's proof retyped).
- FINDING: uses of the three fields (grep of ZInQKernel, VERIFIED): raynaudSemistable → TailZ15 r6 :=
  raynaudCriterion_leaves (PkgI2.RaynaudCriterion: ALL fields K); semistableReductionDVR → TailZ9 r8 :=
  grothendieckMonodromy_final' (PkgI2.GrothendieckMonodromy: ALL fields) and TailZ15 SS1 (number fields);
  semistablePersistsDVR → TailZ15 SS1, SS3 (number fields only). So the cp forms cannot fill raynaudSemistable
  or semistableReductionDVR without restricting r6/r8 (used in TailF/H/I/K, LF4T5); they can fill
  semistablePersistsDVR's two uses.
- SS1 copy `semistableReductionThm_of_leaves_nf (h36 : SemistableReductionDVRnf) (h33 : SemistablePersistsDVRnf)`
  (reduct-split's proof + one `NumberField (F O)` instance), `semistablePersists_final_nf`,
  `semistableReductionThm_final_nf`, `semistableReductionDVRnf_of_raynaudCP` (K1 at number fields from the cp DVR
  form), `ss1_ss3_of_cp_full` (SS1 ∧ SS3 from RaynaudSemistableSHcp, SemistablePersistsSHcp, Pair, Mumford,
  MulEtale, Néron existence, SemistableLocalGlobal, SemistableAlmostAll): VERIFIED compiled.
- `fold_uses`: r6 (PkgI2.RaynaudCriterion), r8 (PkgI2.GrothendieckMonodromy), SS1, SS3 with the TailZ15/TailZ9 terms,
  the three fields replaced by Route B theorems; `fold_uses_K1` (K1 only): VERIFIED compiled.
- Deliverable: mk.sh assembles ReductB.lean = RBBase.lean + Body.lean; chk.sh: `lake env lean
  scratch/reduct-b/ReductB.lean` 52 s, 7.6 GB, no errors, 11 `#print axioms` all [propext, Classical.choice,
  Quot.sound] (VERIFIED 11-14 18:08, axioms.txt). No sorry, no axiom in Body.lean (grep).
- FoldSnippet.lean.txt: generated from TailZ19's OpenResearchLeaves12 (32 fields parsed, 3 dropped, 3 added); UNCHECKED (TailZ19 not built here: lake --no-build lists 667 unbuilt modules, mostly TauCeti/CloudW07).
