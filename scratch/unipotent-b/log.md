# unipotent-b results log

## Setup
- lean/.lake was missing in the worktree ("unknown module prefix 'ZInQ'"); reflink-copied from ../genus-fold/lean/.lake (identical lean/ZInQ, checked by diff -rq).

## UnipotentB.lean (imports ZInQKernel.OneProof.H.TailZ14 only)
- §0 verbatim copies of ReductSplit.SemistableUnipotent, ReductGlue.SemistableUnipotentSH, ReductGlue.StrictHenselizationInside, each `= original := rfl`. VERIFIED (compiled).
- §1 specialFibre (𝒩 ×_O k(s)), IsSemistableRes, HasSemistableReductionRes; resBarEquiv : k(s) ≃+* κ̄ for alg. closed k(s); isSemistableRes_iff, hasSemistableReductionRes_iff (k(s) vs κ̄ semistability agree when k(s) alg. closed). VERIFIED (compiled).
- §2 LEAF SemistableUnipotentPrinted (SGA 7 IX 3.5 printed form, UNVERIFIED wording: SH trait, [CharZero K], [PerfectField k(s)], Ω [IsSepClosure K Ω], semistable over k(s); iff I unipotent; echelon (σ-1)(τ-1)=0). SemistableUnipotentPrintedEchelon (used direction) with echelon_of_printed. SemistableUnipotentSH0 (= SemistableUnipotentSH + [CharZero K] [PerfectField k(s)]); semistableUnipotentSH0_of : PrintedEchelon → SH0. VERIFIED (compiled).
- §3 SemistableUnipotent0 (= SemistableUnipotent + [CharZero K] [PerfectField k(s)]); semistableUnipotent0_of : StrictHenselizationInside → SH0 → SemistableUnipotent0; semistableUnipotent0_of_printed; semistableUnipotent0_of_old. VERIFIED (compiled, no errors/warnings).
- §4 SemistableUnipotentPrintedGen (every field, Ω [IsSepClosure], semistable over k(s)); printed_of_printedGen; GLUE SemiAbelianDescendsSepClosed (κ̄-semistable ⇒ k(s)-semistable for sep. closed k(s)); semiAbelianDescends_of_perfect (proved for perfect k(s)); GLUE SepClosureTateRestrict (inertia restricts to K^s = separableClosure K Ω, T_ℓ over K^s ↠ T_ℓ over Ω equivariantly); semistableUnipotentSH_of_gen : PrintedGen → Descends → TateRestrict → ReductGlue.SemistableUnipotentSH (unchanged statement); semistableUnipotent_of_gen (+ StrictHenselizationInside → ReductSplit.SemistableUnipotent, unchanged statement). VERIFIED (compiled).
- axioms.txt: all 10 #print axioms = [propext, Classical.choice, Quot.sound]. VERIFIED.

## Uses check
- Deps.lean (BFS over used constants from HDec.HSyn.sixContactMin_of_open15, non-Mathlib), output deps.txt. VERIFIED:
  - in closure: ReductSplit.SemistableUnipotent, ReductGlue.raynaudCriterion_leaves (r6), ReductSplit.grothendieckMonodromy_final' (r8); not in closure: ReductGlue.SemistableUnipotentSH.
  - r8: the projections OpenResearchLeaves{2,5,7,8}.r8 are used only to build the next bundle; ResearchLeaves3.mk takes r8 but no ResearchLeaves3.r8 projection is in the closure, and no theorem in the closure takes PkgI2.GrothendieckMonodromy as hypothesis except grothendieckMonodromy_ofK5 (a restatement). r8 is INERT in the final proof.
  - r6 (PkgI2.RaynaudCriterion, every field K) is consumed by HDec.LeafQM.AV.QML3.goodReduction ([CharZero K], arbitrary DVR Ov, residue field not assumed perfect) → HDec.PkgI2.goodReduction_of_QM_rational3' / _of_alg (every field), HDec.G0ModField.KernelField.* (good_of_QML3, kernelFieldExists_*), HDec.HSyn.LinkedTate.qmModelG3_of, HDec.HSyn.linkedTateLocal_of_leaves3, modelG3G6_of_leaves3.
- UsesFail.lean: the r6 proof (raynaudCriterion_of_leaves body) with the restricted field fails: "failed to synthesize instance of type class CharZero K". VERIFIED (expected error).
- UsesCheck.lean: RaynaudCriterion0 (r6 with [CharZero K] [PerfectField k(s)]) proved from the restricted field by the same proof (raynaudCriterion0_of_leaves). VERIFIED (compiled, no errors).

## Unrestricted field: smaller Props proved
- §5 tateMap_surjective (injective φ onto ℓ-power torsion ⇒ Tate.map φ surjective); InertiaRestrictSepClosure, TorsionFromSepClosure (stated); sepClosureTateRestrict_of : InertiaRestrict → TorsionFromSep → SepClosureTateRestrict; semistableUnipotent_of_gen'. VERIFIED.
- §6 isSeparable_of_etale' (any target field), exists_lift_of_etale_sep (points of an étale K-scheme in Ω come from separableClosure K Ω), torsion_from_sepClosure / torsionFromSepClosure_of : MulEtaleAbelianScheme → TorsionFromSepClosure; inertiaRestrictSepClosure (PROVED, restrictNormal). VERIFIED.
- semistableUnipotent_of_printedGen : PrintedGen → SemiAbelianDescendsSepClosed → MulEtaleAbelianScheme → StrictHenselizationInside → ReductSplit.SemistableUnipotent (UNCHANGED statement). VERIFIED.
- semistableUnipotentSH_of_printedGen : PrintedGen → Descends → MulEtale → ReductGlue.SemistableUnipotentSH (unchanged). VERIFIED.
- SemistableUnipotentPrintedGeom (semistability over κ̄) and semistableUnipotent_of_printedGeom : Geom → MulEtale → StrictHenselizationInside → SemistableUnipotent (no glue). VERIFIED.
- axioms.txt: 18 #print axioms, all [propext, Classical.choice, Quot.sound]; file compiles with no errors or warnings. VERIFIED.
