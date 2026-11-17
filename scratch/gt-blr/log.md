# gt-blr results log

## 2026-11-14 21:15 start
- Target: `CToPrinted.BLR_1_2_4` (TailZ19 L63), field `blr_1_2_4` of OpenResearchLeaves (TailZ22 L199, TailZ23 L656). VERIFIED (read).
- Consumers of `blr_1_2_4` (VERIFIED, grep): all go through `CToPrinted.neronLocalizesDVR_of_printed` (TailZ19 L138,
  which uses only `.mp`, at R = 𝓞_L, 𝔭 = center of O, R𝔭 = O). `semistableNeronBaseChange_of_printed_full` (TailZ19 L1650) uses
  `hB` only in `have hL := neronLocalizesDVR_of_printed hB` (L1656). Fold sites: TailZ23 L767 (`ss1_ss3_of14`),
  TailZ23 L794 (`researchLeaves9_of_open14.semistableNeronBaseChange`), TailZ22 L308 (`blr_1_2_4 := r.blr_1_2_4`, field passing).
- Plan (math): .mp holds for ANY commutative ring R, prime 𝔭, fraction field K: given smooth Y/R𝔭,
  (i) uniqueness: Y_K → Y is scheme-theoretically dominant (flat base change of Spec K → Spec R𝔭,
  Mathlib `IsSchemeTheoreticallyDominant.of_isPullback`), Y_K reduced (smooth over a field), hence Y reduced
  (`IsSchemeTheoreticallyDominant.isReduced`), and `ext_of_isDominant_of_isSeparated` with X separated over R;
  (ii) existence on an affine open V: spread V out to a smooth W over Spec R[1/s] (EGA IV 8.8.2(ii), 17.7.8(ii), both
  PROVED in ZInQKernel/Contrib/CloudW01Spread), W is smooth over R (Spec R[1/s] → Spec R open immersion) with
  generic fibre V_K, extend by the Néron property of X over R, glue by (i).
  The risk flagged in gap-triage A10 ("needs a smooth model over all of R") does not arise: W/R[1/s] smooth ⇒ W/R smooth.

## 2026-11-14 21:40 MP proved
- `GapBLR.BLR_1_2_4_MP` (the .mp half, binders of `CToPrinted.BLR_1_2_4`) PROVED: `GapBLR.blr_1_2_4_mp`,
  ZInQKernel/Contrib/OneProof/BLRLocalizes.lean, VERIFIED (lake build +Main +Discharges +BLRLocalizes: success;
  axioms [propext, Classical.choice, Quot.sound]).
  General form `GapBLR.isNeronModelOver_localization`: any CommRing R, IsFractionRing R K, any prime 𝔭 (no Dedekind).
- `GapBLR.neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR` (no hypotheses), VERIFIED.
- `GapBLR.blr_1_2_4_mp_of_printed : CToPrinted.BLR_1_2_4 → BLR_1_2_4_MP`, VERIFIED.
- #discharges (scratch/gt-blr/Discharges.lean): "72 open hypotheses, 61 theorems checked, 0 discharge one" — expected:
  the open field is the full iff; the .mp half matches no open statement. A fold must reroute the consumers.
- Reused from the chain: `LeafQM.AV.R1UnivRigid.isReduced_of_smooth` (TailZ16), `CToPrinted.algOL`,
  `isScalarTower_OL`, `isLocalization_center`, `isNeronModelOver_of`, `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof`,
  `EGAIV_17_7_8_ii_proof`, `smooth_of_iso`. New (not in chain): limit diagram `Spec R_𝔭 = lim Spec R[1/s]` for general
  R (TailZ19 has only the 𝓞_L / valuation-subring instance `specConeOIsLimit`).

## 2026-11-14 22:00 full iff proved
- `GapBLR.blr_1_2_4 : CToPrinted.BLR_1_2_4` (both directions) PROVED, VERIFIED: BLRLocalizes.lean rebuilt
  (lake build +BLRLocalizes: success, no warnings under `lake env lean`), axioms [propext, Classical.choice, Quot.sound].
- `.mpr` = `GapBLR.isNeronModelOver_of_local` (any CommRing R with IsFractionRing R K): local existence `local_pt`
  via `V ⊗ R_𝔭 = lim V ⊗ R[1/s]` (`bcConeIsLimit`) + Mathlib `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
  (Stacks 01ZC); glue over the point cover with `glue_cover`; uniqueness `uqA` over A = R.
- #discharges (scratch/gt-blr/Discharges.lean), VERIFIED:
  `DISCHARGES [OpenResearchLeaves14.blr_1_2_4] by GapBLR.blr_1_2_4 / still assumes: [] / axioms: [propext, Classical.choice, Quot.sound]`
  `#discharges: 72 open hypotheses, 84 theorems checked, 1 discharge one`.
- `neronLocalizesDVR_proved := CToPrinted.neronLocalizesDVR_of_printed blr_1_2_4` (no copied proof).
- Fold check, VERIFIED: `autofold.py scratch/gt-blr/autofold-spec.json --dry-run` → scratch/gt-blr/FoldCheck.lean
  (OpenResearchLeaves15 without blr_1_2_4, sixContactMin_of_open19, and a frozenTarget copy over it) compiles,
  standard axioms; strict count 51/15 on 66 -> 51/14 on 65.
- Dev files Dev1.lean / Converse.lean removed (superseded by the contrib file; Converse.lean would now clash with it).
