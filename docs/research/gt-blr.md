# gt-blr: BLR §1.2 Prop. 4 proved (the open field `blr_1_2_4` is discharged)

**Result (VERIFIED, compiled).** `ZInQKernel/Contrib/OneProof/BLRLocalizes.lean` proves

```lean
theorem GapBLR.blr_1_2_4 : CToPrinted.BLR_1_2_4
```

The theorem covers both directions. It uses only Mathlib and declarations already in the chain, has no `sorry`, and
depends only on the axioms `[propext, Classical.choice, Quot.sound]`. Run as `docs/one-proof/CONTRIBUTING.md`
prescribes (`scratch/gt-blr/Discharges.lean`), `#discharges` reports:

```
DISCHARGES [OpenResearchLeaves14.blr_1_2_4] by GapBLR.blr_1_2_4
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 72 open hypotheses, 84 theorems checked, 1 discharge one
```

So the GLUE field `blr_1_2_4` (`TailZ19.lean` L63, in `OpenResearchLeaves14`) closes outright. It leaves no new leaf
behind. The assigned `.mp` half is proved and also stated separately, as asked:

```lean
def GapBLR.BLR_1_2_4_MP : Prop        -- the binders of CToPrinted.BLR_1_2_4, `↔` replaced by `→`
theorem GapBLR.blr_1_2_4_mp : GapBLR.BLR_1_2_4_MP
theorem GapBLR.blr_1_2_4_mp_of_printed : CToPrinted.BLR_1_2_4 → GapBLR.BLR_1_2_4_MP
theorem GapBLR.neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR   -- no hypotheses
```

Both directions hold for **every commutative ring `R` with fraction field `K`**:
`GapBLR.isNeronModelOver_localization` gives `.mp` at every prime, and `GapBLR.isNeronModelOver_of_local` gives
`.mpr`. The hypothesis `[IsDedekindDomain R]` of the printed statement is never used.

## 1. The statement (checked first, as gap-triage A10 asked)

`CToPrinted.IsNeronModelOver R K X` (TailZ19 L43) says the following. `X` is smooth, separated, locally of finite
type and quasi-compact over `R`. For **every** smooth `R`-scheme `Y`, the map `Hom_R(Y, X) → Hom_K(Y_K, X_K)`,
`f ↦ f_K`, is bijective; here `Y` need not be quasi-compact. `BLR_1_2_4` relates this predicate for `X/R` to the
same predicate for `X ⊗_R R_𝔭 / R_𝔭` at every maximal `𝔭`, where `R_𝔭` is any ring with
`IsLocalization.AtPrime R_𝔭 𝔭` and a compatible map to `K`.

The statement is neither vacuous nor inert, and it is exactly what was proved. The reading risk recorded in
kinds.tsv ("may be printed in the strictly henselian form") does not matter now: the Lean statement is a theorem as
it stands.

The A10 risk does not arise. A10 worried that the `.mp` extension step would need a smooth model of `Y` over all of
`R`. It does not: a scheme smooth over `R[1/s]` is smooth over `R`, because `Spec R[1/s] → Spec R` is an open
immersion. So the Néron property of `X` over `R` applies directly to the spread-out piece, and `.mp` needs none of
the converse's machinery.

## 2. Proof

Throughout, an "`R`-morphism `Y_K → X`" stands for a `K`-morphism `Y_K → X_K`; the two correspond under the pullback.
In Lean all generic fibres are handled through `IsPullback` squares.

**Uniqueness (`uqA`, any base `A ⊆ K`).** Let `W` be smooth over `Spec A`, with `A → K` injective. Then:

* `Spec K → Spec A` is scheme-theoretically dominant, by `isSTD_of_injective`: `A` is reduced, and Mathlib's
  `denseRange_comap_iff_ker_le_nilRadical` applies.
* So `W_K → W` is scheme-theoretically dominant, because it is a flat base change (Mathlib's
  `IsSchemeTheoreticallyDominant.of_isPullback`).
* `W_K` is smooth over a field, hence reduced (the chain's `LeafQM.AV.R1UnivRigid.isReduced_of_smooth`).
* Therefore `W` is reduced (`IsSchemeTheoreticallyDominant.isReduced`).
* Two maps from `W` to a separated `X` that agree on `W_K` are equal (`ext_of_isDominant_of_isSeparated`).

**Gluing (`glue_cover`).** Extensions given on the pieces of an open cover glue by uniqueness on the overlaps.

**`.mp`.**

1. `Spec R_𝔭 = lim_{s ∉ 𝔭} Spec R[1/s]` (`ringCoconeIsColimit`, `specConeIsLimit`). This is new, for general `R`
   and `R_𝔭`; TailZ19 has only the `𝓞_L`/valuation-subring instance `specConeOIsLimit`.
2. Let `V` be smooth and affine over `R_𝔭`. EGA IV 8.8.2(ii) and 17.7.8(ii) give a smooth `W` over some
   `Spec R[1/s]` with `V = W ×_{R[1/s]} R_𝔭` (`exists_spread`). Both results are already proved in the build:
   `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof` and `EGAIV_17_7_8_ii_proof`, in `Contrib/CloudW01Spread`.
3. `W` is smooth over `R`, and its generic fibre is `V_K` (by pasting pullback squares, using that
   `Spec R[1/s] → Spec R` is a monomorphism). The Néron property over `R` therefore extends `V_K → X` to `W`, and
   composing with `V → W` extends it to `V` (`local_ext`, `neron_ext`).
4. Glue over the affine cover of `Y` (`glue_ext`). Bijectivity then follows (`isNeronModelOver_localization`).

**`.mpr`.** Injectivity is `uqA` with `A = R`. For existence near a point `x` of a smooth `R`-scheme `Y`
(`local_pt`):

1. Take an affine open `V ∋ x` and a maximal `𝔭` containing the image of `x`. Put
   `R_𝔭 = Localization.AtPrime 𝔭`, with its map to `K`.
2. The Néron property of `X ⊗ R_𝔭` extends the map on `V ⊗_R R_𝔭` (`neron_ext_loc`).
3. `V ⊗_R R_𝔭 = lim_s V ⊗_R R[1/s]` (`overConeIsLimit`, `bcConeIsLimit`: `Over.pullback` is a right adjoint).
   `X` is locally of finite presentation, so Mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`
   (Stacks 01ZC) factors the extension through some `V ⊗_R R[1/s]`, `s ∉ 𝔭`.
4. Restricting to the open `V ∩ y⁻¹D(s) ∋ x` gives a local extension. Its generic-fibre compatibility is checked by
   explicit pullback bookkeeping.
5. Glue over these opens with `glue_cover` (`isNeronModelOver_of_local`).

## 3. Consumers and the fold

`blr_1_2_4` is discharged by exact type, so the fold is mechanical and no consumer needs rerouting. The consumer
sites that read the field are:

* TailZ22 L308: `blr_1_2_4 := r.blr_1_2_4` (field passing).
* TailZ23 L767: `ss1_ss3_of14`, through `CToPrinted.neronLocalizesDVR_of_printed r.blr_1_2_4`.
* TailZ23 L794: `researchLeaves9_of_open14.semistableNeronBaseChange`, through
  `semistableNeronBaseChange_of_printed_full r.blr_1_2_4`.

In the old generation all three now take `GapBLR.blr_1_2_4`. Every use is `.mp`, through
`CToPrinted.neronLocalizesDVR_of_printed` (TailZ19 L138). In `semistableNeronBaseChange_of_printed_full` (L1650), `hB`
appears only in `have hL := neronLocalizesDVR_of_printed hB`.

Fold spec: `scratch/gt-blr/autofold-spec.json`. Running `autofold.py --dry-run` on it gives
`scratch/gt-blr/FoldCheck.lean`, which adds the generated `OpenResearchLeaves15` (without `blr_1_2_4`) and
`sixContactMin_of_open19`, plus a copy of `frozenTarget` over `OpenResearchLeaves15`. All of it compiles in scratch
with the standard axioms (VERIFIED). The script reports the strict count `51/15 on 66 -> 51/14 on 65`, i.e. one GLUE
field fewer. The fold itself is left to the maintainers; no file outside `Contrib/OneProof/` was edited.

## 4. Files

* `ZInQKernel/Contrib/OneProof/BLRLocalizes.lean` (851 lines, 48 KB; imports only `ZInQKernel.OneProof.Main`).
  Checked with `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.BLRLocalizes`, which succeeds. `lake env lean` on the file prints no warnings.
* `scratch/gt-blr/Discharges.lean`: the `#discharges` run and the axiom checks.
* `scratch/gt-blr/autofold-spec.json` and `scratch/gt-blr/FoldCheck.lean`: the fold check.
* `scratch/gt-blr/log.md`: the results log.

Declarations reused from the chain (none copied):

* `LeafQM.AV.R1UnivRigid.isReduced_of_smooth` (TailZ16)
* `ZInQ.Contrib.SpreadOut.EGAIV_8_8_2_ii_proof`, `EGAIV_17_7_8_ii_proof`, `smooth_of_iso`
* `CToPrinted.IsNeronModelOver`, `BLR_1_2_4`, `neronLocalizesDVR_of_printed`

Locators: BLR, *Néron models*, §1.2 Def. 1 and Prop. 4, as recalled (UNVERIFIED, no network). The proof does not
depend on them, since it proves the Lean statement directly. EGA IV 8.8.2, 17.7.8 and Stacks 01ZC are cited as in the
Contrib files and in Mathlib's `AffineTransitionLimit.lean`.
