# gt-blr: done. BLR 1.2/4 proved, field `blr_1_2_4` discharged

**Verdict.** I proved the full field, not just the `.mp` half that was asked for.
`ZInQKernel/Contrib/OneProof/BLRLocalizes.lean` proves `GapBLR.blr_1_2_4 : CToPrinted.BLR_1_2_4` (both directions)
from Mathlib and the chain. There is no sorry and the axioms are the standard three.

`#discharges` (`scratch/gt-blr/Discharges.lean`) reports:

```
DISCHARGES [OpenResearchLeaves14.blr_1_2_4] by GapBLR.blr_1_2_4
  still assumes: []
```

The run checks 72 open hypotheses and 84 theorems; one theorem discharges one hypothesis.

As asked, the `.mp` half is also stated and proved on its own: `GapBLR.BLR_1_2_4_MP` and `GapBLR.blr_1_2_4_mp`.
`GapBLR.neronLocalizesDVR_proved : ReductGlue.NeronLocalizesDVR` now has no hypotheses.

Both directions hold for any commutative ring `R` with fraction field `K`; `IsDedekindDomain` is never used.

**How.**
- Uniqueness: `Y_K → Y` is scheme-theoretically dominant for flat `Y`, and `Y_K` is reduced, so `Y` is reduced. Then
  `ext_of_isDominant_of_isSeparated` applies.
- `.mp`: a smooth affine `V/R_𝔭` spreads out to a smooth `W` over `R[1/s]`, using the EGA IV 8.8.2/17.7.8 proofs
  already in `Contrib/CloudW01Spread`. `W` is smooth over `R` and has generic fibre `V_K`, so the Néron property of
  `X/R` extends the map; then glue. The risk in gap-triage A10 does not arise.
- `.mpr`: extend over `V ⊗ R_𝔭`, then spread the morphism to `V ⊗ R[1/s]` with Mathlib's Stacks 01ZC. The opens
  `V ∩ y⁻¹D(s)` cover `Y`; glue.

**Compiles (VERIFIED).**
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.BLRLocalizes`
  succeeds.
- The fold dry-run (`scratch/gt-blr/autofold-spec.json` → `FoldCheck.lean`) compiles: `OpenResearchLeaves15`,
  `sixContactMin_of_open19`, and the headline without `blr_1_2_4`, all with the standard axioms. The strict GLUE count
  goes from 15 to 14.

**Remains.** The maintainers' fold: run `autofold.py` with the spec, then the hash guard and `render_open.py`. No
consumer needs rerouting, because the field is matched by exact type. The consumer sites are TailZ22 L308 and
TailZ23 L767 and L794. The BLR locators are as recalled (UNVERIFIED), but the proof does not depend on them.
Report: `docs/research/gt-blr.md`.

(Written 2026-11-14 22:05 PST; this file is the task's last commit.)
