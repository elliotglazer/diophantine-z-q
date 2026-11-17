# gt-ega: EGA IV 8.10.5 (open immersions) proved and folded

**Result (VERIFIED, compiled).** `ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof : CToPrinted.EGAIV_8_10_5_openImm`
(`ZInQKernel/Contrib/OneProof/EGAOpenImm.lean`) proves the LEAF field `egaIV_8_10_5_openImm` of `OpenResearchLeaves14`
with no hypotheses and only `propext`, `Classical.choice`, `Quot.sound`, from Mathlib (Stacks 01Z4: `exists_preimage_eq`,
`exists_map_preimage_le_map_preimage`) and the vendored CloudW01Spread (Stacks 081E
`exists_isIso_baseChange_of_isIso_limitBaseChange`, `baseChangeConeIsLimit`/`baseChangeMap` squares, 02FV(1)). Statement
unchanged; it is neither false nor vacuous. Proof: descend the quasi-compact image `U` to `V ⊆ Y_a`; make `f_b⁻¹V_b = X_b`
at a later stage; the factor `X_b → V_b` is an isomorphism at the limit, so by 081E (on the diagram `Y_•`) at some stage `d`,
where `f_d` is then an open immersion.

**#discharges**: `DISCHARGES [OpenResearchLeaves14.egaIV_8_10_5_openImm] … still assumes: [] axioms: [propext,
Classical.choice, Quot.sound]`.

**Folded** with autofold.py: `ZInQKernel/OneProof/H/TailZ25.lean` (`sixContactMin_of_open19`), Main switched; build OK,
`frozenTarget` standard axioms; hash guard: only `frozenTarget` changed (41 new constants); OPEN.md regenerated: 72 → 71
open hypotheses (H fields 66 → 65, strictest 49/17 → 48/17).

**Finding for the contributor kit:** a contribution importing `ZInQKernel.OneProof.Main` (CONTRIBUTING's first suggestion)
creates a build cycle once folded (Main → TailZ25 → contribution → Main); autofold.py does not catch it. Import the
module defining the statement instead (done here: TailZ19).

Remains: nothing for this target. Report: docs/research/gt-ega.md; log and scratch: scratch/gt-ega/.
