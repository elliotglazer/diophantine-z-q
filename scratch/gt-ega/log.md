# gt-ega results log

Target: `CToPrinted.EGAIV_8_10_5_openImm` (ZInQKernel/OneProof/H/TailZ19.lean L281; field
`HDec.HSyn.OpenResearchLeaves14.egaIV_8_10_5_openImm`).

## Library (VERIFIED by reading source)
- Mathlib `AlgebraicGeometry.exists_preimage_eq` (AffineTransitionLimit.lean L338, Stacks 01Z4(1)),
  `exists_map_preimage_le_map_preimage` (L269), `Scheme.compactSpace_of_isLimit` (L365).
- CloudW01 `exists_isIso_baseChange_of_isIso_limitBaseChange` (…/DescendingMorphisms/Isomorphism.lean L180, Stacks 081E),
  `baseChangeConeIsLimit`, `baseChangeMap`, `baseChangeCone_π_isPullback`, `baseChangeDiagramMap_isPullback`,
  `baseChangeMap_prop_iff` (BaseChange.lean); `locallyOfFinitePresentation_of_comp` (Morphisms/FinitePresentation/Basic.lean, Stacks 02FV).
- `#discharges` (scratch/gt-ega/Discharges.lean, VERIFIED): DISCHARGES [OpenResearchLeaves14.egaIV_8_10_5_openImm] by ZInQ.Contrib.EGAOpenImm.egaIV_8_10_5_openImm_proof; still assumes: []; axioms: [propext, Classical.choice, Quot.sound]; "72 open hypotheses, 2 theorems checked, 1 discharge one" (the second checked theorem is the general lemma exists_isOpenImmersion_baseChange).
- Fold (VERIFIED): `python3 scripts/one_proof/autofold.py scratch/gt-ega/autofold.json` -> "strict count: 51/15 on 66 -> 50/15 on 65;
  strictest 49/17 -> 48/17"; wrote ZInQKernel/OneProof/H/TailZ25.lean (OpenResearchLeaves15, sixContactMin_of_open19), Main.lean, kinds.tsv
  (claims.tsv had no row for the field: unchanged).
- FINDING: with the contribution importing `ZInQKernel.OneProof.Main` (as CONTRIBUTING.md suggests first), the fold makes a build cycle
  (Main -> TailZ25 -> EGAOpenImm -> Main; lake: "build cycle detected"). Fixed by importing the defining module
  `ZInQKernel.OneProof.H.TailZ19` instead (CONTRIBUTING's alternative). autofold.py does not detect this.
- `lake build +ZInQKernel.OneProof.Main` (VERIFIED): success; `sixContactMin_of_open19` and `ZInQ.OneProof.frozenTarget` depend on axioms
  [propext, Classical.choice, Quot.sound].
- Hash guard (VERIFIED; scratch/gt-ega/DumpCompact.lean, cmp_hashes.py = copies of scratch/one-proof's writing into scratch/gt-ega/):
  before 13393, after 13434, only before 0, only after 41 (OpenResearchLeaves15 and its 38 projections/recursors, mk, casesOn …,
  openResearchLeaves14_of_OpenResearchLeaves15, sixContactMin_of_open19), changed 1: ZInQ.OneProof.frozenTarget.
- OpenStatements.lean (VERIFIED): "wrote docs/one-proof/open-statements.json: 71 open hypotheses"; render_open.py --check: "ok: 65 bundle
  fields, all classified"; render_open.py: "wrote docs/one-proof/OPEN.md: 65 H hypotheses, strictest 48/17, 6 others".
