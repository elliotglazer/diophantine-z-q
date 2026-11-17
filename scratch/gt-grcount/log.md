# gt-grcount results log

Target: `ShimuraSplit.GonzalezRotgerCountX6Ab` (ZInQKernel/OneProof/H/TailZ17.lean L31), field
`HDec.HSyn.OpenResearchLeaves16.gonzalezRotgerCountX6Ab`, strict GLUE (composite: witness + count).

## Findings (reading)
- VERIFIED (read TailZ9 L97, TailZ23 L804, grep of ZInQKernel): the field's only consumer is
  `r5count := ShimuraSplit.r5fpCount_of_points r.gonzalezRotgerCountX6` (TailZ9); i.e. the chain uses only
  `LeafQM.AV.R5fpCount` (ZInQKernel/HDecomp/QM/Leaves.lean L599); the witness (Y,Φ,X,Ψ,fY) is inert for the chain.
- VERIFIED (read): the count clause of the Ab form depends on the witness only through the bijection Ψ, so
  R5fpCount + any witness of `R1fpPropsAb ∧ X6Props` gives the Ab form (same proof as TailZ8 `points_of_r5fpCount`).
- VERIFIED (read TailZ22 L64): the open LEAF `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (GR 2006 Thm 5.12) supplies
  such a witness; so does `ShimuraGlue.DeligneComponentsX6PrintedAb` (TailZ22 L33).
- Finite computation? NO: R5fpCount quantifies over all imaginary quadratic orders R (h(R) unbounded) and its
  left side counts isomorphism classes of QM abelian surfaces over Qbar; nothing to `decide`. The only
  finite/arithmetic content is the local factor: 2^{inertCount6 k} = ∏_{p|6}(1-(k/p)) when no p|6 splits
  (Eichler's local optimal-embedding numbers), which is glue (proved below).

## Lean (ZInQKernel/Contrib/OneProof/GRCountX6.lean, namespace GRCountX6)
- Needed: `lean/.lake` reflink-copied from ~/dzq-wt/gt-blr (identical lean/ZInQ) — else "unknown module prefix 'ZInQ'".
- `lake env lean ZInQKernel/Contrib/OneProof/GRCountX6.lean`: 0 errors (after one fix in `conjRel_equivalence.symm`). VERIFIED.
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GRCountX6`:
  success (12926 jobs, 8.5 min); frozenTarget standard axioms. VERIFIED.
- `#discharges` (scratch/gt-grcount/Discharges.lean, output discharges_output.txt): VERIFIED
  - gonzalezRotgerCountX6Ab_of_printed: still assumes [GonzalezRotgerProp56X6, GonzalezRotgerX6Ab]
  - gonzalezRotgerCountX6Ab_of_printed': [GonzalezRotgerProp56X6, DeligneComponentsX6PrintedAb]
  - gonzalezRotgerCountX6Ab_of_r5fpCount: [R5fpCount, GonzalezRotgerX6Ab]
  - gonzalezRotgerCountX6Ab_of_eichler: [EichlerOptEmbCount6, CMPointsOptEmb6, GonzalezRotgerX6Ab]
  - all axioms [propext, Classical.choice, Quot.sound]; "67 open hypotheses, 511 theorems checked, 4 discharge one".
- Also compiled: prop56X6_of_r5fpCount (R5fpCount → new leaf, outright), r5fpCount_of_prop56X6 (converse given
  GonzalezRotgerX6Ab), eichlerFactor6_eq (2-adic/3-adic local factors = 2^inertCount6 when nonzero),
  conjRel_equivalence, one_add_i_mem_units ((1+i)(−1+i) = 1, nrd(1+i) = −1 in O ⊂ (2,−3)), r5fpCount_of_eichler.
- Fold check: `autofold.py scratch/gt-grcount/autofold-spec.json --dry-run` → strictest 45/16 → 46/15 (lenient 47/14
  unchanged); generated module saved as scratch/gt-grcount/FoldCheck.lean, compiles, sixContactMin_of_open21
  standard axioms. VERIFIED.

## Statement checks (consistency, not proofs)
- E (Eichler, O^×-classes) and M (CM points ↔ O^×-classes) self-consistent with: the reviewed Elkies fibres
  (2,2,2 points at discs −4,−3,−24), locators.md (4 points at disc −19), and the D=1 case (forms mod GL2(Z) = h).
  SPECULATIVE-to-STANDARD (argument checked by hand; theorem numbers UNVERIFIED).
