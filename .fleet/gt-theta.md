# gt-theta

**Result: both open hypotheses `igusaPsi4` and `igusaChi10` are proved in Lean as stated, with no hypotheses.**
`GapTheta.igusaPsi4_proof : HDec.QMSplit.Theta.IgusaPsi4` and `GapTheta.igusaChi10_proof :
HDec.QMSplit.Theta.IgusaChi10` (and `thetaModularity_proof : HDec.PkgI1.ThetaModularity`) are in
`ZInQKernel/Contrib/OneProof/ThetaModularityM46.lean` (imports `ZInQKernel.OneProof.Main`; 81 KB). Only the
standard axioms are used.

`#discharges` (scratch/gt-theta/discharges_out.txt):
`DISCHARGES [OpenResearchLeaves14.igusaChi10] by GapTheta.igusaChi10_proof`, the same for `igusaPsi4`, each with
`still assumes: []` and axioms `[propext, Classical.choice, Quot.sound]`; overall
`72 open hypotheses, 204 theorems checked, 2 discharge one`.

The proof uses no Siegel modular form theory. Its parts:
* theta transformations under translations, rotations and the genus-2 partial inversion (cm24-value's `pi0`, i.e.
  Mathlib's `jacobiTheta₂_functional_equation`), on squares of theta constants with real characteristics;
* characteristic permutations and phases checked by `decide`;
* the `spAct`/`spFactor` cocycle;
* an explicit proof that `Sp₄(ℤ)` is generated, as a monoid, by eleven matrices (Bezout in `SL₂(ℤ)`, the
  stabilizer of `e₁`, and Mathlib's `SL2Z_generators`).

The task's specialized target, gap-triage A2's `GapTheta.ThetaModularityM46`, is proved too, at every point of the
Siegel space. So are its consumer forms `s8WeightExact_of'`, `s20WeightExact_of'` and the `GammaStarGen`-only
`s8WeightExact_of_gen`, `s20WeightExact_of_gen`. They are no longer needed for the fold.

What compiles: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.ThetaModularityM46` succeeds, and the module builds in 38 s.

What remains: the fold, done by the maintainers. Run autofold with the two fields discharged by the two theorems.
No consumer rerouting and no new leaf are needed, and the strict LEAF count drops by 2. The specialization route's
consumer sites, which no longer need changing, are listed in docs/research/gt-theta.md §3.

Report: docs/research/gt-theta.md. Log: scratch/gt-theta/log.md.
