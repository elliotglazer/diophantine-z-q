# gt-gamma (done)

**Result: both statements proved in Lean with no hypotheses and only the standard axioms.**

- `HDec.GammaStarArea.gammaStarCocompactArea_proof : HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea`
  (`Γ*` is cocompact Fuchsian with a fundamental domain of area `π/6`).
- `HDec.GammaStarArea.shimizuCovolumeO1_proof : HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1`
  (the open published leaf `shimizuCovolumeO1`: `Γ¹ = ι(𝒪¹)`, covolume `2π/3`).

File: `ZInQKernel/Contrib/OneProof/GammaStarArea.lean` (imports `ZInQKernel.OneProof.Main` only, ~65 KB).
Fundamental domain: the geodesic triangle `i√3, ±(1+√2)+i(2+√2)`. The proof: an exact formula for
`F(ι(y)w) − F(w)`, where `F` measures distance to `i√3`, gives finiteness, proper discontinuity, a covering by the
orbit point nearest `i√3`, the Dirichlet property (an integer vertex inequality: Cauchy–Schwarz plus a small
enumeration) and a.e. disjointness (circles are null). The area is a Tonelli computation with arcsin antiderivatives.
For `Γ¹` the domain is the four coset translates.

Checks (VERIFIED):
- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GammaStarArea`
  completed successfully.
- `#discharges`: `DISCHARGES [OpenAddedLeaves13.shimizuCovolumeO1] by HDec.GammaStarArea.shimizuCovolumeO1_proof`,
  still assumes `[]`, axioms `[propext, Classical.choice, Quot.sound]`; 72 open, 1 discharged.

Remaining: only the fold. `autofold.py` can fill the field `shimizuCovolumeO1` mechanically (71 open after).
Alternative reroutes `valenceFormulaGammaStar_noShimizu` and `qmHauptmodulBase3_noShimizu` are given for TailZ4 L237/L249.
Report: `docs/research/gt-gamma.md`. Scratch, numerics and log: `scratch/gt-gamma/`.
