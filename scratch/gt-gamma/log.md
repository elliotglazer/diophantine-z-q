# gt-gamma results log

Target: `HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea` (TailZ2 L93), no hypotheses.

## Plan (fixed 11-14 21:45)
- p = i√3 (`tau3`, order-6 point of Γ*). F(z) = |z−p|²/Im z, cosh d(z,p) = 1 + F/(2√3).
- Key identity (VERIFIED, compiled `Fp_smul`): for g with matrix ι(y), nrd y > 0,
  F(g z) = F(z) + Φ_y(z)/(nrd(y) Im z), Φ_y = P(U+6) + 2√2(RU − SX), U = |z|²−3, X = 6 Re z,
  P = 4a1²+12a3², R = a0a1−3a2a3, S = a0a3+a1a2.
- T = {X ≤ U, −X ≤ U, U ≤ 6+6√2}: geodesic triangle i√3, ±(1+√2)+i(2+√2) (angles π/3, π/4, π/4).
- Dirichlet property on T ⟸ vertex condition 2P' + R' ∓ S' ≥ 0 (integers A_i = 2a_i);
  Cauchy–Schwarz if A1²+3A3² ≥ 4n, finite enumeration otherwise (python: 84 small cases, 0 bad; VERIFIED).
- Covering: orbit point nearest p (finiteness from cosh d(p, ι(y)p) = 1 + P/n), rotate into the cone
  by the stabilizer, then the bisector with ι(μ)p gives |w|² ≤ 9+6√2.
- Disjointness: on T ∩ γ⁻¹T, Φ_y = 0 (a circle, null) unless P = 0 (stabilizer: cone rays, null).
- Area: Tonelli, ∫ dy/y², arcsin antiderivatives; = 2(π/3 − π/4) = π/6 (numerically VERIFIED).

## Compile log
- 11-14 21:50 GS.lean part 1-2 (Fp_smul, dist_smul_pos, cover_y, finite_O, finite_mob,
  properlyDiscontinuous, exists_min): compiles, no errors (lake env lean, ~8 s).
- 11-14 21:20 GS.lean parts 3-4: cone step, sigma=ι(μ) ∈ Γ*, covering `cover_T`, vertex condition `intV` (C–S + enumeration), `Phi_nonneg`, Dirichlet property `dirichlet`: compile (~19 s).
- 11-14 21:45 GS.lean complete: `HDec.GammaStarArea.gammaStarCocompactArea_proof : HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea` compiles over TailZ3; #print axioms: [propext, Classical.choice, Quot.sound] (VERIFIED, ~19 s).
- 11-14 21:55 contribution file ZInQKernel/Contrib/OneProof/GammaStarArea.lean compiles over Main (lake env lean, no errors).
- 11-14 21:57 first `lake build` started rebuilding ~82 modules of Main's closure that import the upstream `lean/`
  package (the copied lean/.lake from leaf-fold14 has other trace paths); interrupted, which deleted 5 oleans
  (TYZGenus.Package, RingClassGalois, PoleValuationsAux, LocalCongruence, Size.Majorants.Bound); restarted the
  full `lake build +Main +Discharges +GammaStarArea` (sibling worktrees gt-blr/gt-ega did the same rebuild).
- statement.lean: verbatim copies of GammaStarCocompactArea (TailZ2 L46-95) and ShimizuCovolumeO1 (L1007-1020).
- 11-14 22:40 lake build +Main +Discharges +GammaStarArea: Build completed successfully (12920 jobs), exit 0 (VERIFIED).
- 11-14 22:45 Shimizu.lean: `shimizuCovolumeO1_proof : HM.QMSplit.ShimizuCovolumeO1` compiles, standard axioms
  (VERIFIED); appended to the contribution file; module rebuilt (lake build, success).
- 11-14 22:47 #discharges (scratch/gt-gamma/Discharges.lean): "DISCHARGES [OpenAddedLeaves13.shimizuCovolumeO1] by
  HDec.GammaStarArea.shimizuCovolumeO1_proof; still assumes: []; axioms: [propext, Classical.choice, Quot.sound];
  72 open hypotheses, 204 theorems checked, 1 discharge one" (VERIFIED).
