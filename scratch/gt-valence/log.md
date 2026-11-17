# gt-valence results log

Target: `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` (ZInQKernel/OneProof/H/TailZ2.lean L76).
Verbatim copy with dependencies: scratch/gt-valence/statement.lean.

## Findings
- VERIFIED (read): `MeasureTheory.volume` on `UpperHalfPlane` is Mathlib's `dx dy / y^2` measure
  (Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean, `volume_def`), with
  `SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume`. So `vol(s)` in the statement is the hyperbolic area and
  the statement is the genuine valence formula (no vacuity, no mismatch).
- VERIFIED (grep): consumers of the field are only TailZ2 `val_le`, `val_eq`, `val_ex` (for `Γ*`, exact
  automorphy via `abs_auto`), TailZ3 `valenceFormulaGammaStar_of_leaves`, `qmHauptmodulBase3_of_leaves`, and
  GammaStarArea `valenceFormulaGammaStar_noShimizu`, `qmHauptmodulBase3_noShimizu`; all at `Γ = Γ*`.
- Plan: prove the general statement (no reroute needed) by a boundary-free argument: automorphic partition of
  unity `χ` (Σ_γ χ∘γ = 1, compact support), the Riesz identity `∫ log|F| Δχ = 2π Σ ord_ρ χ(ρ)`, conformal
  invariance of `y²Δ`, and `∫_ℍ χ dμ = vol(s)` from the fundamental domain.

## Compiled (lean -o, module VC.*, scratch/gt-valence/mk.sh)
- VC/A1: `integral_mul_laplacian` (Green: ∫ f Δχ = ∫ Δf χ, f C² on open V ⊇ tsupport χ). COMPILED.
- VC/A2: `laplacian_ureg` (Δ ½log(|x|²+ε²) = 2ε²/(|x|²+ε²)²), `laplacian_log_im` (Δ log Im = −1/Im²). COMPILED.
- VC/A3: `locallyIntegrable_log_norm`, `integral_radial` (∫_ℂ 2/(|z|²+1)² = 2π). COMPILED.
- VC/A4: `integral_log_norm_sub_laplacian` (∫ log|x−u| Δχ = 2π χ(u), regularization + dominated convergence). COMPILED.
- VC/A5: `integral_log_norm_analytic` (∫ log|F| Δχ = 2π Σᶠ ord_z(F) χ(z), via Mathlib's extract_zeros_poles_log). COMPILED.
- VC/A6: `laplacian_comp_holomorphic` (Δ(χ∘φ) = |φ'|² Δχ∘φ). COMPILED.
- VC/B1: Möbius maps `mob`, `im_sq_laplacian_comp_mob`; group `permG (subG hΓ)` ⊆ Perm ℍ, measurable and
  measure-preserving instances, `countable_G`, `isFundamentalDomain`, `card_stabilizer`. COMPILED.
- VC/B2: `exists_partition` (automorphic partition of unity). COMPILED.
- VC/B3: `integral_H`/`integrable_H` (∫_ℍ f y² dμ = ∫_ℂ f), `lintegral_chi` (∫_ℍ χ dμ = vol s). COMPILED.
- VC/B4: `integral_invariant_laplacian` (∫ ΦΔχ = 0 for Γ-invariant Φ). COMPILED.
- VC/B5: `main_identity` (2π Σ ord χ = m vol s, vol s < ∞). COMPILED.
- VC/B6: `ord_eq_of_norm`, `ord_smul_eq` (orders constant on orbits). COMPILED.
- VC/B7: `orbit_sum`, `orbit_count`. COMPILED.
- VC/B8: `valenceFormulaCocompactEq_proof : HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq`.
  COMPILED, axioms [propext, Classical.choice, Quot.sound].

## Contribution
- ZInQKernel/Contrib/OneProof/ValenceCocompact.lean = concatenation of VC/A1..B8, imports TailZ2 only.
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ValenceCocompact`:
  Build completed successfully. VERIFIED.
- #discharges (scratch/gt-valence/Discharges.lean): DISCHARGES [OpenAddedLeaves14.valenceFormulaCocompactEq]
  by ValenceCocompact.valenceFormulaCocompactEq_proof; still assumes: []; axioms standard. VERIFIED.
- Note: lean/.lake/build was missing in this worktree (unknown module prefix 'ZInQ'); copied from ~/dzq-lf16
  (lean/ sources identical by diff -rq).
