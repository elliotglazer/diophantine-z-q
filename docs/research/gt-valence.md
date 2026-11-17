# gt-valence: the valence formula for a cocompact Fuchsian group, proved with no hypotheses

## 1. Result

**Proved in Lean, in full generality, no hypotheses, standard axioms only** (VERIFIED: compiled with
`lake build +ZInQKernel.Contrib.OneProof.ValenceCocompact`; `#discharges` output in section 5):

```lean
theorem ValenceCocompact.valenceFormulaCocompactEq_proof :
    HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq
```

in `ZInQKernel/Contrib/OneProof/ValenceCocompact.lean` (92 KB, 1760 lines; imports only
`ZInQKernel.OneProof.H.TailZ2`, the module defining the statement, which already imports all of Mathlib). The
statement is the chain's own constant (TailZ2 L76, copied verbatim with its dependencies in
`scratch/gt-valence/statement.lean`): for every `Γ ⊆ GL₂(ℝ)` satisfying `IsCocompactFuchsian`, every `s`
with `IsFundDomain Γ s`, every `m` and every `F` analytic and not identically zero on `ℍ` with norm automorphy
`‖F(γz)‖ det(γ)^m = |cz+d|^{2m} ‖F(z)‖`:
(1) a finite pairwise-inequivalent set `T` covers the zeros; (2) for every such `T`,
`Σ_{z∈T} ord_z(F)/e_z = 2m·vol(s)/(4π)`; (3) for every pairwise-inequivalent `T`, `≤`.

So the open LEAF `valenceFormulaCocompactEq` (bundle field `HDec.HSyn.OpenAddedLeaves14.valenceFormulaCocompactEq`,
OPEN.md row 52) is closed. No reroute is needed: the general statement is proved, so a fold just fills the field
with `ValenceCocompact.valenceFormulaCocompactEq_proof` and adds no new leaves.

## 2. Checks on the statement (before proving it)

* VERIFIED (read): `MeasureTheory.volume` on `UpperHalfPlane` is Mathlib's `dx dy / y²`
  (`Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean`, `volume_def`), and Mathlib proves
  `SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ volume`. So `vol(s)` is the hyperbolic area and the statement is the
  genuine valence formula: not vacuous, not stronger than Shimura's.
* `ellOrderOf` counts Möbius maps (not matrices), so scalar matrices and `−1` in `Γ` are handled correctly;
  the norm form of automorphy is exactly a unitary multiplier system of weight `2m`.
* Consumers (VERIFIED, grep): TailZ2 `val_le`, `val_eq`, `val_ex`; TailZ3 `valenceFormulaGammaStar_of_leaves`,
  `qmHauptmodulBase3_of_leaves`; GammaStarArea `valenceFormulaGammaStar_noShimizu`,
  `qmHauptmodulBase3_noShimizu`. All use `Γ = Γ*`, but the proof below is uniform in `Γ`, so the general
  statement was proved and no consumer needs rerouting.

## 3. The proof (boundary-free)

The textbook proof integrates `d log F` around a fundamental polygon. The Lean proof avoids polygons, side
pairings and boundary integrals; it needs only the abstract `IsFundDomain` and proper discontinuity.

1. **Group of maps** (Part B1). `Γ̄ := image of Γ in Perm ℍ` (`permG (subG hΓ)`); measurable, measure
   preserving (from Mathlib's `GL(2,ℝ)` invariance), countable (proper discontinuity and σ-compactness),
   `s` is a Mathlib `IsFundamentalDomain` for it, `Nat.card (stabilizer t) = ellOrderOf Γ t`.
2. **Automorphic partition of unity** (Part B2, `exists_partition`). A `C²` function `ψ ≥ 0`, compactly
   supported in `ℍ`, equal to `1` on the compact set `C` of `cocompact` (Mathlib's
   `exists_contMDiffMap_zero_one_of_isClosed`); `Ψ(z) = Σ_{g∈Γ̄} ψ(gz)` is a locally finite sum (proper
   discontinuity), `≥ 1`, `Γ̄`-invariant; `χ = ψ/Ψ` is `C²`, compactly supported in `ℍ`, with
   `Σ_{g∈Γ̄} χ(gz) = 1` for all `z`.
3. **Riesz identity** (Parts A1-A5, `integral_log_norm_analytic`). For `F` analytic, not identically zero on a
   preconnected open `U`, and `χ ∈ C²_c(U)`: `∫_ℂ log|F| Δχ = 2π Σ_ρ ord_ρ(F) χ(ρ)`. Ingredients: Green's
   identity `∫ f Δχ = ∫ Δf χ` for `f ∈ C²(V)`, `V ⊇ supp χ` (two applications of Mathlib's
   `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`); the fundamental solution
   `∫ log|x−u| Δχ = 2π χ(u)` (regularize `½ log(|x−u|²+ε²)`, whose Laplacian is `2ε²/(|x−u|²+ε²)²`; rescale;
   dominated convergence both sides, using local integrability of `log|x|` from
   `integrableOn_ball_of_norm_le_rpow` and `∫_ℂ 2/(1+|z|²)² = 2π` from `integral_fun_norm_addHaar`); Mathlib's
   `MeromorphicOn.extract_zeros_poles_log` (`log|F| = Σ ord_u log|·−u| + log|g|` off a codiscrete set, hence
   a.e. by `ae_restrict_le_codiscreteWithin`); `log|g|` harmonic (`AnalyticAt.harmonicAt_log_norm`).
4. **Conformal invariance** (Part A6, `laplacian_comp_holomorphic`). `Δ(χ∘φ)(z) = |φ'(z)|² Δχ(φz)` for
   holomorphic `φ` (second-order chain rule; the rotation identity `B(a,a)+B(ia,ia) = |a|²(B(1,1)+B(i,i))`
   for real bilinear `B`); for Möbius maps `|γ'(z)|² y² = Im(γz)²`, so `y²Δ` commutes with `Γ`.
5. **Cancellation** (Part B4, `integral_invariant_laplacian`). For a `Γ̄`-invariant `Φ` with `ΦΔχ` integrable,
   `∫_ℂ ΦΔχ = 0`: convert to `∫_ℍ Φ·y²Δχ dμ`, insert `1 = Σ_{g∈S} χ(gz)` (`S` finite) on the support, move each
   `g` across with the invariant measure, use `y²Δχ(g⁻¹z) = y²Δ(χ∘g⁻¹)(z)`, and sum back:
   `Σ_{g∈S} χ∘g⁻¹ ≡ 1` near the support, so its Laplacian vanishes. Only finite sums occur.
6. **Valence identity** (Part B5, `main_identity`). `Φ = log(|F| y^m)` is exactly invariant (also at zeros);
   `Φ = log|F| + m log y` a.e.; `Δ log y = −1/y²`; `∫_ℂ χ/y² = ∫_ℍ χ dμ = vol(s)` by
   `IsFundamentalDomain.lintegral_eq_tsum'` and `Σ_g χ(g⁻¹z) = 1`. Hence `2π Σ_ρ ord_ρ χ(ρ) = m·vol(s)`
   and `vol(s) < ∞`.
7. **Orbit counting** (Parts B6-B7). Orders are constant on orbits (`ord_smul_eq`: norm automorphy plus
   `analyticOrderAt_comp_of_deriv_ne_zero` and a norm-comparison lemma for orders); orbit-stabilizer with the
   fibres of `g ↦ gt` gives `e_t Σ_{ρ∈Γt} χ(ρ) = 1`; orbits of a pairwise-inequivalent `T` are disjoint, so
   `Σ_{t∈T} ord_t/e_t ≤ Σ_ρ ord_ρ χ(ρ)`, with equality when `T` covers the zeros.
8. **Assembly** (Part B8). Representatives `T` (zeros in the compact `C` are finite; one per class by
   `Classical.epsilon`), and the conversion to the `ℝ≥0∞` form of the statement.

## 4. What compiles

* `ZInQKernel/Contrib/OneProof/ValenceCocompact.lean`: VERIFIED, `lake build
  +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ValenceCocompact`
  succeeds (11 s for the new module); axioms `[propext, Classical.choice, Quot.sound]`.
* The development modules `scratch/gt-valence/VC/A1.lean` … `B8.lean` (the same code, split; compiled with
  `scratch/gt-valence/mk.sh NAME`, which writes `.olean`s under `scratch/gt-valence/build/`, git-ignored). The
  contribution file is their concatenation (`import`/`noncomputable section` lines merged).
* No other file under `ZInQKernel/` was edited.

## 5. `#discharges` (VERIFIED, `scratch/gt-valence/Discharges.lean`, output in
`scratch/gt-valence/discharges-output.txt`)

```
DISCHARGES [OpenAddedLeaves14.valenceFormulaCocompactEq] by ValenceCocompact.valenceFormulaCocompactEq_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 653 theorems checked, 1 discharge one
```

## 6. For the fold

* Fill `valenceFormulaCocompactEq` with `ValenceCocompact.valenceFormulaCocompactEq_proof`; no leaves added,
  the strict LEAF count drops by one.
* The contribution imports `ZInQKernel.OneProof.H.TailZ2` only (not Main, not TailZ24), so there is no import
  cycle; all declarations live in the new namespace `ValenceCocompact` (no clash found: the build of Main's
  closure plus this module and `#discharges` succeed together).
* Together with gt-gamma's `gammaStarCocompactArea_proof`, the rows H-87 (`VB.ValenceFormulaGammaStar`, via
  `valenceFormulaGammaStar_noShimizu`) and the valence part of H-88 now rest on no hypothesis.
