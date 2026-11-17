# agent-A2: group A′ (Fuchsian groups, theta functions, Siegel modular forms of genus 2)

Base e38375b3. This pass was read-only, with no Lean or lake run. Branch heads read: origin/wip/cm24-value
d8d1363a, origin/wip/theta-split b285cb60 (an ancestor of base, so it is already in the tree),
origin/wip/theta-glue 336ec1fd, origin/wip/w63 b5ff0474. "VERIFIED-READ" means I opened the file and saw the
statement.

## Headline

The field pair `valenceFormulaCocompactEq` + `shimizuCovolumeO1` is consumed only through **one group (Γ\*) and
one number (Σ ord/e = m/12)**. Both fields can be replaced by the single Γ\*-specific statement
`ValenceFormulaGammaStarEq` (§1.2). The covolume then disappears from the interface.

`igusaPsi4` and `igusaChi10` are consumed only at **two explicit matrices M4, M6 ∈ Sp₄(ℤ)**, at Ω = Ω(z) on the QM
curve. cm24-value's general partial-inversion lemma `pi0` and theta-glue's summability bound make this
specialized form tractable (T1–T2).

---

## 1. valenceFormulaCocompactEq

### 1.1 Identity
- Field `valenceFormulaCocompactEq : LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq`, declared in
  `OpenAddedLeaves9` (ZInQKernel/OneProof/H/TailZ13.lean:32) and `OpenAddedLeaves8` (TailZ4.lean:148).
- Constant `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq`, def at ZInQKernel/OneProof/H/TailZ2.lean:76.
  - Helpers: `IsCocompactFuchsian` (l.47), `IsFundDomain` (l.57, Mathlib's `volume` on ℍ), `Covers` (l.63),
    `ellOrderOf` (l.44).
- Frontier r5 row: **H-135**.
- Form: LEAF, published form (Shimura 1971 Prop. 2.16 / Thm 2.20; Rankin Thm 4.1.4; UNVERIFIED locators)
  (leaf-fold10 §2 l.265).
- Statement: for every Γ ⊆ GL₂(ℝ) with `IsCocompactFuchsian Γ`, every s with `IsFundDomain Γ s`, and every
  analytic F ≢ 0 on ℍ with `‖F(γz)‖·det^m = ‖cz+d‖^{2m}‖F(z)‖`:
  - the zeros lie in finitely many orbits;
  - Σ_T ord/e = 2m·vol(s)/(4π) for a covering set T of representatives;
  - the sum is ≤ 2m·vol(s)/(4π) for any inequivalent finite T.

### 1.2 Use
Chain:
- `OpenAddedLeaves9` → `addedLeaves8_of_open9` (TailZ13:60) → `addedLeaves7_of_open8` (TailZ4:234). There the
  field is used twice:
  - (i) TailZ4:236-238: `qmHauptmodulBase3 := qmHauptmodulBase3_of_leaves (thetaModularity_of r.igusaPsi4
    r.igusaChi10) l.valenceFormulaCocompactEq l.shimizuCovolumeO1 l.igusaCMValue24`.
  - (ii) TailZ4:248-249: `valenceFormulaGammaStar := valenceFormulaGammaStar_of_leaves l.valenceFormulaCocompactEq
    l.shimizuCovolumeO1`.
- `qmHauptmodulBase3_of_leaves` (TailZ3:1211) → `qmHauptmodulBase3_of_shimizu` (TailZ2:1489) →
  `qmHauptmodulBase3_of'` / `qmHauptmodulBase3_of` (TailZ2:992, 768).
- `valenceFormulaGammaStar_of_leaves` (TailZ3:1196) → `valenceFormulaGammaStar_of_eq` (TailZ2:998) →
  `VB.ValenceFormulaGammaStar` (TailO:491). Downstream: `VB.valenceBound_of_formula` (TailO:930) →
  `ValenceBoundGammaStar` (TailJ:396), consumed by `base2_of_base3` (TailO:2461; used at TailO:2971 in
  `qmHauptmodul_of6`) and `qmDenZeroCM3_of''` (TailJ:1115).

Every application of hV (VERIFIED-READ) has Γ = `PkgI1.GammaStar` with hA = `GammaStarCocompactArea` (vol π/6),
so the right side is always m/12 (`arith`). The functions F are:
- `val_le` with F = G8 (m=4): `tau3_facts` (TailZ2:306) and `G8_zero_orbit` (l.333).
- `val_le` with F = G20 (m=10): `G20_tau3_le` (l.419).
- `val_ex` and `val_eq` with F = H_c = 3779136·G20² − c·G8⁵ (m=20), for **every** c ∈ ℂ: `fibre_c` (l.504, 524).
- `ValenceBoundGammaStar` with F = G20: base2_of_base3 at TailO:2475+55.
- `ValenceBoundGammaStar` with F = G8: qmDenZeroCM3, via S8.

**Use (b).** Only Γ\*, the image of N_B(𝒪)⁺ for B = (2,−3 | ℚ), and only F ∈ ℂ[G8, G20] of exact automorphy (`Auto m F`,
TailZ2:132). Weakest statement serving all uses (implied by the leaf together with `GammaStarCocompactArea`, as
`valenceFormulaGammaStar_of_eq` already shows):

```lean
/-- Valence formula for Γ* only: Shimura Thm 2.20 with signature (0;2,4,6) (Takeuchi 1977), or with vol = π/6. -/
def ValenceFormulaGammaStarEq : Prop :=
  ∀ (m : ℕ) (F : ℂ → ℂ), AnalyticOnNhd ℂ F U → (∃ z ∈ U, F z ≠ 0) → Auto m F →   -- exact automorphy for Γs
    (∃ T : Finset ℍ, (T : Set ℍ).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) ∧ Covers Γs T F) ∧
    (∀ T : Finset ℍ, (T : Set ℍ).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) → Covers Γs T F →
       ∑ z ∈ T, ((analyticOrderAt F z : ℕ∞) : ℝ≥0∞) / (VB.ellOrder z : ℝ≥0∞) = (m : ℝ≥0∞) / 12) ∧
    (∀ T : Finset ℍ, (T : Set ℍ).Pairwise (fun z w => ∀ γ ∈ Γs, γ • z ≠ w) →
       ∑ z ∈ T, ((analyticOrderAt F z : ℕ∞) : ℝ≥0∞) / (VB.ellOrder z : ℝ≥0∞) ≤ (m : ℝ≥0∞) / 12)
```

- Using `Auto` instead of the absolute-value hypothesis makes the statement weaker still. It is fine:
  `abs_auto` (TailZ2:152) converts.
- This one statement replaces **both** `valenceFormulaCocompactEq` and `shimizuCovolumeO1`. hA is used only
  inside these applications (val_le/val_eq/val_ex and valenceFormulaGammaStar_of_eq).
- One could restrict further to F ∈ {G8, G20, H_c}. The proof would not get easier, because H_c ranges over
  all c.
- It is still deep: a computation plus a published statement, where the analytic core is the valence formula
  for one fixed group.

### 1.3 Library coverage
- Mathlib `UpperHalfPlane` measure: `instance : MeasureSpace ℍ := ⟨(volume.comap UpperHalfPlane.coe).withDensity
  fun z ↦ ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)⟩` and `instance : SMulInvariantMeasure (GL (Fin 2) ℝ) ℍ
  volume`, both in Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean:41,85. Also `volume_eq_lintegral` (l.73).
  VERIFIED-READ.
- `instance instProperlyDiscontinuousSL2RSubgroup (𝒢 : Subgroup SL(2, ℝ)) [DiscreteTopology 𝒢] :
  ProperlyDiscontinuousSMul 𝒢 ℍ` (UpperHalfPlane/ProperAction.lean:128). VERIFIED-READ.
- `MeasureTheory.IsFundamentalDomain.measure_eq` (MeasureTheory/Group/FundamentalDomain.lean:317). VERIFIED-READ
  (name only). qm-glue already uses it (TailZ3 `isFundamentalDomain_of`, `Fdom_volume`).
- Complex analysis:
  - `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable` (CauchyIntegral.lean:263),
    circle-integral Cauchy formulas.
  - **Jensen's formula** `MeromorphicOn.circleAverage_log_norm` (Analysis/Complex/JensenFormula.lean:307):
    `circleAverage (log ‖f ·‖) c R = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹) + …`.
    VERIFIED-READ.
  - **No argument principle** for general contours, and no valence formula anywhere in Mathlib (grep
    "valence", "argument principle": nothing).
  - The level-one dimension formula (NumberTheory/ModularForms/LevelOne/DimensionFormula.lean) goes through the
    Δ-isomorphism, not the valence formula. VERIFIED-READ (header).
- In tree, for Γ\*:
  - `gammaStarGen_proof` (TailO:452, descent on 𝒪).
  - `ellipticOrderLe6_proof` (e_P ≤ 6) and `ellipticOrderDvd_proof` (TailZ2:927; local rotation at elliptic
    points: the local expansion argument is already formalized).
  - Group laws `gs_one/gs_mul/gs_inv` (TailZ3:416-435) and `gs_fuchsian` (TailZ3:492).
  - Orbit descents `orbit_of_descent` (TailO:1476).

### 1.4 Missing infrastructure (specialized route, in order)
1. Explicit fundamental polygon P of Γ\*: the (2,4,6) quadrilateral with vertices i√3, √2+i and two order-2
   points. Prove covering and a.e. disjointness. This is shared with §2.4.
2. An analytic engine. Options:
   - (a) Argument principle on a piecewise-geodesic Jordan polygon with side pairings, plus indentation at boundary
     zeros. This is a new library piece and large.
   - (b) **Laplacian/Jensen route.** φ = log|F| + m·log Im z is Γ\*-invariant under the hypothesis exactly. Take
     hyperbolic circle averages of φ (Cayley map to the disc plus Mathlib's Jensen formula). Integrate
     A_ρφ − φ over P with the invariant measure. Invariance and unfolding make the left side zero. Jensen turns
     the right side into c(ρ)·Σ ord/e − m·vol(P)·c′(ρ), which gives Σ ord/e = m·vol/(2π)·… = m/12. This avoids
     contour integrals entirely. SPECULATIVE; the constants were not checked here.
3. Bookkeeping: zeros finitely many mod Γ\* (compactness of P plus isolated zeros), and the sum over orbits.

### 1.5 Tier
- General statement: T3 (valence formula for Fuchsian groups, not in Mathlib).
- Specialized `ValenceFormulaGammaStarEq`: T2/T3 boundary. The group side is T2; the analytic engine is one new
  library piece.

### 1.6 Strategy
Specialize to Γ\* and fold the Shimizu field in. Attack via route (b) (Jensen + invariant measure + explicit
polygon). Otherwise keep it cited in the Γ\*-specific form: Shimura Thm 2.20 + Takeuchi signature, which is
"consequence of one theorem".

### 1.7 Notes
- The equality clause is needed (`fibre_c`, degree-one Hauptmodul), not only ≤.
- Specializing also makes a later Sturm-type use possible. Weight-20 Γ\*-forms have dim 1 by Riemann–Roch for
  signature (0;2,4,6): −19 + 5 + 7 + 8 = 1. This could feed `LinYangThetaCurve` (§6.3). SPECULATIVE.

---

## 2. shimizuCovolumeO1

### 2.1 Identity
- Field `shimizuCovolumeO1 : LeafQCheck.HM.QMSplit.ShimizuCovolumeO1` (TailZ13.lean:35; TailZ4.lean:151).
- Constant `HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1`, def TailZ2.lean:1018: `IsCocompactFuchsian Gamma1 ∧
  ∃ s, IsFundDomain Gamma1 s ∧ volume s = ENNReal.ofReal (2 * Real.pi / 3)`, with `Gamma1` = ι(𝒪) ∩ {det = 1}
  (l.1008).
- A verbatim twin `HDec.LeafQCheck.QMSplitVB.ShimizuCovolumeO1` sits at TailZ3.lean:76 (used by
  `valenceFormulaGammaStar_of_leaves'`, not by the field).
- Row **H-136**. Form: LEAF, published form (Shimura 1971 Prop. 9.2; Shimizu 1965; Voight Thm 39.1.13;
  UNVERIFIED).

### 2.2 Use
- The same two sites as §1.2 (TailZ4:237, 249).
- Both pass through `gammaStarFromO1_proof'` (TailZ3:1188; proved: index-4 transfer `QMglue.gammaStarFromO1_proof`,
  TailZ3:879) to obtain `GammaStarCocompactArea` (TailZ2:93), which is used only as hA in §1.2.
- **Use (b).** Only for Γ¹ of the disc-6 maximal order, and only to produce Γ\*'s covolume π/6.
- Weakest statement: `GammaStarCocompactArea` (`IsCocompactFuchsian PkgI1.GammaStar ∧ ∃ s, IsFundDomain
  PkgI1.GammaStar s ∧ volume s = ENNReal.ofReal (π/6)`). It is implied via the proved transfer.
- With §1.2's specialization the field disappears altogether.

### 2.3 Library coverage
- As in §1.3: Mathlib's invariant measure, the proper-discontinuity instance for discrete subgroups of SL(2,ℝ),
  and `IsFundamentalDomain.measure_eq`.
- In tree:
  - the index-4 transfer and fundamental-domain comparison (TailZ3:492-879);
  - `fix_finite`/`fix_null` (fixed points are null; TailZ3:569, 608);
  - `gs_countable`.
- Arcsine derivative `Real.hasDerivAt_arcsin` (Analysis/SpecialFunctions/Trigonometric/InverseDeriv.lean:51), for
  explicit area integrals. VERIFIED-READ (name only).
- No Gauss–Bonnet and no hyperbolic polygon area in Mathlib.

### 2.4 Missing infrastructure (direct proof of `GammaStarCocompactArea`, in order)
1. Discreteness: ι(𝒪) is a full-rank lattice in M₂(ℝ) (one 4×4 determinant). From this get Γ¹ ⊆ SL(2,ℝ)
   discrete, then the Mathlib instance, then the `properlyDiscontinuous` field. Then pass to Γ\* via `gs_fuchsian`
   pieces.
2. Dirichlet reduction at a generic center P₀ with finitely many explicit neighbours γ₁..γ_n. Strict descent of
   cosh d(z, γP₀) terminates because orbit points are integral pure quaternions; this is leafq-check's
   `form`/nlinarith recipe. This gives cocompactness and covering by P = ∩ H_i.
3. A.e. disjointness: for z ∈ int P, d(z,P₀) < d(z,γP₀) for every γ ∉ Stab. This reduces to a finite enumeration
   of integral w with w² = −N in a compact region (interval_cases / decide).
4. Area: vol(P) = π/6, by explicit Fubini with `∫dy/y²` and an arcsine antiderivative after a Möbius normalization
   (Mathlib invariance). Alternatively 2 × (π − π/2 − π/4 − π/6).

### 2.5 Tier
T2 (explicit polygon; the group machinery exists).

### 2.6 Strategy
Prove `GammaStarCocompactArea` directly for Γ\* (simpler than Γ¹; the (2,4,6) triangle group) and drop Shimizu. Or
absorb it into `ValenceFormulaGammaStarEq` (§1).

### 2.7 Notes
- The polygon in item 2.4 is the same object that route (b) of §1.4 needs. Do it once.
- Γ\*'s polygon numerics already exist: leafq-check `py/hm_cone.py`, and cosh d(i√3, √2+i) = √3 (TailJ
  GammaStarGen docstring).

---

## 3. igusaPsi4  and  4. igusaChi10 (joint section; they are used together)

### 3.1 Identity
- Fields `igusaPsi4 : QMSplit.Theta.IgusaPsi4` and `igusaChi10 : QMSplit.Theta.IgusaChi10`, in
  `OpenResearchLeaves10` (TailZ15.lean:26-27), with copies at TailZ9:28, TailZ4:70, TailX:77.
- Constants `HDec.QMSplit.Theta.IgusaPsi4` (TailU.lean:1797) and `IgusaChi10` (TailU.lean:1807). The statement,
  with χ₁₀ analogous at weight 10:

  ```lean
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    psi4 (spAct M Ω) = spFactor M Ω ^ 4 * psi4 Ω
  ```

  Here psi4 = ¼·thetaSum8 and chi10 = −2⁻¹⁴·thetaProd2. `thetaConst`, `spAct`, `spFactor`, `SiegelH2` are in
  LPrefix.lean:297-336.
- Rows **H-131**, **H-132**. Form: LEAF, published form, with the flag that Igusa defines ψ₄ as an Eisenstein
  series (leaf-fold10 l.201-202).

### 3.2 Use
Chain:
- `researchLeaves9_of_open10` (TailZ15:96-97) → … → TailX:200 `r4 := thetaModularity_of r.igusaPsi4 r.igusaChi10`.
  `thetaModularity_of` (TailU:1812) produces `PkgI1.ThetaModularity` (LPrefix:375).
- Also TailZ4:237 (`qmHauptmodulBase3_of_leaves`).

Every consumer of `ThetaModularity` (VERIFIED-READ) reaches it through `g8Auto_of_sp` (TailJ:4020) or
`g20Auto_of_sp` (TailO:2038), via `g8Auto_gen`/`g20Auto_gen` and `g8Auto_g4/g6` (TailJ:4259, 4272) /
`g20Auto_g4/g6` (TailO:2108, 2121):
- `s8WeightExact_of` (TailJ:4309), `s20WeightExact_of` (TailO:2135);
- `auto8`/`auto20`/`autoHc` (TailZ2:162-199);
- `base2_of_base3` (TailO:2461), `qmDenZeroCM3_of_leaves4` (TailK:99).

The only application is `hT M hM (PkgI1.Omega z) (omegaSiegel_proof z _)` with M = `M4` or `M6` (TailJ:4118,
4167):
- `M4 = fromBlocks !![1,0;0,1] !![1,-2;-2,2] !![0,1;1,0] !![-1,2;1,-1]`;
- `M6 = fromBlocks 0 !![0,-1;1,0] !![0,1;-1,0] !![-1,2;-1,1]`.

`PkgI1.thetaRatio_invariant` (general M) is not on the live chain: grep finds only its definition and a #print.

**Use (b).** Weakest statement:

```lean
def ThetaModularityM46 : Prop :=
  ∀ M ∈ ({M4, M6} : Set (Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)), ∀ z : ℂ, 0 < z.im →
    thetaSum8 (spAct M (Omega z)) = spFactor M (Omega z) ^ 4 * thetaSum8 (Omega z) ∧      -- from IgusaPsi4
    thetaProd2 (spAct M (Omega z)) = spFactor M (Omega z) ^ 10 * thetaProd2 (Omega z)     -- from IgusaChi10
```

- It is implied, since `M4_symp`, `M6_symp` and `omegaSiegel_proof` are proved.
- Wiring: change the `hT` argument of `g8Auto_of_sp`/`g20Auto_of_sp` and the callers' signatures (a mechanical
  refactor).
- Kind: a finite computation plus Poisson summation, no Siegel modular form theory.

### 3.3 Library coverage
- Mathlib: `theorem jacobiTheta₂_functional_equation (z τ : ℂ) : jacobiTheta₂ z τ = 1 / (-I * τ) ^ (1 / 2 : ℂ) *
  cexp (-π * I * z ^ 2 / τ) * jacobiTheta₂ (z / τ) (-1 / τ)` (NumberTheory/ModularForms/JacobiTheta/TwoVariable.lean:466).
  VERIFIED-READ.
- Mathlib: `jacobiTheta_S_smul`, `jacobiTheta_T_sq_smul` (JacobiTheta/OneVariable.lean:43, 37). VERIFIED-READ.
- Mathlib has **no Siegel modular forms** and no generation theorem for Sp₄(ℤ). Only
  LinearAlgebra/SymplecticGroup.lean mentions `symplecticGroup`, and it has no `closure`. VERIFIED (grep).
- origin/wip/cm24-value `scratch/cm24-value/T1.lean`:
  - **general genus-2 partial inversion** `theorem pi0 {α β γ : ℂ} (hα : 0 < α.im) (c0 c1 d0 d1 : ℝ) (hs …) (hs' …)
    : Th2 α β γ c0 c1 d0 d1 = 1 / (-I * α) ^ (1 / 2 : ℂ) * cexp (2 * π * I * c0 * d0) * Th2 (-1 / α) (β / α)
    (γ - β ^ 2 / α) (-d0) c1 c0 d1` (l.87). VERIFIED-READ (git show);
  - `dup2` (l.166) and the bridge `thetaConst_eq` (P3.lean).
- origin/wip/theta-glue `ThetaGlue.lean`: absolute convergence of every genus-2 theta series on 𝔥₂ and the
  duplication formula `thetaConst_sq_eq`. SPECULATIVE-READ: report only, Lean not opened.
- theta-glue §3: numerically, the generators' action on second-order thetas gives invariance of ψ₄ and χ₁₀ (exact
  Python).

### 3.4 Missing infrastructure (in order)
1. Theta transformation under the three generator types, for all Ω ∈ 𝔥₂:
   - translation Ω ↦ Ω+B (reindexing plus 8th-root phases; characteristics permuted);
   - rotation Ω ↦ UΩUᵀ (reindex n ↦ Uᵀn);
   - partial inversion J₁ (cm24 `pi0` plus summability).
2. Factor M4 and M6 as explicit words in these generators (finite matrix identities). Prove spAct/spFactor of each
   word by direct 2×2 matrix algebra, or prove the cocycle law plus invertibility of CΩ+D on 𝔥₂.
3. Phase bookkeeping:
   - for Σθ⁸ the phases are 8th powers of 8th roots, hence 1;
   - for ∏θ², a finite product of 4th roots = 1 (decide);
   - the factor is ((−iα)^{1/2})^{8 or 20} = (−iα)^{4 or 10} (cpow_nat_mul, no branch issue). Match with spFactor.
4. For the general leaf only: generation of Sp₄(ℤ) by these generators (Hua–Reiner; not in Mathlib).

### 3.5 Tier
- Specialized `ThetaModularityM46`: T1–T2 (one task if cm24/theta-glue code is reused).
- General IgusaPsi4/IgusaChi10: T2 (plus generation of Sp₄(ℤ)).

### 3.6 Strategy
Specialize and compute. Replace both fields by `ThetaModularityM46` (or by its two clauses, one per field) and
prove it from Mathlib's functional equation.

### 3.7 Notes
- The Igusa-normalization flag (Eisenstein vs theta) becomes irrelevant once the leaf is proved.
- The machinery also gives ψ₆/χ₁₂ transformation laws needed for §6.3 ideas.

---

## 5. igusaCMValue24: DONE

1. Identity:
   - Field `igusaCMValue24 : LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` (TailZ13.lean:37; TailZ4.lean:153).
   - Constant `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24`, def TailZ3.lean:1093. It is Lin–Yang's Igusa
     vector at j = −16/27 at the fixed point of ι(μ), μ = 2j+ij.
   - Row **H-144**. Form: LEAF, published form (leaf-fold10 l.267). It is equivalent to the glue
     `ThetaQuotientValue24` (TailZ2:119) by `thetaQuotientValue24_of_igusa` / `igusa_of_thetaQuotientValue24`
     (TailZ3:1103, 1118).
2. Consumers:
   - TailZ4:238 → `qmHauptmodulBase3_of_leaves` (TailZ3:1211) → `thetaQuotientValue24_of_igusa` →
     `ThetaQuotientValue24` (hC) in TailZ2;
   - `G20_tau24_ne` (l.398: G20(τ₂₄) ≠ 0, used in `G20_tau3_le` for the valence bound);
   - the −16/27 clause of `qmHauptmodulBase3_of` (l.768).
   - Use (b): already a statement about one point.
3. **DONE.** cm24-value (origin/wip/cm24-value d8d1363a; docs/research/cm24-value.md, .fleet/cm24-value.md, read)
   proves `CM24.igusaCMValue24_field : …Value24.IgusaCMValue24` in `scratch/cm24-value/CM24Kernel.lean`
   (imports TailZ3). It has no leaf, standard axioms, and no CM theory.
   - Inputs: Mathlib's `jacobiTheta₂_functional_equation` only, used for:
     - genus-2 partial inversion `pi0`, applied twice: Ω₂₄ ↦ W = −Ω₂₄⁻¹, with 2W ≡ diag(i√6, i√6/2);
     - genus-2 duplication `dup2`;
     - Landen and Jacobi identities;
     - the cubic modular equation θ₃(τ)θ₃(3τ) = θ₂θ₂′ + θ₄θ₄′ (lattice rearrangement).
   - Algebra: the minimal polynomial m(k) = k⁴+12k³+2k²−12k+1 of λ\*(6); positivity on the imaginary axis; the
     divisibility `CM24Alg.core` and a Bezout certificate `core_ne`.
   - Folded in origin/wip/w63 as `TailZ18` (leaf-fold11 l.18, 30: "OpenAddedLeaves11 drops it").
4. Bonus: `CM24.singularModulus6` (λ\*(6) = (2−√3)(√3−√2)) is also proved.
5. Tier: done.
6. Strategy: done.
7. The general genus-2 tools (`Th2`, `pi0`, `dup2`) are the key reusable assets for §3 and §6.

---

## 6. thetaRatiosAlgebraic: IN FLIGHT

### 6.1 Identity
- Field `thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic` (TailZ13.lean:20; TailZ4:135; TailX:159;
  older copies TailO, TailN, TailK, TailI, TailE, TailD, TailA:4952).
- Constant `HDec.HSyn.G0Split.ThetaPt.ThetaRatiosAlgebraic`, def ZInQKernel/OneProof/H/TailA.lean:4386. For every
  abelian variety A over a number field, analytic uniformization, and period matrix Ω ∈ 𝔥₂: ∃ m₀, θ_{m₀}(Ω) ≠ 0 and
  every θ_m/θ_{m₀} is algebraic.
- Row **H-44**. Form: GLUE (composite) (leaf-fold10 l.255; Shimura 1976, Mumford Tata II IIIa §8, Igusa).

### 6.2 Use
- TailZ13:48 → TailZ4:235 → TailX:258 → … → TailA:5010 `thetaPoint := ThetaPt.thetaPointOfFibre_of_qm_ratios
  gp2.fibreQMPeriod gp2.thetaRatiosAlgebraic`.
- `thetaPointOfFibre_of_qm_ratios` (TailA:~4480) → `thetaNullAlgebraic_of_ratios` (TailA:4407) →
  `thetaPointOfFibre_of` (TailA:4430).
- It is applied once, at Ω = `BPAnalytic.QM.Omega τ` for the τ from `FibreQMPeriod`, where jNum/jDen(Ω(τ)) =
  J(u) ∈ ℚ∖{0} (VERIFIED-READ; matches theta-split §1).
- **Use (b).** Infinitely many **non-CM** points of the explicit curve τ ↦ Ω(τ). Weakest form, theta-split's
  `ThetaRatiosAtQM`: Im τ > 0 and j_θ(Ω(τ)) = q ∈ ℚ∖{0} ⇒ ∃ m₀, θ_{m₀}(Ω(τ)) ≠ 0 ∧ ∀ m, θ_m/θ_{m₀} algebraic.
- The A/σ/Λ data are irrelevant to the conclusion.

What the branches did:
- **theta-split** (b285cb60, in tree: `scratch/theta-split/ThetaUse.lean`, `docs/research/theta-split.md`):
  - `thetaPointOfFibre_of_qm_atQM` (drop-in);
  - Route 1: `QMThetaSymmetricCore` (e_k(θ⁸) = qmR_k(j_θ)(Σθ⁸)^k along the curve, 2≤k≤9). It splits into
    `ThetaEightSquare` (global) and `QMThetaSymmetricCurve` (3≤k≤9);
  - Route 2: `ShimuraCMThetaAlgebraic` (LEAF, CM points) + `QMThetaShape` + `QMCMNodesNumeric` (4 CM nodes,
    j = 0, 81/64, 1296/125, 194481/10⁶), with Lagrange interpolation compiled.
- **theta-glue** (origin/wip/theta-glue 336ec1fd; docs/research/theta-glue.md, .fleet/theta-glue.md, log):
  - **`ThetaEightSquare` PROVED.** Method: duplication formula plus a degree-16 `ring`, no modular forms.
  - `QMThetaSymmetricCurve` reduced (`qmThetaSymmetricCurve_of_alg59`) to:
    - one composite LEAF `LinYangThetaCurve` (along Ω(τ): ψ₄ψ₆ = 2¹²3⁵χ₁₀ and ψ₄³+ψ₆² = 2¹²3⁶χ₁₂; Lin–Yang
      Ex. 29 with j eliminated);
    - closed polynomial identities `IgusaAlg k`. k = 3 and 4 are proved by `ring` (1.5 min / 14 GB and
      4.3 min / 21 GB). k = 5..9 are verified by exact expansion only; every Lean method tried exceeded 24 GB.
  - Igusa's structure theorem is not needed.

### 6.3 Coverage, missing pieces, tier, strategy, notes (brief)
- Coverage: as §3.3 and §5 (Mathlib functional equation; cm24 and theta-glue genus-2 tools).
- Missing:
  - (i) `IgusaAlg 5..9` in Lean. This is engineering: a faster certified polynomial normalizer, or finer splitting
    with precomputed normal forms, or more memory.
  - (ii) `LinYangThetaCurve`, either kept as a cited composite or proved. SPECULATIVE proof route: both sides
    pulled back along Ω are Γ\*-automorphic of weight 20 (m=10, a 1-dimensional space). With
    `ValenceFormulaGammaStarEq` (§1) and `ThetaModularityM46`-type laws for ψ₆, χ₁₂, one exact comparison would
    suffice, e.g. at τ₂₄ via cm24's machinery or at the product point √2+i.
- Tier: T2, given what is already done.
- Strategy: reduce to smaller printed statements (Route 1) and finish the `IgusaAlg` engineering.
- Note: the docstring at TailE:6521 ("CM period matrix") is inaccurate (theta-split §8).

---

## Summary table

| field | consumers | use (a/b) | tier | strategy | best attack idea (one line) |
|---|---|---|---|---|---|
| valenceFormulaCocompactEq | `qmHauptmodulBase3_of` (TailZ2:768, via TailZ3:1211), `valenceFormulaGammaStar_of_eq` (TailZ2:998, via TailZ3:1196) → `base2_of_base3`, `qmDenZeroCM3_of''` | b: Γ\* only, F ∈ {G8, G20, H_c} | T3 (general); T2/T3 for Γ\* | specialize | Replace with Γ\*-only `ValenceFormulaGammaStarEq` (Σ ord/e = m/12); prove via Jensen's formula + invariant measure on an explicit (2,4,6) polygon |
| shimizuCovolumeO1 | same two sites, only via `gammaStarFromO1_proof'` → `GammaStarCocompactArea` | b: Γ¹ only, to get Γ\* covolume π/6 | T2 | prove directly / absorb | Prove `GammaStarCocompactArea` for the (2,4,6) triangle group by Dirichlet reduction (leafq-check descent) + explicit area; or fold into `ValenceFormulaGammaStarEq` |
| igusaPsi4 | `thetaModularity_of` → `g8Auto_of_sp` (TailJ:4020) at M4, M6, Ω(z) | b: two matrices, the QM curve | T1–T2 (specialized); T2 (general) | specialize and compute | Theta transformation under translations, rotations, and partial inversion (cm24 `pi0` from Mathlib's `jacobiTheta₂_functional_equation`); factor M4, M6 |
| igusaChi10 | `thetaModularity_of` → `g20Auto_of_sp` (TailO:2038) at M4, M6, Ω(z) | b: same | T1–T2 / T2 | specialize and compute | Same as psi4; phase product of the ten θ² is a finite check |
| igusaCMValue24 | `qmHauptmodulBase3_of_leaves` → `ThetaQuotientValue24` (`G20_tau24_ne`, the −16/27 clause) | b: one point τ₂₄ | done | done (cm24-value, TailZ18 in w63) | — (proved from Mathlib theta functional equation, duplication, cubic modular equation) |
| thetaRatiosAlgebraic | `thetaPointOfFibre_of_qm_ratios` (TailA:5010) | b: non-CM points Ω(τ), j_θ ∈ ℚ∖{0} | T2 | reduce (theta-split Route 1, theta-glue) | Finish `IgusaAlg 5..9` (normalizer engineering); keep `LinYangThetaCurve` cited or prove it via Γ\* valence + one exact value |
