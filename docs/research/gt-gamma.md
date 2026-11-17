# gt-gamma: `Γ*` is cocompact Fuchsian with covolume `π/6`, and Shimizu's `2π/3` for `𝒪¹`, proved with no hypotheses

## 1. Result

**Proved in Lean, no hypotheses, standard axioms only** (VERIFIED: compiled, `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`):

```lean
theorem HDec.GammaStarArea.gammaStarCocompactArea_proof :
    HDec.LeafQCheck.HM.QMSplit.GammaStarCocompactArea
```

in `ZInQKernel/Contrib/OneProof/GammaStarArea.lean` (imports `ZInQKernel.OneProof.Main` only). The statement is the
chain's own constant (TailZ2 L93, copied verbatim in `scratch/gt-gamma/statement.lean`):

```lean
def GammaStarCocompactArea : Prop :=
  IsCocompactFuchsian PkgI1.GammaStar ∧
    ∃ s, IsFundDomain PkgI1.GammaStar s ∧ MeasureTheory.volume s = ENNReal.ofReal (Real.pi / 6)
```

The fundamental domain is the closed geodesic triangle `T` with vertices `i√3`, `±(1+√2) + i(2+√2)` (angles
`π/3, π/4, π/4`, the union of two `(2,4,6)` triangles):

```lean
def Tset : Set UpperHalfPlane := {w | Xq w ≤ Uq w ∧ -Xq w ≤ Uq w ∧ Uq w ≤ 6 + 6 * √2}
-- Uq w = |w|² − 3,  Xq w = 6 Re w
```

**The same file proves the open leaf itself**, so `shimizuCovolumeO1` leaves the open list
(`#discharges`, VERIFIED, section 6):

```lean
theorem HDec.GammaStarArea.shimizuCovolumeO1_proof : HDec.LeafQCheck.HM.QMSplit.ShimizuCovolumeO1
```

The fundamental domain of `Γ¹ = ι(𝒪¹)` is `S1 = ⋃ᵢ rᵢ⁻¹ T` (`rᵢ = 1, x₄, x₆, x₄x₆`, the chain's coset
representatives `g4`): it covers since every `γ ∈ Γ*` is `rᵢ h` with `h ∈ Γ¹` (`cover_mob`); the pieces
`rᵢ⁻¹T ∩ h⁻¹ r_j⁻¹ T` are translates of `T ∩ (r_j h rᵢ⁻¹)⁻¹ T`, null unless `r_j h rᵢ⁻¹` acts trivially, which
by the chain's `coset_eq` forces `i = j` and `h` trivial; the four translates are a.e. disjoint (same argument with
`h = 1`) and each has area `π/6`, so `vol S1 = 2π/3`. Proper discontinuity of `Γ¹` is inherited from `Γ* ⊇ Γ¹`.
This is Shimizu's volume formula `(π/3)∏_{p|6}(p − 1)` for this one order, proved by the explicit domain rather
than by the zeta-function argument of the source.

## 2. The proof (all steps compiled)

Notation: `p = i√3` (the chain's `tau3`, the order-6 elliptic point); `y = a₀ + a₁i + a₂j + a₃k ∈ B = (2,−3)`;
`ι(y) = [[a₀ + a₁√2, −3a₂ − 3√2a₃], [a₂ − √2a₃, a₀ − a₁√2]]` (`iota_apply`).

1. **One identity drives everything** (`Fp_smul`, VERIFIED). With `F(w) = |w − p|²/Im w` (so
   `cosh d(w, p) = 1 + F(w)/(2√3)`, `cosh_dist_p0`), for `g` with matrix `ι(y)`, `nrd y > 0`:
   `F(g w) = F(w) + Φ_y(w)/(nrd(y) Im w)`, with
   `Φ_y = P(U + 6) + 2√2(RU − SX)`, `P = 4a₁² + 12a₃²`, `R = a₀a₁ − 3a₂a₃`, `S = a₀a₃ + a₁a₂`,
   `U = |w|² − 3`, `X = 6 Re w`. (A polynomial identity modulo `√2² = 2`, `√3² = 3`; the
   `linear_combination` certificate was computed by `scratch/gt-gamma/py/phi_cert.py`.)
   At `w = p`: `cosh d(p, ι(y)p) = 1 + P/nrd(y)` (`cosh_dist_smul_p0`).
2. **Elements.** Every `γ ∈ Γ*` acts as `ι(y)` with `y ∈ 𝒪`, `nrd y ∈ {1,2,3,6}` (`cover_y`, from the chain's
   `cover_mob`, which rests on leafq-check's `gammaStarGen_proof`). Matrices of positive determinant are
   isometries (`dist_smul_pos`, via Mathlib's `IsIsometricSMul SL(2,ℝ) ℍ`).
3. **Finiteness and proper discontinuity.** `P` together with `nrd y ≤ 6` bounds all four coordinates of
   `y ∈ 𝒪`, so `{γ· : d(p, γp) ≤ C}` is finite (`finite_O`, `finite_mob`). Hence `properlyDiscontinuous` (via the
   triangle inequality) and an orbit point nearest `p` (`exists_min`).
4. **Covering** (`cover_T`). Take the nearest orbit point `w`. The stabilizer of `p` acts linearly on `(X, U)`
   (`cone_smul`); one of six explicit elements (`1`, `x₆`, `x₆⁻¹`, `(1±j)/2`, `j = x₆(1−j)/2`) moves `w` into the
   cone `U ≥ |X|` without changing `d(w, p)` (`cone_step`). Comparing with `σ = ι(μ)`, `μ = 2j + ij ∈ N(𝒪)`
   (`sigma_mem`, `conj_mu`): `Φ_μ = 12(6 − (√2 − 1)U) ≥ 0`, i.e. `U ≤ 6 + 6√2`. So `w ∈ T`.
5. **Dirichlet property** (`dirichlet`): `d(w, p) ≤ d(γw, p)` for `w ∈ T`, `γ ∈ Γ*`. `Φ_y` is affine in
   `(U, X)` and `T` is the triangle `0 ≤ |X| ≤ U ≤ L`, `L = 6 + 6√2`; the barycentric identity
   `2LΦ = 12(L − U)P + (U + X)Φ(L, L) + (U − X)Φ(L, −L)` and `Φ(L, ±L) = 6(2 + √2)(P + 2(R ∓ S))` reduce it to
   the integer inequality (`intV`, `A_i = 2a_i`)
   `2(A₁² + 3A₃²) + (A₀A₁ − 3A₂A₃) ∓ (A₀A₃ + A₁A₂) ≥ 0` whenever `A₀² − 2A₁² + 3A₂² − 6A₃² = 4N`,
   `N ∈ {1,2,3,6}`, `A₁ ≡ A₃ (2)`: Cauchy–Schwarz (`(R − S)² ≤ (4/3)(R² + 3S²) = (4/3)(4N + 2P)P`) when
   `P = A₁² + 3A₃² ≥ 4N`; otherwise `P ∈ {0, 4, 12, 16}`, three norm equations are impossible mod 3 (`no_sq3`)
   and two are enumerated (`sq3_16`, `sq3_48`). (Python: the 84 small solutions all satisfy it, and 0
   violations in the box `|A_i| ≤ 20`; `py/check.py`.)
6. **A.e. disjointness** (`disjoint_T`). On `T ∩ γ⁻¹T` both Dirichlet inequalities hold, so `F(γw) = F(w)`,
   `Φ_y(w) = 0` (`Phi_zero`). If `P ≠ 0` that is the circle/line `(P + 2√2R)|w|² − 12√2S Re w + 3P − 6√2R = 0`,
   null (`null_quadric`: Mathlib's `addHaar_sphere`, a vertical line via `volume_preserving_equiv_real_prod`).
   If `P = 0`, `y = a₀ + a₂j` fixes `p`; the twelve such `y` are enumerated, `±1` act trivially (excluded), and
   for the ten rotations the cone argument (`cone_rigid`) leaves the two rays `U = ±X` (null).
7. **Area** (`volume_T`, `AreaCalc.area_TC`). Mathlib's `UpperHalfPlane.volume_eq_lintegral`, the
   measure-preserving `ℂ ≃ ℝ²`, Tonelli, `∫ dy/y² = 1/lo − 1/up` on the vertical sections
   `lo = √(3 + 6|x| − x²)`, `up = √(9 + 6√2 − x²)`, `|x| ≤ 1 + √2`, and the antiderivative
   `arcsin((x − 3)/(2√3)) − arcsin(x/√(9 + 6√2))` on `[0, 1+√2]` (evenness for `[−1−√2, 0]`), with
   `arcsin(√3/2) = π/3` and `arcsin((√2 − 2)/(2√3)) = arcsin(1/√3) − π/4`: total `2(π/3 − π/4) = π/6`.

Measurability: `T` is closed. Compactness (`isCompact_T`): `Im w ≥ 1` on `T` and `cosh d(w, p) ≤ 22`.

Differences from the gap-triage plan (A6): no descent certificates on `ℍ` were needed (the covering uses the
nearest orbit point, finiteness coming from `cosh d(p, ι(y)p) = 1 + P/nrd y`); the "finite enumeration of
integral elements" became the vertex inequality `intV` plus the stabilizer list.

## 3. Reuse of the chain (no declaration copied)

`QMglue.cover_mob`, `gamma1_iff`, `gamma1_sub`, `one_mem_gamma1`, `mul_mem_gamma1`, `inv_mem_gamma1`, `gs_one`,
`gs_mul`, `gs_inv`, `det_pos_of_mem`, `g4`, `g4_mem`, `g4_coe`, `rep`, `repi`, `rep_repi`, `nrd_rep`, `inv_coe`,
`inO_mul`, `coset_eq`; `LeafQCheck.iota_apply`, `iota_mul`, `det_iota_eq`, `nrd`, `nrd_mul`, `inO_iff`, `glOf`,
`coe_glOf`, `x6i`; `PeriodGlue.x4`, `x6`; `PeriodMap.tau3`; `PkgI1.mu`, `muInv`, `mu_mul_muInv`, `GammaStar`, `iota`,
`InO`; Mathlib's invariant measure on `ℍ` (`UpperHalfPlane.volume_eq_lintegral`, `measure_preimage_smul`,
`measure_smul`) and hyperbolic metric (`UpperHalfPlane.cosh_dist`, `ProperSpace ℍ`).

## 4. Checks

* `lake env lean ZInQKernel/Contrib/OneProof/GammaStarArea.lean`: no errors (VERIFIED, 11-14 21:55).
* `#print axioms HDec.GammaStarArea.gammaStarCocompactArea_proof`: `[propext, Classical.choice, Quot.sound]`
  (VERIFIED, in `scratch/gt-gamma/GS.lean`).
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.GammaStarArea`:
  `Build completed successfully` (VERIFIED, 11-14; the first run rebuilt the 82 modules of `Main`'s closure that
  import the upstream `lean/` package, as in the sibling worktrees; `frozenTarget` unchanged, standard axioms).
* `#print axioms HDec.GammaStarArea.shimizuCovolumeO1_proof`: `[propext, Classical.choice, Quot.sound]`
  (VERIFIED, `scratch/gt-gamma/Shimizu.lean`).

## 5. The fold: consumer sites

`shimizuCovolumeO1` (bundle field `HDec.HSyn.OpenAddedLeaves13.shimizuCovolumeO1`, TailZ24 L783) is used only
through `gammaStarFromO1_proof' l.shimizuCovolumeO1`:

* TailZ4 L237: `qmHauptmodulBase3 := LeafQCheck.HM.QMSplit.qmHauptmodulBase3_of_leaves (…) l.valenceFormulaCocompactEq
  l.shimizuCovolumeO1 l.igusaCMValue24` → `HDec.GammaStarArea.qmHauptmodulBase3_noShimizu (…)
  l.valenceFormulaCocompactEq l.igusaCMValue24`;
* TailZ4 L249: `valenceFormulaGammaStar := LeafQCheck.HM.QMSplit.valenceFormulaGammaStar_of_leaves
  l.valenceFormulaCocompactEq l.shimizuCovolumeO1` → `HDec.GammaStarArea.valenceFormulaGammaStar_noShimizu
  l.valenceFormulaCocompactEq`;
* inside `qmHauptmodulBase3_of_shimizu` (TailZ2 L1489) and `valenceFormulaGammaStar_of_leaves` (TailZ3 L1196):
  `gammaStarFromO1_proof' hS` → `gammaStarCocompactArea_proof`.

The later generations (TailZ13 L35/61, TailZ17 L203/267, TailZ18 L1224/1243, TailZ22 L247/328, TailZ23 L754,
TailZ24 L783/827) only pass the field down. With `shimizuCovolumeO1_proof` (section 1) no rerouting is needed:
the fold fills the field (`shimizuCovolumeO1 := HDec.GammaStarArea.shimizuCovolumeO1_proof`) in the next generation
of `OpenAddedLeaves13`, which `autofold.py` does mechanically.

## 6. `#discharges`

`scratch/gt-gamma/Discharges.lean` (imports `Main`, `Discharges`, the module), output
(`scratch/gt-gamma/discharges-output.txt`, VERIFIED):

```
DISCHARGES [OpenAddedLeaves13.shimizuCovolumeO1] by HDec.GammaStarArea.shimizuCovolumeO1_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 72 open hypotheses, 204 theorems checked, 1 discharge one
```

`gammaStarCocompactArea_proof` is not itself an open hypothesis (it is glue under the field), so it matches
nothing; the field it makes redundant is discharged directly.

## 7. What remains

Nothing for these two statements. For the integration lead: fold `shimizuCovolumeO1` (strict LEAF, kind
published) with `autofold.py` (discharged field, no new leaves), giving 71 open hypotheses. The headline's other
inputs at this node (`valenceFormulaCocompactEq`, `igusaCMValue24`, the theta modularity) are untouched.
