# gt-theta: Igusa's `ψ₄` and `χ₁₀` proved modular on all of `Sp₄(ℤ)`

Task gt-theta, 2026-11-14. Base 8c273897 (`origin/wip/autofold`). Lean:
`ZInQKernel/Contrib/OneProof/ThetaModularityM46.lean` (the contribution; imports `ZInQKernel.OneProof.Main`;
1481 lines, 81 KB). Development files and numerics are in `scratch/gt-theta/`, and the results log is
`scratch/gt-theta/log.md`. No other file under `ZInQKernel/` or `blueprint/`, and no other task's notes or
scratch, was edited. This is model work with no human review.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means a judgement. Theorem numbers recalled from memory are **UNVERIFIED** (no network).

## 1. Result

**Both open hypotheses are proved in Lean, as stated, with no hypotheses** (VERIFIED):

```lean
theorem GapTheta.igusaPsi4_proof  : HDec.QMSplit.Theta.IgusaPsi4
theorem GapTheta.igusaChi10_proof : HDec.QMSplit.Theta.IgusaChi10
theorem GapTheta.thetaModularity_proof : HDec.PkgI1.ThetaModularity   -- row H-2, via thetaModularity_of
```

The statements are the ones in `ZInQKernel/OneProof/H/TailU.lean` L1797 and L1807, unchanged:

```lean
def IgusaPsi4 : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    psi4 (spAct M Ω) = spFactor M Ω ^ 4 * psi4 Ω
def IgusaChi10 : Prop :=
  ∀ M ∈ Matrix.symplecticGroup (Fin 2) ℤ, ∀ Ω ∈ SiegelH2,
    chi10 (spAct M Ω) = spFactor M Ω ^ 10 * chi10 Ω
```

`#discharges` output (`scratch/gt-theta/Discharges.lean`, saved as `scratch/gt-theta/discharges_out.txt`;
VERIFIED):

```
DISCHARGES [OpenResearchLeaves14.igusaChi10] by GapTheta.igusaChi10_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves14.igusaPsi4] by GapTheta.igusaPsi4_proof
  still assumes: []
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 72 open hypotheses, 204 theorems checked, 2 discharge one
```

So the two published LEAF hypotheses `igusaPsi4` and `igusaChi10` (Igusa 1962/1967) leave the list without any
new leaf. The fold is the standard one (`scripts/one_proof/autofold.py`): drop both fields from the next
generation of `OpenResearchLeaves14` and fill them with the two theorems. No consumer has to be rerouted.

The task's own target, gap-triage A2's specialization, is also proved, with its consumer forms (VERIFIED):

```lean
theorem GapTheta.thetaModularityM46 : GapTheta.ThetaModularityM46          -- at M4, M6 and Ω(z)
theorem GapTheta.thetaModularityM46Siegel : GapTheta.ThetaModularityM46Siegel  -- at M4, M6, all Ω ∈ 𝔥₂
theorem GapTheta.s8WeightExact_of' (hT : ThetaModularityM46) (hG : GammaStarGen) : S8WeightExact
theorem GapTheta.s20WeightExact_of' (hT : ThetaModularityM46) (hG : GammaStarGen) : <type of LQ20.s20WeightExact_of>
theorem GapTheta.s8WeightExact_of_gen (hG : GammaStarGen) : S8WeightExact
theorem GapTheta.s20WeightExact_of_gen (hG : GammaStarGen) : <type of LQ20.s20WeightExact_of>
```

All of these depend only on `propext`, `Classical.choice` and `Quot.sound` (VERIFIED, `#print axioms`).

Build (VERIFIED): `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.ThetaModularityM46` succeeds. The contribution module compiles in 38 s.

## 2. The proof

The file reuses the chain's declarations and copies none of them: `PkgI1.thetaConst`, `spAct`, `spFactor`,
`SiegelH2`, `evenChars`, cm24-value's `CM24.Th2`, `pi0`, `th2_swap`, `th2_shift_c`, `th2_shift_d`, `th2_phase`,
`cast_even`, `thetaConst_eq`, `cpow_half_sq` (TailZ18), period-glue's `M4`, `M6`, `M4_map`, `M6_map`,
`spAct_of_poly`, `spFactor_of_poly` and the `G8Auto`/`G20Auto` machinery (TailJ, TailO), and `posDef_fin_two`,
`omegaSiegel_proof` (TailJ).

### 2.1 Theta transformations with real characteristics (Part I)

Write `Th2 α β γ c₀ c₁ d₀ d₁` for the theta series at `[[α,β],[β,γ]]` with real characteristics. Let `PDq α β γ`
say that the imaginary part is positive definite (`Im α > 0`, `det Im > 0`). It gives summability through the
bound `(a+c)·q(x) − (ac−b²)|x|² = (ax+by)² + (bx+cy)²` (`PDq.bound`), and it is preserved by the partial inversion
(`PDq.j1`) and by the swap.

* **Inversion** `Ω ↦ −Ω⁻¹`, squared (`inv_sq`, `inv_sq'`): apply cm24-value's `pi0` twice, with two swaps. This is
  Mathlib's `jacobiTheta₂_functional_equation` used twice. The square removes the branch of `(−iα)^{1/2}`.
* **Translation** `Ω ↦ Ω + S` for integral symmetric `S` (`th2_trans`): the exponent changes by `πi(s₀₀n₀(n₀−1) + …)`,
  which lies in `2πiℤ`.
* **Rotations**: `diag(1,−1)` (`th2_neg`), the swap, `T = [[1,1],[0,1]]` and `T⁻¹` (`th2_rotT`, `th2_rotTinv`),
  all by reindexing `ℤ²`.
* **Reduction** of half-integral characteristics mod `ℤ²`, squared (`th2_sq_red`): the sign `±1` squares away.
* **Assembly** (`assemble`): suppose `θ_m(Ω')² = −D·exp(πiN_m/4)·θ_{σm}(Ω)²` for every even `m`, where `σ` is a
  permutation of the ten even characteristics, every `N_m` is even and `Σ N_m ≡ 0 mod 8`. Then
  `Σθ⁸(Ω') = D⁴Σθ⁸(Ω)` and `∏θ²(Ω') = D¹⁰∏θ²(Ω)`. The finite facts are checked by `decide`.

**`M4`, `M6`** (`thetaM4`, `thetaM6`). Both have invertible `C`, and each factors as
`M = T(S₁)·R(C⁻ᵀ)·J·T(S₂)` with `S₂ = [[1,−1],[−1,2]]`. The other factor is `S₁ = [[0,1],[1,0]]` for `M4` and
`S₁ = 0` for `M6`. Hence `spAct M6 Ω = −(Ω+S₂)⁻¹` rotated and `spFactor M6 = det(Ω+S₂)`; likewise
`spFactor M4 = −det(Ω+S₂)` (`spAct_M4`, `spAct_M6`, `spFactor_M4`, `spFactor_M6`). For example, at `M6` the
permutation sends `(a,b) ↦ (−b₁, b₀; a₁−b₁+1−b₀, −a₀+2b₀+2+b₁) mod 2`, and
`N = 4a₀b₀ + 4a₁b₁ − 2b₁² + 4b₁ − 4b₀² − 8b₀ − 4b₀b₁`. Before the Lean proof, these formulas were checked
numerically on all 20 cases (`scratch/gt-theta/py/chain.py`, truncated theta sums, relative error ≤ 3.3e-15;
VERIFIED).

### 2.2 Generation of `Sp₄(ℤ)` (Part II)

`sp_mem_closure` (VERIFIED) says that every `M ∈ Matrix.symplecticGroup (Fin 2) ℤ` lies in the **monoid**
generated by eleven matrices. They are the images of `S, T, T⁻¹` under three homomorphisms
`iota1, iota2, rot : SL(2,ℤ) →* Mat4` (`SL₂` on the coordinates `(a₁,c₁)`, on `(a₂,c₂)`, and `U ↦ [[U,0],[0,U⁻ᵀ]]`),
together with the translations by `±[[0,1],[1,0]]`. The proof is an explicit reduction with no induction on a size:

1. Bezout in `SL₂(ℤ)` (`bezout_sl`) is applied to `(a₂,c₂)` by `iota2` (`red_all`), then to `(a₁,c₁)` by `iota1`
   (`red_c2`), then to `(a₁,a₂)` by `rot` (`red_c0`). After these steps the first column is `(g,0,0,0)`.
2. The symplectic relation `ω(col₁, col₃) = −1` gives `g = ±1` (`red_sign`).
3. A symplectic matrix with first column `e₁` equals `T([[q−st, s],[s, 0]])·rot(T^{−t})·iota2(γ)` (`red_stab`).
   This uses the sixteen relations `ω(Meₐ, M e_b) = ω(eₐ, e_b)` (`sp_rel`).

`SL₂(ℤ)` itself is handled by Mathlib's `SpecialLinearGroup.SL2Z_generators` (`hom_mem`). This part imports only
Mathlib; it was developed in `scratch/gt-theta/Gen.lean`.

### 2.3 Cocycle and generators

`sp_comp` proves `spAct (MN) Ω = spAct M (spAct N Ω)` and `spFactor (MN) Ω = spFactor M (NΩ)·spFactor N Ω`
whenever the two determinants are nonzero. So the matrices that keep `𝔥₂` stable, have a nonvanishing factor and
satisfy both laws form a submonoid (`goodSub`). Each of the eleven generators is shown to lie in it:

* translations: `good_Tm`, with six `decide` instances;
* rotations: `good_rotS`, `good_rotT`, `good_rotTinv`, with factor 1;
* partial inversions: `good_J1` and `good_J2`, with factor `Ω₀₀` and `Ω₁₁` respectively, `N = 2 + 4a₀b₀`, and
  the identity `i = exp(πi/2)`.

`good_sp` follows from these, and then `igusaPsi4_proof` and `igusaChi10_proof` by clearing Igusa's constants.

## 3. What this changes

* **Leaves.** The two published leaves `igusaPsi4` and `igusaChi10` (H-131, H-132) become theorems. The strict
  LEAF count drops by 2, and no new leaf or glue is added. The proof uses no Siegel modular form theory, no
  Eisenstein series and no structure theorem. It needs only Mathlib's one-variable theta functional equation
  and finite algebra.
* **Fold.** Run autofold with the two fields discharged by `GapTheta.igusaPsi4_proof` and
  `GapTheta.igusaChi10_proof`. Every downstream use goes through `QMSplit.Theta.thetaModularity_of r.igusaPsi4
  r.igusaChi10` (TailX L196, TailZ4 L237), so it is unaffected.
* **If only the specialization were kept** (gap-triage A2's route; not needed now), these consumer sites would have
  to be rerouted:
  * TailX L196: `r4 := thetaModularity_of …`, feeding the old field `r4`. That field is read at TailK L315
    (`qmDenZeroCM3_of_leaves4 r.r4`, via `s8WeightExact_of`) and at TailO L2881 (`base2_of_base3 r.r4`, via
    `s8WeightExact_of` L2469 and `s20WeightExact_of` L2526).
  * TailZ4 L237: `qmHauptmodulBase3_of_leaves (thetaModularity_of …)`. It leads through TailZ3 L1211 into the section
    `variable (hT : PkgI1.ThetaModularity)` of TailZ2 (L294). There every use is `auto8 hT` or `auto20 hT`, which
    are `s8WeightExact_of hT` and `s20WeightExact_of hT`.
  * TailJ L5039: `s8WeightExact_of hTM hG`.

  `s8WeightExact_of_gen` and `s20WeightExact_of_gen` are the replacements at all these sites.
* **Sources.** The statements are Igusa's (Amer. J. Math. 84 (1962); 89 (1967); locators in the TailU docstrings,
  UNVERIFIED). The proof does not depend on them. The generation of `Sp₄(ℤ)` by translations, rotations and `J` is
  classical (Hua–Reiner 1949; Klingen, *Introductory lectures on Siegel modular forms*, §I; UNVERIFIED). It is proved
  here directly and not cited.

## 4. Files

* `ZInQKernel/Contrib/OneProof/ThetaModularityM46.lean`: the contribution. Part I covers `ThetaModularityM46` and the
  consumer forms; Part II covers generation, the cocycle, the generators, and the two hypotheses.
* `scratch/gt-theta/Dev.lean`: Part I development, importing TailZ18.
* `scratch/gt-theta/Gen.lean`: generation, Mathlib only.
* `scratch/gt-theta/Full.lean`: Part II development. It compiled against the Part I-only version of the
  contribution and is now superseded: the contribution contains its body, so recompiling it would duplicate names.
* `scratch/gt-theta/Discharges.lean` and `discharges_out.txt`: the `#discharges` check.
* `scratch/gt-theta/py/chain.py`: numerics for the `M4`/`M6` chain.
* `scratch/gt-theta/log.md`: the results log.
