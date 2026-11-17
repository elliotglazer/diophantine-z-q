# theta-glue: `ThetaEightSquare` proved; `QMThetaSymmetricCurve` reduced to Lin–Yang plus exact algebra

Task theta-glue, 2026-11-14/15. Base e667561d (wip/w62). Lean: `scratch/theta-glue/ThetaGlue.lean`
(imports `ZInQKernel.OneProof.H.TailA`); development file `scratch/theta-glue/Dup.lean`; exact algebra
and numerics in `scratch/theta-glue/py/` (pure Python with `fractions`; sympy is not installed on this
host and there is no network); generator `scratch/theta-glue/gen/gen_igusa.py`; results log
`scratch/theta-glue/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another task's notes or
scratch was edited. This is model work with no human review.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with a
reference. **SPECULATIVE** means a judgement. Theorem numbers and locators recalled from memory are
**UNVERIFIED** (no network).

## 1. Main result

theta-split's Route 1 (docs/research/theta-split.md) replaced the field `thetaRatiosAlgebraic` with
two statements:

* `ThetaEightSquare`: `Σθ_m¹⁶ = (Σθ_m⁸)²/4` on `𝔥₂`;
* `QMThetaSymmetricCurve`: `e_k(θ_m⁸) = R_k(j_θ)(Σθ⁸)^k` along `τ ↦ Ω(τ)` for `3 ≤ k ≤ 9`.

1. **`ThetaEightSquare` is proved in Lean.** The theorem `thetaEightSquare : ThetaEightSquare` holds
   for a verbatim copy of the statement. It compiles with no `sorry` and uses only the axioms
   `propext`, `Classical.choice` and `Quot.sound` (VERIFIED). The proof is self-contained and uses
   no Siegel modular form theory:
   * every genus-2 theta series converges absolutely on `𝔥₂`. The key bound is
     `(y₀₀+y₁₁)·q_Y(x) − det Y·|x|² = (y₀₀x₀+y₀₁x₁)² + (y₀₁x₀+y₁₁x₁)²`, combined with Mathlib's
     `jacobiTheta₂` majorant;
   * the **duplication formula** `θ[a;b](Ω)² = Σ_{c∈{0,1}²} (−1)^{(c+a)·b} θ[c;0](2Ω)·θ[c+a;0](2Ω)`
     (`thetaConst_sq_eq`) is proved by the change of variables
     `(c,k,l) ↦ (l+k+c(1−a), l−k−ca)` (an explicit `Equiv`);
   * a degree-16 polynomial identity in the four second-order theta constants
     `U_c = θ[c;0](2Ω)`, checked by `ring`.
2. **`QMThetaSymmetricCurve` is reduced to one composite LEAF plus closed polynomial identities.**
   All of the following compiles with standard axioms (VERIFIED):
   * `qmThetaSymmetricCurve_of : LinYangThetaCurve → IgusaThetaSymmetric → QMThetaSymmetricCurve`;
   * `igusaThetaSymmetric_of_alg : (∀ k, 3 ≤ k → k ≤ 9 → IgusaAlg k) → IgusaThetaSymmetric`;
   * the final form `qmThetaSymmetricCurve_of_alg`;
   * with `IgusaAlg 3` and `IgusaAlg 4` proved in Lean (§4):
     `qmThetaSymmetricCurve_of_alg59 : LinYangThetaCurve → (∀ k, 5 ≤ k → k ≤ 9 → IgusaAlg k) →
     QMThetaSymmetricCurve`.

   The three statements:
   * **LEAF (composite) `LinYangThetaCurve`.** Along `τ ↦ Ω(τ)`, `ψ₄ψ₆ = 2¹²3⁵χ₁₀` and
     `ψ₄³ + ψ₆² = 2¹²3⁶χ₁₂`, where `ψ₄, ψ₆, χ₁₀, χ₁₂` are given by Igusa's theta expressions. This is
     Lin–Yang's Example 29 vector `s₃²/s₂³ = j`, `s₅/(s₂s₃) = 1`, `s₆/s₂³ = j+1` with `j` eliminated,
     so it is weaker than the printed statement. It is numerically VERIFIED at 80 digits.
   * **GLUE `IgusaThetaSymmetric`.** Seven global identities `e_k(θ_m⁸) = P_k(ψ₄,ψ₆,χ₁₀,χ₁₂)` on
     `𝔥₂` with explicit `P_k`, each having 3 to 8 monomials. These are where Igusa's structure
     theorem would be used. Here they need no structure theorem: by the duplication formula
     (proved) they reduce to
   * **GLUE `IgusaAlg k`.** Closed polynomial identities in four complex variables of degree `8k`.
     All seven are VERIFIED by exact symbolic expansion (`py/verify_pk.py`). `k = 3, 4` are **proved in
     Lean** by `ring`. `k = 5..9` (degrees 40-72) exceed the memory budget of every proof method tried
     (§4).

   Substituting the leaf into the `P_k` reproduces theta-split's numerically fitted `qmR k` exactly
   for every `k = 3..9`. The Lean proof does this in `qmThetaSymmetricCurve_of`. So the `R_k` now
   have an exact derivation.

**Verdict.** Route 1 for `thetaRatiosAlgebraic` now rests on:
* `ThetaEightSquare`, proved;
* one composite literature leaf in printed variables, `LinYangThetaCurve`;
* five closed polynomial identities `IgusaAlg 5..9` with no analytic content. Each is verified by exact
  computer algebra; none is proved in Lean. `IgusaAlg 3` and `IgusaAlg 4` are proved in Lean.

Neither Igusa's structure theorem nor any modularity theorem is needed as a leaf.

## 2. Statements (`scratch/theta-glue/ThetaGlue.lean`, namespace `HDec.HSyn.G0Split.ThetaPt.ThetaGlue`)

| name | kind | content | status |
|---|---|---|---|
| `thetaEight`, `qmR`, `ThetaEightSquare`, `QMThetaSymmetricCurve` | verbatim copies | from scratch/theta-split/ThetaUse.lean | compiled |
| `thetaEightSquare` | theorem | `ThetaEightSquare` | **PROVED** |
| `thetaConst_sq_eq` | theorem | duplication formula on `𝔥₂` | **PROVED** |
| `psi4Th`, `psi6Th`, `chi10Th`, `chi12Th` | definitions | Igusa's theta expressions (§3) | — |
| `LinYangThetaCurve` | LEAF (composite) | along `Ω(τ)`: `ψ₄ψ₆ = 2¹²3⁵χ₁₀`, `ψ₄³+ψ₆² = 2¹²3⁶χ₁₂` | cited; numerically VERIFIED |
| `igusaP` | definition | the seven `P_k` | from `py/pk.py` |
| `IgusaThetaSymmetric` | GLUE | `∀ Ω ∈ 𝔥₂, 3 ≤ k ≤ 9: e_k(θ⁸) = P_k(ψ₄,ψ₆,χ₁₀,χ₁₂)` | ⇐ `IgusaAlg` |
| `Sq`, `IgusaAlg k` | GLUE (closed) | `∀ u : {0,1}² → ℂ`, with `t_m = Σ_c ±u_c u_{c+a}`: `e_k(t⁴) = P_k(ψ₄(t), …)` | exact expansion VERIFIED; Lean: §4 |
| `qmThetaSymmetricCurve_of` | theorem | LEAF + GLUE ⇒ `QMThetaSymmetricCurve` | **PROVED** |
| `igusaThetaSymmetric_of_alg` | theorem | `IgusaAlg 3..9` ⇒ `IgusaThetaSymmetric` | **PROVED** |
| `qmThetaSymmetricCurve_of_alg` | theorem | LEAF + `IgusaAlg 3..9` ⇒ `QMThetaSymmetricCurve` | **PROVED** |
| `igusaAlg3`, `igusaAlg4` | theorems | `IgusaAlg 3`, `IgusaAlg 4` | **PROVED** (`ring`) |
| `qmThetaSymmetricCurve_of_alg59` | theorem | LEAF + `IgusaAlg 5..9` ⇒ `QMThetaSymmetricCurve` | **PROVED** |

The whole file compiles with no `sorry` in 6 min 23 s, with a peak of 23.5 GB, mostly from `igusaAlg4`.
All twelve `#print axioms` lines are `[propext, Classical.choice, Quot.sound]` (VERIFIED). For a lighter
check, remove §7. That section is also available as the standalone files `Alg3.lean` and `Alg4.lean`,
which carry their own copies of the definitions and take 1 min 36 s and 4 min 21 s.

Combined with theta-split's `qmThetaSymmetricCore_of` and `thetaPointOfFibre_of_qm_curve`, this gives:
`ThetaPointOfFibre ⇐ FibreQMPeriod ∧ LinYangThetaCurve ∧ IgusaAlg 3..9`.

## 3. Igusa's forms in second-order theta constants (exact, `py/`)

Every even `θ_m²` is a quadratic form `S_m(U)` in `U = (U₀₀, U₀₁, U₁₀, U₁₁)`. The four `m = (00, b)` give
`U₀₀² ± U₀₁² ± U₁₀² ± U₁₁²`; the six others give `2(U_cU_{c'} ± U_dU_{d'})`. Results:

* **Modularity criterion** (`py/invariants.py`, after Runge). A polynomial of degree `2k` in `U` is
  invariant under the images of generators of `Sp₄(ℤ)`:
  * `U₁₀,U₁₁ ↦ iU₁₀,iU₁₁`;
  * `U₀₁,U₁₁ ↦ iU₀₁,iU₁₁`;
  * `U₁₁ ↦ −U₁₁`;
  * permutations of `U₀₁,U₁₀,U₁₁`;
  * `U ↦ (H/2)U`, where `U(−Ω⁻¹) = s(H/2)U(Ω)` with `s² = det(−iΩ)` (numerically VERIFIED,
    `py/jtrans.py`).

  The invariant dimensions are 1, 1, 1, 2, 3, 2, 4 in weights 4 to 16. These equal Igusa's
  `dim M_k(Sp₄(ℤ))` (VERIFIED, computed).
* `ψ₄ = Σθ⁸/4` and `χ₁₀ = −∏θ²/2¹⁴` are invariant, with `ψ₄|diag = E₄⊗E₄` and `χ₁₀|diag = 0`.
* The normalized weight-6 invariant `ψ₆` restricts to `E₆⊗E₆`.
* The weight-12 form with `χ₁₂|diag = Δ⊗Δ` equals **Igusa's theta expression**
  `2⁻¹⁷3⁻¹ Σ_{15 Göpel quadruples Q} ∏_{m∉Q} θ_m⁴` exactly (VERIFIED, exact).
* **Signs of `ψ₆`** (`py/signs.py`). The generators permute the ten `θ_m⁴` up to sign and act
  transitively on the 60 syzygous triples. So the signs in `ψ₆ = 2⁻² Σ_{syzygous} ±(θθθ)⁴` are forced,
  and with them the expression equals `ψ₆` exactly. Igusa's printed sign rule was not available to
  check (UNVERIFIED); the signs used are the unique modular ones.
* **Global identities** (`py/pk.py`, `py/verify_pk.py`). `e_k(θ_m⁸) = P_k(ψ₄,ψ₆,χ₁₀,χ₁₂)` holds for
  `k = 3..9` as polynomial identities in `Q[U]`, checked by full expansion. The `e_k` have 119 to 1533
  terms. For example:
  * `e₃ = (116/27)ψ₄³ − (8/27)ψ₆² + 2¹⁵3·11χ₁₂`, where `1081344 = 2¹⁵·3·11`;
  * `e₉ = 2⁴⁸χ₁₂³ − (246290604621824/27)ψ₆χ₁₀³ − (175921860444160/3)ψ₄χ₁₀²χ₁₂`.

  The `k = 3` case agrees with theta-split's diagonal computation (`py/lycheck.py` there).
* **Along the curve** (`py/curve_check.py`, 80 digits, at 12 random `τ`). Lin–Yang's relations hold
  at the Lean `Ω(τ)`, with relative residuals ≤ 9e-78 and ≤ 5e-75. Also `j_θ = ψ₆²/ψ₄³`.

## 4. Lean status of `IgusaAlg k`

| k | degree in `U` | terms of `e_k` | Lean | method, time, peak memory (VERIFIED, `lake env lean`) |
|---|---|---|---|---|
| 3 | 24 | 119 | **PROVED** (`igusaAlg3`) | unfold + one `ring`; 1 min 36 s, 14 GB |
| 4 | 32 | 249 | **PROVED** (`igusaAlg4`) | unfold + one `ring`; 4 min 21 s, 21.4 GB |
| 5 | 40 | 447 | not proved | one `ring`: not done after 10 min at 21.7 GB; split proof: >24 GB |
| 6-9 | 48-72 | 721-1533 | not proved | (larger) |

All seven are VERIFIED by exact symbolic expansion in `Q[U]` (`py/verify_pk.py`, 1 s).

Methods tried for `k ≥ 5` (all VERIFIED by running; details in the log):
* one `ring` after unfolding;
* a dynamic programme with `ring_nf` after each step;
* an integer-coefficient identity in a generic `CommRing`;
* `grind (ringSteps := 10⁸)`;
* a split proof. This used the convolution `e_k(Y₀..Y₉) = Σ_a e_a(Y₀..Y₄)e_{k−a}(Y₅..Y₉)`, proved
  generically, together with explicit normal forms checked by separate `ring` calls. Profiling showed
  that most of the time went into elaborating long polynomial texts.
* proof by reflection: verified list-based polynomial arithmetic, about 150 lines, sound for all inputs
  (`gen/reflect_core.lean`, compiles), evaluated by `decide +kernel`. It proves the `k = 3` identity,
  but the kernel evaluates only about 10³ term products per second, and large literals are expensive
  to elaborate.

None of these brings `k = 5` under the 24 GB memory cap of this task. The obstruction is engineering,
not mathematics. A faster certified polynomial normalizer (or a larger memory budget for `ring`) would
close `IgusaAlg 5..9` mechanically. The statements are closed, explicit and small: each is one line of
`igusaP` plus the definitions in §4 of the Lean file.

## 5. The leaf

`LinYangThetaCurve` is a composite leaf, in the same way as the project's `PkgI1.QMHauptmodul`. It
combines three inputs:
1. Lin–Yang's printed vector on the QM curve (Math. Z. 295 (2020); arXiv:1807.00466v1, Example 29,
   eqs. (13)-(14)), with `j` normalized at the CM points of discriminants −4 and −24, as restated in
   scratch/h-v14/igusa_check.py.
2. Igusa's theta expressions (Amer. J. Math. 89 (1967)).
3. The identification of `Ω(τ)` as the period matrix of the principally polarized QM surface at `τ`
   (pkg-I1 §4).

Eliminating `j` makes the leaf weaker than the printed statement. A more faithful form would quantify
over all `Ω ∈ 𝔥₂` that carry a concrete QM structure: integer matrices for `i, j` with `i² = 2`,
`j² = −3`, `ij = −ji`, holomorphic and Rosati-compatible. It would then leave as glue the fact that
`Ω(τ)` carries this structure, which bp-analytic's lattice lemmas could prove. This was not attempted.

## 6. Files

| file | content |
|---|---|
| `ThetaGlue.lean` | all Lean above (§0-§7 in the file) |
| `Dup.lean` | development copy of the duplication formula and `ThetaEightSquare` (namespace `HDec.ThetaGlue`) |
| `Alg3.lean`, `Alg4.lean` | standalone proofs of `IgusaAlg 3`, `IgusaAlg 4` (copies of the definitions) |
| `gen/alg_prefix.lean`, `gen/gen_alg_*.py` | generators of the `IgusaAlg` proofs (tree, DP, split, generic-ring variants) |
| `gen/reflect_core.lean`, `gen/gen_reflect.py` | proof-by-reflection experiment (verified list polynomials) |
| `py/poly.py`, `py/linalg.py` | exact polynomials and linear algebra over `Q` |
| `py/dup_num.py`, `py/dup_sym.py`, `py/jtrans.py` | duplication formula (numeric and symbolic), `J`-transformation |
| `py/igusa.py`, `py/invariants.py`, `py/igusa2.py`, `py/signs.py` | characteristics, modular invariants, `ψ₆`, `χ₁₂` |
| `py/pk.py`, `py/verify_pk.py` (+ output) | the `P_k` and their exact verification |
| `py/hp.py` (copy of theta-split's), `py/curve_check.py` | 80-digit check of the leaf along `Ω(τ)` |
| `gen/gen_igusa.py`, `gen/igusa_defs.lean` | generator of the Lean definitions |

## 7. Integration notes

* Replace theta-split's two GLUE fields. In `GluePieces3` and its copies, theta-split's Route 1 has the
  fields `ThetaEightSquare` and `QMThetaSymmetricCurve`. `ThetaEightSquare` is now a theorem
  (`ThetaGlue.thetaEightSquare`), so drop that field. Replace `QMThetaSymmetricCurve` with the fields
  `LinYangThetaCurve` (LEAF) and `∀ k, 5 ≤ k → k ≤ 9 → IgusaAlg k` (GLUE), and use
  `qmThetaSymmetricCurve_of_alg59` together with theta-split's `thetaPointOfFibre_of_qm_curve`.
* The verbatim copies `thetaEight`, `qmR`, `ThetaEightSquare` and `QMThetaSymmetricCurve` in §0 must be
  identified with theta-split's originals. The texts are identical; check with `Iff.rfl` once both
  files are in one module.
* The leaf list gains `LinYangThetaCurve`, a composite leaf in the same style as `PkgI1.QMHauptmodul`.
  It loses `ThetaRatiosAlgebraic`.
* `ThetaGlue.lean` needs only TailA's names (`PkgI1.*`, `isSiegel_Omega`, `ZInQ.LeafPush2.IsSiegel`),
  so it can follow TailA in the chain.

## 8. Findings

* The `R_k` that theta-split fitted numerically are now derived exactly: global identities in Igusa's
  generators combined with Lin–Yang's vector give exactly `qmR 3..9`.
* The `χ₁₂` theta expression recalled from Igusa,
  `2⁻¹⁷3⁻¹ Σ_{Göpel Q} ∏_{m∉Q} θ_m⁴`, equals exactly the cusp form normalized by `χ₁₂|diag = Δ⊗Δ`.
  This, together with the 80-digit check of the leaf, confirms the normalizations
  `s₅ = 2¹²3⁵χ₁₀` and `s₆ = 2¹²3⁶χ₁₂` used in scratch/h-v14/igusa_check.py.
* No statement was found false, vacuous or inert.
