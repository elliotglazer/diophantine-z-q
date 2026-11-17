# theta-split: the field `thetaRatiosAlgebraic`, replaced by statements on the explicit QM curve

Task theta-split, 2026-11-14. Base 484eddb1 (wip/w61). Lean: `scratch/theta-split/ThetaUse.lean`
(imports `ZInQKernel.OneProof.H.TailA`); numerics `scratch/theta-split/py/`; results log
`scratch/theta-split/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another task's notes or scratch
was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. Theorem numbers and locators recalled without a source are **UNVERIFIED**
(no network here).

## 1. Main result

**How the field is used.** Every consumer of `G0Split.ThetaPt.ThetaRatiosAlgebraic` (TailA l.5010, TailD
l.588, TailE l.6663, TailI l.257, TailK l.322, TailO, TailZ4) passes it to
`ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`. That theorem uses the field once: at the period matrix
`Ω(τ)` (pkg-I1 / bp-analytic `Omega`, the period matrix of the QM lattice `ι(𝒪)(τ,1)ᵀ`) for the `τ`
supplied by `FibreQMPeriod`, where `jNum(Ω(τ))/jDen(Ω(τ)) = J(u)` with `u ∈ ℚ \ 𝒞`. So `j_θ(Ω(τ)) ∈ ℚ \ {0}`
(VERIFIED, read). These are **infinitely many points of the explicit one-parameter family `τ ↦ Ω(τ)`, not
finitely many CM points**, and by the project's NoCM step (`G0FibreSimple.FibreComTrivial`, TailC l.1140)
the fibre surfaces have no CM there. Shimura's theorem on theta values at CM points therefore does not
apply directly at the points of use.

**What is proved (VERIFIED: compiled, no `sorry`, every `#print axioms` = `[propext, Classical.choice,
Quot.sound]`).**

1. *The use form replaces the field.*
   `thetaPointOfFibre_of_qm_atQM : FibreQMPeriod → ThetaRatiosAtQM → ThetaPointOfFibre`
   is a drop-in replacement for `thetaPointOfFibre_of_qm_ratios` (same `hQM`). `ThetaRatiosAtQM` speaks
   only about the explicit functions `τ ↦ θ_m(0, Ω(τ))`: no abelian variety, no polarization, no
   uniformization. qm-glue's finding (no polarization object in `PkgI3.AbVar`, so no further reduction)
   was about the universal form; **the use does not need a polarization object**. qm-split's leaf
   `ThetaNullNonvanishing` is not needed either: `J(u) ≠ 0` forces all ten even theta constants at
   `Ω(τ)` to be nonzero.
2. *Route 1: one explicit closed statement.*
   `thetaPointOfFibre_of_qm_core : FibreQMPeriod → QMThetaSymmetricCore → ThetaPointOfFibre`, and the core
   splits further: `qmThetaSymmetricCore_of : ThetaEightSquare → QMThetaSymmetricCurve →
   QMThetaSymmetricCore`. Here `ThetaEightSquare` is the global genus-2 identity `Σθ_m¹⁶ = (Σθ_m⁸)²/4` on all
   of `𝔥₂`, and `QMThetaSymmetricCurve` is the part `3 ≤ k ≤ 9`, which is specific to the curve (final form
   `thetaPointOfFibre_of_qm_curve`).
   `QMThetaSymmetricCore` says that along the curve the elementary symmetric functions of the ten even
   `θ_m(Ω(τ))⁸` are explicit polynomials with rational coefficients in `j_θ(Ω(τ))`, times powers of
   `Σθ_m⁸`, for `2 ≤ k ≤ 9`. The cases `k = 0, 1, 10` are proved. The core is
   **numerically VERIFIED** (80-digit arithmetic at 30 random points, worst relative residual `7.5·10⁻⁷⁷`),
   and **`k = 3` is cross-checked against Lin–Yang's printed Igusa vector of the QM curve**: an independent
   computation from Lin–Yang's vector and Igusa's forms predicts exactly `R_3 = 283/3888 + j/972`. Every
   constant term `R_k(0)` is checked against the product point `diag(i, i)`, i.e. `E_i × E_i`.
   It is GLUE. It is a consequence of Igusa's theta expressions and structure theorem plus Lin–Yang's
   vector (Example 29, the manuscript's own F1 input), with the same identification of `τ ↦ Ω(τ)` with
   the QM locus that F1 uses.
3. *Route 2: the arithmetic input is Shimura's CM theorem in its own form.*
   `thetaPointOfFibre_of_qm_cm' : FibreQMPeriod → QMThetaShape → QMCMNodesNumeric →
   ShimuraCMThetaAlgebraic → ThetaPointOfFibre`. The pieces:
   * LEAF `ShimuraCMThetaAlgebraic`: theta-null ratios are algebraic at every `Ω ∈ 𝔥₂` whose lattice
     `Ωℤ²+ℤ²` is stable under a non-real scalar.
   * GLUE `QMThetaShape`: the shape of Route 1's identities with unknown complex coefficients, degree ≤ 3.
     It is analytic, with no arithmetic content, and it follows from the core (`qmThetaShape_of_core`).
   * GLUE `QMCMNodesNumeric`: at four explicit CM points `τᵢ` of the curve, `Σθ⁸ ≠ 0` and the four
     values `j_θ` are pairwise distinct. This is numerically VERIFIED: `j_θ = 0, 81/64, 1296/125, 194481/10⁶`.

   Lean proves that each `Ω(τᵢ)` has scalar CM (`scalarCM_cmTau`, from the lattice `ι(𝒪)(τ,1)ᵀ`), and it
   proves the Lagrange-interpolation and Vieta steps.

**Verdict.** The field `thetaRatiosAlgebraic` can be replaced, with no change to any statement, by
`QMThetaSymmetricCore`, a single closed and numerically verified statement about theta constants along
the explicit curve. Alternatively it can be replaced by Shimura's CM theorem in published form
(restricted), one analytic shape statement and four numerical facts. Neither route needs a polarization
on `PkgI3.AbVar`. The universal `ThetaRatiosAlgebraic` itself is untouched; it is true by the model
argument (`NS(A_ℚ̄) = NS(A_ℂ)` plus GAGA plus algebraicity of theta nulls of ppav over `ℚ̄`), but it is
stronger than the use.

## 2. The statements (`scratch/theta-split/ThetaUse.lean`, namespace `HDec.HSyn.G0Split.ThetaPt.ThetaSplit`)

| name | kind | content | status |
|---|---|---|---|
| `ThetaRatiosAlgebraicCopy` | copy | verbatim copy of the field; `Iff.rfl` with `ThetaPt.ThetaRatiosAlgebraic` | compiled |
| `ThetaRatiosAtQM` | GLUE (use form) | `Im τ > 0`, `jNum(Ω(τ))/jDen(Ω(τ)) = q ∈ ℚ\{0}` ⇒ `∃ m₀, θ_{m₀}(Ω(τ)) ≠ 0 ∧ ∀ m, θ_m/θ_{m₀}` algebraic | reduced (routes 1, 2) |
| `QMThetaSymmetric` | GLUE | `∃ R_k ∈ ℚ[X]`, `∀ τ` with `Σθ⁸ ≠ 0`, `∀ k ≤ 10`: `e_k(θ_m⁸) = R_k(j_θ)·(Σθ⁸)^k` | ⇐ core |
| `QMThetaSymmetricCore` | GLUE (explicit, closed) | the same with `R_k = qmR k` (§3), `2 ≤ k ≤ 9` | ⇐ the next two |
| `ThetaEightSquare` | GLUE (global Siegel identity) | `∀ Ω ∈ 𝔥₂`, `Σ_{m even} θ_m¹⁶ = (Σ_{m even} θ_m⁸)²/4` | numerically VERIFIED; derivation from `dim M₈(Sp₄(ℤ)) = 1` (Igusa 1962) |
| `QMThetaSymmetricCurve` | GLUE (explicit, closed) | the core for `3 ≤ k ≤ 9` | numerically VERIFIED |
| `QMThetaShape` | GLUE (analytic) | `∃ R_k ∈ ℂ[X]`, `deg ≤ 3`, the same identities | ⇐ core |
| `ShimuraCMThetaAlgebraic` | LEAF (consequence of Shimura) | `Ω ∈ 𝔥₂`, `w ∉ ℝ`, `w(Ωℤ²+ℤ²) ⊆ Ωℤ²+ℤ²`, `θ_{m'}(Ω) ≠ 0` ⇒ `θ_m(Ω)/θ_{m'}(Ω)` algebraic | cited |
| `QMCMNodes` | GLUE | four `τᵢ ∈ ℍ` with scalar CM, `Σθ⁸ ≠ 0`, distinct `j_θ` | ⇐ `QMCMNodesNumeric` |
| `QMCMNodesNumeric` | GLUE (closed, numeric) | at the explicit `cmTau i`: `Σθ⁸ ≠ 0` and `j_θ` injective | numerically VERIFIED |

Proved theorems (all compiled, standard axioms):

| theorem | statement |
|---|---|
| `Jmap_ne_zero` | `u ∉ 𝒞 → J(u) ≠ 0` (as kernel `J_ne_zero`, reproved) |
| `thetaPointOfFibre_of_qm_atQM` | `FibreQMPeriod → ThetaRatiosAtQM → ThetaPointOfFibre` |
| `isAlgebraic_of_esymm` | a root of a monic polynomial over `ℂ` with rational elementary symmetric functions is algebraic |
| `thetaRatiosAtQM_of_symmetric` | `QMThetaSymmetric → ThetaRatiosAtQM` |
| `esymm_one`, `esymm_ten` | `e_1(θ⁸) = Σθ⁸`; `e_10(θ⁸) = j_θ²(Σθ⁸)¹⁰/3779136²` (from the definitions of `jNum`, `jDen`) |
| `qmR_identity`, `qmThetaSymmetric_of_core` | core ⇒ all `k ≤ 10` ⇒ `QMThetaSymmetric` |
| `thetaPointOfFibre_of_qm_core` | `FibreQMPeriod → QMThetaSymmetricCore → ThetaPointOfFibre` |
| `two_esymm_two`, `qmThetaSymmetricCore_of`, `thetaPointOfFibre_of_qm_curve` | `2e_2 = p_1² − p_2`; `ThetaEightSquare → QMThetaSymmetricCurve → QMThetaSymmetricCore`; Route 1 in final form |
| `qmThetaShape_of_core` | `QMThetaSymmetricCore → QMThetaShape` |
| `mem_of_esymm_mem`, `esymm_mem` | the same with algebraic coefficients (`algebraicClosure ℚ ℂ`); symmetric functions of algebraic numbers |
| `eval_mem_of_nodes` | Lagrange interpolation: `deg R ≤ 3` and algebraic values at 4 distinct algebraic nodes ⇒ `R(q)` algebraic for algebraic `q` |
| `node_values` | at a scalar-CM point with `Σθ⁸ ≠ 0`: `j_θ` and every `e_k(θ⁸)/(Σθ⁸)^k` are algebraic (from the leaf) |
| `thetaRatiosAtQM_of_cm`, `thetaPointOfFibre_of_qm_cm` | `QMThetaShape → QMCMNodes → ShimuraCMThetaAlgebraic → ThetaRatiosAtQM` (resp. `ThetaPointOfFibre` with `FibreQMPeriod`) |
| `iota_mul'`, `latVec_mul`, `latVec_sum` | `ι` multiplicative and additive; `ι(bμ)(τ,1)ᵀ = ι(b)·ι(μ)(τ,1)ᵀ` |
| `scalarCM_of_stable` | `w·ι(b_k)(τ,1)ᵀ ∈ ι(𝒪)(τ,1)ᵀ` for all `k` ⇒ `ScalarCM (Ω(τ)) w` (through bp-analytic's `map_periodLattice_Omega`) |
| `latVec_node` | for `μ = x + y i + z j`: `ι(μ)(τ,1)ᵀ = w(τ,1)ᵀ` at `τ = (y√2 + i√(3z²−2y²))/z`, `w = x + i√(3z²−2y²)` |
| `node_mul`, `scalarCM_cmTau` | right multiplication tables of the four `μᵢ`; each `Ω(τᵢ)` has scalar CM |
| `qmCMNodes_of_numeric`, `thetaPointOfFibre_of_qm_cm'` | `QMCMNodesNumeric → QMCMNodes`; Route 2 in final form |

## 3. The explicit identities (Route 1)

Write `E_k = e_k(θ_m(Ω(τ))⁸ : m even)`, `E_1 = Σθ_m⁸ = 4ψ₄`, `j = j_θ(Ω(τ)) = 3779136(∏θ_m)⁴/E_1⁵`.
Along the curve `E_k = R_k(j)·E_1^k` with

| k | `R_k(j)` (`qmR k`) |
|---|---|
| 0, 1 | `1` (identities) |
| 2 | `3/8` (global: `Σθ_m¹⁶ = (Σθ_m⁸)²/4` on all of `𝔥₂`, weight 8 has dimension 1) |
| 3 | `283/3888 + j/972` |
| 4 | `1529/186624 − j/1458` |
| 5 | `13/23328 + 17j/314928` |
| 6 | `521/22674816 + 95j/5668704 + j²/2834352` |
| 7 | `19/34012224 + 313j/272097792 − j²/2834352` |
| 8 | `1/136048896 + 107j/3673320192 + 49j²/1836660096` |
| 9 | `(1 + 9j/8 + j²/4 + j³)/24794911296` |
| 10 | `j²/3779136²` (identity, proved: `e_10 = ∏θ⁸`) |

`deg R_k = ⌊k/3⌋`. The coefficients come from `py/fit_hp.py`, with `d+1` points used for the fit and the
remaining points as checks: residuals `≤ 5·10⁻⁷⁵`, and denominators of the form `2^a3^b`. They are checked
independently by `py/verify.py` at 30 fresh points with `0.35 ≤ Im τ ≤ 3`, `|Re τ| ≤ 3`: worst relative
residual `7.5·10⁻⁷⁷`. Truncation of the theta series is checked (`N = 22` against `N = 30`: identical to 80
digits). `py/leanpoly.py` parses `qmR` out of the Lean file and compares it with the table: ALL MATCH.
`py/hp.py` reproduces `j_θ(Ω(i√(9+6√2))) = −16/27` to 78 digits. All of this is VERIFIED (computed).

**Cross-check with Lin–Yang (VERIFIED, computed, `py/lycheck.py`).** On diagonal period matrices
`diag(τ₁, τ₂)` (theta constants factor into genus-1 ones, `ψ₄ = E₄⊗E₄`, `ψ₆ = E₆⊗E₆`, `χ₁₂ = Δ⊗Δ`) one finds
`e_3(θ⁸) = (116/27)ψ₄³ − (8/27)ψ₆² + 1081344·χ₁₂` (residual `10⁻⁷⁷`; weight 12 has no `χ₁₀` term, so this is
the global identity). Lin–Yang's vector on the QM curve, as restated in `scratch/h-v14/igusa_check.py`, is
`[ψ₄ : ψ₆ : 2¹²3⁵χ₁₀ : 2¹²3⁶χ₁₂] = [j : j² : j³ : j³(j+1)]`. Together these predict
`E_3/E_1³ = (116/27 − 8j/27 + 1081344(j+1)/2985984)/64 = 283/3888 + j/972`, which matches. So the core is
consistent with the manuscript's own printed input, in the same theta normalization that F1 uses.

**Constant terms (VERIFIED, computed, `py/check_j0.py`).** For `k = 2, …, 10`, `e_k/e_1^k` at
`Ω = diag(i, i)` equals `R_k(0)`, with relative difference `≤ 10⁻⁷⁷`. So the `j = 0` point of the curve
(`τ = √2 + i`) is the product `E_i × E_i` with the product polarization, up to `Sp₄(ℤ)`. There
`θ_m⁴ ∝ (1/2, 1, 1/2) ⊗ (1/2, 1, 1/2)` (Jacobi: `θ₂(i)⁴ = θ₄(i)⁴ = θ₃(i)⁴/2`), so the constant terms are
explained exactly by genus-1 data.

**Global versus curve (VERIFIED, computed, `py/global_ids.py`).** `e_2 = (3/8)e_1²` holds at 16 random
`Ω ∈ 𝔥₂` (`ThetaEightSquare`). `e_6, …, e_9` are not polynomials in `e_1, e_3, e_4, e_5` on `𝔥₂`, because
the `θ⁸`-symmetric forms do not separate `ψ₆²` from `χ₁₂`. So the seven curve identities do not reduce to
fewer curve identities through global `θ⁸`-symmetric identities.

**Why the core is true (derivation; model argument, locators UNVERIFIED).**

1. `e_k(θ_m⁸)` is a Siegel modular form of weight `4k` for `Sp₄(ℤ)`. The theta transformation formula
   permutes the even `θ_m⁸` with the common factor `det(CΩ+D)⁴` (Igusa, *Theta functions*, 1972, Ch. V;
   Mumford, *Tata I*, II §5). It has rational Fourier coefficients.
2. By Igusa's structure theorem it is therefore a polynomial over `ℚ` in `ψ₄, ψ₆, χ₁₀, χ₁₂` (Igusa, Amer. J.
   Math. 84 (1962), 86 (1964)).
3. On the QM locus Lin–Yang's vector holds (Lin–Yang, arXiv:1807.00466v1, Example 29 with eqs. (13)-(14);
   Baba–Granath, Canad. J. Math. 60 (2008), Prop. 3.6). `τ ↦ Ω(τ)` parametrizes that locus with `j = j_θ`.
   This is the identification that F1, `FibreQMPeriod` and `PkgI1.QMHauptmodul` already rest on.

Substituting gives the core. Steps 1-2 are global identities of Siegel modular forms (provable from
finitely many Fourier coefficients). Step 3 is the published input.

## 4. Route 2 in detail

* **`ShimuraCMThetaAlgebraic` (LEAF).** The hypothesis `w(Ωℤ²+ℤ²) ⊆ Ωℤ²+ℤ²` with `w ∉ ℝ` makes
  `Λ ⊗ ℚ` a 2-dimensional `K = ℚ(w)`-space with `K ⊗ ℝ = ℂ` acting by scalars. So `ℂ²/Λ` is isogenous to
  `(ℂ/𝒪_K)²`, a CM abelian surface (elementary). Shimura's theorem then gives algebraic theta-null ratios at
  CM points: Shimura, *Theta functions with complex multiplication*, Duke Math. J. 43 (1976), 673–696.
  Equivalently: Siegel modular functions with algebraic Fourier coefficients take algebraic values at CM
  points (Shimura, Ann. of Math. 102 (1975)); `θ_m/θ_{m'}` has level `(4,8)` and coefficients in `ℚ(ζ₈)`.
  All locators are UNVERIFIED. Form: the published statement restricted to this kind of CM point, so it is
  weaker than the published statement. The elementary step is not formalized.
* **`QMThetaShape` (GLUE, analytic).** `E_k/E_1^k ∘ Ω` is `Γ*`-invariant (step 1 of §3 through the modular
  embedding `Ω(γτ) = M_γ·Ω(τ)`, pkg-I1 §4). It is meromorphic on the compact curve `Γ*\ℍ`, whose
  Hauptmodul is `j_θ ∘ Ω` (`PkgI1.QMHauptmodul`), and its poles lie only at the zeros of `E_1 ∘ Ω`. Hence it
  is a polynomial in `j_θ`. The degree bound `⌊k/3⌋` is observed numerically. The statement is implied by
  the core.
* **`QMCMNodesNumeric` (GLUE, numeric).** The nodes are the fixed points of `ι(μ)` for `μ = i + j`,
  `1/2 + i + (3/2)j`, `i + 2j`, `1/2 + 2i + (5/2)j` (discriminants `−4, −19, −40, −43`):
  `τ = √2 + i, (2√2 + i√19)/3, (√2 + i√10)/2, (4√2 + i√43)/5`, with `w = i, (1+i√19)/2, i√10, (1+i√43)/2`.
  `py/verify_nodes.py` (80 digits) gives `|Σθ⁸| = 33.9, 12.2, 6.84, 18.1` and `j_θ = 0` (`|j| < 2·10⁻³¹⁵`),
  `81/64`, `1296/125`, `194481/10⁶` (errors `≤ 10⁻⁷⁶`). These are Elkies' rational CM values of `X*(6)`
  (STANDARD; Elkies, ANTS-III 1998; table locator UNVERIFIED). `81/64` is the discriminant `−19` value that
  `igusa_check.py` cites from Lin–Yang. A Lean proof would need certified evaluation of the theta series at
  four points; this was not attempted.
* The CM clause is proved: `scalarCM_cmTau`. `w·ι(b)(τ,1)ᵀ = ι(bμ)(τ,1)ᵀ ∈ ι(𝒪)(τ,1)ᵀ`, with explicit
  integer tables `b_kμ = Σ n_{kl} b_l` (`node_mul`), and `F'(τ)` is `ℂ`-linear (`scalarCM_of_stable`).

Comparison. Route 1 has one GLUE statement, closed and explicit, which a contributor can attack directly
(it is a finite list of identities among theta constants on an explicit curve). Route 2 puts all arithmetic
into a published theorem in its own form. Its GLUE is either analytic (shape) or a numerical fact at four
explicit points.

## 5. Other CM points found (`py/cmnodes.py`, double precision)

| D | `j_θ` | D | `j_θ` |
|---|---|---|---|
| −3, −12, −27 | `∞` (`Σθ⁸ ≈ 0`, product polarization) | −43 | `194481/1000000` |
| −4, −16, −36 | `0` | −51 | `−2401/1728` |
| −19, −76 | `81/64` | −52 | `−5184/15625` |
| −24 | `−16/27` | −84 | `−3136/729` |
| −40 | `1296/125` | −67, −100 | `≈ 44.49, 140.52` (not rational at this precision) |

## 6. Files and checks

| file | content | check |
|---|---|---|
| `scratch/theta-split/ThetaUse.lean` | all Lean above | `lake build ZInQKernel.OneProof.H.TailA` once (builds the two upstream `lean/` helper modules, 6 s), then `lake env lean scratch/theta-split/ThetaUse.lean` (~20 s) |
| `scratch/theta-split/T0.lean` | import/name check | same |
| `py/hp.py` | 80-digit theta constants at the Lean `Ω(τ)` (pure Python, `decimal`) | `python3` |
| `py/fit_hp.py`, `py/verify.py` (+ `.output.txt`), `py/leanpoly.py` (+ `.output.txt`) | fit, 30-point check, Lean table check | `python3` (no numpy/mpmath needed) |
| `py/lycheck.py` | Lin–Yang cross-check of `R_3` | `python3` |
| `py/check_j0.py`, `py/global_ids.py` (+ `.output.txt`) | constant terms at `diag(i,i)`; global identities on `𝔥₂` | `python3` |
| `py/cmnodes.py`, `py/nodes_lean.py`, `py/verify_nodes.py` (+ `.output.txt`) | CM points, multiplication tables, node numerics | `python3` |
| `py/dnum.py`, `py/fit.py`, `py/linsolve.py` | double-precision exploration | `python3` |

## 7. Integration notes

* Drop-in: in `GluePieces3` (and its copies TailD, TailE, TailI, TailK, TailO, TailZ4), replace the field
  `thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic` by
  `qmThetaSymmetricCore : ThetaSplit.QMThetaSymmetricCore`, or by the two fields `ThetaEightSquare` and
  `QMThetaSymmetricCurve`. Replace `thetaPointOfFibre_of_qm_ratios hQM gp.thetaRatiosAlgebraic` by
  `ThetaSplit.thetaPointOfFibre_of_qm_core hQM gp.qmThetaSymmetricCore` (respectively
  `thetaPointOfFibre_of_qm_curve`). For Route 2, use the three fields
  `qmThetaShape`, `qmCMNodesNumeric`, `shimuraCM` and `thetaPointOfFibre_of_qm_cm'`.
* `ThetaUse.lean` needs only TailA's names (`ThetaPt.*`, `PkgI1.*`, `BPAnalytic.QM.*`,
  `ZInQ.LeafPush2.thetaConst`), so it can follow TailA in the chain.
* The leaf list gains `ShimuraCMThetaAlgebraic` (Route 2) or nothing (Route 1, where the core is glue). It
  loses `ThetaRatiosAlgebraic` and qm-split's `ThetaNullNonvanishing`/`ThetaFourthRatiosAlgebraic`.

## 8. Findings on existing text

* `ThetaRatiosAlgebraic` as stated (universal over abelian surfaces over number fields,
  uniformizations and period matrices) is **true** by the model argument. The uniformization makes
  `A(ℂ)_σ ≅ ℂ²/Λ` biholomorphically (GAGA). The principal polarization of `Ω` is then a class in
  `NS(A_ℂ) = NS(A_ℚ̄)`, so `(ℂ²/(Ωℤ²+ℤ²), Ω)` is a ppav over `ℚ̄`, and theta-null ratios of ppav over `ℚ̄`
  are algebraic. It is neither vacuous nor false. It is stronger than its use (§1), and it is not one
  printed theorem.
* The docstring of `OpenAddedLeaves2.thetaRatiosAlgebraic` (TailE l.6521) says "theta-constant ratios at a
  CM period matrix are algebraic". That is inaccurate: the field is universal, and it is used at the
  non-CM points `Ω(τ)` with `j_θ = J(u)`. A theorem about CM points alone does not supply the use. The
  route through CM points (Route 2) needs the interpolation glue in addition.
* `ThetaRatiosAlgebraic`'s docstring (TailA l.4371-4385) cites "Shimura, Duke 43 (1976)" for algebraic
  values of Siegel modular functions at points whose ppav is defined over `ℚ̄`. That paper, *Theta functions
  with complex multiplication*, treats CM points (recalled, UNVERIFIED). The statement for arbitrary ppav
  over `ℚ̄` belongs to the arithmetic theory of Siegel modular functions and canonical models (Shimura, Ann.
  of Math. 102 (1975), or Faltings–Chai Ch. V; SPECULATIVE attribution, locators UNVERIFIED).
