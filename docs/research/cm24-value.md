# cm24-value: the field `igusaCMValue24` is a theorem

Task cm24-value, 2026-11-14. Base e38375b3 (wip/w62). Lean: `scratch/cm24-value/` (results log `log.md`,
compile log `compile.out`, script `chk.sh`); numerics and certificates: `scratch/cm24-value/py/`. No file under
`ZInQKernel/`, `blueprint/`, or another task's notes or scratch was edited. This is model work with no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. Locators recalled without a source are **UNVERIFIED** (there is no network here).

## 1. Verdict

**`IgusaCMValue24` is proved in Lean with no leaf and no hypothesis.** VERIFIED: compiled, no `sorry`, and
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem below.

| theorem | type |
|---|---|
| `CM24.igusaCMValue24_field` | `HDec.LeafQCheck.HM.QMSplit.Value24.IgusaCMValue24` (the field `igusaCMValue24`) |
| `CM24.thetaQuotientValue24_field` | `HDec.LeafQCheck.HM.QMSplit.ThetaQuotientValue24` (qm-split's glue) |
| `CM24.thetaValueAtOmega24_field` | `…Value24.ThetaValueAtOmega24`: `jDen Ω₂₄ ≠ 0 ∧ jNum Ω₂₄ / jDen Ω₂₄ = −16/27` |
| `CM24.singularModulus6` (bonus) | `SingularModulus6`: `θ₃(i√6) ≠ 0 ∧ θ₂(i√6)² = (2−√3)(√3−√2)·θ₃(i√6)²` (the classical `λ*(6)`, Mathlib's `jacobiTheta₂`) |

Two files contain the proof, and both compile:

* `scratch/cm24-value/CM24Value.lean` imports only Mathlib. It contains a verbatim copy of
  `scratch/qm-glue/ThetaValue24.lean` (lines 1-447) followed by the proof. Run `lake env lean`; it takes about 15 s.
* `scratch/cm24-value/CM24Kernel.lean` imports `ZInQKernel.OneProof.H.TailZ3` and proves the statement over the
  build's own definitions: `IgusaCMValue24` is `TailZ3.lean` l.1093, the type of the field `igusaCMValue24` in
  `TailZ4.lean` l.153 and `TailZ13.lean` l.37.
  * This file was checked with the oleans of `~/dzq-check2`. Its sources for all 527 modules in the import closure
    of `TailZ3` are byte-identical to this base (compared file by file), and its oleans are newer than the sources.
  * After a local `lake build ZInQKernel.OneProof.H.TailZ3`, `lake env lean` works too.
  * TailZ3's section `Value24` (l.894-1142) is textually identical to the copied qm-glue lines 199-447 (VERIFIED,
    `diff`).

Consequences:

* The published leaf `IgusaCMValue24` (Lin–Yang (2), (14) at the Baba–Granath value) is no longer needed. Row H-88
  (`qmHauptmodulBase3_of_leaves`) loses one leaf.
* The exact value `j_θ(τ₂₄) = −16/27` needs **no CM theory**. It is an elementary consequence of theta identities:
  * the inversion formula;
  * the duplication formula;
  * the cubic modular equation `θ₃(τ)θ₃(3τ) = θ₂(τ)θ₂(3τ) + θ₄(τ)θ₄(3τ)`.

  All three are proved here from Mathlib's `jacobiTheta₂_functional_equation` and series rearrangements.
* qm-glue §2.3 expected that an exact proof would need CM theory. That judgement was too pessimistic.

## 2. The proof (mathematics)

Notation: `θ[c;d](Ω) = Σ_{n∈ℤ²} exp(πi (n+c)ᵀΩ(n+c) + 2πi (n+c)·d)` with real characteristics (`CM24.Th2`).
PkgI1's `thetaConst (a,b) Ω` is `θ[a/2; b/2](Ω)` (`thetaConst_eq`).

1. **An extra involution.** `py/endo.py` computes End(A_{Ω₂₄}) (rank 8). The Sp₄(ℤ)-stabilizer of `Ω₂₄` contains
   `R ≠ ±1`, which is block lower triangular, so its fixed locus becomes the Humbert H₄ normal form after inversion.
   Indeed (VERIFIED, exact sympy):

   `W := −Ω₂₄⁻¹ = [[1 + i√6/2, 1/2], [1/2, 1/2 + i√6/4]]`, and
   `2W = diag(i√6, i√6/2) + [[2,1],[1,1]]`.

   The points `i√6` and `i√6/2` are the CM points of discriminant −24, one for each ideal class.
2. **Inversion** (`invert`, `sq_inv`). Two partial inversions, each one application of Mathlib's one-variable
   functional equation inside a double sum (`pi0`), plus coordinate swaps give
   `θ[a/2;b/2](Ω₂₄)² = 𝓔 · θ[b/2;a/2](W)²` for even `(a,b)`, where `𝓔 = 1/((−iα₀)(−iγ₁)) ≠ 0`.
3. **Duplication at W** (`dup2`, `sqW`) is `θ[c;d](Ω)² = Σ_σ θ[σ/2+c; 2d](2Ω)·θ[σ/2; 0](2Ω)`. It is followed by
   the translation `2W ↦ diag` (`U00`, `U10`, `U01`, `U11`).
   * The values are `U(0,0) = A₀B₁`, `U(½,0) = iA₂B₀`, `U(0,½) = e^{πi/4}A₁B₂` and `U(½,½) = 0`.
   * Here `A_j = θ₀₀, θ₀₁, θ₁₀` at `i√6` and `B_j` are the same at `i√6/2` (`th1`, bridged to Mathlib's
     `jacobiTheta₂` by `th1_eq`).
   * The ten squared theta constants at `Ω₂₄` are `𝓔·(x ± y ± z)`, `𝓔·2U₀₀U₁₀` (twice), `𝓔·2U₀₀U₀₁` (twice) and
     `±𝓔·2U₀₁U₁₀`, with `x = U₀₀²`, `y = U₁₀²`, `z = U₀₁²` (`sqc0`…`sqc9`).
4. **Genus one.**
   * Landen at `i√6/2` (`dupA/B/C`, from the one-variable duplication `dup1`): `B₀² = A₀² + A₂²`, `B₁² = A₀² − A₂²`,
     `B₂² = 2A₀A₂`.
   * Jacobi's identity `A₀⁴ = A₁⁴ + A₂⁴` (`jacobi`, also from `dup1`).
   * With `k = A₂²/A₀²` these give `x = A₀⁴(1−k)`, `y = −A₀⁴k(1+k)` and `z² = −4k(1−k²)A₀⁸`.
5. **The algebraic input.**
   * The cubic modular equation (`cubic`) at `τ' = i√6/3` has `3τ' = i√6`. The S-transformation `τ' = −1/(i√6/2)`
     (`sA`, `sB`, `sC`) turns it into `A₀B₀ = A₂B₁ + A₁B₂`.
   * Squaring twice and eliminating with Landen and Jacobi gives `(k²−2k−1)²·m(k) = 0`, where
     `m(k) = k⁴ + 12k³ + 2k² − 12k + 1` is the minimal polynomial of `k₆ = (2−√3)(√3−√2)` (`mpoly_A`).
   * On the imaginary axis `A₀, A₂ > 0` and `B₁ = (positive real)·θ₁₀(τ')` by S (`th1_imag`, `K_real`). So
     `B₁² > 0`, hence `0 < k < 1` and `k² − 2k − 1 ≠ 0`.
6. **The value.**
   * `F = 3779136·P²/S⁵` with `S = Σ(θ²)⁴` and `P = ∏θ²`. Then `3779136·P² + (16/27)·S⁵` is divisible by `m(k)`
     (degree-36 quotient, `CM24Alg.core`).
   * `S ≠ 0` because `S` and `m` are coprime: a Bezout certificate, `CM24Alg.core_ne`.
   * The radical value of `k` is never needed. Either root of `m` in `(0,1)` gives `−16/27`.

## 3. Lean inventory (all compiled)

| file | content |
|---|---|
| `T1.lean` | `Th2`/`term2` (genus 2, real characteristics); summability; partial inversion `pi0`; swap and shift lemmas; `dup2`; genus-1 `th1`, Mathlib bridge `th1_eq`, `dup1`, `th2_diag`, `th1_odd`; explicit matrices `α0…wc` and `invert`; translation `U00…U11`; cubic modular equation `cubic` |
| `Alg.lean` | `CM24Alg.core`, `core_ne` (identities modulo `m(k)`), `mpoly_k6` (`m((2−√3)(√3−√2)) = 0`) |
| `P3.lean` | bridge `thetaConst_eq`; `sq_inv`, `sqW`, `sqc0…sqc9`; Landen and Jacobi; `SingularModulus6` with `igusaCMValue24_of_singularModulus6`; S-transforms, positivity, elimination `mpoly_A`, `mpoly_theta`; final `thetaValueAtOmega24`, `igusaCMValue24`, `thetaQuotientValue24` and the `_field` forms; bonus `a0_ge_one`, `a2_le`, `a2_lt`, `root_select`, `singularModulus6` |
| `mk.py`, `mk_kernel.py` | assemble `CM24Value.lean` (qm-glue copy + T1 + Alg + P3) and `CM24Kernel.lean` (import TailZ3 + T1 + Alg + P3) |
| `py/` | `endo.py` (End and stabilizer), `w.py` (W), `split.py`/`check2.py`/`conv.py` (numerical checks of every step, 30-50 digits), `exact2.py`, `kpoly.py`, `cert.py`, `bezout.py`, `elim.py` (exact certificates) |

`SingularModulus6` is the classical singular modulus `λ*(6) = (2−√3)(√3−√2)`, stated with Mathlib's
`jacobiTheta₂`. Published form: Borwein–Borwein, *Pi and the AGM*, the table of `λ*(n)` (locator UNVERIFIED). It
was first an intermediate leaf (`igusaCMValue24_of_singularModulus6`). It is now **proved** as a bonus
(`CM24.singularModulus6`); the field does not use it. The proof:
* `mpoly_theta` gives `m(k) = 0`.
* Crude bounds give `θ₀₀(i√6) ≥ 1` (`a0_ge_one`) and `θ₁₀(i√6) < 7/10` (`a2_le`, `a2_lt`: Gaussian tail against a
  geometric series, `e^x ≥ 1 + x`, `π > 3`, `√6 > 12/5`). So `0 < k < 1/2`.
* `m` factors over `ℚ(√2, √3)` into four linear factors, and only one root lies in `(0, 1/2)` (`root_select`).

## 4. Integration notes

* `CM24Kernel.lean` is ready to become a module (for example under `ZInQKernel/Contrib/`) importing
  `ZInQKernel.OneProof.H.TailZ3`.
  * `CM24.igusaCMValue24_field` discharges the field `igusaCMValue24` of the TailZ4/TailZ13 leaf bundles.
  * `CM24.thetaQuotientValue24_field` discharges qm-split's glue `ThetaQuotientValue24`.
  * The namespaces `CM24` and `CM24Alg` are new. `SingularModulus6` is a new top-level name and can be dropped.
* The genus-2 machinery (`Th2`, `pi0`, `dup2`, translation, diagonal factorization) is general. SPECULATIVE: it
  may also give exact values at theta-split's other CM nodes (`QMCMNodesNumeric`).

## 5. What remains

Nothing for this field, and nothing for the bonus value `λ*(6)`. No leaf was introduced.
