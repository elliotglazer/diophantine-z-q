# theta-split results log

## 2026-11-14

- Setup: `lake build ZInQKernel.OneProof.H.TailA` (6 s; only the 2 upstream `lean/` helper modules
  were missing), then scratch files `import ZInQKernel.OneProof.H.TailA` and are checked with
  `lake env lean scratch/theta-split/<file>.lean`. VERIFIED (T0.lean).
- Consumers of `G0Split.ThetaPt.ThetaRatiosAlgebraic` (VERIFIED, read): every consumer (TailA:5010,
  TailD:588, TailE:6663, TailI:257, TailK:322, TailO, TailZ4) passes the field to
  `ThetaPt.thetaPointOfFibre_of_qm_ratios hQM hAlg`, which uses it once, at `Ω = Ω(τ)` (pkg-I1 /
  bp-analytic `Omega`) for the `τ` supplied by `FibreQMPeriod`, i.e. `Im τ > 0` and
  `jNum(Ω(τ))/jDen(Ω(τ)) = J(u)` with `u ∈ ℚ \ 𝒞`. `J(u) ≠ 0` (kernel `J_ne_zero`, PRArith l.131).
- Finding (VERIFIED by the above): the use is at infinitely many period matrices `Ω(τ)`, all on the
  explicit QM curve `τ ↦ Ω(τ)`, with rational nonzero `j_θ`; not at finitely many CM points. The
  fibres are NoCM (`FibreComTrivial`), so a theorem about CM points (Shimura's CM theory) does not
  cover the use.
- Numerics (double precision, `py/dnum.py`, `py/fit.py`; 30 random τ): with `E_k = e_k(θ_m⁸(Ω(τ)))`
  (elementary symmetric functions of the ten even θ⁸) and `j = j_θ(Ω(τ))`:
  `E_2/E_1² = 3/8` (a global Siegel identity), and `E_k/E_1^k` is a polynomial in `j` of degree 1 for
  k = 3, 4, 5 and degree 2 for k = 6, 7 (fit residual ≤ 5e-9); k ≥ 8 needs higher precision.
  E.g. `E_3/E_1³ ≈ 0.0727881 + 0.0010288 j` (`1/972 = 0.00102880…`).
- High-precision numerics (`py/hp.py`: decimal, 80 digits; `py/fit_hp.py`, 14 points, fit with
  d+1 points, check on the rest): `E_k/E_1^k = R_k(j)` with `deg R_k = ⌊k/3⌋` and **rational**
  coefficients, residual ≤ 5e-75 (VERIFIED, computed):
  R_1 = 1, R_2 = 3/8, R_3 = 283/3888 + j/972, R_4 = 1529/186624 − j/1458,
  R_5 = 13/23328 + 17j/314928, R_6 = 521/22674816 + 95j/5668704 + j²/2834352,
  R_7 = 19/34012224 + 313j/272097792 − j²/2834352,
  R_8 = 1/136048896 + 107j/3673320192 + 49j²/1836660096,
  R_9 = (1 + 9j/8 + j²/4 + j³)/24794911296, R_10 = j²/3779136² (trivial identity).
  Check: `j_θ(Ω(i√(9+6√2))) = −16/27` to 78 digits with this code.
- Cross-check against Lin–Yang (`py/lycheck.py`, VERIFIED computed): on diagonal period matrices
  `e_3(θ⁸) = (116/27)ψ₄³ − (8/27)ψ₆² + 1081344·χ₁₂` (ψ₄=E₄⊗E₄, ψ₆=E₆⊗E₆, χ₁₂=Δ⊗Δ; residual 1e-77);
  with Lin–Yang's QM vector `ψ₆²/ψ₄³ = j`, `2¹²3⁶χ₁₂/ψ₄³ = j+1` (as restated in
  scratch/h-v14/igusa_check.py) this predicts `R_3 = 283/3888 + j/972`: MATCH.
- `ThetaUse.lean` (imports `ZInQKernel.OneProof.H.TailA`) COMPILES, no sorry, all four
  `#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED, `lake env lean`, ~20 s):
  verbatim copy `ThetaRatiosAlgebraicCopy ↔ ThetaRatiosAlgebraic := Iff.rfl`;
  `thetaPointOfFibre_of_qm_atQM : FibreQMPeriod → ThetaRatiosAtQM → ThetaPointOfFibre`;
  `thetaRatiosAtQM_of_symmetric : QMThetaSymmetric → ThetaRatiosAtQM`;
  `qmThetaSymmetric_of_core : QMThetaSymmetricCore → QMThetaSymmetric` (k = 0, 1, 10 proved:
  `esymm_one`, `esymm_ten`); `thetaPointOfFibre_of_qm_core`.
- Route 2 added to `ThetaUse.lean` (COMPILES, standard axioms; VERIFIED):
  `thetaRatiosAtQM_of_cm : QMThetaShape → QMCMNodes → ShimuraCMThetaAlgebraic → ThetaRatiosAtQM`,
  `thetaPointOfFibre_of_qm_cm`, `qmThetaShape_of_core : QMThetaSymmetricCore → QMThetaShape`;
  helper lemmas `mem_of_esymm_mem` (roots of monic polys with algebraic coefficients),
  `esymm_mem`, `eval_mem_of_nodes` (Lagrange interpolation, Mathlib `Lagrange.eq_interpolate`),
  `node_values` (j and e_k/S^k algebraic at a scalar-CM point, from the leaf).
- CM points on the curve (`py/cmnodes.py`, double precision): fixed points of ι(μ), μ ∈ 𝒪, give
  j_θ = 0 (D=−4, τ=√2+i), 81/64 (D=−19), −16/27 (D=−24), 1296/125 (D=−40), 194481/10⁶ (D=−43),
  −2401/1728 (D=−51), −5184/15625 (D=−52), −3136/729 (D=−84); D=−3 (and −12, −27) has Σθ⁸ ≈ 0
  (j = ∞). Values recognized to 1e-10 (double precision), match Elkies' rational CM points on X*(6)
  (STANDARD, Elkies, *Shimura curve computations*, ANTS 1998, UNVERIFIED table locator).
- §6 of `ThetaUse.lean` COMPILES (standard axioms, VERIFIED): `iota_mul'`, `latVec_mul`,
  `scalarCM_of_stable` (lattice stability ⇒ `ScalarCM (Ω(τ)) w`, via bp-analytic's
  `map_periodLattice_Omega`), `latVec_node` (fixed point of `ι(x + y i + z j)` is
  `τ = (y√2 + i√(3z²−2y²))/z`, eigenvalue `w = x + i√(3z²−2y²)`), `node_mul` (right multiplication
  tables, `py/nodes_lean.py`), `scalarCM_cmTau` (four nodes, D = −4, −19, −40, −43),
  `qmCMNodes_of_numeric : QMCMNodesNumeric → QMCMNodes`, `thetaPointOfFibre_of_qm_cm'`.
- `py/verify_nodes.py` (80 digits, VERIFIED computed): at the Lean nodes `cmTau`,
  |Σθ⁸| = 33.9, 12.2, 6.84, 18.1 and j_θ = 0 (|j| < 2e-315), 81/64, 1296/125, 194481/10⁶
  (errors ≤ 1e-76). So `QMCMNodesNumeric` holds numerically.
- `py/check_j0.py` (VERIFIED computed): `e_k/e_1^k` at the product point `diag(i,i)` equals `R_k(0)`
  for k = 2..10 (relative diff ≤ 1e-77): the j = 0 point of the curve is the product E_i × E_i with
  the product polarization, and the constant terms of all `R_k` are explained by genus-1 data.
- `py/global_ids.py` (VERIFIED computed): `e_2(θ⁸) = (3/8)e_1²` at 16 random Ω ∈ 𝔥₂ (9e-78): a
  global identity; e_6..e_9 are NOT polynomials in e_1, e_3, e_4, e_5 globally (fits fail), so the
  curve part k = 3..9 is not reducible to fewer curve identities by θ⁸-symmetric global identities.
- §7 of `ThetaUse.lean` COMPILES (standard axioms): `two_esymm_two`, `ThetaEightSquare` (global
  identity Σθ¹⁶ = (Σθ⁸)²/4), `QMThetaSymmetricCurve` (k = 3..9),
  `qmThetaSymmetricCore_of : ThetaEightSquare → QMThetaSymmetricCurve → QMThetaSymmetricCore`,
  `thetaPointOfFibre_of_qm_curve`. All 12 `#print axioms` = [propext, Classical.choice, Quot.sound].
- Final state (VERIFIED, `lake env lean scratch/theta-split/ThetaUse.lean`: 0 errors, no sorryAx; 12
  `#print axioms` lines all standard). Report docs/research/theta-split.md (§8 records two docstring
  findings: TailE l.6521 "at a CM period matrix" is inaccurate; the Shimura 1976 citation is for CM points).
