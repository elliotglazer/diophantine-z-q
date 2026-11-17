# sh-route results log

Base e38375b3 (wip/w62). Lean 4.35 / Mathlib v4.35.0.

## Setup
- Base.lean, Body.lean: verbatim copies of scratch/reduct-glue/{Base,Body}.lean. olean/ShRG.lean = their
  concatenation (diff with scratch/reduct-glue/ReductGlue.lean empty, VERIFIED); compiled to olean/ShRG.olean
  (110 s, 7.6 GB, no errors, VERIFIED 17:20).

## Top.lean (namespace ShRoute) — compiles over ShRG (VERIFIED 17:40, no errors)
- `IsSHUnram O O₁ hO` := SH DVR ∧ K₁/K algebraic ∧ uniformizer ↦ uniformizer ∧ κ₁/κ separable.
- LEAF `NeronBaseChangeSH` (BLR 7.2/1, 1.2/2; UNVERIFIED): char 0, IsSHUnram ⇒ Néron base change.
- `isSHNeronExt_of : NeronBaseChangeSH → IsSHUnram → IsSHNeronExt`.
- GLUE (commutative algebra) `SHExists0`, `SHInside0`, `SHPair0`.
- `StrictHenselization{Neron,Pair,Inside}0` = reduct-glue statements + `[CharZero K] [PerfectField κ(O)]`;
  each proved from NeronBaseChangeSH + the matching CA Prop.
- `RaynaudSemistable0`, `SemistablePersistsDVR0`, `SemistableUnipotent0` (char-0 forms) proved from the printed
  SH leaves (reduct-glue's proofs replayed).

## CA1.lean (Mathlib only) — compiles, no sorry (VERIFIED 19:05, 18 s)
- `exists_of_mem`: valuation subring W ⊇ R (Dedekind) of Frac R with nonzero center: x ∈ W ⇒ x = a/s, s ∉ center.
- `unit_mul_pow_of_div`: from 𝔮·j ⊆ ϖR (j ∉ 𝔮) every nonzero a/s (s ∉ 𝔮) is ϖⁿ·unit of W (induction on 𝔮-adic order).
- `key_finite`: M/K finite Galois, A ⊆ K DVR with perfect residue field, W over A; x ∈ W∖0 fixed by every σ ∈ Gal(M/K)
  acting trivially mod 𝔪_W ⇒ x = ϖⁿ·unit(W). Proof: S = integralClosure A M, P = S ∩ 𝔪_W, H = Ideal.inertia P,
  E = Fix(H), R = integralClosure A E, 𝔮 = P ∩ R; Mathlib `Ideal.card_inertia_eq_ramificationIdxIn` over A and over R
  (group H, inertia of P in H is ⊤) + `ramificationIdx_tower` ⇒ e(𝔮|p) = 1; `ramificationIdx_eq_multiplicity` ⇒
  p𝓞_E = 𝔮·J, J ⊄ 𝔮; inertia elements act trivially mod 𝔪_W on W (via exists_of_mem) so x ∈ E.

## CA2.lean (imports ShRG, Top, CA1 oleans) — compiles, no sorry (VERIFIED, 16 s)
- `inertiaField w : IntermediateField K Ω` = {x | ∃ finite Galois M ∋ x, every τ ∈ Aut(Ω/K) with τy−y ∈ 𝔪_w for
  y ∈ w∩M fixes x}; `inertia_fixes`: IsInertia w σ ⇒ σ fixes it.
- `mem_inertiaField_of_simple_root` (core): root α of g over wE whose residue is a simple root of g mod 𝔪_w lies in
  the inertia field (two roots with one residue ⇒ double root mod 𝔪_w).
- `henselian_wE`, `isSepClosed_wE`, `isDVR_wE` (from `key_finite` via `unit_pow`), `irreducible_comapHom`
  (uniformizer of O stays a uniformizer), `res_isAlgebraic` (residue ext of algebraic ext is algebraic),
  `exists_comap_eq` (extension of valuation rings).
- **`shInside0 : SHInside0`, `shExists0 : SHExists0` PROVED.**

## CA3.lean — compiles, no sorry (VERIFIED, 8 s)
- `inertM`: inertia subgroup of Gal(M/K) (submonoid of finite group).
- `inertiaField_le`: inertia field over K ⊆ inertia field over K' (K'/K finite, same w).
- `inertiaField_le_adjoin`: inertia field over K' ⊆ E(t') (t' finite generating K'), via finite Galois correspondence
  Fix(I ∩ Gal(M/K')) = Fix(I) ⊔ K' in a finite Galois M.
- **`shPair0 : SHPair0` PROVED** (Ω = AlgebraicClosure K', w from `exists_comap_eq`, κ(O') perfect as algebraic over κ(O)).

## Final assembly (VERIFIED 18:10)
- `mk.sh` → ShRoute.lean = Base + Body (diff with reduct-glue's copies empty) + Top + CA1 + CA2 + CA3 + Final.
- `chk.sh`: `lake env lean scratch/sh-route/ShRoute.lean`, 68 s, 7.75 GB, no errors; 58 `#print axioms` lines, all
  `[propext, Classical.choice, Quot.sound]` (axioms.txt). No `sorry` (only in docstrings).
- Pitfall: the file-level `open ... MonObj` / Polynomial opens of Base/Body make `mul_one`, `one_mul`, `eval_map`,
  `eval` ambiguous in appended parts; qualified as `_root_.` / `Polynomial.`.
- Final: `strictHenselization{Neron,Pair,Inside}0_final : NeronBaseChangeSH → …0`; `route_final`;
  `neronBaseChangeSH_of_unramified : NeronBaseChangeUnramifiedDVR → NeronBaseChangeSH`; `char0_of_general`.
