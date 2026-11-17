# c-to-printed2 results log

Fields: `r17 : LadicCond.CarayolR17'`, `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists`,
`eigenformHTNew : ZInQ.Contrib.HodgeSplit.EigenformHTNew` (leaf-fold10 §2, all GLUE (c)).
Base e38375b3. Compile command: `lake env lean scratch/c-to-printed2/<file>.lean` (prebuilt oleans in the worktree).

## 2026-11-14

- `HTDual.lean` (imports `OneProof.H.TailT`): **VERIFIED** compiles, `#print axioms CToPrinted2.htDual_proof` =
  `[propext, Classical.choice, Quot.sound]` (about 70 s).
  - `htDual_proof : TateTwistInvariants → AxSenTate → HTDual`. `HTDual` and `dualGR` are modular-split's
    (`scratch/modular-split/EigenHT.lean`), copied verbatim into namespace `CToPrinted2`.
  - Route: pairing `Y_i(ρ) × Y_j(ρ^∨) → ℂ_ℓ(−i−j)^{G_E}` (`pair_twist`; zero by Tate, in `E` by Ax–Sen–Tate);
    hodge-split's `exists_basis_Ysp`; the dual basis lies in `Y_{−j}(ρ^∨)` (`cvec_mem`); `finrank_Ysp_dual`,
    `finrank_Ysp_dual_eq`; hodge-split's `htMult_eq_finrank_Ysp`.
  - Consequence: modular-split's glue `HTDual` is closed by two existing bundle LEAF fields (`tateTwistInvariants`,
    `axSenTate`).
- Build note: the worktree lacked the upstream helper package build (`lean/.lake`), so `import ...TailZ15` failed
  with "unknown module prefix 'ZInQ'"; copied `~/dzq-wt/leaf-fold10/lean/.lake` (sources `diff -rq` identical).
- `CToPrinted2.lean` (imports `OneProof.H.TailZ15`): **VERIFIED** compiles, 0 errors, 7 `#print axioms` lines all
  `[propext, Classical.choice, Quot.sound]` (output `CToPrinted2_out.txt`, about 20 s).
  - §0: the three fields copied verbatim; `rfl` against `LadicCond.CarayolR17'`,
    `ZInQ.Contrib.HodgeSplit.EigenformHTNew`, `HDec.WeilPairing.T09_SymmIsogenyExists`; projections from
    `OpenResearchLeaves10` / `OpenAddedLeaves9` typecheck at these types.
  - §1–5 = `HTDual.lean`; under the TailZ15 import `IsGalois.mk` hit the synthInstance limit (instance drift);
    fixed with `set_option synthInstance.maxHeartbeats 400000 in` on `htDual_proof`.
  - §6: `eigenformHTNew_of_printed : KatoRealizationCoh → TateTwistInvariants → AxSenTate → EigenformHTNew`;
    `katoRealization_iff_field : DSThm965 → DSThm966 → (KatoRealization ↔ EigenformHTNew)`.
  - §7: `carayolR17'_of_realization` (modular-split, verbatim);
    `carayolRealization_iff_field : DSThm965 → DSThm966 → (CarayolRealization ↔ CarayolR17')`.
  - §9: `fields_of_printed (hK : KatoRealizationCoh) (hC : CarayolRealization) (l : OpenAddedLeaves9)`.
- Added to `CToPrinted2.lean`: `perp`, `finrank_perp`, `dualGR_isSemisimple` (contragredient of a semisimple rep is
  semisimple), leaf `KatoRealizationCohSS` (= `KatoRealizationCoh` with semisimple witness; implied by it,
  `katoRealizationCohSS_of_coh`), `katoRealization_of_cohSS`, `eigenformHTNew_of_printedSS`;
  `fields_of_printed` now takes `KatoRealizationCohSS`. **VERIFIED** 0 errors, 9 axiom lines all standard.
- Added `katoRealizationCohSS_of_field`, `katoRealizationCohSS_iff_field : DSThm965 → DSThm966 →
  TateTwistInvariants → AxSenTate → (KatoRealizationCohSS ↔ EigenformHTNew)`. **VERIFIED** 0 errors, 10 axiom
  lines all `[propext, Classical.choice, Quot.sound]`.
- `T09Roadmap.lean`: `PicRepresentableAbVar` (Grothendieck representability of `picardFunctor A.X.hom` for
  `A : PkgI3.AbVar K`, unused) compiles with no errors (**VERIFIED** statable; nothing proved).
- Independent model review: no mathematical error found; wording fixes applied (report §1, §2.1 `ā_p` caveat, §5,
  §7; two docstrings in `CToPrinted2.lean`). Re-run: `CToPrinted2.lean` 0 errors, 10 standard axiom lines;
  `HTDual_out.txt` 0 errors, standard axioms; `T09Roadmap_out.txt` empty. **VERIFIED**.
