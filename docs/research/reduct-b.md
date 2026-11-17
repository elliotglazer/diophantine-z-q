# reduct-b: the three SGA 7 IX DVR fields as theorems

Task reduct-b, 2026-11-14. Base `b5ff0474` (wip/w63; `frozenTarget` through `HDec.HSyn.sixContactMin_of_open15`).

**Lean.** `scratch/reduct-b/ReductB.lean` is one file that imports only kernel modules. `mk.sh` assembles it from two
parts:
- `RBBase.lean`: reduct-glue's `ReductGlue.lean` without its `#print` lines. Up to imports, headers and `#print`
  lines, its two halves are the kernel's `OneProof/H/TailZ7.lean` (`ReductSplit`) and `OneProof/H/TailZ14.lean`
  (`ReductGlue`) (VERIFIED by `diff`).
- `Body.lean`: namespace `ReductB`, the new work.

The file has no `sorry` and no `axiom`. All 11 `#print axioms` lines report `[propext, Classical.choice, Quot.sound]`
(VERIFIED, `scratch/reduct-b/axioms.txt`). Results log: `scratch/reduct-b/log.md`. Nothing under `ZInQKernel/` or
`blueprint/` was edited. This is model work with no human review.

Marks: **VERIFIED** = compiled or read in a file. **STANDARD** = published, with a reference. **SPECULATIVE** = a
judgement. **UNVERIFIED** = a theorem number recalled without a source. SGA 7, EGA and BLR could not be consulted
(no network), so every locator is UNVERIFIED.

## 1. Main result

**All three strict-GLUE fields are theorems.** No statement was changed.

| field (type) | theorem in `ReductB` | inputs |
|---|---|---|
| `semistableReductionDVR` (`ReductSplit.SemistableReductionDVR`, SGA 7 IX 3.6) | **K1** `semistableReductionDVR_of_raynaud` | `RaynaudSemistable` + textbook fields `mumfordTorsionAlgClosed`, `mulEtaleAbelianScheme` |
| `raynaudSemistable` (`ReductSplit.RaynaudSemistable`, 4.7) | `raynaudSemistable_of_SH_pair` | `ReductGlue.RaynaudSemistableSH` + `ReductGlue.StrictHenselizationPair` + `mulEtaleAbelianScheme` |
| `semistablePersistsDVR` (`ReductSplit.SemistablePersistsDVR`, 3.3a) | `semistablePersistsDVR_of_SH_pair` | `ReductGlue.SemistablePersistsSH` + `StrictHenselizationPair` |

The combined theorem is `three_fields_of_printed : RaynaudSemistableSH → SemistablePersistsSH →
StrictHenselizationPair → MumfordTorsionAlgClosed → MulEtaleAbelianScheme → SemistableReductionDVR ∧
RaynaudSemistable ∧ SemistablePersistsDVR`.

`fold_uses` checks the consumers. It builds every consumer of the three fields in the chain with the same terms
they have there, the three fields replaced by the theorems above:
- `r6`: `PkgI2.RaynaudCriterion`, via `raynaudCriterion_leaves` (TailZ15);
- `r8`: `PkgI2.GrothendieckMonodromy`, via `grothendieckMonodromy_final'` (TailZ9);
- SS1: `semistableReductionThm_final`;
- SS3: `semistablePersists_final`.

The consumers were found by grep of `ZInQKernel/` (VERIFIED). `fold_uses_K1` is the same check with only K1 applied.

**The `[CharZero K]` / `[PerfectField κ(O)]` variant (Route B-cp)** gives two results:
- **3.3a works.** The restricted strictly henselian (SH) leaf `SemistablePersistsSHcp` and the pair prove
  `SemistablePersistsDVRcp`. Both uses of 3.3a, SS1 and SS3, still type-check: `ss1_ss3_of_cp`.
- **4.7 and 3.6 do not.** The cp form of 4.7 gives SS1 (`ss1_ss3_of_cp_full`, through K1 at number fields), but
  not `r6` or `r8`. Those two are stated over **every field** (`PkgI2.RaynaudCriterion`,
  `PkgI2.GrothendieckMonodromy`), and the general-DVR 4.7 and 3.6 are used there. A cp-only fold would have to
  restate `r6`/`r8` and their roughly 25 consumers in TailF/H/I/K and LF4T5. Some of these are stated over an
  arbitrary field (for example LF4T5's `goodReduction_of_QM_rational3_C`, `{K} [Field K]`). This was not attempted.
  The recommended fold therefore uses the unrestricted SH leaves (§4, option B).

## 2. K1: 3.6 from 4.7 (VERIFIED)

`semistableReductionDVR_of_raynaud (hR : RaynaudSemistable) (hM : MumfordTorsionAlgClosed)
(hE : MulEtaleAbelianScheme) : SemistableReductionDVR`. The proof:

1. **`m`.** `exists_three_le_isUnit` gives `m ∈ {3, 4}` with `m` a unit in `O`. If `3` is not a unit, then
   `4 + (−3) = 1` and `IsLocalRing.isUnit_or_isUnit_of_isUnit_add` make `4` a unit. This is the task's "`m = 4` if
   the residue characteristic is 3", with no case split on the characteristic.
2. **`K'`.** Take `K'` from reduct-split's `torsionFieldOfDefinition_of`, using `torsionStructure_of_mumford hM`. It
   is finite over `K`, and every `σ ∈ Aut(K̄/K)` fixing `K'` fixes `A(K̄)[m]`.
3. **Rationality over `K'`, the transfer step.** Let `O'` be a DVR of `K'` over `O`, and
   `x ∈ A_{K'}((K')‾)[m]`, where `(K')‾ = AlgebraicClosure K'`.
   - Choose `κ' : K̄ →ₐ[K'] (K')‾` by `IsAlgClosed.lift`. `K̄` is algebraic over `K'`. The two
     `Module.IsTorsionFree K' _` instances must be given explicitly, or instance search times out.
   - `torsion_descends_etale` with `κ = κ'|_K` gives `p ∈ A(K̄)[m]` with `bcPt⁻¹(extPt κ p) = x`.
   - `p` is fixed by `Aut(K̄/K')`. The new lemma `fixedTorsionRational_inter` (below) gives `z ∈ A(K')` with
     `extPt (K'.val) z = p`.
   - Then `y = bcPt⁻¹ z ∈ A_{K'}(K')` satisfies `extPt ofId y = x`. This uses `bcPt_extPt`, `extPt_extPt`, and
     `κ ∘ K'.val = ofId` (`κ'.commutes`). Because `κ'` is a `K'`-embedding and not an arbitrary `K`-embedding, no
     Galois action ever has to be moved between `K̄` and `(K')‾`.
4. **Conclusion.** `m` is a unit in `O'` via `comapHom`. Raynaud's criterion over `(K', O')` concludes.

New descent lemmas, each generalizing reduct-glue's version from `K` to an intermediate field `F ⊆ K̄`:
- `mem_of_isSeparable_of_fixed_inter`: an element separable over `F` and fixed by `Aut(K̄/F)` lies in `F`. The proof
  uses `separableClosure F K̄` and `AlgEquiv.liftNormal`, with `IsAlgClosure F K̄` from `tower_top`.
- `exists_rational_of_fixed_etale_inter`: a `K̄`-point of an étale `K`-scheme fixed by `{σ | σ|_F = id}` comes from
  an `F`-point.
- `fixedTorsionRational_inter`: the same for `A[m]`, via the pullback of `[m]` along the unit.

## 3. Route B (VERIFIED)

- **`strictHenselizationNeron_of_pair : StrictHenselizationPair → StrictHenselizationNeron`.** This is the instance
  `K' = K`, `O' = O` of the pair, with `comap_algebraMap_self : O.comap (algebraMap K K) = O`. The pair's first
  `IsSHNeronExt O P hP` is literally the body of `StrictHenselizationNeron`. The proof is
  `exact ⟨E, _, _, P, hP, hSHP⟩`.
- **`raynaudSemistable_of_SH_pair`** is `raynaudSemistable_of_SH' hR (strictHenselizationNeron_of_pair hPair) hE`.
  So 4.7 needs no separate `StrictHenselizationNeron` field: one pair field serves both 4.7 and 3.3a.
- **`semistablePersistsDVR_of_SH_pair`** is `persistsFromSH_of hPair hP`.
- **`semistableReductionDVR_of_SH_pair`** is K1 composed with the 4.7 reduction.

**cp variants.** These are new `def`s in `ReductB`. Each is the reduct-glue Prop with `[CharZero K]` and
`[PerfectField (IsLocalRing.ResidueField O)]` added. No `[NumberField K]` appears on any SH form.

| def | what |
|---|---|
| `RaynaudSemistableSHcp`, `SemistablePersistsSHcp` | restricted printed leaves: strictly henselian, `K` of characteristic 0, residue field perfect, hence algebraically closed (Mathlib `isAlgClosed_of_perfectField`) |
| `RaynaudSemistableCP`, `SemistablePersistsDVRcp` | the DVR forms reachable from them |
| `SemistablePersistsDVRnf`, `SemistableReductionDVRnf` | the number-field forms (the generality of SS1/SS3) |

Theorems:
- `cp_of_general`: the cp SH leaves are specializations of the general DVR forms, so they are not stronger than the
  print.
- `raynaudSemistableCP_of_SH` and `semistablePersistsDVRcp_of_SH`. `CharZero E` comes from the injectivity of
  `algebraMap`. `PerfectField κ(P)` comes from `Algebra.IsAlgebraic.perfectField`, applied to the algebraic residue
  extension in `IsSHNeronExt`.
- `perfectField_residue_nf`: the residue field of a DVR of a number field is finite (`𝓞/𝔭` is finite,
  `Ideal.bijective_algebraMap_quotient_residueField`, reduct-glue's `resIso`), hence perfect.
- `semistableReductionThm_of_leaves_nf` and `semistablePersists_of_leaves_nf`: reduct-split's SS1/SS3 proofs with
  `h33` (and `h36`) retyped to the number-field forms. The only addition is a `NumberField (F O)` instance.
- `semistableReductionDVRnf_of_raynaudCP`: K1 at number fields.
- `ss1_ss3_of_cp`, `ss1_ss3_of_cp_full`.

## 4. Field table for a fold (top bundle `OpenResearchLeaves12`, TailZ19)

Kinds as in the task: the review counts the three DVR fields as GLUE (consequences, not the printed form).

| field | before | option A: K1 only | option B: K1 + Route B (recommended) |
|---|---|---|---|
| `semistableReductionDVR` | GLUE | **removed**: `semistableReductionDVR_of_raynaud r.raynaudSemistable t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme` | **removed**: `semistableReductionDVR_of_SH_pair r.raynaudSemistableSH r.strictHenselizationPair t.mumfordTorsionAlgClosed t.mulEtaleAbelianScheme` |
| `raynaudSemistable` | GLUE | kept (GLUE) | **removed**: `raynaudSemistable_of_SH_pair r.raynaudSemistableSH r.strictHenselizationPair t.mulEtaleAbelianScheme` |
| `semistablePersistsDVR` | GLUE | kept (GLUE) | **removed**: `semistablePersistsDVR_of_SH_pair r.semistablePersistsSH r.strictHenselizationPair` |
| `raynaudSemistableSH : ReductGlue.RaynaudSemistableSH` | — | — | **added**, LEAF (SGA 7 I IX 4.7 over a strictly henselian trait; a specialization of the general-DVR statement) |
| `semistablePersistsSH : ReductGlue.SemistablePersistsSH` | — | — | **added**, LEAF (SGA 7 I IX 3.3, first assertion, strictly henselian base) |
| `strictHenselizationPair : ReductGlue.StrictHenselizationPair` | — | — | **added**, LEAF candidate, composite (EGA IV₄ 18.8.10/18.6.8 or Stacks 05WR, with BLR §1.2 Prop. 2) |
| total, research bundle | 32 | 31 (−1 GLUE) | 32 (−3 GLUE, +2 LEAF, +1 composite LEAF) |

- Under option B the frozen target's field count stays at 61. Strict GLUE drops by 3, or by 2 if the composite pair
  is counted as GLUE. The textbook fields `mumfordTorsionAlgClosed` and `mulEtaleAbelianScheme` are already in
  `OpenTextbookLeaves10`.
- sh-route is working on proving the strict-henselization leaves from a BLR base-change leaf. If it succeeds, the
  pair field is replaced by that leaf, with no change to this report's proofs.

**Fold recipe** (UNCHECKED; `TailZ19` is not built in this worktree):
1. Put `Body.lean` after its import line into a new `OneProof/H/TailZ20.lean` that imports `TailZ19`. It uses only
   `ReductSplit` and `ReductGlue` names, which are in TailZ7/TailZ14 verbatim, plus Mathlib.
2. Add `scratch/reduct-b/FoldSnippet.lean.txt`. It is generated mechanically from TailZ19 and contains:
   - `OpenResearchLeaves13`, with the 29 kept fields copied with their docstrings;
   - `researchLeaves12_of_open13`;
   - `sixContactMin_of_open16`.
3. `Main.lean` would call `sixContactMin_of_open16`.

`fold_uses` is the compiled evidence that the replaced terms have the types the consumers expect.

## 5. Statement review

- **No statement was changed.** `RBBase.lean` is reduct-glue's file. The three fields' types are used exactly as
  `ReductSplit` states them.
- **None of the three statements is false, vacuous or inert.**
  - They are now theorems from published-form leaves.
  - Their hypotheses (a DVR, an abelian variety) are satisfiable, and so are those of the SH leaves: strictly
    henselian DVRs exist, for example `O^sh`, which `StrictHenselizationPair` itself provides.
  - The cp SH leaves are not vacuous either: `K` of characteristic 0 with a strictly henselian DVR whose residue
    field is algebraically closed, such as the completion of the maximal unramified extension of `ℚ_p`
    (SPECULATIVE example, standard).
- **Reading risks** (SPECULATIVE):
  - If SGA 7 IX states 4.7 and 3.3 over a strictly henselian trait **with algebraically closed residue field**, the
    printed form is the cp leaf, not `RaynaudSemistableSH`. Then option B's 4.7 field would be stronger than the
    print for imperfect residue fields. The cp route covers SS1/SS3 but not `r6`/`r8` (§1).
  - A further possibility, not checked: SGA 7 states 4.7 over an arbitrary DVR. In that case the original field was
    already a LEAF.
  - `StrictHenselizationPair` combines two printed results. Its Néron part is BLR 1.2/2 for strict henselization,
    which reduct-glue also uses.

## 6. Checks

- `scratch/reduct-b/chk.sh` runs `mk.sh`, then `lake env lean scratch/reduct-b/ReductB.lean`: 52 s, 7.6 GB, no
  errors, 11 `#print axioms` lines, all standard (VERIFIED, 11-14 18:08).
- During development `RBBase.lean` was compiled once to `/tmp/rblib/RBBase.olean` (50 s), and `Body.lean` against
  it with `t.sh` (about 7 s per run), one Lean process at a time.
- Build setup: reduct-glue's `.lake/build/lib` was copied into this worktree. `lake build` of the 10 imported kernel
  modules replayed them (9359 jobs, no rebuild). Their sources are unchanged since w60.
