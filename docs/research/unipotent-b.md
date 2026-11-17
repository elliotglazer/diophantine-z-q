# unipotent-b: SGA 7 IX 3.5 in printed form, and the field `semistableUnipotent` derived from it

Task unipotent-b, 2026-11-14. Base b5ff0474 (wip/w63). Lean: `scratch/unipotent-b/UnipotentB.lean`. It imports only
`ZInQKernel.OneProof.H.TailZ14`, has no `sorry` and no `axiom`, and compiles with no errors or warnings. All 18
`#print axioms` lines report `[propext, Classical.choice, Quot.sound]` (VERIFIED, `scratch/unipotent-b/axioms.txt`).
The other files in `scratch/unipotent-b/` are listed in §6. The results log is `scratch/unipotent-b/log.md`. Nothing
under `ZInQKernel/` or `blueprint/` was edited. This is model work and no human has reviewed it.

Marks: **VERIFIED** means compiled or read in a file. **STANDARD** means published, with a reference.
**SPECULATIVE** means a judgement. **UNVERIFIED** means a theorem number or wording recalled from memory. This host
has no network, so SGA 7, SGA 3, BLR and Serre's *Corps locaux* could not be consulted, and every locator below is
UNVERIFIED.

## 1. Main result

1. **The field keeps its statement and is proved from the printed form of 3.5 (recommended).**
   `semistableUnipotent : ReductSplit.SemistableUnipotent` keeps its statement word for word. It is now a Lean
   theorem from three leaves and one glue Prop. The glue is needed only for imperfect residue fields.

   ```
   UnipotentB.semistableUnipotent_of_printedGen
     (hP : SemistableUnipotentPrintedGen)          -- LEAF: SGA 7 IX 3.5 as printed (strictly henselian trait,
                                                   --   K^s, semistable over k(s), iff + echelon clause)
     (hD : SemiAbelianDescendsSepClosed)           -- GLUE: the k(s) axis (proved here for perfect k(s))
     (hE : AvSplit.T4.MulEtaleAbelianScheme)       -- bundle LEAF already in use (BLR 7.3/2)
     (hIn : ReductGlue.StrictHenselizationInside)  -- LEAF candidate already in use (reduct-glue)
     : ReductSplit.SemistableUnipotent
   ```

   The strictly henselian field `ReductGlue.SemistableUnipotentSH` (field `sga7_3_5` of reduct-glue's
   `ReductLeavesPrinted`) also keeps its statement. `semistableUnipotentSH_of_printedGen` proves it from `hP`, `hD`
   and `hE`. All three review axes are handled:
   - **base**: the printed strictly henselian form is moved to a DVR with reduct-glue's `unipotentFromSH_of` and
     `StrictHenselizationInside`;
   - **`K^s` versus `K̄`**: two Props, both proved here (§3.3);
   - **`k(s)` versus `κ̄`**: proved when `k(s)` is perfect, and left as the named glue
     `SemiAbelianDescendsSepClosed` otherwise.

   The echelon clause `(σ-1)(τ-1) = 0` is part of the leaf. The field's `(σ-1)² = 0` is its case `σ = τ`.

2. **The form the task asked for is proved, but it does not fold into the current chain.**
   - `SemistableUnipotentPrinted` is 3.5 over a strictly henselian trait with `[CharZero K]` and
     `[PerfectField k(s)]`, echelon clause included.
   - From it, `semistableUnipotentSH0_of` gives `SemistableUnipotentSH0`, which is `SemistableUnipotentSH` plus the
     two instances.
   - With `StrictHenselizationInside`, `semistableUnipotent0_of_printed` then gives `SemistableUnipotent0`, which is
     the field plus the two instances. This route uses no glue.

   **However, the field cannot gain these instances.** The uses check fails (§4):
   - Row r6 (`PkgI2.RaynaudCriterion`) is a kernel Prop quantified over **every** field. Its proof
     (`ReductGlue.raynaudCriterion_leaves`) applies `semistableUnipotent` at that arbitrary `K`.
   - With the restricted field, that proof fails with `failed to synthesize instance of type class CharZero K`
     (VERIFIED, `UsesFail.lean`).
   - r6 is consumed through `HDec.LeafQM.AV.QML3.goodReduction`. That theorem has `[CharZero K]` but an arbitrary
     DVR `Ov`, whose residue field is not assumed perfect, so even a `CharZero`-restricted r6 would not be enough
     there.

   The other use, row r8 (`PkgI2.GrothendieckMonodromy`), is **inert**: no theorem in the dependency closure of
   `HDec.HSyn.sixContactMin_of_open15` reads it (VERIFIED, `Deps.lean`).

   This is why item 1, which keeps the statement, is the recommended form.

3. **No statement was found false, vacuous or inert, except row r8**, which is carried in the bundles but never used
   (§4). The strictly henselian printed leaves do not assume `[NumberField K]`, so they are not vacuous: an example
   is the fraction field of the strict henselization of `ℤ_(p)`, of characteristic `0` with residue field `F̄_p`.

## 2. The printed statement (LEAF)

`UnipotentB.SemistableUnipotentPrintedGen` (Grothendieck, SGA 7 I, Exp. IX, Prop. 3.5; the number and wording are
recalled from memory, **UNVERIFIED**):

```lean
def SemistableUnipotentPrintedGen : Prop :=
  ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O],
    IsStrictlyHenselianDVR O →
    ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (w : ValuationSubring Ω),
    w.comap (algebraMap K Ω) = O → ∀ A : PkgI3.AbVar K,
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
      (HasSemistableReductionRes A O ↔ InertiaUnipotent A w ℓ) ∧
      (HasSemistableReductionRes A O → ∀ σ τ : Ω ≃ₐ[K] Ω, IsInertia w σ → IsInertia w τ →
        (galTΩ A ℓ σ - 1) * (galTΩ A ℓ τ - 1) = 0)
```

What each part means:
- `O` is a strictly henselian DVR, that is, a strictly local trait (reduct-glue's `IsStrictlyHenselianDVR`:
  henselian, with separably closed residue field).
- `Ω = K^s` is a separable closure of `K`.
- `T_ℓ(A) = lim A(K^s)[ℓⁿ]` (`TΩ`). `ℓ` is invertible in `O`, so it is different from the residue characteristic.
- `I` is the inertia group of `w`. Because `O` is strictly henselian, `w` is the only extension and `I = Gal(K^s/K)`.
  The residue field of `w` is purely inseparable over the separably closed `k(s)`, so `IsInertia` holds for every
  `σ`.
- **Semistable reduction is read over `k(s)` itself** (`HasSemistableReductionRes`): a Néron model whose special
  fibre `𝒩 ×_O k(s)` has semi-abelian identity component (height-split's `HasSemiAbelianIdentityComponent`).
- `InertiaUnipotent A w ℓ` says that every `σ ∈ I` has `σ - 1` nilpotent on `T_ℓ(A)`.
- The second conjunct is the **echelon `≤ 2`** clause.

Why it is the print, or a consequence of it:
- The iff and the echelon clause are the printed content as recalled (UNVERIFIED).
- The `⇐` direction also uses Néron's existence theorem (BLR §1.4 Thm 3), because `HasSemistableReductionRes` asks
  for a Néron model as a `GroupModelO`.
- The forward conjunct is the only part used.

Variants:
- `SemistableUnipotentPrinted` is the same statement with `[CharZero K]` and `[PerfectField k(s)]` added, so it is
  weaker. It is the form the task asked for. `printed_of_printedGen` derives it.
- `SemistableUnipotentPrintedEchelon` is only the used direction of `SemistableUnipotentPrinted`
  (`echelon_of_printed`).
- `SemistableUnipotentPrintedGeom` reads semistability over `κ̄` instead. It is a LEAF **only if** SGA 7 IX defines
  semistable reduction through the geometric special fibre (UNVERIFIED). In that case
  `semistableUnipotent_of_printedGeom` derives the field with **no glue**.

## 3. Proofs (all VERIFIED by compilation)

### 3.1 `k(s)` versus `κ̄`

- `isSemistableRes_iff`: for an algebraically closed `k(s)`, semistability over `k(s)` and over `κ̄` agree. The map
  `k(s) → κ̄` is an isomorphism (`IsAlgClosed.algebraMap_bijective_of_isIntegral`). The two fibres are identified by
  reduct-glue's `pbCompIso`, and the transport uses `semiAbelianFieldIsoInvariant`, which is proved in `TailZ14`.
- A separably closed, perfect `k(s)` is algebraically closed (`IsSepClosed.isAlgClosed_of_perfectField`). This
  gives `semiAbelianDescends_of_perfect`, the glue below in the perfect case.

### 3.2 The restricted route (task form)

- `semistableUnipotentSH0_of : SemistableUnipotentPrintedEchelon → SemistableUnipotentSH0`. In characteristic `0`
  an algebraic closure is a separable closure (`IsSepClosure.of_isAlgClosure_of_perfectField`). §3.1 moves the
  hypothesis to `k(s)`. `sq_form` turns `(σ-1)(σ-1) = 0` into the field's `σσt - 2•σt + t = 0`.
- `semistableUnipotent0_of : StrictHenselizationInside → SemistableUnipotentSH0 → SemistableUnipotent0`. This is
  reduct-glue's `unipotentFromSH_of`, with the two instances carried to the inertia field `E`:
  - `CharZero E` comes from `charZero_of_injective_algebraMap`;
  - `PerfectField k(w ∩ E)` comes from the algebraic residue extension in `IsSHNeronExt` and
    `Algebra.IsAlgebraic.perfectField`.

### 3.3 The unrestricted route (recommended)

- `semistableUnipotentSH_of_gen : PrintedGen → SemiAbelianDescendsSepClosed → SepClosureTateRestrict →
  SemistableUnipotentSH`. The proof restricts `σ` to `K^s = separableClosure K Ω`, applies the leaf there with
  `σ = τ`, and pushes the result to `T_ℓ` over `Ω` through a surjective equivariant map.
- `SepClosureTateRestrict` is proved from two smaller Props (`sepClosureTateRestrict_of`). **Both are proved.**
  - `InertiaRestrictSepClosure` (`inertiaRestrictSepClosure`) is proved without leaves:
    - `σs = σ.restrictNormal (separableClosure K Ω)`, which works because `K^s/K` is Galois;
    - decomposition: `σs • (w ∩ K^s) = w ∩ K^s`;
    - inertia: `σs a - a` maps into `𝔪_w`, and `w ∩ K^s → w` sends units to units.
  - `TorsionFromSepClosure` (`torsionFromSepClosure_of`) is proved from the bundle leaf `MulEtaleAbelianScheme`:
    - `exists_lift_of_etale_sep` is reduct-glue's `exists_lift_of_etale` with `K^s` in place of an algebraically
      closed field. The coordinates of a point of an étale `K`-scheme are separable
      (`isSeparable_of_etale'`, for any target field), so they lie in `separableClosure K Ω`.
    - `A[m]` is the étale pullback of `[m]` along the unit section, as in `torsion_descends_etale`.
  - `tateMap_surjective`: an injective map onto the `ℓ`-power torsion gives a surjection on `T_ℓ`, level by level,
    with compatibility by injectivity. Injectivity of `A(K^s) → A(Ω)` is `extPt_injective` and equivariance is
    `extPt_galAct`, both kernel lemmas.
- `semistableUnipotent_of_printedGen` is `unipotentFromSH_of hIn` applied to the above.

## 4. Uses check

The check is `scratch/unipotent-b/Deps.lean` (output in `deps.txt`). It runs a BFS over the constants used in the
types and values reachable from `HDec.HSyn.sixContactMin_of_open15` (the H side of `OneProof/Main.lean`), skipping
Mathlib and core. It found the following (VERIFIED):
- **In the closure:** `ReductSplit.SemistableUnipotent`, `ReductGlue.raynaudCriterion_leaves` (r6) and
  `ReductSplit.grothendieckMonodromy_final'` (r8). `ReductGlue.SemistableUnipotentSH` is not in the closure.
- **r8 is inert.**
  - The projections `OpenResearchLeaves{2,5,7,8}.r8` are used only to build the next bundle.
  - `ResearchLeaves3.mk` takes `r8`, but neither the projection `ResearchLeaves3.r8` nor its recursor is in the
    closure.
  - No theorem in the closure takes `PkgI2.GrothendieckMonodromy` as a hypothesis, apart from the restatement
    `grothendieckMonodromy_ofK5`.
  - So the r8 call `grothendieckMonodromy_final' r.semistableReductionDVR r.semistableUnipotent ...` (`TailZ9`) is a
    dead branch. Each of those fields still has other live uses: `semistableUnipotent` and
    `neronSchemeModelExistsDVR` in r6, and `semistableReductionDVR` in `semistableReductionThm_final` (`TailZ15`).
    Whether to drop r8 is the lead's decision.
- **r6 is used.** `PkgI2.RaynaudCriterion` quantifies over every `K` and is consumed by:
  - `HDec.LeafQM.AV.QML3.goodReduction` (`[CharZero K]`, arbitrary DVR `Ov`), then
    `HDec.PkgI2.goodReduction_of_QM_rational3'` and `_of_alg` (every field);
  - `HDec.G0ModField.KernelField.good_of_QML3` and the `kernelFieldExists_*` theorems;
  - `HDec.HSyn.LinkedTate.qmModelG3_of`, `HDec.HSyn.linkedTateLocal_of_leaves3` and `modelG3G6_of_leaves3`.
- `UsesFail.lean` replays the r6 proof with the restricted field. It fails with
  `failed to synthesize instance of type class CharZero K` (VERIFIED, as expected).
- `UsesCheck.lean` proves `RaynaudCriterion0`, which is r6 restricted to `[CharZero K]` and `[PerfectField k(s)]`,
  from the restricted field by the same proof (VERIFIED). That restricted row is not the kernel's r6, though, and its
  consumers above are stated for more general `(K, Ov)`.

**Conclusion: if the field gained `[CharZero K]` and `[PerfectField k(s)]`, the uses would not type-check.**
Folding the restricted field would require restating r6 and its consumer chain. The unrestricted route (§1, item 1)
avoids that: the field keeps its statement, so every use type-checks unchanged.

## 5. Before/after field table

| field / Prop | before (w63) | after: recommended (statement unchanged) | after: task's restricted form |
|---|---|---|---|
| `semistableUnipotent : ReductSplit.SemistableUnipotent` | LEAF (consequence of the print questioned on base, `K^s`, `k(s)` and the echelon clause) | **proved**: `semistableUnipotent_of_printedGen hP hD hE hIn` | would become `SemistableUnipotent0` (field + `[CharZero K]` `[PerfectField k(s)]`), proved by `semistableUnipotent0_of_printed hP0 hIn` with no glue, but **breaks r6** (§4) |
| `sga7_3_5 : ReductGlue.SemistableUnipotentSH` (reduct-glue `ReductLeavesPrinted`) | LEAF (printed base, other axes open) | **proved**: `semistableUnipotentSH_of_printedGen hP hD hE` | `SemistableUnipotentSH0`, proved by `semistableUnipotentSH0_of` |
| new `SemistableUnipotentPrintedGen` | — | **LEAF**: SGA 7 IX 3.5 as printed (UNVERIFIED wording), echelon clause included | — |
| new `SemistableUnipotentPrinted` | — | (consequence: `printed_of_printedGen`) | **LEAF**: the same with `[CharZero K]` and `[PerfectField k(s)]` |
| new `SemiAbelianDescendsSepClosed` | — | **GLUE** (the `k(s)` axis; proved for perfect `k(s)`) | not needed |
| new `SepClosureTateRestrict` = `InertiaRestrictSepClosure` + `TorsionFromSepClosure` | — | **proved** (the second from the bundle leaf `MulEtaleAbelianScheme`) | not needed (in char. 0, `K^s = K̄`) |
| `ReductGlue.StrictHenselizationInside` | LEAF candidate (reduct-glue) | used, unchanged | used, unchanged |
| `AvSplit.T4.MulEtaleAbelianScheme` | bundle LEAF | used, unchanged | not used |
| `SemistableUnipotentPrintedGeom` (variant) | — | LEAF only if SGA 7 reads semistability geometrically (UNVERIFIED); then `semistableUnipotent_of_printedGeom hG hE hIn`, no glue | — |

Net effect on the leaf count, for the recommended route: the field `semistableUnipotent` (1 LEAF) becomes one new
LEAF (`SemistableUnipotentPrintedGen`) and one GLUE (`SemiAbelianDescendsSepClosed`). The other two hypotheses,
`StrictHenselizationInside` and `MulEtaleAbelianScheme`, are already in the chain.

**The glue `SemiAbelianDescendsSepClosed`.** For a DVR `O` with separably closed residue field `k`, a group model
whose geometric special fibre has semi-abelian identity component already has it over `k`.

It is believed true (SPECULATIVE argument; the locators are UNVERIFIED):
1. Over `κ̄`, the torus part is the unique maximal torus.
2. A maximal torus `T` of the smooth connected group `G⁰_k` exists over `k` (SGA 3 II, Exp. XIV, Thm 1.1), and
   `T_κ̄` is maximal.
3. `G⁰_k / T` becomes an abelian variety over `κ̄`, so it is proper (properness descends along field extensions,
   EGA IV₂ 2.7.1). Being also smooth and connected, it is an abelian variety.
4. Tori over a separably closed field are split.

It is needed only when `k(s)` is imperfect, which never happens at a DVR of a number field. It is not needed at all
if SGA 7 IX defines semistable reduction geometrically.

## 6. Files

- `scratch/unipotent-b/UnipotentB.lean` is the deliverable, in seven parts:
  - §0: verbatim copies of `ReductSplit.SemistableUnipotent`, `ReductGlue.SemistableUnipotentSH` and
    `ReductGlue.StrictHenselizationInside`, each checked `= original := rfl`;
  - §1: semistability over `k(s)`;
  - §2: the printed leaf and `SemistableUnipotentSH0`;
  - §3: `SemistableUnipotent0`;
  - §4: the unrestricted reduction;
  - §5: `SepClosureTateRestrict` from the two smaller Props;
  - §6: those Props proved, the final theorems and the geometric variant.
- `scratch/unipotent-b/UsesCheck.lean`: `RaynaudCriterion0` from the restricted field (compiles).
- `scratch/unipotent-b/UsesFail.lean`: the r6 proof with the restricted field. It fails as expected, and is kept as
  the record.
- `scratch/unipotent-b/Deps.lean` and `deps.txt`: the dependency-closure check.
- `scratch/unipotent-b/axioms.txt`, `log.md`.

Check with `lake env lean scratch/unipotent-b/UnipotentB.lean`. A fresh worktree needs `lean/.lake` (upstream ZInQ
build); here it was reflink-copied from `../genus-fold/lean/.lake`, whose `lean/ZInQ` is identical.

## 7. What remains

- SGA 7 IX Prop. 3.5 should be read in the print, to fix three things: the wording of `SemistableUnipotentPrintedGen`
  (strictly henselian setting, "unipotent", the echelon clause), whether SGA 7 IX defines semistability over `k(s)`
  or geometrically, and the number.
- `SemiAbelianDescendsSepClosed` is unproved glue. It is needed only for imperfect residue fields, and the unused
  generality of r6 over every field is what makes it needed.
- Row r8 is inert in the final proof. Dropping it would remove a dead branch, but that is a lead decision.
