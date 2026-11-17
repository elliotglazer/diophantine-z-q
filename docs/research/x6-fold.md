# x6-fold: x6-glue folded into the single proof (`r1r2Ab` and `x6ConicModel` from published-form leaves)

**Result.** `ZInQ.OneProof.frozenTarget` now goes through `HDec.HSyn.sixContactMin_of_open16`
(`ZInQKernel/OneProof/H/TailZ22.lean`). It has 65 open fields, and the strict LEAF/GLUE count is **55/10** (it was
61 fields, 50/11).
* Under the r5 §4.8 reading (`gonzalezRotgerCountX6Ab` a composite) the count is 54/11.
* If the fibre clause of Elkies' leaf is counted as a composite (§5), it is 54/11 strict. The GLUE count does not
  rise under either reading, so the fold was taken.

The TYZ and GZ hypotheses are unchanged. The checks below are all VERIFIED:
* `lake build +ZInQKernel.OneProof.Main` passes.
* `#print axioms ZInQ.OneProof.frozenTarget` is `[propext, Classical.choice, Quot.sound]`.
* No existing OneProof constant changed its type or value hash.

Branch `wip/x6-fold`, on top of `wip/leaf-fold11` (b73da969), with `origin/wip/x6-glue` (685a56e1) merged. Model work,
no human review. Marks: **VERIFIED** = compiled, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a locator or display recalled without a source (there is no network on
this host; the locators are x6-glue's and shimura-glue's).

## 1. The fold

| Step | Source | Fields removed | Fields added | Strict count |
| --- | --- | --- | --- | --- |
| x6-fold (TailZ20-TailZ22) | x6-glue (with shimura-glue, shimura-split, qm-glue, coarse-factor) | `r1r2Ab` (GLUE, comp), `x6ConicModel` (GLUE, c) | `babaGranathRationalAb`, `gonzalezRotgerX6Ab`, `elkiesEquationsX6Ab`, `deligneComponentsX6PrintedAb`, `geomConnOfAlgClosure` (LEAF), `rayClassCMAb` (GLUE, c) | 61, 50/11 → 65, 55/10 |

New modules. Each is under 150 KB, and none of them edits an existing module.

* **`H/TailZ20.lean`** (104.5 KB) and **`H/TailZ21.lean`** (71.5 KB) hold x6-glue's `scratch/x6-glue/X6Glue.lean`.
  That file is shimura-glue's `RowsGlue.lean` verbatim, followed by x6-glue's parts `EvalAffine`, `Charts`,
  `ConicProof` and `X6New`. Three kinds of material were removed (`scratch/x6-fold/mk_tail.py`, `mk_modules.py`):
  * Every declaration that the chain already has, meaning the same name with the same type hash (`Dump2.lean`,
    `x6dups.tsv`): 258 of them. Of these, 37 are in `TailU` (qm-split's `ModuliSplit`), 53 in `TailR` (`ModelGlue`
    and all of curve-split's `CurveSplit`), 165 in `TailZ12` (shimura-glue's `Adelic`/`Deligne`, including
    `ShimuraGlue.DeligneComponentsX6Printed`, and shimura-split's `Y3Conn`) and 3 in `TailZ8` (`Count`). The
    chain's copies are used.
  * Every declaration that is not needed by `r1r2_of_published`, `x6ConicModel_of_published`, `X6Leaves`,
    `x6Rows_of_leaves` or `ElkiesEquationsX6`. The dependency closure comes from `Dump3.lean` / `x6edges.tsv`.
    Removed this way are the bundles `ShimuraSplitLeaves`, `ShimuraGlueLeaves*`, their `rows_of_*`, the converses,
    and all `example`s and `#print`s.
  * Twelve lemmas of coarse-factor's `CoarseFactorAG`. Their text after the docstring is a verbatim copy of
    `TailR`'s `CurveSplit.*`, so they are replaced by `open _root_.CurveSplit (…)`. A thirteenth,
    `isDedekindDomain_sections`, has different section variables in `TailR` and is kept.

  240 declarations remain, and nothing in them is edited.
  * `TailZ20` contains qm-glue's coarse comparison, coarse-factor's `FactorThroughSurj` proof, and shimura-split's
    Bridge, BG and PairsLift parts with its additions.
  * `TailZ21` contains shimura-glue's Möbius glue (`mobiusCompose`) and ray-class part (`reciprocityCanonical_of_rayClass`),
    and x6-glue's parts: `ev_injective`, `ev_surjective`, `ev_comp`, `ElkiesCharts`, `conicModelT_of_charts`,
    `ElkiesEquationsX6`, `elkiesConicX6_of_equations`, `r1r2_of_published`, `x6ConicModel_of_published`, `X6Leaves`
    and `x6Rows_of_leaves`.
* **`H/TailZ22.lean`** (21 KB) has the following parts:
  * **Abelian-scheme forms of the five leaves stated on a moduli witness.** These are `DeligneComponentsX6PrintedAb`,
    `RayClassCMAb`, `GonzalezRotgerX6Ab`, `ElkiesEquationsX6Ab` and `BabaGranathRationalAb`.
    * Each one is the original text with `R1fpProps` replaced by `R1fpPropsAb`, in the original's namespace and with
      the original's `open`s.
    * Each has an `L_iff_ab` proved by `unfold; rw [r1fpProps_eq_ab' hR]`.
    * This is exactly route-a-fold's treatment of the other moduli leaves (`TailZ17`). Since route-a-fold, the bundles
      state moduli leaves on abelian schemes, the objects of the published fine-moduli problem. The task text
      planned the seven leaves in their `R1fpProps` form; the abelian-scheme form keeps the bundles uniform and is
      equivalent under the existing field `mumfordRigidityCore`.
  * **The bundles** `OpenResearchLeaves13` (35 fields) and `OpenAddedLeaves12` (14 fields).
  * **The conversions:**
    * `x6Rows_of_open13` builds x6-glue's `X6Leaves` from the bundles. Each leaf comes via
      `(L_iff_ab (mumfordRigidity_of_core r.mumfordRigidityCore)).mpr`, and T5 comes from the textbook field
      `mumfordTorsionAlgClosed` by the chain's `AvSplit.torsionStructure_of_mumford`.
    * `researchLeaves12_of_open13` fills `r1r2Ab := (r1R2fpRep_iff_ab (mumfordRigidity_of_core …)).mp (r1r2_of_published …)`.
    * `addedLeaves11_of_open12` fills `x6ConicModel := x6ConicModel_of_published …`.
  * **The new top:** `sixContactMin_of_open16 r t l g := sixContactMin_of_open15 (researchLeaves12_of_open13 r t l) t
    (addedLeaves11_of_open12 r t l) g`.
* **`Main.lean`**: `frozenTarget` now takes `OpenResearchLeaves13`, `OpenTextbookLeaves10`, `OpenAddedLeaves12` and
  `OpenGlue7`, and goes through `sixContactMin_of_open16`. Its doc comment was updated.

**Existing fields reused, not duplicated (VERIFIED by reading the four top bundles):**
* T5 is not a field. It is proved from `OpenTextbookLeaves10.mumfordTorsionAlgClosed` (`TailQ`), as `TailZ7`
  already does.
* `GeomConnOfAlgClosure` (EGA IV 4.5, `X_{k̄}` connected ⇒ geometrically connected) is not a field. The textbook
  field `geomConnOfRationalPoint` (Stacks 04KV, a rational point ⇒ geometrically connected) is a different statement.
* `gonzalezRotgerCountX6Ab` (González–Rotger Prop. 5.6, the count) is a different theorem from `GonzalezRotgerX6`
  (Thm 5.12, residue fields).
* `deligneComponentsY3PrintedAb` is Deligne's theorem at level `K₃` on `Y₃`. The new
  `deligneComponentsX6PrintedAb` is the same theorem at level `𝒪̂^×` on `X₆`, a different instance.

## 2. frozenTarget's hypotheses, removed and added

| | field | bundle | type | kind | source |
| --- | --- | --- | --- | --- | --- |
| removed | `r1r2Ab` | research | `LeafAdopt.R1R2fpRepAb` | GLUE (comp) | R1(a,c,d), R2, R5 on one `Y₃`, `X₆` (Shimura 1967; Deligne 1971; Baba–Granath 2008; González–Rotger 2006; Lemma QP) |
| removed | `x6ConicModel` | added | `X6Kummer.X6ConicModel` | GLUE (c) | Kurihara 1979; Elkies 1998 §3 |
| added | `babaGranathRationalAb` | research | `QMSplit.Moduli.BabaGranathRationalAb` | LEAF (printed; one table reading UNVERIFIED) | Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1 (audit YES) |
| added | `gonzalezRotgerX6Ab` | research | `QMSplit.Moduli.GonzalezRotgerX6Ab` | LEAF (printed) | González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 (audit YES) |
| added | `elkiesEquationsX6Ab` | research | `QMSplit.Moduli.ElkiesEquationsX6Ab` | LEAF (printed, equations as a scheme); comp under the strict reading of its fibre clause (§5) | Elkies, ANTS-III, LNCS 1423 (1998), §3 (UNVERIFIED) |
| added | `rayClassCMAb` | research | `ShimuraGlue.Ray.RayClassCMAb` | GLUE (c) | Shimura, Ann. of Math. 85 (1967), Main Thm I; Deligne 1971 §3 (UNVERIFIED) |
| added | `deligneComponentsX6PrintedAb` | added | `ShimuraGlue.DeligneComponentsX6PrintedAb` | LEAF (printed; the double coset `ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×) = 1` is computed in Lean, `TailZ12`) | Deligne, Sém. Bourbaki 389 (1971) Thm 2.4, §3; PSPM 33 (1979) 2.6.3 (UNVERIFIED) |
| added | `geomConnOfAlgClosure` | added | `QMSplit.Moduli.GeomConnOfAlgClosure` | LEAF (textbook, weakened: adds `IsProper`, `CharZero k`) | EGA IV 4.5; Stacks 0389 (UNVERIFIED) |

Every new moduli leaf is stated on one canonical witness with the clause list `R1fpPropsAb`. As for `r1r2Ab`,
`gonzalezRotgerCountX6Ab` and `deligneComponentsY3PrintedAb`, the specialization of Deligne's PEL moduli to that
clause list (with Lemma QP) is the open human check that frontier.md lists.

Counting `r1r2Ab` as GLUE (comp) follows leaf-fold10's table, which leaf-fold11 inherited. Its statement is unchanged
in the chain; only its source changed.

## 3. Hash guard

The new tree was compared with the base top by op-compact's `DumpCompact`:
* `scratch/x6-fold/DumpBase.lean` covers `TailZ19` and the other imports of `Main`, without `Main`.
* `scratch/x6-fold/DumpNew.lean` covers `Main`.

The before tree is the same set of oleans: no existing OneProof H module was rebuilt. The result is
`scratch/x6-fold/cmp_hashes_out.txt` (VERIFIED):
* 12767 constants before, 13226 after. leaf-fold11 reports 12768, which includes `frozenTarget`; the base dump
  omits `Main`.
* 0 deleted and 0 changed.
* 459 new: 111 in `TailZ20`, 255 in `TailZ21`, 92 in `TailZ22`, and `ZInQ.OneProof.frozenTarget` (its statement
  changes as in §2).
* No `ZInQKernel/HDecomp`, `ZInQKernel/Contrib` or existing `OneProof/H` file changed. No HDec copy was deleted, so
  FaithCheck was not needed.

## 4. Checks

All VERIFIED in this worktree, one Lean process at a time:

* `lake env lean scratch/x6-fold/Test1.lean` (the trimmed body as one file over `TailZ19`): 0 errors, 1 min.
  `r1r2_of_published` and `x6ConicModel_of_published` have standard axioms.
* `lake build ZInQKernel.OneProof.H.TailZ21`, then `ZInQKernel.OneProof.H.TailZ22`: both pass. The six `#print axioms`
  lines in `TailZ22` (`r1r2_of_published`, `x6ConicModel_of_published`, `x6Rows_of_open13`,
  `researchLeaves12_of_open13`, `addedLeaves11_of_open12`, `sixContactMin_of_open16`) are all
  `[propext, Classical.choice, Quot.sound]`.
* `lake build +ZInQKernel.OneProof.Main`: passes (12916 jobs, 8.5 min). It also rebuilt two stale, unrelated modules
  (`Compiler.Exponential.AlphaEquations`, `Multiplication.Certificate.Parity`) and their dependents, including
  `OneProof.TopChain` and `OneProof.TYZSplit`, from unchanged sources. `ZInQ.OneProof.frozenTarget` depends on
  `[propext, Classical.choice, Quot.sound]`.
* `scratch/x6-fold/PruneScan.lean` (genus-fold's scan) finds 0 unused fields. The top bundles are
  `OpenResearchLeaves13` (35), `OpenTextbookLeaves10` (15), `OpenAddedLeaves12` (14) and `OpenGlue7` (1): 65 fields.
* The five `L_iff_ab` proofs (`rw [r1fpProps_eq_ab' hR]`) check that each `LAb` elaborates to the original term with
  only `R1fpProps` replaced.

## 5. Reading risks and remaining strict GLUE (10)

Reading risks, carried over from x6-glue §3–§5:

* **Elkies' display, section number and orientation: UNVERIFIED.** The paper was not read: there is no network.
  * The leaf asserts `X₆ = X*(6)(√−t, √(3(t−1)))` as the affine charts `s² = −t, r² = 3(t−1)` (over `t ≠ ∞`) and
    `a² = −1/t, b² = 3(1/t − 1)` (over `t ≠ 0`).
  * It also asserts `t = 0, 1, ∞` at the CM points of discriminants `−24, −4, −3`.
  * The residue fields fix `t = 1 ↔ D = −4`. Which of `0` and `∞` goes with `−24` and which with `−3` rests on
    Elkies' text.
  * x6-glue's review notes that the chart statement itself is invariant under `t ↦ 1/t`. Only the CM labels depend
    on the orientation.
  * The reading "the function field ⇒ the smooth projective model" is SPECULATIVE with standard reasons
    (Hartshorne I.6.12, II.6.8, numbers UNVERIFIED).
* **Elkies' fibre clause.** "`t(x) = t(x')` iff the QM pairs are `Aut(𝒪)`-twists" combines two statements:
  * Elkies' "`t` is a coordinate on `X₆/W`";
  * the moduli meaning of `W ≅ Aut(𝒪)` acting by twists, as in Baba–Granath Thm 2.1.

  x6-glue §5.2 calls this a composite of two published statements. Under that strict reading
  `elkiesEquationsX6Ab` is GLUE (comp), and the count is 54/11 instead of 55/10: neutral, not a rise.
* **One Baba–Granath table reading: UNVERIFIED.** In `BabaGranathRational`, the clause "the CM points of
  discriminants `−4, −3, −24` are exactly the fibres over three rational points" is read from the §3.1
  elliptic-order table. locators.md grades that table's row NO for a different claim, its ramification indices.
* **`RayClassCM` is a consequence**, not the printed statement. Shimura reciprocity at CM points gives `k(x)` as the
  class field of `k^× k_∞^× {s : ι(s) ∈ gK₃g⁻¹}`. Two steps lead from there to the leaf:
  * the inclusion `ι(1 + 3𝒪̂_k) ⊆ g(1 + 3𝒪̂)g⁻¹` for an optimal embedding;
  * the dictionary "CM by `𝒪_k`" ↔ "`[h_k, g]` with `ι(𝒪_k) ⊆ gÔg⁻¹`", which needs the adelic uniformization of
    `Y₃` with its moduli interpretation. That is not in the kernel (x6-glue §5.1).
* `GeomConnOfAlgClosure` is weaker than the print, because it adds properness and characteristic 0. The locators EGA
  IV 4.5 and Stacks 0389 are UNVERIFIED.

**Remaining strict GLUE (10).** This is leaf-fold11's 11, less `r1r2Ab` and `x6ConicModel`, plus `rayClassCMAb`.
* Some are being worked on elsewhere: c-to-printed2 (`r17`, `t09SymmIsogenyExists`, `eigenformHTNew`), theta-glue
  (`thetaRatiosAlgebraic`) and `QuotientP1Coordinate`.
* Others are blocked:
  * `shimuraFamilyAb` needs global class field theory;
  * `r11r12` (no `B_st`) and `r16` cannot be split over Mathlib's present definitions.
* `rayClassCMAb` would need the adelic uniformization of `Y₃` with its moduli interpretation.

**Possible further dedupe (not done).** Some of the copied parts overlap the chain in content but not by name:
* shimura-split's Part 1 in `TailZ20` (`ShimuraSplit.fieldOfModuli3_eq_residueImage`, `r5fp_of_point`) overlaps
  leaf-fold9's `ZInQ.LeafFold9` versions in `TailZ5`;
* coarse-factor's remaining `CoarseFactorAG` lemmas overlap `TailR`'s `CurveSplit`.

Merging them would mean editing copied proofs. It was left alone.

## 6. Files

* `ZInQKernel/OneProof/H/TailZ20.lean`, `TailZ21.lean`, `TailZ22.lean` (new); `ZInQKernel/OneProof/Main.lean` (switched).
* `scratch/x6-fold/`:
  * the results log `log.md`;
  * `Dump1.tail.lean` and `Dump3.tail.lean`, appended to `X6Glue.lean` to make `x6names.tsv` and `x6edges.tsv`;
  * `Dump2.lean`, which makes `x6dups.tsv`;
  * the generators `mk_tail.py`, `mk_modules.py`, `mk_bundle.py`, `mk_tailz22.py`, with their outputs `x6body.lean`
    and `x6kept.tsv`;
  * the hash guard `DumpBase.lean`, `DumpNew.lean`, `cmp_hashes.py`, `cmp_hashes_out.txt`;
  * `PruneScan.lean`.
