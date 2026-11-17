# x6-glue results log

Base e38375b3 (wip/w62). One Lean process at a time (`lake env lean`).

## Step 0: state of the two fields at the base (VERIFIED by reading)
- shimura-split: `r1r2fpRep_of_printed_t5 : DeligneComponentsX6 → GeomConnOfAlgClosure → T5 → BabaGranathX6' →
  ReciprocityCanonical → GonzalezRotgerX6 → R1R2fpRep`; `x6ConicModel_of_elkies_t5` from `ElkiesConicX6`, r1r2, T5.
- shimura-glue (already in the base, scratch/shimura-glue/): the X6 double coset and the X6 Deligne leaf are
  done: `pi0_Kfull_eq_one` (`ℚ^×_{>0}\𝔸_f^×/nrd(𝒪̂^×)` is a point; `nrd(𝒪̂^×) = ℤ̂^×` by local Hensel
  representations; `𝔸_f^× = ℚ^×_{>0} ℤ̂^×`), `deligneComponentsX6_of_printed : DeligneComponentsX6Printed →
  DeligneComponentsX6`; `ElkiesConicT` (Elkies' coordinate `t`, points form) with
  `elkiesConicX6_of_t' : ElkiesConicT → ElkiesConicX6`; `BabaGranathRational`, `RayClassCM`.
- Remaining non-printed leaves on the two fields: `ElkiesConicT` (points form of Elkies §3) and `RayClassCM`
  (ray-class consequence of Shimura reciprocity).

## Step 1: re-check of the Deligne X6 computation in this tree
- scratch/x6-glue/DeligneX6.lean = scratch/shimura-glue/Deligne.lean verbatim. `lake env lean`: 0 errors,
  1 min 29 s; all 6 `#print axioms` lines `[propext, Classical.choice, Quot.sound]` (incl.
  `ShimuraGlue.deligneComponentsX6_of_printed`, `printed_of_deligneComponentsX6`). VERIFIED.

## Step 2: values of sections at field points of an affine open (parts/EvalAffine.lean, Mathlib + kernel `ToP1` lemma)
- `ev U y h : Γ(X,U) →+* K` (the recipe of the kernel's `ToP1.val`); `eq_specMap_psi` (a point in an affine
  open is `Spec.map ψ ≫ fromSpec`), `ev_eq_psi`, `ev_injective`, `ev_surjective` (K-points in an affine `U`
  ↔ ring homs `Γ(U) → K`), `ev_comp` (naturality), `specQ_hom_ext` (maps `Spec K → Spec ℚ` are unique).
  COMPILED (T1.lean dev file over `ZInQKernel.HDecomp.QM.Leaves`), 0 errors.

## Step 3: Elkies' equations in chart form and the conic model (parts/Charts.lean, parts/ConicProof.lean)
- `ElkiesRing = ℚ[t,s,r]/(s² + t, r² − 3(t − 1))`; `ElkiesCharts X t`: `t.U`, `t.V` affine,
  `Γ(t.U) ≃+* ElkiesRing` with `t ↦ t.f`, `Γ(t.V) ≃+* ElkiesRing` with `u ↦ t.g`, gluing `s·a = 1`,
  `r·a = b` on `t.U ∩ t.V`.
- `X6Glue.conicModelT_of_charts : ElkiesCharts X t → ConicModelT X t` (shimura-glue's points form).
  COMPILED in T1.lean (dev copies of `ConicPt`, `conicGal`, `ConicModelT`, verbatim), axioms
  `[propext, Classical.choice, Quot.sound]`.
- Chart algebra (by hand, VERIFIED): on `U ∩ V`, `a = 1/s`, `b = r/s`, `u = 1/t` give `a² + u = 0`,
  `b² − 3(u − 1) = 0` from `s² = −t`, `r² = 3(t − 1)`.

## Step 4: assembly X6Glue.lean (mk_x6glue.py = shimura-glue RowsGlue.lean verbatim + parts)
- Build note: `lean/.lake` (upstream ZInQ package build) was missing in this worktree; reflink-copied from
  ~/dzq-prune (identical `lean/ZInQ` sources, `diff -rq` empty).
- First run: `X6Kummer.ConicPt` must be written `HDec.X6Kummer.ConicPt` outside namespace HDec (fixed).
- Second run: X6Glue.lean (7362 lines) `lake env lean`: **0 errors**, 2 min 4 s; x6glue_result.txt has 82
  `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`. New ones: `X6Glue.ev_injective`,
  `ev_surjective`, `conicModelT_of_charts`, `HDec.QMSplit.Moduli.elkiesConicT_of_equations`,
  `elkiesConicX6_of_equations`, `r1r2_of_published`, `x6ConicModel_of_published`, `x6Rows_of_leaves`,
  `rows_of_shimuraGlueLeaves4`; the fully qualified `example : X6Leaves → R1R2fpRep ∧ X6ConicModel` compiles.
  VERIFIED.
- ConicDev.lean (= former T1.lean: dev copies + EvalAffine + Charts + ConicProof over
  `ZInQKernel.HDecomp.QM.Leaves` only): 0 errors, standard axioms.

## Step 5: independent model review (read-only agent, no Lean) of ElkiesCharts / ElkiesEquationsX6 / ConicProof
- OK on all four points: the genuine conic satisfies ElkiesCharts (U = {Z≠0}, V = {X≠0}, rings, gluing,
  affine); not stronger than Elkies' function-field statement (smooth ⇒ integral closure); not vacuous; proof
  logic sound; fibre/CM clauses verbatim those of ElkiesConicT; residue fields consistent.
- Notes: gluing conjuncts unused by the proof (kept for faithfulness); Hartshorne locator → I.6.12/II.6.8
  (UNVERIFIED, applied); leaf truth independent of Elkies' 0/∞ orientation (t ↦ 1/t symmetry).
