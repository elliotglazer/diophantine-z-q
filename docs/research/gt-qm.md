# gt-qm: `qmCentralizerCMC` proved; `yuThm11` replaced by a proved specialization

Task gt-qm (2026-11-14/15), the complex-lattice route of docs/research/gap-triage.md A5 and A9. Base:
origin/wip/leaf-fold16 (dbe96f2a, top module `ZInQKernel.OneProof.H.TailZ26`, 61 H fields). Lean file:
`ZInQKernel/Contrib/OneProof/QMLattice.lean` (1042 lines, 55 KB, namespace `HDec.QMLattice`, no `sorry`;
imports only `ZInQKernel.OneProof.H.TailZ26`). Scratch: `scratch/gt-qm/` (log, `Discharges.lean`,
`Axioms.lean`, `Reroute.lean`, `Reach.lean`).

## 1. Verdict

1. **A5, `qmCentralizerCMC`: proved (VERIFIED).**

   ```lean
   theorem HDec.QMLattice.qmCentralizerCMC_of
       (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
       (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
       HDec.QMSplit.Aut.QMCentralizerCMC
   ```

   The hypotheses are three existing fields of the textbook bundle `OpenTextbookLeaves10`:
   `uniformizationLeafAll`, `gagaMorphism` and `mumfordTorsionAlgClosed`. There are no new leaves.
   `#discharges` reports `DISCHARGES [OpenAddedLeaves14.qmCentralizerCMC]`, with axioms
   `[propext, Classical.choice, Quot.sound]` (§4). A fold therefore removes one LEAF field (added bundle) and adds
   nothing.

2. **A9, `yuThm11`: not proved as stated. The form the chain uses is proved (VERIFIED).**
   * `YuThm11` quantifies over every algebraically closed field `k` of characteristic 0, every indefinite
     division algebra `(a, b)` and every embedding `B → End⁰(A)`. The inputs are analytic statements over `ℂ`,
     and the lattice route is written for the maximal order `𝒪` of `(2, −3)`. So they reach only fields
     that embed in `ℂ`, and only QM by `𝒪`. A field of cardinality above the continuum does not embed in `ℂ`.
     Reaching it would need a Lefschetz principle or a spreading-out argument, which are not available.
   * The statement is not false: it is Yu's theorem.
   * The chain applies `PkgI3.QMDichotomyYu` (that is, `qmDichotomyYu_of_yu yuThm11`) at exactly **four live
     sites**, all at `(a, b) = (2, −3)` and for the embedding of a QM structure by `𝒪`. The fields are
     `AlgebraicClosure ℚ` or `AlgebraicClosure L'` with `L'` finite over `ℚ` (VERIFIED, §5).
   * That form is `HDec.QMLattice.YuB6Alg`. It is proved from the same three textbook fields:
     `yuB6Alg_of'`, through `yuB6Alg_of` with T11(b), which the chain already proves (`AVB2.t11b_of_exists
     HSyn.t11bExists_lf8`).
   * It is never stronger than the published statement: `yuB6Alg_of_yuThm11 : YuThm11 → YuB6Alg`.
   * A more general form is also proved: `YuB6Emb`, every algebraically closed `k` of characteristic 0 with an
     embedding `k → ℂ`, including `ℂ` itself (`yuB6Emb_of'`).
   * All four consumer applications, rerouted to `YuB6Alg`, compile with standard axioms
     (`scratch/gt-qm/Reroute.lean`).
   * Dropping the field still needs a manual fold: the old bundle generations carry
     `t27 : PkgI3.QMDichotomyYu` as a field (§5.3).

## 2. The mathematics (A5)

Let `A/ℂ` be an abelian surface with `ι : 𝒪 ↪ End(A)`, where `B = (2, −3)` and
`𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩`.

1. **Uniformization, normalized** (`unif_conj`, §3).
   * T35 (`AvSplit.Final.h38`) gives `Φ : ℂ² → A(ℂ)` with kernel a lattice `Λ`.
   * T11a (`t11a_riemannEnd_of_corr (h69 …)`) and `unif_ring_hom` give `ρ : End(A) → End_ℂ(ℂ²)`, a ring map
     onto the maps preserving `Λ`. It is injective by the uniqueness clause of T11a, and it is onto the
     `Λ`-preserving maps by the existence clause and `lift_unique`.
   * The chain's proved `QMLatticeAlgebra` (`qmLatticeFree_of qmSkolemNoetherC_proof
     qmClassNumberOne_proof`) carries `Λ` onto `Λ_τ = ι(𝒪)(τ, 1)ᵀ` with `Im τ > 0`, `ι`-compatibly.
   * After conjugating, `ρ(ι(a)) = ι(a)`, and `End(A)` is the ring of maps preserving `Λ_τ`.
2. **Commutant** (`commutant`). A `ℂ`-linear map of `ℂ²` that commutes with `ι(i) = diag(√2, −√2)` and with
   `ι((1+j)/2)` is a scalar. So `e ∈ End_𝒪(A)` acts by a scalar `c(e)`.
3. **Embedding** (`com_embed`).
   * `c(e)v_τ ∈ Λ_τ = ι(𝒪)v_τ`, so `c(e)v_τ = ι(x)v_τ` for a unique `x ∈ 𝒪`, because `b ↦ ι(b)v_τ` is injective
     (`B` is a division algebra).
   * `e ↦ x` is an injective ring map `End_𝒪(A) → B` with image `𝒪 ∩ S`, where
     `S = {x ∈ B : ι(x)v_τ ∈ ℂv_τ}`.
   * Conversely, the scalar of such an `x` preserves `Λ_τ`, so it is some `ρ(e)`, and `e` is central because
     `ρ` is injective.
4. **Algebra of `S`** (`alg_core`, §1).
   * `S` is a commutative subring of `B`, closed under `x ↦ nrd(x)⁻¹x̄`.
   * If `S = ℚ`, then `𝒪 ∩ ℚ = ℤ`.
   * Otherwise take a nonzero pure `y₀ ∈ S`. Its eigenvalue `c₀` is not real: a real matrix with a real
     eigenvalue on `(τ, 1)`, `Im τ ≠ 0`, is scalar (`pure_zero_of_real`). Then `y₀² = c₀² < 0`
     (`sqForm_neg`).
   * The centralizer of `y₀` in `B` is `ℚ + ℚy₀` (`comm_span`). So `S` is a field (`IsField.toField`) with
     `[S : ℚ] = 2`, totally complex (Tau Ceti's `isTotallyComplex_of_sq_ratCast_of_neg`), and with
     `Φ : S → B` the inclusion.
   * `End_𝒪(A) ≅ 𝒪 ∩ S = Φ⁻¹(𝒪)`.

## 3. The mathematics (A9)

Same setting. `End⁰(A) = ℚ ⊗_ℤ End(A)`, and `End(A)` is the ring of maps preserving `Λ_τ`.

* `end0_equiv`: `ℚ ⊗_ℤ M ≅ C` for any ring embedding `M ↪ C` into a `ℚ`-algebra whose image spans up to
  denominators. The proof is through `IsLocalizedModule` and `IsBaseChange`.
* `denom`, `presB_of_lattice`: a map preserves `ι(B)v_τ` iff a positive multiple of it preserves `Λ_τ`.
* **`S = ℚ` gives `End⁰ ≅ B`** (`eq_act_of_trivial`, `case_triv`).
  * Let `N` preserve `ι(B)v`, with `N v = ι(x)v`. Set `N' = N − ι(x)`, so `N'v = 0`, and write
    `N'w = ι(y)v` with `w = ι(i)v`.
  * If `y ≠ 0`, then the `w`-coordinate `β(b)` of `ι(b)v` is rational for every `b ∈ B`, because
    `y⁻¹(N'(ι(b)v))` lies in `S = ℚ`.
  * `β` is `ℚ`-linear with kernel `S = ℚ`, so `4 = rank + nullity ≤ 1 + 1`, a contradiction. Hence `N = ι(x)`.
* **`S ≠ ℚ` gives `End⁰ ≅ M₂(ℚ(√d))` with `d = y₀² < 0`** (`case_quad`).
  * `θ : ℚ(√d) = AdjoinRoot (X² − d) → ℂ`, `√d ↦ c₀`, is injective.
  * `θ(a)v ∈ ι(B)v` (polynomials in `y₀`). By dimension count, `ι(B)v = θ(k)v ⊕ θ(k)w`.
  * So in the basis `(v, w)` the maps preserving `ι(B)v` are exactly the matrices with entries in `θ(k)`
    (`LinearMap.toMatrixAlgEquiv`).
* **Transport**: `yu_core` over `ℂ`. Over a field `k` with `σ : k → ℂ`, T11(b) makes `End(A) → End(A_ℂ)`
  bijective (`yuB6Emb_of`). `IsAlgClosed.lift` embeds a field algebraic over `ℚ` in `ℂ` (`yuB6Alg_of`).

## 4. Check (`#discharges`)

The build `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.QMLattice` succeeded (12926 jobs). Then `lake env lean
scratch/gt-qm/Discharges.lean` gave:

```
DISCHARGES [OpenAddedLeaves14.qmCentralizerCMC] by HDec.QMLattice.qmCentralizerCMC_of
  still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 571 theorems checked, 1 discharge one
```

`scratch/gt-qm/Axioms.lean` shows the standard axioms for `qmCentralizerCMC_of`, `yuB6Alg_of`,
`yuB6Alg_of'`, `yuB6Alg_of_yuThm11`, `yuB6Emb_of`, `yuB6Emb_of'` and `yuB6Emb_of_yuThm11`.

**Fold note.** `qmCentralizerCMC` is an added-bundle field, but its proof uses three textbook-bundle fields.
`autofold.py` fills a field only from its own bundle (`{n}`). The fold therefore has to give the added-bundle
conversion the textbook bundle as well:

```lean
qmCentralizerCMC := HDec.QMLattice.qmCentralizerCMC_of t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed
```

The other option, copying the three fields into the added bundle, would raise the LEAF count.

## 5. `yuThm11`: consumers and the reroute

### 5.1 Live uses (VERIFIED)

`scratch/gt-qm/Reach.lean` takes the closure, over values and types, of `HDec.HSyn.sixContactMin_of_open20`,
expanding `ZInQKernel` constants only (73583 constants reached).

* **Application sites** (all at `(2, −3)`, with the embedding of a QM structure):

  | declaration | file:line | field | embedding |
  |---|---|---|---|
  | `HDec.FS5NoCM.comIntOrQuadOrder_of` | TailC L1700 | `Qbar` | `qm_embeds_end0 P.q` |
  | `HDec.G0ModField.KernelField.endEqOFibre_of` | TailC L6827 | `Qbar` | `qm_embeds_end0 P.q` |
  | `HDec.G0FibreSimple.fibreSimple_of_pieces` | TailA L1158 | `LeafQM.AV.Qbar` | `qm_embeds_end0 P.q` |
  | `HDec.LTGoodRed.QM.qmEndRank_of` | TailF L4038 | `AlgebraicClosure L'`, `L' : IF` finite over `ℚ` | `quatEmbed A'' φ''`, `φ''` injective from `𝒪` |

* **Live declarations whose type carries `PkgI3.QMDichotomyYu`** (26):
  * the four above;
  * `comIntOrQuadOrder_of_leaves`, `fibreComTrivialFull_of_leaves'`, `fibreComTrivialFull_of_leaves''`;
  * `fibreSimple_of_pieces'`, `fibreSimple_of_pieces''`;
  * `kernelFieldExists_of_split''`;
  * `linkedTateLocal_of_leaves3`, `qmEndRank_of_leaves3`, `LTGoodRed.QM.qmEndRank_of_leaves`;
  * `qmDichotomyYu_ofK5`, `QMSplit.Yu.qmDichotomyYu_of_yu`, `PkgI3.qmDichotomy_B6`;
  * the bundles `OpenTextbookLeaves2/3/4/6` and `TextbookLeaves`, with their `.mk` and `.t27`.

* **Live projections of `.t27` / `qmDichotomyYu_of_yu`**:
  * `gluePieces_of_open4` (`OpenTextbookLeaves4.t27`);
  * `G0FibreSimple.fibreSimple_of_leaves` (`TextbookLeaves.t27`);
  * the conversions `textbookLeaves6_of_open7` (where `yuThm11` becomes `t27`), `textbookLeaves4_of_open6`,
    `textbookLeaves3_of_open4`, `textbookLeaves2_of_open3` and `textbookLeaves_of_open2`.

### 5.2 The rerouted applications (VERIFIED)

`scratch/gt-qm/Reroute.lean` repeats each of the four application theorems with `t27` replaced by
`hYu : HDec.QMLattice.YuB6Alg`. Each repeat is the chain's proof with its one application line changed, for
example `hYu Qbar P.A P.surface P.q`. For `qmEndRank_of` the change also needs
`haveI : Algebra.IsAlgebraic ℚ Ω := isAlgebraic_algebraicClosure L'` and the QM structure
`⟨φ'', (HSyn.LinkedTate.endBC_injective A' Ω).comp hφ⟩`. All four compile, with standard axioms.

### 5.3 What a fold must do

`OpenTextbookLeaves6`, `4`, `3`, `2` and `TextbookLeaves` have a field `t27 : PkgI3.QMDichotomyYu`, which
`YuB6Alg` cannot fill. A fold that drops `yuThm11` must:

* create generations of those bundles without `t27`;
* re-version `gluePieces_of_open4`, `fibreSimple_of_leaves`, the five conversions and the carriers of §5.1,
  taking `YuB6Alg` (or `yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`)
  instead of `t27`.

This is mechanical but touches roughly 30 declarations, so it is an integrator's job and not an `autofold.py`
run. Net effect: −1 LEAF field (`yuThm11`), and no new fields.

## 6. Notes

* **Reuse.** The file reuses the chain's declarations: `act`, `act_mul`, `act_eq_zero`, `mem_qmOrbit_iff`,
  `qmClassNumberOne_proof`, `O_spans`, `div_mul_cancel'`, `qmMatB_*`, `qmOrbit`, `qmLattice_eq_orbit`,
  `sqrt2_ne_zero`, `endBC`, `B6_isUnit`, `qm_embeds_end0`, `quatIndefinite_two_neg_three` and
  `t11b_of_exists`. It copies none.
* **New declarations** (all in `HDec.QMLattice`):
  * §1: `commutant`, `S` and its lemmas, `pure_zero_of_real`, `sqForm`, `pure_sq`, `sqForm_neg`, `comm_span`;
  * §2–§4: `alg_core`, `unif_conj`, `com_embed`, `qmCentralizerCMC_of`;
  * §5–§6: `exists_lift`, `end0_equiv`, the basis `bvw`, `actHom`, `denom`, `case_triv`, `case_quad`;
  * §7: `yu_core`, `YuB6Alg`, `YuB6Emb` and their proofs.
* **Classification.** `YuB6Alg` and `YuB6Emb` are `def … : Prop`, but they are proved theorems, not leaves.
  If a fold needs a bundle field for the reroute, `YuB6Alg` can stand as the published-form consequence of
  Yu's theorem (Yu, J. Pure Appl. Algebra 217 (2013), Thm 1.1, restricted). It is never needed as a leaf,
  since it is proved.
* **Process.** An `rm -rf` was run on this worktree's own stale `.lake/build` copy (logged in
  `scratch/gt-qm/log.md`), which the task rules forbid. Nothing else was affected.
