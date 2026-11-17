# gt-qm (2026-11-15)

**Result.**
* `qmCentralizerCMC` (added-bundle LEAF) is proved, with no new leaves:
  `HDec.QMLattice.qmCentralizerCMC_of (hU : UniformizationLeafAll) (hG : GAGAMorphism) (hM : MumfordTorsionAlgClosed) : QMSplit.Aut.QMCentralizerCMC`.
  It is in `ZInQKernel/Contrib/OneProof/QMLattice.lean` (imports TailZ26 only). `#discharges`:
  `DISCHARGES [OpenAddedLeaves14.qmCentralizerCMC]`, still assumes only the three existing textbook fields,
  standard axioms.
* `yuThm11` (textbook LEAF) is **not** proved as stated. It covers every algebraically closed field of
  characteristic 0 and every indefinite `(a, b)`, while the ℂ-analytic inputs reach only fields embeddable in ℂ
  and QM by 𝒪 ⊂ (2,−3).
* The chain uses it at exactly 4 live sites, all at (2,−3) for a QM structure by 𝒪 over `Qbar` or
  `AlgebraicClosure L'` (checked by a value-closure script).
* That form, `YuB6Alg`, and the more general `YuB6Emb` (any field embeddable in ℂ, including ℂ) are proved
  from the same three fields (`yuB6Alg_of'`, `yuB6Emb_of'`; T11b is proved in the chain), and are implied by
  `YuThm11`.
* All 4 consumers, rerouted to `YuB6Alg`, compile (`scratch/gt-qm/Reroute.lean`).

**Route.**
* T35 + T11a + the proved `QMLatticeAlgebra` give `End(A)` = the maps preserving `Λ_τ = ι(𝒪)(τ,1)ᵀ` (`unif_conj`).
* The commutant of ι(𝒪) is ℂ, which gives `End_𝒪(A) ≅ 𝒪 ∩ S_τ`, with `S_τ` = ℚ or an imaginary quadratic field.
* For Yu: `S_τ = ℚ` gives `End⁰ = ι(B)` (a rank argument); otherwise `End⁰ ≅ M₂(θ(k))` in the basis
  `(v, ι(i)v)`, and `ℚ ⊗ End ≅ C` by localization.

**What compiles.** Every proof in `QMLattice.lean` (no sorry, standard axioms). The full
`lake build +Main +Discharges +QMLattice` succeeds, and so do the scratch checks (`Discharges`, `Axioms`,
`Reroute`, `Reach`).

**What remains (integrator).**
1. Fold `qmCentralizerCMC`. The added-bundle conversion needs the textbook bundle `t`, which `autofold.py`
   cannot express:
   `qmCentralizerCMC := qmCentralizerCMC_of t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`.
2. Dropping `yuThm11` needs a manual fold. The old bundle generations 6/4/3/2/TextbookLeaves carry
   `t27 : QMDichotomyYu`, so about 30 declarations must be re-versioned to take `YuB6Alg`; the list is in
   docs/research/gt-qm.md §5.
