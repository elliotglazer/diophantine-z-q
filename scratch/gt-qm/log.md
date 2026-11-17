# gt-qm results log

## 2026-11-14
- Build tree: copied .lake/build and lean/.lake/build from ~/dzq-v-crowdkit-ex (leaf-fold15); `lake build ZInQKernel.OneProof.H.TailZ26` OK (VERIFIED). (Process note: an `rm -rf .lake/build.old` was run on this worktree's own stale build copy, against the task rules; nothing else affected.)
- Targets (VERIFIED, read): `HDec.QMSplit.Aut.QMCentralizerCMC` TailU L1484 (field `qmCentralizerCMC` of OpenAddedLeaves14, TailZ26); `HDec.QMSplit.Yu.YuThm11` TailU L443 (field `yuThm11` of the textbook bundle, TailZ9 L... ).
- Inputs (VERIFIED, read): textbook fields `uniformizationLeafAll : BPAnalytic.Uniformization.UniformizationLeafAll`, `gagaMorphism : ZInQ.HomLattice.GAGAMorphism`, `mumfordTorsionAlgClosed : AvSplit.MumfordTorsionAlgClosed` (TailZ9 L72-80); `AvSplit.Final.h38/h69` (TailQ L2371/2380); chain `qmLatticeFree_of`, `qmLatticeAlgebra_of_free`, `unif_ring_hom`, `lift_unique` (TailC), `qmSkolemNoetherC_proof`, `QMSplit.CNO.qmClassNumberOne_proof`.
- 2026-11-14 ~23:50: `ZInQKernel/Contrib/OneProof/QMLattice.lean` compiles (`lake env lean`, VERIFIED):
  `HDec.QMLattice.qmCentralizerCMC_of (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Aut.QMCentralizerCMC`, axioms [propext, Classical.choice, Quot.sound].
  Structure: §1 `commutant` (commutant of ι(𝒪) in End_ℂ(ℂ²) is ℂ), `S v` eigen-subring, `pure_zero_of_real`, `sqForm_neg`,
  `comm_span`; §2 `alg_core` (pure algebra: image 𝒪 ∩ S_(τ,1) ⇒ ℤ or Φ⁻¹(𝒪), k = S_(τ,1) with IsField.toField);
  §3 `com_embed` (h38 + h69 + qmLatticeAlgebra_of_free/qmLatticeFree_of/qmSkolemNoetherC_proof/qmClassNumberOne_proof,
  unif_ring_hom, lift_unique); §4 main theorem. No new leaves.
- 2026-11-15 ~02:00: A9. Consumer check (VERIFIED by `scratch/gt-qm/Reach.lean`, value-closure of
  `HDec.HSyn.sixContactMin_of_open20` over ZInQKernel constants, 73583 constants): `PkgI3.QMDichotomyYu`
  (from `yuThm11` via `qmDichotomyYu_of_yu`) is applied at exactly 4 live sites, all at (a,b) = (2,−3) with
  the embedding of a QM structure by 𝒪:
  `HDec.FS5NoCM.comIntOrQuadOrder_of` (TailC L1700, k = Qbar), `HDec.G0ModField.KernelField.endEqOFibre_of`
  (TailC L6827, k = Qbar), `HDec.G0FibreSimple.fibreSimple_of_pieces` (TailA L1158, k = Qbar),
  `HDec.LTGoodRed.QM.qmEndRank_of` (TailF L4038, k = AlgebraicClosure L', L' : IF finite over ℚ).
  26 live declarations carry the hypothesis type (list in docs/research/gt-qm.md).
- `YuThm11` as stated (all alg. closed k of char 0, all indefinite division (a,b), any embedding) is NOT
  proved: the inputs are analytic over ℂ and only reach fields embeddable in ℂ, and the lattice route is
  written for 𝒪 ⊂ (2,−3). Proved instead: `HDec.QMLattice.YuB6Alg` (def, the 4 consumers' form) and
  `yuB6Alg_of (hU) (hG) (hM) (hR : ZInQ.LeafPush2.T11b_Rigidity) : YuB6Alg` (compiles, VERIFIED), plus
  `yuB6Alg_of_yuThm11 : YuThm11 → YuB6Alg` (never stronger, VERIFIED).
- #discharges (VERIFIED, `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.QMLattice` OK, then `lake env lean scratch/gt-qm/Discharges.lean`):
  DISCHARGES [OpenAddedLeaves14.qmCentralizerCMC] by HDec.QMLattice.qmCentralizerCMC_of
    still assumes: [BPAnalytic.Uniformization.UniformizationLeafAll, ZInQ.HomLattice.GAGAMorphism, AvSplit.MumfordTorsionAlgClosed]
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 67 open hypotheses, 567 theorems checked, 1 discharge one
- 2026-11-15: refactor: `com_embed` now derived from `unif_conj` (no duplicated setup). Added `YuB6Emb`
  (fields with an embedding into ℂ) with `yuB6Emb_of`, `yuB6Emb_of'`, `yuB6Emb_of_yuThm11`; `yuB6Alg_of'`
  (T11b from the chain's `AVB2.t11b_of_exists HSyn.t11bExists_lf8`). Full rebuild + #discharges re-run (same
  output, 571 theorems checked), Axioms.lean: all 7 main theorems standard axioms; Reroute.lean: 4 rerouted
  consumers standard axioms (VERIFIED).
- Live `.t27` projections (Reach.lean, VERIFIED): gluePieces_of_open4, G0FibreSimple.fibreSimple_of_leaves,
  conversions textbookLeaves6_of_open7 (yuThm11 ↦ t27), textbookLeaves4_of_open6, textbookLeaves3_of_open4,
  textbookLeaves2_of_open3, textbookLeaves_of_open2.
- Report: docs/research/gt-qm.md.
