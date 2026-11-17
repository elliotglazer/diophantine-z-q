# gt-valence: done. The valence formula for a cocompact Fuchsian group is proved, and the field `valenceFormulaCocompactEq` is discharged

**Verdict.** I proved the full statement `HDec.LeafQCheck.HM.QMSplit.ValenceFormulaCocompactEq` (TailZ2 L76),
not just the `Γ*` case, and with no hypotheses. The theorem is
`ValenceCocompact.valenceFormulaCocompactEq_proof` in `ZInQKernel/Contrib/OneProof/ValenceCocompact.lean`
(92 KB). The file imports only `ZInQKernel.OneProof.H.TailZ2`. The axioms are the standard three.

**Statement check.** The volume on `ℍ` is Mathlib's `GL₂(ℝ)`-invariant measure `dx dy/y²`. So `vol(s)` is the
hyperbolic area, and the statement is the genuine valence formula: it is not vacuous and not stronger than its
source. All consumers use it only for `Γ*`, but no reroute is needed because the general form is proved.

**Proof.** It uses no fundamental polygon and no boundary integral:
* an automorphic partition of unity `χ`, with `Σ_g χ(gz) = 1`;
* the Riesz identity `∫ log|F| Δχ = 2π Σ ord_ρ χ(ρ)`, from Green's identity, the regularized fundamental
  solution of `Δ`, and Mathlib's `extract_zeros_poles_log`;
* the conformal invariance of `y²Δ` under Möbius maps;
* finite-sum unfolding against the invariant measure, which gives `∫ log(|F| y^m) Δχ = 0`;
* `∫_ℍ χ dμ = vol(s)`, from Mathlib's `IsFundamentalDomain`;
* orbit-stabilizer counting.

**What compiles (VERIFIED).**
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ValenceCocompact`
  succeeds.
* `#discharges` reports that `ValenceCocompact.valenceFormulaCocompactEq_proof` discharges
  `OpenAddedLeaves14.valenceFormulaCocompactEq`. It still assumes nothing, and its axioms are
  `[propext, Classical.choice, Quot.sound]`. The run found 67 open hypotheses, 653 theorems checked, 1 discharge.

**What remains.** Nothing for this field. The fold should fill `valenceFormulaCocompactEq` with the theorem; it
adds no new leaves. The report is `docs/research/gt-valence.md`. The development modules are in
`scratch/gt-valence/VC/`, and the log is `scratch/gt-valence/log.md`.
