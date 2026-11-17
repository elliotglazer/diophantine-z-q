# gt-shpair results log

Target: `ReductGlue.StrictHenselizationPair` (ZInQKernel/OneProof/H/TailZ14.lean L2055), GLUE composite.

## Plan (2026-11-14 23:00)
- Leaf: a strict-henselization form of BLR 1.2/2 (Néron models commute with O -> O^sh), stated for
  `IsSHUnram`-type extensions with `K₁/K` separable algebraic (pins O₁ ≅ O^sh in every characteristic);
  a specialization of the chain's existing `ReductGlue.NeronBaseChangeUnramifiedDVR` (checked in Lean).
- Glue (commutative algebra), to be proved in Lean in every characteristic and for imperfect residue
  fields: generalize sh-route's CA1-CA3 (char 0, perfect residue field).
  * key_finite: replace `card_inertia_eq_ramificationIdxIn` (needs separable residue fields) by
    |I|·|Aut(κP/κp)| = e·f and separable degrees: e(𝔮|p)·f(𝔮|p) = sepdeg(κ𝔮/κp) ≤ f(𝔮|p).
  * inertia field: separability of simple roots; normal closures of separable extensions.
  * E_{K'} ⊆ E_K(K'): p-power trick (x^q ∈ E_K(K'), x separable over E_K(K')).

## Results (2026-11-14 23:15)
- VERIFIED (compiled) `T1.lean`: `card_inertia_mul_card_gal` (|I_P|·|Aut(κP/κp)| = e·f, no separability),
  `eq_one_and_isSeparable_of_card`, `inertia_unram` (e(𝔮|p)=1 and κ(𝔮)/κ(p) separable for the inertia ring).
- VERIFIED `T2.lean`: `exists_sep_poly` (residue of a/s is a root of a polynomial with separable reduction).
- VERIFIED `GTCA1.lean` (Mathlib only): general `key_finite` (no PerfectField), parts (a) unit·ϖⁿ, (b) sep. poly.
- VERIFIED `GTCA2.lean` (imports TailZ14 + GTCA1): inertia field in any characteristic: henselian, sep-closed
  residue field, DVR, uniformizer irreducible.
- VERIFIED `GTCA3.lean`: `res_isSeparable`, `inertiaField_isSeparable`, `inertiaField_le`,
  `inertiaField_le_adjoin` (p-power argument).
- VERIFIED `GTFinal.lean`: leaf `NeronBaseChangeStrictHenselization`, `shPair` (no hypotheses),
  `strictHenselizationPair_of_neron`, `strictHenselizationPair_of_unramified`;
  `#print axioms` = [propext, Classical.choice, Quot.sound].
- VERIFIED `lake build +ZInQKernel.Contrib.OneProof.StrictHenselizationPair`: success (~30 s).
- Pitfalls: `Ω[X]` parses as Kähler notation under TailZ14 (use `Polynomial Ω`); worktree lacked
  `lean/.lake` (copied from ../gt-blr, identical lean/ZInQ); instance mismatch on `MulAction H (Ideal S)` for
  subgroup stabilizers: avoid rewriting `Nat.card (stabilizer H P)`, state counts via inertia only.
- VERIFIED `lake build +Main +Discharges +Contrib.OneProof.StrictHenselizationPair`: success (12926 jobs, ~10 min).
- VERIFIED `#discharges` (scratch/gt-shpair/Discharges.lean): strictHenselizationPair discharged by
  `strictHenselizationPair_of_neron` (still assumes `GapSHPair.NeronBaseChangeStrictHenselization`) and by
  `strictHenselizationPair_of_unramified` (still assumes `ReductGlue.NeronBaseChangeUnramifiedDVR`);
  axioms standard. "67 open hypotheses, 593 theorems checked, 2 discharge one".
