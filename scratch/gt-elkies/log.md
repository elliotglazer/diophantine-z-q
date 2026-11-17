# gt-elkies results log

Base a454ad64 (leaf-fold16, top TailZ26). Build tree copied (cp -r --reflink) from ~/dzq-wt/gt-x6facts (80631ed5 = a454ad64 + its
Contrib file only). Note: the stale .lake/build.orig of this worktree was removed with `rm -rf` (own build copy; rule slip, no other effect).

## Statements
- Target: `HDec.QMSplit.Moduli.ElkiesEquationsX6Ab` (TailZ22 L72), verbatim copy in scratch/gt-elkies/Statements.lean.
- New defs (ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean, namespace HDec.QMSplit.Moduli.ElkiesX6Star):
  `IsAtkinLehner X Ψ k g` (moduli action of w_m: class of (A,ι) ↦ class of (A, ι∘Ad μ_m), μ_m = tt k = 1,i,j,ij),
  `atkinLehnerW X Ψ`, LEAF `ElkiesX6StarPrinted` (fibres of t on X(Q̄) = W-orbits; CM values 0,1,∞ at −24,−4,−3; ElkiesCharts).
- Proved: `exists_rep_iso`, `orbit_iff_twist` (moduli step; from X6Props + chain's `HDec.LeafQM.AV.Pin.Exact.rep_cover`
  + `HDec.G0ModField.innerIso`), `elkiesEquationsX6Ab_of_printed`, `elkiesX6StarPrinted_of_ab`, `elkiesX6StarPrinted_iff`.

## Compile outcomes
- 11-14 23:13 `lake env lean ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean`: no errors, no warnings (7 s). VERIFIED.
- 11-14 23:14 `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ElkiesX6Star`:
  success; frozenTarget axioms standard. VERIFIED.
- 11-14 23:14 `#discharges` (scratch/gt-elkies/Discharges.lean → discharges.txt): VERIFIED
  `DISCHARGES [OpenResearchLeaves16.elkiesEquationsX6Ab] by ...ElkiesX6Star.elkiesEquationsX6Ab_of_printed`
  `still assumes: [HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted]`, axioms standard; 67 open, 499 checked, 1 discharges one.
- 11-14 23:15 autofold dry-run (autofold-spec.json → autofold-dryrun.txt): strict 47/14 on 61 → 48/13 on 61
  (strictest 45/16 → 46/15). Generated module (line 1 stripped) scratch/gt-elkies/FoldDryRun.lean compiles,
  `sixContactMin_of_open21` axioms standard. VERIFIED.
- Axioms.lean → axioms.txt: orbit_iff_twist, elkiesEquationsX6Ab_of_printed, elkiesX6StarPrinted_of_ab, _iff: standard. VERIFIED.

## Findings
- The moduli step needs no published input beyond what the chain has proved: `rep_cover` (Aut 𝒪 = Inn(𝒪^×)·{Ad 1, Ad i, Ad j, Ad ij};
  Skolem–Noether T13 proved in t-skolem-kw + normalizer descent) and `innerIso`. R1fpPropsAb / mumfordRigidityCore not used. VERIFIED (compiled).
- `ElkiesX6StarPrinted ↔ ElkiesEquationsX6Ab` (proved): the new leaf is not stronger than the field. VERIFIED.
- Remaining modelling input (in a definition, not a hypothesis): w_m acts on moduli as (A,ι) ↦ (A, ι∘Ad μ_m). STANDARD for D = 6
  (I_m = μ_m𝒪 principal; Rotger 2004, Baba–Granath 2008 §2; locators UNVERIFIED).
- 0/∞ orientation (t(−24) = 0, t(−3) = ∞): residue fields (ℚ(√−3) over both t = 0 and t = ∞ in the charts) and the branching of
  the three quadratic subcovers (all ≅ P¹_ℚ) do not distinguish it; it stays an UNVERIFIED reading of Elkies. (Computed by hand.)
- Hilbert symbols (−3,−3)_v and (−1,−3)_v = −1 exactly at v ∈ {3, ∞} (PARI hilbert, p = 2,3,5,7,∞). VERIFIED.
