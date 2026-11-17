# gt-grcount (fleet summary)

**Verdict: reduced, not proved outright.** `ShimuraSplit.GonzalezRotgerCountX6Ab` (TailZ17 L31) is proved in Lean
from one new published-form leaf plus an open LEAF already in the bundle. That removes its composite flag
(strictest count 45/16 → 46/15 by `autofold.py --dry-run`; lenient 47/14 unchanged).
- New leaf `GRCountX6.GonzalezRotgerProp56X6`: González–Rotger 2006 Prop. 5.6 at (6,1), stated for *every* witness of
  the moduli description of X0(6,1), with no existence claim. It follows outright from the kernel's `R5fpCount` and is
  equivalent to it given a witness.
- The model comes from `HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (open LEAF, GR Thm 5.12); `DeligneComponentsX6PrintedAb`
  also works.
- Finding: the chain uses the field only through `R5fpCount` (TailZ9 `r5count`), and the count sees the witness only
  through Ψ.
- **Not a finite computation.** The count ranges over all imaginary quadratic orders, with h(R) unbounded, and
  counts iso classes of QM surfaces. The only arithmetic is the local factor 2^{inertCount6} = ∏_{p|6}(1−(k/p)),
  proved (`eichlerFactor6_eq`).
- Further split (compiled glue): `R5fpCount ⇐ EichlerOptEmbCount6` (LEAF, pure quaternion-order algebra over
  ℍ[ℚ,2,0,−3] and LeafQM.O) `∧ CMPointsOptEmb6` (consequence of Shimura's CM correspondence). This does not lower
  the strict count further.

**Compiles:** `ZInQKernel/Contrib/OneProof/GRCountX6.lean` (0 errors, standard axioms). The lake build of
Main + Discharges + GRCountX6 succeeds. `#discharges`: 4 theorems discharge `gonzalezRotgerCountX6Ab`
(scratch/gt-grcount/discharges_output.txt). The fold spec is scratch/gt-grcount/autofold-spec.json; the generated
fold module scratch/gt-grcount/FoldCheck.lean compiles.

**Remains:** the leaf `GonzalezRotgerProp56X6` (or Eichler plus the correspondence). Theorem numbers for Eichler,
Vignéras, Voight, Jordan and Shimura are UNVERIFIED (no network). The leaves have no non-vacuity witness yet.
Report: docs/research/gt-grcount.md.
