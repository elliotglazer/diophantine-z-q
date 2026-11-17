# gt-elkies (2026-11-14)

**Result.** `elkiesEquationsX6Ab` is discharged. It now follows from one published leaf, `ElkiesX6StarPrinted`,
and the moduli step is proved in Lean.
* **The leaf** is Elkies 1998 §3 on the canonical witness: `t` is a coordinate on `X*(6) = X₆/W`, in its ℚ̄-point
  form (the fibres of `t` are the orbits of `W = {1, w₂, w₃, w₆}`). It also carries the CM values `t = 0, 1, ∞`
  at discriminants −24, −4, −3 and the charts `s² = −t`, `r² = 3(t − 1)` (the existing `X6Glue.ElkiesCharts`).
* **`W` is a definition** (`IsAtkinLehner`, `atkinLehnerW`), not a hypothesis. It is given by the moduli action
  of `w_m`: `[(A, ι)] ↦ [(A, ι ∘ Ad μ_m)]`, with `μ_m = 1, i, j, ij` (the chain's `tt`/`rep`). This is the
  standard description for D = 6, where `I_m = μ_m𝒪` is principal.
* **The moduli step `orbit_iff_twist` is proved.** Two points are in one `W`-orbit iff their QM pairs are
  isomorphic up to a twist by some `α ∈ Aut 𝒪`. It uses only `X6Props` and the chain's proved `rep_cover`
  (Skolem–Noether plus the normalizer descent) and `innerIso`. No published input and no rigidity are needed.
* **The new leaf is equivalent to the field** (`elkiesX6StarPrinted_iff`), so it is not stronger.

**Compiles (VERIFIED).**
* `ZInQKernel/Contrib/OneProof/ElkiesX6Star.lean` imports only `TailZ22`. Every theorem uses only the standard
  axioms.
* `#discharges` output (`scratch/gt-elkies/discharges.txt`):
  `DISCHARGES [OpenResearchLeaves16.elkiesEquationsX6Ab] by …ElkiesX6Star.elkiesEquationsX6Ab_of_printed`,
  `still assumes: [HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted]`, axioms standard.
* The autofold dry-run (`scratch/gt-elkies/autofold-spec.json`) gives strict 47/14 → 48/13 on 61: one GLUE
  field fewer. The generated module `FoldDryRun.lean` compiles.

**What remains.**
* Elkies' section number, display, and `0/∞` orientation are still UNVERIFIED (no network). Residue fields and
  local points cannot tell `0` from `∞`.
* Taking the ideal-quotient definition of `w_m` instead of the twist form would need quotient abelian
  varieties, which the chain does not have.
* After the fold, gt-x6facts' theorem takes `elkiesEquationsX6Ab_of_printed`.

Report: docs/research/gt-elkies.md.
