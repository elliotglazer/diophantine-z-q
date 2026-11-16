# Jones–Pall: exact squarefree 1-mod-8 supplier

This upstream contribution preserves the full statement:

```lean
∀ n : ℕ, Squarefree n → n % 8 = 1 →
  ∃ x y z : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 + 16 * z ^ 2
```

Export: `ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof`.
No Jones–Pall or Legendre caller premise, positivity addition, bounded input
range, desired-result instance, new axiom or weakened output is supplied.

## Exact source and missing assembly boundary

Primary source: `a9bc2e35c42a34a2be1cc3eeccb33cbc41de53c4`.
The fork's defining proposition is
`ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16` at
`Contrib/OneProof/TYZLemma29Mod2.lean:610–611`. This defining module and the
surrounding H29 assembly are not accepted on the current publication base
`4c13e0c3485e6333e4a441bca4bcf8a3dd3ac043`. The original focused proof checks
were executed at the preceding `fe026617ddd1f2275d7dd0190e5a3814a1c5d1b6`
source epoch; their provenance is retained below.

This supplier keeps the same public export name and writes the exact expanded
signature. The entry's proof body remains `jonesPall_representation`, and all
four primary helper files are byte-identical. The missing defining import is
replaced by the existing Mathlib tactic import. No H29 Prop, entire fork,
PR114 assembly or recognized headline provider is copied or silently admitted.

## One common Atlas dependency, not a second provider

The representation imports the existing canonical namespace
`ZInQ.Contrib.OneProof.LegendreThreeSquares.Atlas.Nat` from the module
`ZInQKernel.Contrib.OneProof.LegendreThreeSquares.Atlas`.
[Upstream draft PR131](https://github.com/elliotglazer/diophantine-z-q/pull/131)
at `5b0c71a10e12d6ae6f7dfdd542d91e8338ac4207` supplies that shared source.
It is an **unmerged dependency**, not a baseline acceptance.

This self-contained proposal carries only the exact three common payloads at
their canonical upstream paths: `LegendreThreeSquares/Atlas.lean`, the complete
license, and the historical notice. Their bytes are identical to PR131. The
Atlas theorem and namespace occur once in this source graph. The intended
source overlap is explicitly recorded, not misreported as zero global overlap.
There is no `JonesPall.Atlas` copy or second Ankeny implementation. The separate
Legendre entry theorem is not added by this PR. After authorized dependency
integration, identical paths can drop from the diff; that is not an instruction
to land, rewrite history, or change the other contributor's branch.

The Atlas source is pinned to
`facebookresearch/atlas-lean@8860f7b55276b96e51df600021845dd5eb48f5ab`,
`MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean`.
Removing only its primary namespace wrapper and notice recovers original
SHA-256 `a902763f2e8c6ca272f03774536d58b93c99f5843214288efe226f5e767da284`.
The canonical wrapped source SHA-256 is
`ca50ef1ad9cd9519c4fb440d53803810e9b6c9d8b8a9ca3bea75d74fbaed4797`.

## Load-bearing source-to-consumer map

1. If every prime factor of squarefree `n` is not 3 modulo 4, Mathlib's genuine
   two-square criterion yields the required representation with `z = 0`.
2. Otherwise choose an actual prime `p ∣ n` with `p % 4 = 3`, hence `p ≠ 2`.
   The common natural three-square theorem supplies integer coordinates after
   exact casting and equation reversal. The 1-mod-8 condition permits orientation
   with one odd and two even coordinates. Squarefreeness excludes all three
   coordinates being divisible by `p`.
3. For the resulting pure integral quaternion `v`, its norm equals `n` and
   `v * v = -n`. Balanced lifting produces a nonzero annihilator with norm
   `k*p`, `0 < k < p`. Minimality, left norm-two halving, and the odd Euler
   remainder descent construct a quaternion `q` of norm exactly `p` while
   preserving `q*v = 0 mod p`. Scalar coprimality, nonzero norms, exact divisibility
   and zero-remainder cases are proved inside the source, not assumed.
4. Exact integral division of `q*v*star(q)` by `p` gives a pure quaternion with
   norm `n`. The finite mod-4 lemma switches the oriented bad residue pattern;
   division by the odd prime preserves four-divisibility of its final coordinate.
5. That coordinate equals `4*z`; the norm identity gives the exact integer
   equality `n = x² + y² + 16*z²`. The target is unbounded; finite residue checks
   prove only the residue lemmas used by the general argument.

The source uses actual Mathlib integral Hamilton quaternions, conjugation,
coordinatewise division, norm and prime-factor APIs. It adapts the genuine
Lagrange/Euler method in `Mathlib.NumberTheory.SumFourSquares`, not an unproved
quaternion norm-prime or local-global assertion.

## Preserved notices and public evidence

`ThirdParty/JonesPall/Mathlib.LICENSE` and `NOTICE-fork.md` preserve the primary
license/notice bytes. The common Atlas full license, including its prefatory
line, and historical notice are preserved at
`ThirdParty/LegendreThreeSquares/{LICENSE,NOTICE-fork.md}`. Original source
copyright and attribution are retained; no new license grant is asserted.

Historical notices and Atlas adjacency comments describe their original fork
layout. This index supersedes only those location references: compiled source
is in Contrib, license/historical notices are in ThirdParty. Historical
receipt/defining-import sentences are not new upstream verification or a
forecast of the primary writer's cold registry/discharge run.

`TRANSFER.json` binds every original and adapted path/hash and identifies the
three exact shared dependency payloads. Public evidence uses portable/redacted
command descriptions, not private literal argv or restricted-access links.
Complete original runtime records remain private. Existing mathematical files,
statements, root imports, pins, audit code and protected contract are unchanged.

## Original proof epoch and current publication-base compatibility

The six-module compiler/type/axiom results and seven-module selected replay
below were actually run at upstream source epoch
`fe026617ddd1f2275d7dd0190e5a3814a1c5d1b6`. They are not claimed as fresh
execution, full CI, or approved reviewer/App acceptance at the newer base.

Before publication the unpublished candidate was fast-forwarded to
`4c13e0c3485e6333e4a441bca4bcf8a3dd3ac043`. Its 21-path base delta changes
only review-policy/configuration documents, the review workflow, and review
unit tests. An exact Git tree comparison found every one of the 948 baseline
Lean blobs unchanged, along with compiler/package pins, root imports, the
protected contract, source checker and kernel auditor. All six contribution
sources and their import graph, and the three shared PR131 payload blobs, also
match the reviewed old-epoch inputs. The old 14-file payload and raw receipts
remain preserved; only current documentation gained this compatibility addendum.

The current review policy was read rather than treated as interchangeable with
the old policy: editorial notes are distinct from substantive errors/gaps;
unfinished review scope and any administrative override stay explicit and do
not become a model acceptance or mathematical repair. Earlier obligations and
report-publication limitations remain recorded. No override is invoked here.
The current draft early-return and merge-readiness refusal still reject draft
PRs; successful ready reviews can still request merge or auto-merge. Therefore
this proposal remains draft, without a review command or landing permission.

`TRANSFER.json` and `VERIFICATION.json` bind this **same-source base check**
separately from the old proof execution. No compiler/type/axiom/replay rerun or
new-base full registry, CI or App pass is inferred from source identity. A full
workflow implementation audit is not claimed; the current policy documents and
the draft/readiness/direct-or-auto-merge/publication branches were inspected.

## Verification and remaining scope

Fresh isolated checks completed at the original source epoch against the
unchanged Lean 4.35.0
(`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

- All six source modules compiled afresh; zero borrowed project object files.
- Full independent literal hJP type, closed `@` export, integer witnesses and
  the `n = 1` example passed. Six actual axiom reports contain exactly
  `propext`, `Classical.choice`, and `Quot.sound`.
- The unchanged upstream auditor passed selected replay of seven modules
  (six source modules plus a separate independent literal type reference):
  190 serialized declarations, no skipped runtime declarations or duplicate
  names, standard-three opaque-body axiom closure and full literal type check.
- Seven source-contract tests and eighteen actual pinned-kernel adversarial
  tests passed. These do not replace full project CI or App review.

These are selected source-bound component checks, not full upstream registry/CI,
approved reviewer acceptance, primary H29 discharge, or full unconditional H10.
Old primary checks remain historical, not new upstream admission. This supplier
proves only the exact representation edge.

Portable reproduction instructions (not literal original private argv):

```sh
lake exe cache get
lake build +ZInQKernel.Contrib.OneProof.JonesPall
# Import the module in a scratch file and check the full literal type,
# closed @ export, and actual #print axioms outputs.
lake env lean JPTypeAxioms.lean
```

This is AI-assisted source reuse and delivery of the primary author's proof,
not a new ownership claim, human reading, or a printed-source flag clearance.

## Draft-only delivery

The upstream ready-review workflow can merge or enable auto-merge. This task has
no landing permission, so the PR remains draft. No ready flag,
`/protocol-b review`, auto-merge, main push, merge or human outreach is requested
or performed. The primary fork publication and PR131 remain untouched.
