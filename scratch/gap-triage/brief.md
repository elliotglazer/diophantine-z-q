# Brief for gap-triage reading agents

Repository root: the task worktree (git worktree, branch wip/gap-triage, base e38375b3 = fork main w62).
Project: Lean 4.35 / Mathlib v4.35 formalization of "Z is Diophantine in Q". The single proof is
`ZInQ.OneProof.frozenTarget` (ZInQKernel/OneProof/Main.lean). Its hypotheses are four bundles of open statements
(fields) plus six top statements. The H chain is ZInQKernel/OneProof/H/ (LPrefix, TailA ... TailZ15); each newer
bundle (OpenResearchLeaves10 in TailZ15.lean, OpenTextbookLeaves10 in TailZ11.lean, OpenAddedLeaves9 in TailZ13.lean,
OpenGlue7 in TailX.lean) is converted to the previous generation's bundle by theorems like
`researchLeaves9_of_open10`, where fields are renamed or fed into reduction theorems. The kernel declarations they
eventually reach live in ZInQKernel/HDecomp/, ZInQKernel/Contrib/, and the OneProof/H Tail files themselves.

Field reports: docs/research/leaf-fold10.md section 2 (every field with form and source), docs/research/frontier.md
(row IDs H-nn, T-nn, Z-n), docs/research/h-decomposition.md section 2 (sources), docs/research/prereq-survey.md
(old library survey; predates vendored code). The next integration origin/wip/w63 (read with
`git show origin/wip/w63:PATH`; docs/research/leaf-fold11.md there) removed genusX1Field, igusaCMValue24,
neronLocalizesDVR, faltingsLemma5BC, semistableNeronBaseChange (the last three replaced by printed leaves) and
restated r1r2, shimuraFamily, gonzalezRotgerCountX6, deligneComponentsY3Printed on abelian schemes (`...Ab`, new
field mumfordRigidityCore).

Library locations: Mathlib sources .lake/packages/mathlib/Mathlib; vendored: ThirdParty/ (TauCeti, GreenTao),
ZInQKernel/Contrib/ (including CloudW01Spread (AxiomMath/Stacks parts), CloudW02Connectedness, CloudW03NeronSurj
(Anthropic FLT parts, Néron models over henselian DVR), CloudW06PoincareRigidity, CloudW07JacobiansCurves
(frenzymath Jacobian-Challenge; has AlgebraicGeometry.projectiveLine over a field), CloudW08EigenformTwists,
TauCeti, SpreadOut, SmoothFibre, Dim, ...), and lean/ (upstream helpers).

RULES for you: read-only. Do NOT run lean, lake, or any build; no network; do not edit any file except your own
output file named in your prompt (under scratch/gap-triage/). Use grep/search tools and file reads.

For EACH statement assigned to you, write a section with exactly these items:
1. Identity: field name; Lean constant (fully qualified) and the file + line where it is DEFINED (search for
   `def <Name>` / `structure <Name>` / `abbrev <Name>`); frontier r5 row ID; form (published form / consequence of
   one theorem / composite / project glue) as recorded in leaf-fold10 §2 (or frontier).
2. Use: trace the field through the OneProof/H chain: grep `\.<field>\b` and `<field> :=` in
   ZInQKernel/OneProof/H/*.lean, follow renames into older bundle generations, until you reach the theorem(s) that
   actually take the statement as a hypothesis and apply it. Name those consumer declarations (file:line). Then read
   the consumers and say whether the statement is used (a) in full generality, or (b) only at specific objects
   (the Shimura curves Y3 / X6, QM abelian surfaces of the construction, curves C_d, X0(32), particular primes,
   levels, discriminants, a fixed number field, ...). In case (b), write the WEAKEST statement that would serve those
   uses as a Lean signature sketch, which must be implied by the published statement (never stronger), and say
   whether it is a finite computation, a computation plus a published statement, or still deep.
3. Library coverage: what Mathlib / vendored code / Tau Ceti provides toward a proof. Name declarations with file
   paths. Mark each claim VERIFIED-READ only if you opened the file and saw the declaration's statement (quote the
   signature line); otherwise mark it SPECULATIVE. Theorem numbers from memory: UNVERIFIED.
4. Missing infrastructure: the definitions and theorems that would have to be built, in order.
5. Tier: T1 (provable now from what is in the tree; one agent task), T2 (needs one bounded new library piece; a few
   tasks), T3 (needs a major theory not in the tree, e.g. abelian schemes, Néron models, p-adic Hodge theory,
   Siegel modular forms; many tasks), T4 (research-scale; keep cited).
6. Strategy: prove directly / specialize and compute / reduce to smaller printed statements / keep as cited.
7. Notes: anything that makes it easier or harder (e.g. the statement is vacuous-risky, an existing partial proof
   on a branch: you may list branches with `git for-each-ref refs/remotes/origin` and read with `git show`).

Be concrete and terse. Quote Lean signatures you rely on. End your file with a short summary table:
field | consumers | use (a/b) | tier | strategy | best attack idea (one line).
