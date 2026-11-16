# Y3 tangent trace — minimal upstream prerequisite port

This contribution delivers the seven frozen tangent-trace helpers from
[fork draft PR40](https://github.com/Deicyde/diophantine-z-q/pull/40), source
`b7964a7a69534e736ef66dfe46e532a7b371f086`. It is **not** an R1 witness,
QMAbScheme projection, level/torsion result, global family or H10 proof.
The fixed researched upstream source parent is
`581ab23c9e3c5b3af96086ff556a8d649c88a873`; later API-base changes remain
separate dated context, not a reason to relabel this proof execution.

## Actual source and minimal defining cone

- **Seven frozen Y3 modules:** all mathematical bodies, signatures, namespaces,
  hypotheses and conclusions remain unchanged. Only three imports of the
  original QM defining module are redirected to the accepted
  `ZInQKernel.Contrib.HDecomp.QM.Structures` path.
- **Three canonical W03 defining dependencies admitted:** `PortUtil.lean`,
  `Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier.lean`, and
  `Def_AlgebraicGeometry_RelativeGroupLaw.lean`, at their exact existing fork
  paths and `ZInQ.Contrib.CloudW03NeronSurj.FLT` names. They are not yet upstream
  baseline files. All three bytes are preserved, not replaced by a trimmed or
  alternate definition/provider.
- **Three accepted upstream defining imports reused:** current QM Structures
  and ROOT A6 are byte-identical to the original sources; actual upstream ROOT
  Objects is rebuilt, not replaced by the fork copy. Its differences from the
  fork concern unconsumed QMDichotomy/Yu leaf packaging. No use or acceptance of
  that unrelated mathematical route is inferred.

The same actual `LeafQM.O` carrier, `B = QuaternionAlgebra ℚ 2 0 (-3)`,
`ofInt`, `oi`, `oj` and their ring relations are consumed. No second order,
W28 maximality/ramification proof, full W03 Neron closure, PR68/PR114 union,
TailZ16 or new open-R1 predicate is copied.

The exact source graph is therefore 13 modules: seven Y3 helpers, three W03
compatibility dependencies and three accepted baseline modules. The additional
literal contract/reference module used by audits is private check scratch,
not a contributed predicate or R1 target.

## Runtime compatibility boundary — not a hidden proof grade

The canonical **PortUtil is runtime elaborator/namespace infrastructure**.
It contains the original fork's renamed elaboration, alias and scoped-activation
helpers. Only `w03_open` is used by these two defining modules; it opens root
and prefixed namespaces and activates scopes. `w03_exact_reverting` elaborates
a term against the goal and checks metavariable completion, rather than changing
kernel trust. No introduced axiom or kernel bypass was found in this capsule.

The seven Y3 helpers introduce none of those commands, but that must not be
misstated as “no elaborator anywhere” across all ten added Lean files. Runtime
and generated declarations, and any unsafe/partial material skipped by the
unchanged auditor, are enumerated separately. Runtime behavior is **not** certified
by a Lean declaration replay or by the trace theorem. The auditor and its skip
controls are not modified. Historical deleted-diagnostic/no-reference claims
in the original W03 notice retain their original scope, not an all-world absence
claim for this proposal.

## Source-to-consumer mathematical route

Main export:
`ZInQ.Contrib.OneProof.Y3FineModuli.literal_order_charZero_tangent_trace`.
It retains the complete source-style affine `RelativeGroupLaw` and
`SchemeHomOver` hypotheses, not a fabricated tangent or Tate model.

1. **Actual tangent geometry:** `geomPoint`, `tangentBase`, `tangentZero`,
   `tangentScale` and `IsTangentVector` are actual scheme maps using
   `Spec(DualNumber k)` and restriction to the group identity. Literal guards
   pin all five definitions.
2. **Dimension is derived:** cotangent/dual-number lifts identify actual tangent
   points with the dual of the identity stalk's cotangent space. Smooth relative
   dimension provides the finite free differential rank. An injective,
   exhaustive, additive and scalar-compatible `τ` yields `finrank k V = n`.
   The generic dimension theorem retains only `Field k` and has no added
   algebraic-closedness, finite-V or desired-rank premise.
3. **Operators are constructed:** the actual scheme action, exhaustive range
   and injectivity construct a unital ring map `LeafQM.O →+* Module.End k V`.
   Addition, scalar compatibility, reversed scheme-composition multiplication
   and uniqueness `ρ m = Φ` are proved through the same `τ`, not assumed as a
   derivative bridge.
4. **Literal arithmetic trace:** cyclic trace and `oi²=2`, `oj²=-3`,
   `oj*oi=-(oi*oj)` force the generator traces to vanish. The exact twice-ofInt
   identity gives trace `2*n₀+n₂`, identified with integer reduced trace from
   `m+star(m)=n`. This new proof is not generic maximality or ramification.
5. **Composition:** the geometry theorem retains `Field`, `IsAlgClosed`,
   `CharZero`, finite V, all test-scheme action clauses, exhaustive `τ`,
   additive/scalar compatibility and the actual intertwined operator `Φ`.
   `finrank=2` is derived inside this composition, not supplied to it. The final
   trace theorem uses its retained `[Module.Finite k V]` binder directly; it does
   **not** claim to derive that input finiteness. The generic dimension theorem
   remains stronger and needs no finite-V premise. The rank premise belongs only
   to the separate linear-representation lemma.

## Preserved source/license/notice dictionary

Public source is
`anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2`.
The complete original LICENSE, NOTICE and ATTRIBUTION are preserved byte-for-byte
at `ThirdParty/Y3FineModuli/`; their exact bytes also cover the canonical W03
source capsule. No new license grant or independent authorship is asserted.

`ThirdParty/Y3FineModuli/NOTICE-fork.md` is the **updated final** Y3 notice,
SHA-256 `ae277d3736aca81ce260eda2a8f39e30a97a97b56acab09ea97cdf169e8d032d`,
not the obsolete initial-packet notice. It records the elaboration-only
`backward.isDefEq.respectTransparency.types=false` option; kernel checking is
unchanged. `W03-NOTICE-fork.md` preserves the original W03 source/change history.
Only its three defining files are selected here, not its Basic/Main/Audit or
complete Neron proof claim.

`SOURCE_MAP-fork.md` and `VERIFICATION-fork.md` preserve the final original fork
source map and verification text. Their fork layout and original-source/run
claims remain historical. The compiled sources stay under Contrib; all license,
notice and current documentation files are outside Contrib under the actual
upstream source-checker rule. This index supersedes only old path locators and
identifies baseline reuse versus new intake. `TRANSFER.json` binds every path,
source hash and adaptation. No original proof history is rewritten or scrubbed.

## Prior findings and unresolved scope

Original non-author source review and its supplement remain preserved:
L1–L3 were resolved by the final notice/command provenance and five definition
guards; M1, M2 and L4 stay explicit:

- **M1:** no target `QMAbScheme`/GrpObj-to-RelativeGroupLaw or affine localization
  bridge is supplied. This is not a QMAbScheme or R1 projection.
- **M2:** this is a helper/prerequisite draft, not an exact open-field discharge;
  `#discharges` is not claimed successfully run.
- **L4:** lint warnings are preserved and scoped, not silently called warning-free.

Not supplied: the primary writer's new affine object-action primitive; full-81
geometric torsion/generation/annihilator transport; moduli curve, Qbar point,
all-characteristic-zero-field PtEquiv; global universal family/classification/
gluing; full R1/H10, registry or designated-App acceptance. Original review
verdicts do not replace current source/type/receipt checking.

## Verification and public/private limits

Fresh upstream checks completed at this fixed source parent with unchanged
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:

- All **13 actual source modules** were rebuilt from source into a fresh output;
  seven frozen Y3 helpers, three newly admitted exact W03 dependencies and three
  existing accepted defining imports. Zero old project objects were reused.
- Complete closed source-style order/geometry/dimension contracts and all five
  tangent-definition guards passed. **Nine actual AX prints across two checks**
  (five distinct principal exports, not nine independent proofs) contain exactly
  `propext`, `Classical.choice` and `Quot.sound`.
- The unchanged upstream auditor considered **14 modules / 934 serialized
  declarations**, including a separate private literal reference. The actual
  skip report has **one generated executable** NOT replayed:
  `ZInQ.Contrib.OneProof.Y3FineModuli.Source.CerednikDrinfeld.QM.nsmulPt._unsafe_rec`.
  The safe mathematical `nsmulPt` definition is distinct from that executable
  helper. The mathematical replay, standard-three opaque-body axiom closure and
  exact full source-style geometry type passed; no zero-skip claim is made.
- A separate raw metadata inventory lists **all 23 PortUtil declarations**, with
  their generated names, types and safety flags. Those namespace/elaborator
  definitions have declaration checks, not certified executable behavior.
  The inventory's unsafe/partial set exactly matches the auditor's skip set;
  no auditor or skip control was changed to obtain these results.
- Eighteen actual pinned-kernel negative controls and seven current fixed-parent
  source-contract tests passed. The candidate checker records 945 locks and 954
  modules with acceptance false; this is not hosted CI or App acceptance.

The scoped builds contain **38 positioned warning diagnostics**, including 22
in the seven Y3 helpers. The earlier 39-line substring count also matched one
Objects-log explanatory hint saying “silence this warning:”; that hint is not a
second diagnostic. Original logs and the earlier count are retained with an
explicit metadata-only counting correction, without changing proof bytes or
verification outcomes. No warning-free build or imported-library whole-world
replay is claimed. The full runtime inventory, skips, source/check/output hashes
and scoped count correction are in `VERIFICATION.json`, with raw records private.
Full registry/CI, approved App review, human mathematical reading and
source/provider serving-model identity are not inferred from a requested
configuration or a component check.

Only retained public source-key/hash/comment-matched standard Mathlib inputs are
used. This is not an independently signed master-origin certificate, a full
Mathlib source rebuild or private/project/C7/A4 cache admission. Original paths,
argv, complete logs and private source review packets remain private; public
command labels are portable/redacted templates, not literal private argv.

```sh
lake exe cache get
lake build +ZInQKernel.Contrib.OneProof.Y3FineModuli
# In separate scratch, compare the complete literal geometry/order/dimension
# contracts and all five tangent definitions; print the actual export axioms.
lake env lean CheckFrozenGeometryContracts.lean
```

The public branch name is neutral mathematical/date-based. Private runner IDs
stay in private receipts, not public branch metadata. Current policy notes,
substantive gaps, incomplete review and admin decisions keep separate records.
No override, ready/PB request, auto-merge, merge, main push, human outreach or
edit of another actor's work is authorized. Publication is **draft only** after
independent scoped review and the parent final source/receipt gate.
