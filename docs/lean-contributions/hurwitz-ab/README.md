# Hurwitz A/B prerequisites: exact literal upstream suppliers

This focused contribution preserves the primary fork's two closed prerequisites
at source `84a9f2e6773e3c15873f2ac1b18ebdf5439e03f0`,
[fork draft PR39](https://github.com/Deicyde/diophantine-z-q/pull/39).
The fixed upstream source parent is
`581ab23c9e3c5b3af96086ff556a8d649c88a873`.
It does not supply hP23, hfx, an adelic `I(g)` construction, or H10.

## Literal output, not a replacement order predicate

The original defining module is
`ZInQKernel.Contrib.OneProof.TYZLemma29Mod2.lean`, lines 256–257 at fork base
`2880fef1e827a05ab9238cd200e555c585f00e30`:

```lean
IsHurwitz (q : ℍ[ℚ]) :=
  ∃ a b c d e : ℤ, q = ⟨a - e / 2, b + e / 2, c + e / 2, d + e / 2⟩
```

That defining module is absent from the current upstream source inventory.
The entry therefore spells out the **full literal five-integer conclusion**,
without copying H29 or defining a substitute `IsHurwitz` alias. The rational
Hamilton carrier, coefficient signs, exact equality, witnesses and strict norm
bound are retained. Both original entry proof bodies are unchanged;
`Coordinates.lean` is byte-identical. Only the unavailable defining import,
its namespace opening, output ascriptions and boundary prose are adapted.

The public names remain:

- `TYZSquareOddness.hurwitz_norm_approximation` (A)
- `TYZSquareOddness.hurwitz_of_integral_trace_norm` (B)

### A — actual rational approximation

For every `q : ℍ[ℚ]`, there is an actual `a : ℍ[ℚ]` satisfying BOTH:

```lean
(∃ r s t u e : ℤ, a =
  (⟨(r : ℚ) - (e : ℚ) / 2, (s : ℚ) + (e : ℚ) / 2,
    (t : ℚ) + (e : ℚ) / 2, (u : ℚ) + (e : ℚ) / 2⟩ : ℍ[ℚ])) ∧
Quaternion.normSq (q - a) < 1
```

The integer-rounding bound is weak (`≤ 1/2`). If any one coordinate error is
strict, one strict squared bound plus three weak bounds gives norm error `<1`.
If all four coordinate errors tie, each is reconstructed as an integer plus
`1/2`, including negative errors. Choosing `e=1` and shifting the real integer
coordinate by one makes the approximant exactly `q`; its error is zero. Thus
the proof does not incorrectly replace four weak inequalities by a strict one.

### B — the five original scalar integrality inputs

For every `q : ℍ[ℚ]`, the conclusion is the same literal five-integer equality
for `q`, from precisely these inputs:

```lean
(∃ a : ℤ, 2 * q.re = (a : ℚ))
(∃ b : ℤ, -2 * q.imI = (b : ℚ))
(∃ c : ℤ, -2 * q.imJ = (c : ℚ))
(∃ s : ℤ, -(q.re + q.imI + q.imJ + q.imK) = (s : ℚ))
(∃ n : ℤ, Quaternion.normSq q = (n : ℚ))
```

The first four integrality conditions are **unconjugated** `Trd(q*b)` values
for `b=1,i,j,zeta`, with `zeta=(-1+i+j+k)/2` and `Trd(x)=2*x.re`;
the fifth is Hamilton norm integrality. They are not `Trd(q*star b)` values.
If the first four integer values are `a,b,c,s`, the fourth double coordinate is
`2*q.imK = -2*s - a + b + c`. Those signs and the scalar normalization are
unchanged in the source.

The helper derives `a²+b²+c²+d²=4*n`. Its sixteen parity branches cover all
integer signs: fourteen mixed patterns are impossible modulo four, leaving
all-even or all-odd coordinates. The exact witnesses use `e=0` or `e=1`,
respectively, with the required negative real/positive imaginary half-shifts.
No maximality, ramification, principal-ideal, test-vector, positivity, hP23,
pre-existing membership or desired-result typeclass premise is added.

## Minimal source and import boundary

Only two Lean source files are included. The helper uses existing pinned
Mathlib Quaternion, rounding, integer parity and tactic modules; the adapted
entry imports it and existing Mathlib tactics. No external Lean package or
Lake dependency is added, and no proof code is vendored or new third-party
license grant asserted. Original source/proof history and attribution are
retained; no proof-body rewrite or ownership claim is made by this delivery.

The unchanged helper's introductory reference to transporting witnesses to
actual H29 describes its original fork use. In this upstream entry the output
is that definition's exact literal expansion. This index records the missing
source-level predicate/assembly boundary rather than pretending it is imported.
The defining source is a reference for type comparison, not a new contribution.

All right-lattice, basis, closure, denominator, fractional-principality and
local/global `I(g)` files are excluded. They remain the primary writer's
separate work and require their own gates. No `Un`, `InPiZ`, hP23/hfx, registry
or full H10 discharge follows from these two prerequisites alone.

## Verification provenance

The original primary checks are historical input evidence, not new upstream
acceptance. Current focused checks completed on a fresh isolated 32 GiB worker at the
fixed upstream source parent, with unchanged Lean 4.35.0
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`:

- Both source modules freshly compiled; zero borrowed project objects, exit 0.
- Independent full literal A/B statements, closed `@` exports and the actual
  rational Hamilton/integer-witness carriers passed. All four theorem axiom
  prints contain exactly `propext`, `Classical.choice` and `Quot.sound`.
- The unchanged upstream auditor passed two selected runs on the **same three
  modules** (the two sources plus a separate complete literal A/B reference).
  Each run replays **23 serialized declarations**, with zero runtime skips or
  duplicate bodies, standard-three axiom closure, and the exact complete A or B
  headline type. Counts are not added to misrepresent two copies as new proofs.
- Eighteen actual kernel negative controls and seven source-contract tests pass.

The two focused build logs contain zero warning lines. This narrow observation
does not relabel the original fork defining-module warning-bearing build as
warning-free, nor certify every imported library. Results and raw-output hashes
are recorded in `VERIFICATION.json` and the public-safe `AXIOMS.txt`.
Full imported-library kernel replay, full registry/hosted CI, designated-App
acceptance and human mathematical reading remain separate unclaimed grades.

`TRANSFER.json` records old/new hashes and the exact defining-source literal.
Original private argv, sources, logs and receipts remain preserved privately.
Public commands are portable/redacted reproduction labels, not literal private
argv, and contain no restricted-access links or runtime paths.

```sh
lake exe cache get
lake build +ZInQKernel.Contrib.OneProof.TYZSquareOddness
# In an unsubmitted scratch file: compare complete literal A/B types,
# use the closed @ exports, and print axioms of all four named theorems.
lake env lean ABTypeAxioms.lean
```

The fixed source snapshot is kept distinct from later API-base policy changes;
no old proof execution or review result is relabeled as a new CI/App pass.
The draft workflow's early return and merge-readiness refusal are checked
against the researched source parent. Success of a ready review can request
merge or auto-merge, so this delivery is **draft only**.

No ready transition, `/protocol-b review`, override, auto-merge, merge, main
push, human outreach, edit of another PR, or takeover of primary construction
work is authorized. AI-assisted source reading/delivery and focused checks do
not clear printed-source/human-reading flags or constitute H10 acceptance.
