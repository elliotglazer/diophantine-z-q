# Accepted Lean helper snapshot

This directory contains the 48 modules accepted in integration 31. The Lean source files, root imports, dependency metadata, and frozen target are copied byte for byte from that snapshot. `SOURCE_MANIFEST.json` records their hashes and the source integration manifest hash. Historical filenames containing `Draft` are retained to preserve imports; those helper modules belong to the accepted snapshot.

**This is not a formal proof of the 11/5 manuscript's main theorem.** The snapshot contains 463 explicit public declarations and 69 private declarations, including definitions and helper results. The whole-model, height, restricted-converse, pole-completeness, multiplication, compiler, construction/bounds, and final composition obligations are not closed by this snapshot.

`Frozen/BoundedIntegerPolynomial.lean` is the exact approved, unproved target for the original polynomial in 292,890,231,905 total variables and contains one `sorry`. It is not a formal statement of the Version 4 quartic in 4,973 variables. No quartic-specific frozen target or completed quartic proof is included in this snapshot. It is excluded from `ZInQ.lean`, the default library, and the axiom audit. Its hash is checked so that the intended statement cannot silently change.

## Source provenance

The dated research archive contains the original paths under `formalization/z-in-q/` and the source record `outputs/z-in-q-integration-31.json`. The [research guide](../docs/research-guide.md) explains how to find those files. A few source comments refer to relative paths inside that archive. They are provenance references, not build dependencies.

The source integration manifest SHA-256 is:

```text
0e6ea11e782b845c7d316e2c5c01427583e85511ff15146c489c540e4ce9f45b
```

Upstream Mathlib and its dependencies are not vendored here. Their URLs and commit revisions are recorded in `lake-manifest.json`; their own licenses continue to apply. The alpha-sequence modules cite the Archive of Formal Proofs' `DPRM_Theorem` development where its mathematical arguments were used.

## Check source identity

From the repository root, with Python 3.9 or later:

```sh
python scripts/check_lean.py
```

This checks every listed source hash, the 48-module import closure, the absence of proof holes and custom axioms in the accepted modules, and the quarantine of the one frozen target. It does not run Lean or establish mathematical correctness.

## Rebuild and audit

Install Lean's `elan` toolchain manager and make `lean` and `lake` available on `PATH`. The checked-in `lean-toolchain` requests Lean 4.35.0. From the repository root:

```sh
cd lean
lake exe cache get
python ../scripts/check_lean.py --build
```

The first command resolves the pinned Lake dependencies and fetches their published compiled cache. The Python command verifies each dependency checkout revision and its tracked-source cleanliness. It then compiles all 48 project modules and the root into a new `.checks/` subdirectory, using only those new project artifacts and the pinned dependency libraries. It never imports an old project build directory.

Every compiler invocation includes `-Ddebug.skipKernelTC=false`. The last invocation checks `Checks/Axioms.lean`, which inspects imported declarations originating in the 48 project modules and rejects dependencies on any axiom outside `propext`, `Quot.sound`, and `Classical.choice`. The declaration count includes compiler-generated declarations and therefore need not equal the explicit-source count.

The output directory contains a log for every module, `axioms.log`, `commands.json`, and, only after success, `RESULT.json`. A failure stops the check. Do not report the main theorem as proved when these helper checks pass.

For an existing read-only cache of the same pinned dependencies, `--dependencies PATH` selects its packages directory. `--lean PATH` selects the compiler executable. `--output PATH` chooses the fresh project-output directory and refuses an existing directory. These options do not alter the source or dependency pins.

The default is two concurrent single-threaded compilers. `--jobs 1` through `--jobs 4` changes the concurrency without changing the checked targets. Git newline conversion is disabled within this directory to preserve the source hashes across platforms.

## Validation scope

The release preparation checks are recorded in the [validation report](VALIDATION.json) and the [704-declaration axiom ledger](AXIOMS.json). They distinguish a fresh build of the project modules from a rebuild of upstream dependencies. Published dependency caches are trusted inputs; this procedure does not independently rebuild Lean or Mathlib, and an axiom audit does not replace review of a theorem's statement or its relation to the 11/5 manuscript.

## Optional compact-group recurrence examples

[Examples/CompactRecurrence.lean](Examples/CompactRecurrence.lean) gives anonymous
applications of an existing Mathlib result to a product of two compact topological
groups. **Draft: kernel compilation and axiom validation are pending.** These
examples are outside the accepted 48-module snapshot and the default `ZInQ` root.
With the pinned dependencies already prepared, run from `lean/`:

```sh
lake env lean -Ddebug.skipKernelTC=false -DwarningAsError=true Examples/CompactRecurrence.lean
```

The additive contract is: for any `x : A`, `y : B`, neighborhoods `U` of zero
and `V` of zero, and bound `N : ℕ`, obtain **one** `a : ℕ` with
`N < a`, `0 < a`, `a • x ∈ U`, and `a • y ∈ V`. The multiplicative example
has the corresponding powers and identity neighborhoods. Both apply recurrence
to `(x, y)` in the product, use `prod_mem_nhds` for `U ×ˢ V`, and extract a
witness above `N` using `Filter.frequently_atTop` at `N + 1`. Separate return
indices for the factors would not establish this contract. The output is
arbitrarily late simultaneous returns; it asserts no convergence of all iterates
and requires no infinite-order assumption. Torsion and identity elements are in
scope, and no Hausdorff or commutativity assumption is added.

The supplier is
[`mapClusterPt_one_atTop_pow`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/Algebra/Group/SubmonoidClosure.lean#L53-L56),
whose `to_additive` counterpart is `mapClusterPt_zero_atTop_nsmul`, at the
Mathlib commit pinned in `lake-manifest.json`, with Lean 4.35.0. Its exact
conclusion is `MapClusterPt 1 atTop (x ^ · : ℕ → G)` (additively, zero and
natural multiples). `mapClusterPt_iff_frequently` in `Mathlib.Topology.ClusterPt`
and the product-neighborhood and filter results unpack this conclusion.
The examples print the axiom closures of these suppliers and the order lemmas;
only `propext`, `Quot.sound`, and `Classical.choice` are permitted. They import
only `Mathlib.Topology.Algebra.Group.SubmonoidClosure`, with no `CondZQ` import.
Mathlib's source credits Yury Kudryashov and is Apache 2.0 licensed; its proof
is called, not copied. Its upstream notices and license continue to apply.

### Conditional connection to HypCC

The intended consumer is
[`CondZQ.HypCC` in PR #6 at `7663a196`](https://github.com/elliotglazer/diophantine-z-q/blob/7663a19635390053716f02bfcbd16b97c42bd26a/lean/CondZQ/Hypotheses.lean#L109-L114),
which refers to `eq:close-complete`, TeX 6109–6127 of
[`audited-baseline.tex`](../docs/theorem-application-audit/source/audited-baseline.tex).
This is a comparison with that fixed, unmerged source, not a build dependency.
Its target is `∀ n κ : ℤ, n ∉ Cset → κ ≠ 0 → ∃ a l j : ℤ, accept n κ a l j`.
For each already fixed **signed** `n` and nonzero **signed** `κ`, the required
conditions, from PR #6's `CondZQ.Model.accept`, are

```text
1 ≤ a,  1 ≤ l,  j = n*a,
|rval a j - n| < eps l,
4 * eps l < ((4 : ℚ) ^ Bval n κ)⁻¹.
```

The following interfaces remain unproved by these examples:

1. The actual compact topological additive groups of real points of the two
   base changes of `E/K0` under `σ₊, σ₋ : ℚ(√2) → ℝ`, including the identity.
   These are the two factors abbreviated as `E(ℝ) × E(ℝ)` in the manuscript.
2. One homomorphism `Φ : E(K0) →+ E_{σ₊}(ℝ) × E_{σ₋}(ℝ)` with
   `Φ(m • P0) = m • Φ(P0)` for signed integers `m`. Both coordinates must
   arise from this same `K0` point and index; two unrelated real orbits do not
   identify `CondZQ.zcoord`, `eps`, or `rval`.
3. Compatibility and continuity of the local parameter `z = -x/y`, extended
   at the identity, with these embeddings; the needed nonzero denominators
   along admissible positive multiples; and strictly positive `eps l` that
   become arbitrarily small along simultaneous returns. The abstract
   recurrence also permits torsion, so it supplies none of this nonvanishing.
4. For each permitted signed `n`, a punctured local limit derived from the
   derivative of `[n]` at the identity, compatible with the rational-part
   quotient defining `rval`: `rval a (n*a) → n` along those returns. This
   needs an actual local-coordinate argument, not just the recurrence result.
5. Transfer of the real estimates to the exact strict rational inequalities
   in `accept`, with its particular `eps`, `rval`, and `Bval` definitions.

Conditionally on these interfaces, a sufficient witness order is to fix
`n ∉ Cset` and `κ ≠ 0`, then choose a positive `l` with
`0 < eps l` and `4 * eps l < ((4 : ℚ) ^ Bval n κ)⁻¹`. For that fixed
positive tolerance, the ratio limit supplies a product neighborhood (and any
needed lower bound) in which the first strict inequality holds. Apply the
additive example to `Φ(P0)` to choose a common positive `a`, and put `j = n*a`.
Cast the positive natural witnesses to integers; `j` can be negative.
This order keeps the tolerance and both coordinates tied to the same actual
orbit. It supplies a conditional use of the abstract contract, without an
elliptic instance, a proof of HypCC, or a proof of the main theorem.

This is an optional example and supplier-to-consumer note, not a research
release or a change to any manuscript application. Manuscripts, PDFs, release
manifests, archived evidence, accepted helper hashes, and the quarantined target
are outside its scope. Local checks do not constitute independent acceptance;
that review remains required before acceptance of this contribution. The
examples and this mapping are AI-assisted work by Codex and carry no claim of
new mathematics, a geometric identification, or a solved open problem.
