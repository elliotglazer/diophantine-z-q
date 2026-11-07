# Version 6 refinement: 933 variables with explicit integer coefficients

Status: additive arithmetic proposal; exact algebraic replay passed; independent mathematical review pending.

This package builds on upstream Version 6 at commit `f87226569fa7ceeae0c783c3e4d1241ac727733a`. It preserves the released package and the earlier 1,267- and 1,180-variable experiments. All counts include the input coordinate.

| Construction | Variables | Quadratic residuals | Monomials | Coefficient format |
|---|---:|---:|---:|---|
| Upstream Version 6 | 962 | 919 | 55,409 | Symbolic fixed integer S=3^(2^27) |
| Version 6 with our smaller explicit anchor chain | 979 | 936 | 55,459 | Ordinary integer strings |
| Add doubled comparison targets | 955 | 912 | 54,379 | Ordinary integer strings |
| Remove the redundant delta inverse | 946 | 903 | 54,461 | Ordinary integer strings |
| Lower only beta precision to 12 (not selected) | 951 | 908 | 54,382 | Ordinary integer strings |
| **Use precisions 12/40 and quotient weights** | **933** | **890** | **51,907** | **Ordinary integer strings** |

Every ordinary-coefficient variant in the table has maximum coefficient bit length 3,247. The selected quartic has primitive content one. Its complete ordinary polynomial has SHA-256 `5dade132700c872ea5fbfb60913e1dd82b2f6d39cb86a0db37d3b1de71303c7a`.

The new result saves 247 variables relative to our 1,180-variable construction. Most of that improvement comes from adopting Version 6's point chart, shared polynomial circuits, scaled pole witnesses and finite-correction chain. Those changes belong to the upstream authors; this package composes them with our arithmetic refinements and the new quotient-weight circuit below. No minimality claim is made.

## Current upstream and next candidate

Upstream Version 8 at `5856286a57fba19574a40704571ee70e79738281` is integrated.
Its Version 7 Gaussian repairs apply to the completeness dependency; the finite
circuit is unchanged. Historical source hashes are preserved at their relocated
paths. The separate [909-variable direct-target candidate](../overnight-20261106/DIRECT_TARGETS.md)
has passed algebraic replay but is not substituted for this frozen package.
See the [intuitive proof architecture](../overnight-20261106/INTUITIVE_PROOF.md)
and [continuation record](../overnight-20261106/CONTINUATION.md).

## What is inherited, and what changes

`INPUTS.json` pins the actual builder, compiler, checker, manuscript and proof dependencies. Version 6's `quartics/quartic-962/PROOF.md` supplies projection-preserving witness maps from its optimized source to Version 5. These maps preserve the named points and detector quantities needed here.

Our exponent-19 height argument and explicit anchor specialization are in [ARITHMETIC.md](../combined-comparison/ARITHMETIC.md). The doubled-target and removed-inverse arguments are in [REFINEMENTS.md](../combined-comparison/REFINEMENTS.md). The adaptations to the new source are explained below. The 1,267- and 1,180-variable artifacts remain historical, with their original input hashes.

The current arithmetic dependency is Version 6's simultaneous-prime construction and its in-manuscript Gaussian ray-field estimate. Frei–Tinková is methodological provenance, not an assumed theorem in Version 6. The older frozen package prose still describes the earlier dependency boundary; that historical wording is not the dependency claim of this proposal. Version 6's remaining source-version qualifications and incomplete Lean status are retained. This work does not independently referee the entire upstream arithmetic argument.

## Detector domains in the Version 6 coordinates

In each detector let A be its scale, delta=A lambda−1, F its quintic contact product, and e its weight. Version 6 retains the inverse of w0 and defines

    N=(w0²−2w1²)/(2w0).

Consequently N is nonzero over Q. Replace the delta inverse, its square, and the previous B computation by

    d2=delta², d3=d2 delta, d3 q1=e,
    E=e delta, B E=N².

The final equation forces E, B, e and delta nonzero. Version 6's unchanged point chart forces its abscissae positive at both real embeddings, so all scales A are positive. Its weight equation

    F e=(A delta)^5

therefore forces F nonzero as well. Thus q1=e/delta³ and B=N²/(e delta), exactly as before. Conversely an old solution determines every new coordinate uniquely. Recover the old delta inverse and Rnorm=N/(e delta); the original B=N Rnorm follows. These maps prove projection equivalence without assuming the main integrality conclusion. In particular, the domain proof is not circular even though the equation forcing nonvanishing occurs later in the displayed program.

The scaled pole witnesses of Version 6 are unchanged. Their denominator 17B remains nonzero by the preceding argument. Our earlier pole fusion is not applied a second time.

## A shorter quotient circuit for the precision weights

At precisions 12 and 40 the required weights are q12=q1 e^22 and q40=q1 e^78. Compute the seven powers

    e², e⁴, e⁸, e¹⁶, e²⁴=e¹⁶e⁸,
    e⁴⁰=e²⁴e¹⁶, e⁸⁰=(e⁴⁰)².

Then impose the two quadratic quotient equations

    e² q12=q1 e²⁴,
    e² q40=q1 e⁸⁰.

Since e is nonzero by the detector-domain argument, both equations have unique solutions with precisely the desired values. This uses nine coordinates for powers and weights, one fewer per detector than the Version 6 16/52 circuit. The saving is nine coordinates across nine detectors. It does not change either detector predicate or require a new nonvanishing assumption.

## Logarithms and the arithmetic precision change

The beta logarithm is the original G2 polynomial, evaluated directly as a quadratic in w. This removes one field assignment at each of U1 and V1, saving four rational coordinates. For the other eight logarithms write the original G9 polynomial as

    G9(w)=A0(w)+w³(A1(w)+w³(A2(w)+a9 w³)),
    Aj(w)=a_(3j)+a_(3j+1)w+a_(3j+2)w².

Compute w², w³, the inner block A1+w³(A2+a9 w³), and the final block. Every assignment is quadratic in available coordinates. This uses the same number of field assignments as Version 6's degree-twelve square-completion circuit. `verify_identities.py` independently expands the actual emitted logarithm gates over Q[f0,f1] and checks their equality with the coefficient recurrence for G2 and G9.

The exponent-19 proof in the linked `ARITHMETIC.md` provides exactly the local errors 12/40, global nonvanishing, height transfer, and both final contradictions. It applies unchanged to the named points preserved by Version 6's point chart. The degree-nine block circuit only changes evaluation of the same polynomial. The order-32 scalar construction remains unchanged. The experiment reducing only the beta precision has a more expensive joint power chain and is explicitly not selected.

## Doubled targets and the common index

Use Qi=ni P*, H=hP*, Ui=ui P*, with targets 2P*,2Qi. The two full logarithm ratios are ui/h and (ui−2ni)/(h−2). At any consumed odd prime, split or inert, at least one denominator is a unit. The existing cross tests and relative-error lemma give integral truncated ratios and absolute errors. Multiplication by h and h−2, followed by subtraction and division by 2, recovers Li=ni modulo the assigned precision. This is the soundness argument in `REFINEMENTS.md` with the same Version 5 index conventions retained by Version 6.

For completeness, at each selected split prime the two full reduced group orders d− and d+ have 2-adic valuations 6 and 2, and opposite orders are pairwise coprime away from 2. Full rational two-torsion gives doubling images of orders d−/4 and d+/4. P* belongs to 2E(K), so these orders annihilate its reductions. For their least common multiples M−,M+ and the scalar continuity modulus L, the parent prime construction gives

    gcd(M−,M+)=1, gcd(M−,L)=16, gcd(M+,L)=1.

The parent choice has 64 dividing h0 and L. Hence h=0 modulo M−, h=2 modulo M+, and h=h0 modulo L are compatible. The same real-progression argument chooses h avoiding 0 and ±2; H and Ui are formal at the primary places and their target differences at the opposite places. Their ratios are ni. Version 6's point chart has an explicit inverse to the old halfpoint chart, so all these witnesses are representable. No assumption of cyclic reduced groups is used.

## Explicit anchor and coefficient size

The smaller anchor is S'=3^(2^26). The linked height proof bounds log2(H19) by 2,093,966 and obtains |a|>(40H19)^10 from this anchor. These bounds are sufficient for the 12/40 comparison argument and scalar order 32. For the variants retaining precisions 16/52, the stronger local orders imply the same height-transfer inequalities.

Seventeen protected coordinates encode c10=3^1024 and c_(j+1)=c_j² for j=10,...,25. Their unique rational values supply S' in the translated anchor; all residuals remain quadratic. Reducing S is an arithmetic refinement, not an identity with the released fixed-S system. The final exported table has no symbolic parameter or omitted coefficient digits. The checker input retains only unused historical parameter metadata for compatibility.

## Reproduce and review

From the repository root, using Python and Node standard libraries:

```sh
python3 -B research/v6-comparison/check_artifacts.py
python3 -B research/v6-comparison/explore.py --out /tmp/v6-replay
```

The output directory must be new. `--only 4` regenerates just the selected variant. Generation validates pinned inputs and runs the unchanged Version 6 algebraic checker. The shipped replay checks compressed and uncompressed hashes, the unique constant chain, exact arithmetic budgets, emitted logarithm identities, reduction certificates, coordinate maps, the complete sum of residual squares, and coefficient statistics. `RESULTS.json` records every experiment, including the unsuccessful count reduction.

These finite checks do not prove the detector-domain lemmas, height theorem, prime construction or doubled-target arithmetic argument. Independent human mathematical review is still pending. The new composition, quotient-weight circuit, exposition and scripts were developed with AI assistance under the repository owner's direction. The upstream source architecture, Version 6 optimizations and independent compiler/checker retain their original attribution.
