# Exact 12,504-variable release audit

This review concerns only the wave13 endpoint
`reciprocal-stages/coordinates`, with named source
`reciprocal64-beta16-compressed-s1-b5e836d77643`. The later combined H19,
37-contact and lower-precision proposals are outside this release.
No frozen source, certificate, verifier or manuscript was edited.

Static review found no source-construction, initial-lift or final-expansion
defect in the inspected endpoint. The reported positive checks already pass
in wave13. An additional executable test packet closes a specific coverage
gap at the new named-source lift and exported quartic. Its remote execution
is still required; this note does not claim those new tests have run.

## The exact claim and byte chain

The polynomial has **12,504 total variables**, comprising its free input and
12,503 existential rational witnesses. Its maximum coefficient in absolute
value is 685783949153203534233601, strictly below
2^80 = 1208925819614629174706176. The endpoint has degree four, 135,721
nonzero monomials and 11,939 nonzero quadratic residuals.

| Object | SHA256 |
| --- | --- |
| Expanded polynomial text | `7f5aa3117af82a0b323f0a4e74a18599204f5540408106d3ce99612b5ed830ca` |
| Complete algebraic certificate gzip | `9f7979c1e786bebad624b9ea4631b7eccd879f4bebb5b9ab69250b945973b268` |
| Named verifier | `d2079177a4960740c5b7d42fbd0756dfc4ce8953cc947cee91c8786ba26fa8ba` |
| Named source gzip | `ce9eeac7c4730aced8cfb70a1ab3b1b6a7fb2110c597afad1f56ddc92aeea73f` |
| Source plain residual stream | `b5e836d7764363fcbfdafbacefe80a5f53e0979eba73af990827942b0fa9351d` |
| Source construction checker | `495ca32737687fca335704c6bdbabacf8f20a7698839aa680639e8e1b60a948f` |
| Independent construction map | `edad166ce99d33fe50271e2afdc1628bbec0361d812762212240cadd30f93cfe` |
| Reciprocal arithmetic proof | `be5b08dd9ded743606d5c6a5fc869c4e9764575da49e5d80af13aca09950a98a` |

The named verifier embeds the complete source entry, not just an editable
external source digest. It checks the initial entry digest, compressed and
plain source digests, the exact source header and its variable range. A new
source cannot be accepted by changing a certificate's source hash alone.
The release runner must retain these byte identities and independently
rerun the source audit against the six pinned original module files.

## Source outputs and arithmetic lemmas

The source checker imports neither source producer nor original builder.
Its `coefficients` function constructs the binomial convolution in the
reviewed proof. `expected_g` forms, over rational polynomial pairs,

    G_J(D f^2) = sum_{j=0}^J a_j (D f^2)^j,
    D = 11 - 6 sqrt(2).

Every arithmetic definition in the submitted comparison module is expanded
from an acyclic, uniquely solvable equation. The checker then compares
every expanded core row and every ordered call argument with its independent
polynomial. This includes all five fused G outputs. Thus there is no need
for a further sample-evaluation test to establish the G identity.

| Source point label | Arithmetic role | Precision | Terms, largest exponent |
| --- | --- | --- | --- |
| H | Shared denominator | 64 | 16, J=15 |
| X0 | Beta numerator | 16 | 4, J=3 |
| X1, X2, X3 | Other numerators | 64 | 16, J=15 |

The compressed source retains exactly

    Lambda*p_H = G_H,
    A_i = C_i*p_i,
    A_i*Lambda = G_i,

with the sign convention Lambda=-L_H and z_i=-1/p_i. The checker verifies
these equations after expansion, not merely their labels. It also verifies
the four chart equations for each private primary point, all six field
subtraction equations and the abscissa guard for each difference point.
It checks complete local allocation and every consumer; omitted, extra or
externally captured core constraints cannot be hidden behind G metadata.

Both required nonfinite facts are in the reviewed reciprocal proof.
For every selected prime p>76176, its entire-tail bound gives relative
precision at least p^64 or p^16 from these exact term counts. Its valuation
at 2 proves G_J(D f^2) nonzero for every f in Q(sqrt(2)), since J>=2 and
each nonconstant coefficient has valuation one. The latter is required
to deduce p_i and Lambda are nonzero before reconstructing z_i and the
former inverse of L_H. It cannot be replaced by finitely many numerical
examples.

The chart reconstruction divisions are justified in that same proof.
The retained xf=1 implies f is nonzero. From

    f*p^2 = v^2*(1+d*f)

and p nonzero follows v nonzero, so h=u*p and w=u*p/v reconstruct the old
chart. The source checker checks the polynomial premises of these identities.
The published proof must retain the all-field nonvanishing argument.

The exact field-test order is

    [1]*11 + [16,64,64,64,64,16,64,64,64].

The rational tests, including the root error first, have orders

    [1]*23 + [16]*2 + [64]*8 + [16]*2 + [64]*6.

The first 64 after the three primary high tests belongs to H's alternate
test. Lowering it would invalidate the shared-denominator argument. The
checker verifies the expressions as well as this order list, and verifies
all norm-tree leaves and intermediate powers. It pins the unchanged root,
anchor, scalar-height and parity modules. Hence this source still has 41
root comparison calls, 24 anchor squarings, height exponent 24 and scalar
orders [1,1,1,1,48,48].

`INDEPENDENT_RECIPROCAL_REVIEW.md` and
`BETA16_INDEPENDENT_REVIEW.md` review the proof with the digest above.
The first arithmetic contradiction uses only the three high comparisons.
The beta-only second contradiction uses precision sixteen. The global
nonvanishing proof and full soundness/completeness argument are part of
the source theorem, outside the algebraic certificate verifier's scope.
The changed finite logarithm is not claimed to have the same polynomial
output as the old finite logarithm. The two sources define the same input
set by their soundness and completeness arguments.

## Initial lift and final expansion

The initial lift may reuse a product only after checking an actual retained
source equation xy=s*v with nonzero rational s. Those anchor equations
remain among the lifted rows and are checked without applying the reuse
rules to themselves. Every new product coordinate is allocated in order
and has its exact defining equation. All products depend only on previously
available coordinates. Expanding the new products and reducing by the
retained anchors matches each original source row up to a nonzero rational
factor. All resulting residuals have degree at most two.

These checks provide the two rational solution maps. A source solution
extends by evaluating each product. A lifted solution restricts to a source
solution because every anchor and product identity is retained. No square
root or variable division enters this initial lift, and the input remains
coordinate zero.

At the endpoint the verifier replays all 1,467 algebraic operations. It
compares the saved rows, the complete active-coordinate set and the compact
residuals. It fixes coordinate zero in the compaction. It then recomputes
the weighted sum of squares using all ordered term products, compares every
integer coefficient with the exported polynomial, and checks both the raw
and gzip exports. Finally it checks degree, variable coverage, the strict
coefficient bound and every reported count. Positive weights make the sum
of squares equivalent to the rational residual system.

The current certificate uses 205 norm inverse replacements, 41 redundant
inverse removals, six point-chart replacements, two ordinate removals, 42
parity replacements, one batch absorption, 366 row operations, 800 direct
eliminations and four shears. No circuit-cache acceptance is used in this
endpoint. Those transformation proofs remain required release material;
their implementation is under the separate general checker review.

## Additional tests and remaining release checks

Wave13 already reports 38 source mutations rejected, including swapped
mixed-order expressions, missing G interfaces, extra constraints/calls,
forward references, corrupted flattening and mismatched gzip twins. Its
five resource regressions distinguish aborts from semantic rejections.

The old algebraic mutation script expects cse and translation events, which
this new endpoint does not contain. `test_named_certificate.py` therefore
adds 30 endpoint-specific cases. They cover source-entry binding, reuse
anchors, product allocation and definitions, retained source rows, input
preservation, elimination coverage, final row and allocation commitments,
compaction, full polynomial coefficients, gzip agreement and report counts.
One case multiplies all positive square weights and every exported
coefficient by 2^80. It therefore reaches the strict coefficient-bound
assertion after passing exact polynomial comparison.

The script starts with an exact positive replay. Each malformed case must
raise AssertionError at its intended verifier statement. An exception at
another statement, a timeout, a missing fixture, a resource failure or an
import error fails the run. Cases execute in isolated subprocesses with
per-case and overall limits. Temporary copies leave the frozen artifact
untouched.

For publication, obtain a passing remote receipt for these tests and the
clean regeneration/replay runner. Include the reviewed source arithmetic
argument and the unchanged height/rank/prime-pattern/Lucas inputs on which
it relies. Describe the arithmetic review and finite certificate checks
separately. Preserve the exact 12,504 total-variable claim and byte pins
above when copying the final public artifact.
