# Independent reciprocal source-construction audit

This audit checks source equations and compilation. It does not authorize a
new arithmetic source pin or prove that the new source has the same rational
input projection as the old source. The changed finite logarithms are not
equal polynomials. Their arithmetic equivalence needs the separate review
of `precision-next/RECIPROCAL_PROOF.md`.

## What the executable checker verifies

`check_source.py` imports neither the original builder nor the reciprocal
compiler. It pins all six original module files by their observed SHA256
digests and pins the original builder digest. It compares the proposed root,
scalar-height batch, parity source, and anchor equations to those exact
modules. At precision 52 it permits only the explicit anchor change from 24
to 26 squarings, the matching global anchor index, and root precision metadata.
Thus fixed generator coordinates, curve constants, root equations, contacts,
41 comparison calls, auxiliary points, scalar order 48, and parity equations
remain fixed. At precision 64 those four module objects are identical.

For `q_compare4`, the checker validates every allocation and equation-log
entry. Only a row with a nonzero constant coefficient on its newly allocated
arithmetic target is accepted as an arithmetic definition. It must be
acyclic and quadratic. Every other row must match one of the independently
written chart, six subtraction, subtraction-inverse, logarithm-inverse, or
compressed-ratio equations. Both components of every field equation are
checked. There can be no extra core equation or undefined core coordinate.

The checker expands arithmetic definitions exactly and computes
G(D f^2) independently using the binomial-convolution coefficient formula.
It checks the shared denominator with high precision, the beta numerator
with label precision, and every other numerator with high precision. It
does not trust coefficient metadata, an output digest, or a circuit count.

For compressed charts it checks all four field equations for each primary
point and the exact expressions y=xp in the subtraction equations. It also
checks Lambda*p0=G0, all four Ai=Ci*pi equations, and all four Ai*Lambda=Gi
equations. Each newly introduced core coordinate must occur in the checked
system. There are no primary z coordinates; all ten rational difference-z
coordinates are retained. The unchanged root module retains common J and
root-point parameters. All 42 outgoing batch arguments are compared to
their exact expected expressions, in order, after expanding all arithmetic
definitions. This complete consumer check covers private arithmetic
coordinates even if an arithmetic expression is shared.

For `q_batch41`, the checker independently builds the ordered leaf plan,
expands all shared power definitions, and checks every bottom and upper norm
equation, the constant first leaf, the nonzero-r guard, the final square,
and the exact parity input. The rational orders must be

    [1]*23 + [label]*2 + [high]*8 + [label]*2 + [high]*6.

It then independently instantiates the full module DAG, allocates every
coordinate, creates the shared squaring chain, and compares every flattened
residual, all derived counts, and the polynomial recipe. It requires exactly
41 comparison and norm-batch instances, 42 parity instances, and one each
of the root, anchor and height batch. Its optional construction map records
the independently derived coordinates and row ranges for later source-bound
conversions.

Polynomial expansion and whole-check elapsed-time limits make malformed or
unexpectedly large inputs fail closed. They raise a dedicated
`CheckerResourceError`, which the mutation harness re-raises. A timeout or
resource failure therefore aborts the run and cannot count as a successful
semantic rejection. Bounds cover allocations before range construction,
monomial degree before tuple concatenation, term counts, coefficient
arithmetic, normalization denominator growth, aggregate module expansions,
and residual streams. Separate resource-regression tests check this behavior.
Both residual encodings, when present, must have identical decompressed bytes
and are both hash-bound in the report. None of the checker computations was
executed locally by this agent.

## Static coordination

The charts reviewer reported no blocking static compiler issue. The source
wrapper calls the pinned original main with chart 10, parity 7, base gates,
unit scaling, and logarithm block 2. This preserves d=3-sqrt(2),
D=11-6sqrt(2), and the existing scaled generator. Its field-order audit
agrees with the independently written order list above. Its detailed
static review is `precision-next/COMPILER_REVIEW.md`.

The precision author confirmed that the kernel and wrapper were stable
during this implementation. The checker does not import them; later
compiler changes still have to satisfy the same equations.

## Remaining proof and acceptance obligations

1. Independently approve the formal curve identity and normalized logarithm
   identity for G, and the full selected-prime tail estimate, including
   coefficients with p in their denominators. Finite coefficient checks
   alone do not prove this estimate.
2. Independently approve global nonvanishing of each finite G polynomial
   over Q(sqrt(2)), including all valuation cases. This is required to infer
   Lambda and every primary p_i nonzero in the compressed source. The source
   equation checker verifies the exact G polynomials and relevant equations;
   it does not assert the valuation theorem on their behalf.
3. Independently approve the mixed-precision soundness and completeness
   proof, the precise applications of the unchanged height/rank/Lucas inputs,
   and the use of the common denominator at high precision. A source PASS
   establishes the compiled test positions, not those arithmetic arguments.
4. Approve the two-direction compressed-chart reconstruction, including
   z_i=-1/p_i, y_i=x_i p_i, and the proof that v_i cannot vanish. The exact
   interfaces checked here match that proof. They do not remove its need.
5. Run this checker and its coherent-omission/malformed-source tests on
   every proposed source variant actually considered. The current compiler
   supports all-five compression or no compression. Partial mixed chart
   compression is outside this checker's accepted format and requires a
   separate explicit review and test family if introduced.
6. After arithmetic and source review, create a new source pin and a fresh
   quadratic lift. Adapt every later source-specific conversion explicitly,
   replay all conversion certificates, independently expand the final
   quartic, and enforce strict coefficient magnitude below 2^80. Do not
   inherit the old source hash or old single-input log-nonzero checker.

The current status is implemented, unexecuted source-construction audit.
No new source has been accepted and no new variable count is claimed.
