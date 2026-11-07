# A reusable comparison lemma and the next reduction barriers

Research derivation, 7 November 2026. This is AI-authored mathematical work,
not independent human review. It assumes the inherited contact-to-height
theorem and Lucas lemma; it does not prove either deep input.

## The abstract argument

Let H >= 1, B >= A >= 1, and alpha, k, ell, s > 0. Suppose a nonzero
integer discrepancy Delta would satisfy

    B² < 7H |Delta|^(alpha/k) + 6,
    |Delta| <= c B^d,                 c >= 1, d > 0.

Set epsilon = 2-alpha*d/k and C = 7 c^(alpha/k)+6. If epsilon > 0,
division by B^(alpha*d/k), using B >= 1 and H >= 1, gives

    B^epsilon < C H.

Consequently A^epsilon >= C H forces Delta = 0. This accounts for
the additive 6; discarding it before division would not be justified.
At epsilon = 0 this argument gives only 1 < C H, and when epsilon < 0
large B makes the inequality easier. Thus k > alpha*d/2 is the precise
threshold for this particular comparison argument.

Now assume Delta = 0 implies log B > A-3. Suppose a second nonzero
discrepancy has integer numerator N with

    B² < 7H N^(alpha/ell)+6,
    N <= 2 exp(h) B,                 0 <= h <= H A^(alpha/s).

Put eta = alpha/ell, rho = 2-eta, and D = 7*2^eta+6.
For rho > 0 the same division gives

    rho log B < log(DH)+eta*h.

Hence the second discrepancy vanishes whenever

    log(DH)+eta*H*A^(alpha/s) <= rho*(A-3).

This is a sufficient condition, not a necessary one. It cleanly separates
the scalar height bound from the low-order local comparison.

## Recovering the present proof, with constants

Take alpha=19, d=4, k=40, ell=12, s=32 and c=5.
Then epsilon=1/10, eta=19/12 and rho=5/12.
The elementary bounds 5^(19/40)<5/2 and 2^(19/12)<4 yield
C<24 and D<34<40. The existing anchor A>(40H)^10 therefore
implies A^epsilon>40H>C H.

For either s=24 or s=32, 10*(1-19/s)>1, so
H*A^(19/s)<A/40. Also log(40H)<A/40: for x>=40,
log x<x and x^10>40x. We obtain

    log B < (12/5)log(40H)+(19/5)h < 31A/200.

Since A>(40H)^10>4, 31A/200<A-3. Both contradictions follow.
The elementary part of the proof is now a reusable lemma with four
interfaces: discrepancy size, contact-to-height transfer, scalar height,
and Lucas growth. Improving any one interface can be evaluated without
rewriting the whole construction.

## What numerical improvement would unlock smaller circuits?

These are strict thresholds for this method; equality is insufficient.

| Desired change | Required improvement, retaining the other interfaces |
| --- | --- |
| High precision 40 to 36, degree four | height exponent alpha < 18 |
| High precision 40 to 32, degree four | alpha < 16 |
| Low precision 12 to 8 | alpha < 16, plus a compatible scalar/anchor budget |
| Degree-four discrepancy to degree three, alpha=19 | precision 32 clears the degree threshold |
| Scalar order 32 to 24 at alpha=19 | already permitted; previous compilation found no coordinate saving |

For an anchor A>(40H)^R, the simple sufficient scalar condition used
above is R*(1-alpha/s)>1. With R=10, alpha=19, the smallest multiple
of four meeting this condition is 24. Order 20 fails this sufficient
budget; that is not a proof that a different anchor cannot support it.

A cubic substitute for the Lucas relation is an attractive structural
direction, but it must retain both exponential growth of every valid
solution and completeness with the required index divisibility. Merely
introducing an auxiliary variable to lower the displayed degree does
not suffice: its height and all new relations enter the comparison.

## A limited optimality result for the current weight circuit

Each detector needs q12=q1*e^22 and q40=q1*e^78. The existing circuit
uses seven multiplication gates for the positive powers

    2, 4, 8, 16, 24, 40, 80

and two quadratic quotient equations

    e² q12 = q1 e^24,       e² q40 = q1 e^80.

In the restricted architecture consisting of positive powers of e formed
by multiplication, followed by one quotient equation for each output,
these nine gates are optimal. After six power gates the largest exponent
is at most 2^6=64. The q40 equation requires a numerator exponent at
least 78 (and at least 79 if the denominator has positive exponent),
so at least seven power gates are necessary, plus the two output gates.

This does NOT cover circuits that reuse q12 internally, mix q1 and e in
intermediate monomials, use intermediate divisions, or eliminate gates
against other residuals. It prevents repeating a search within one
already optimal architecture, not a claim of global circuit optimality.

The denominator e² is safe only on the established source domain:
the retained w0 inverse and the norm relation imply e*delta != 0.
This lemma does not authorize dropping that obligation or its guards.

## Map to the full proof

The contact-to-height interface is the exponent-19 refinement in
`research/combined-comparison/ARITHMETIC.md`, sections 2 and 4, built
on `thm:quartic-height19` and `lem:v5-height-transfer` in the preserved
manuscripts. Scalar height comes from `v5:scalar32-bridge`; Lucas growth
from `lem:o8-lucas`. The anchor calculation is section 3 of ARITHMETIC.md.
`../overnight-20261106/INTUITIVE_PROOF.md` explains the local observations
and common-witness completeness that precede these interfaces.

No improvement to the Gaussian prime-pattern input, elliptic-curve group
calculation, height theorem or Lucas growth theorem is claimed here.
