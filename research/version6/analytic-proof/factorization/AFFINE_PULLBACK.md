# Fixed-modulus affine interpolation and W-tricked minor arcs

Date: 2026-11-06. All integer moduli in this file are fixed before the size
parameter tends to infinity. This supplies a proof of the interpolation
step; fractional arguments are not treated as automatically equidistributed.

## 1. Affine interpolation lemma

Fix W>=1 and an integer b with 0<=b<W. Fix m,d. There are positive a,sigma
depending only on m,d, and thresholds depending on W,m,d, such that the
following holds. Let G/Gamma, its rational filtration, metric, and polynomial
sequence g satisfy the Green–Tao conventions. Let the adapted basis be
Q-rational. Assume

    N^(-sigma) <= delta <= delta0(W,m,d),
    Q <= delta^(-a),
    (g(n)Gamma)_(1<=n<=N) is totally delta-equidistributed.

There is a polynomial sequence gtilde on Z, of the same filtration degree,
with

    gtilde(Wn+b)=g(n) for every integer n,                (A1)

and (gtilde(t)Gamma)_(1<=t<=WN+b) is totally delta^a-equidistributed.
The constants a,sigma can be decreased without affecting the assertion.

### Construction

Extend g to real arguments by its polynomial Mal'cev coordinate
interpolation. More explicitly, each second-kind coordinate of g(n) is
the polynomial in binomial coefficients furnished by the one-parameter
coordinate characterization in published Green–Tao Lemma 6.7. Evaluate
those same coordinate polynomials at real u and apply the inverse Mal'cev
coordinate map. Denote the resulting map by g_R(u). It agrees with g on
integers. Composing these coordinate polynomials with (t-b)/W preserves
the required coordinate degree bounds, so

    gtilde(t)=g_R((t-b)/W)

belongs to poly(Z,G_bullet). This proves (A1). Equivalently one can use
the Taylor product of real powers of the Taylor coefficients; real powers
are defined because G is connected, simply connected, and nilpotent.
No assertion that the fractional argument is an integer is being made.

### A linear coefficient fact

Suppose p is a degree-d scalar polynomial modulo one, X>=1,
P(t)=u+v*t with integers u,v and v nonzero, |u|<=C X, |v|<=E, and L>=X/E.
Then for some integer 1<=k<=C_d E^C_d,

    ||k*p||_C-infinity[X]
       <= C_d (C+E)^C_d ||p composed P||_C-infinity[L].   (A2)

For completeness, expand binom(u+vt,j) in the binomial basis in t.
The coefficients are integers, the diagonal coefficient is v^j, and
the coefficient in row l is O_d((C+E)^j X^(j-l)). Starting at j=d,
clear the nonzero diagonal entries successively. Their product is a
nonzero integer bounded by E^O_d(1). At step j, the factor X^j/L^j is
at most E^j, and all higher-row errors are multiplied by X^(h-j), which
cancels their X^(-h) bound. This is the same triangular argument as the
quadratic coefficient lemma in `../quotient-audit/NORM_TRANSFER.md`, now
with degree one. It proves (A2).

### Equidistribution proof

Put X=WN+b and epsilon=delta^a. If the asserted total epsilon
equidistribution fails, there is an arithmetic progression

    u+v*[L] contained in [X], L>=epsilon*X,
    1<=v<=2/epsilon, |u|<=2X,

on which gtilde is not epsilon-equidistributed. The published
one-parameter quantitative Leibman theorem, Theorem 2.9, gives a
nontrivial horizontal character eta with

    |eta| <= C epsilon^(-C),
    ||eta composed gtilde composed (u+v*t)||_C-infinity[L]
          <= C epsilon^(-C).

Its rationality hypothesis holds since Q<=epsilon^(-1). Apply (A2),
absorbing the factor two into the exponent. There is k<=C epsilon^(-C)
such that

    ||k*eta composed gtilde||_C-infinity[X]
          <= C epsilon^(-C).                            (A3)

Compose now with the fixed integer map t=Wn+b. The forward binomial
composition matrix is integral. Since X is comparable to WN and b is
bounded by W, its coefficient estimates give

    ||k*eta composed g||_C-infinity[N]
          <= C_(W,d) epsilon^(-C).                      (A4)

The character k*eta remains nontrivial. Choose a so small that the bounds
in (A4) and for |k*eta| are below delta^(-c0), where c0 is the horizontal
character obstruction exponent proved in the norm-transfer note. All
fixed W-dependent constants are absorbed by decreasing delta0. That
obstruction contradicts total delta-equidistribution of g. Choose sigma
smaller than its floor/size exponent. This proves the lemma.

More explicitly, let C_aff be a fixed exponent, depending only on m,d,
which bounds all epsilon losses in (A2)–(A4) and the character size. Fix
0<a<min(1,c0/(2*C_aff)) and
0<sigma<min(sigma0,1/(2*a)), where sigma0 is the obstruction lemma's
size exponent. Then a*C_aff<c0/2, leaving room to absorb W-dependent
constants into delta0, and epsilon*X grows at least like N^(1/2).
Thus all progression parametrizations and floors above are valid for
N>=N0(W,m,d).

The proof explicitly covers all subprogressions of [WN+b], including
ones not contained in the residue b modulo W. It is therefore a total
equidistribution conclusion on that full interval, not merely a claim
on the original embedded progression.

## 2. Applying the Gaussian estimate

Let T_chi(t)=sum_(N(a)=t) Lambda_E(a) chi(a), with E=Q(i) and fixed ray
character chi. Assume the independently derived estimate

    |sum_{N(a)<=X, N(a) in R} Lambda_E(a)chi(a)
                    F0(h(N(a))Gamma)|
      <= C_(H,m,d) Q1 X log(2X)^7 eta^cE ||F0||_Lip      (A5)

when h is totally eta-equidistributed, the basis is Q1-rational, F0
has mean zero, and R is an arbitrary interval progression of modulus
at most Q1. This is the power interface in `../type-i-ii/TYPE_I_II.md`.

For an interval progression P in [N] of modulus q<=Q, the constraints
t=Wn+b and n in P form an interval progression R of modulus Wq. Therefore

    sum_{n in P} T_chi(Wn+b) F0(g(n)Gamma)

equals the ideal sum in (A5) with h=gtilde, X=WN+b, and
Q1=max(Q,Wq,2)<=C_W Q. By the interpolation lemma this is bounded by

    C_(H,W,m,d) Q N log(2N)^7 delta^(a*cE) ||F0||_Lip.   (A6)

No equidistribution under a fractional reparameterization is assumed;
it is precisely the lemma proved above. No short progression needs to
be discarded. The same argument applies to E=Q and its independently
derived ordinary von Mangoldt estimate, with its exponent cQ.

## 3. Finite character expansion and prime-power errors

Suppose the exact Gaussian ray expansion supplied by the arithmetic
argument is

    Lambda'_C(t) = (1/2) sum_chi c_chi T_chi(t) + error(t),

where the finitely many coefficients and characters depend only on the
fixed ray modulus, and

    sum_{t<=X} |error(t)| <= C_H sqrt(X) log(2X)^2.        (A7)

The factor 1/2 accounts for the two conjugate Gaussian prime ideals above
an eligible split rational prime. Its validity requires the selected
ray-class condition to be conjugation invariant. This file assumes the
arithmetic expansion has been checked; it does not replace that check.

Summing (A6) over the finite characters and using (A7) gives the W-tricked
ray-prime minor-arc estimate, with an additional
C_(H,W) sqrt(N) log(2N)^2 ||F0||_infinity error. The ordinary Lambda'
weight has the same elementary prime-power error relative to Lambda.

In the regime delta>=N^(-sigma1), choose sigma1>0 smaller than the
interpolation exponent sigma and so that

    sigma1 * a * min(cE,cQ) < 1/4.

Then the square-root errors are bounded by the main expression in (A6)
for large N. Thus any fixed linear combination of these W-tricked
ray-prime and ordinary-prime weights has an estimate of the form

    C Q N log(2N)^7 delta^cW ||F0||_Lip,                 (A8)

with cW=a*min(cE,cQ)>0, under

    delta>=N^(-sigma1), Q<=delta^(-a), delta<=delta0.

For delta>=delta0 the trivial O(N log N) estimate, or an enlargement of
the constant when appropriate, supplies the unused bounded-delta range.
The factorization proof only uses delta tending to zero as a negative
power of a polylogarithmic M, so the displayed restricted regime alone
is sufficient.

For example this applies to the proposed centered weight

    h_b(n) = (phi(W)/W) Lambda'_C(Wn+b)
                - mu_C(b) Lambda_(b,W)(n),

provided Lambda_(b,W) denotes the specified normalized ordinary-prime
weight and the arithmetic definition of mu_C(b) is fixed. Both the
normalization and mu_C(b) are constants for fixed W. They affect the
implied constant, not the positive exponents. The progression main-term
argument must still verify that this particular centering satisfies (SW)
in `FACTORIZATION.md`.

## 4. Choice order and provenance

First fix the arithmetic moduli H,W and the nilmanifold dimensions.
Then fix a,cW,sigma1 and the regime exponents. These do not depend on the
factorization parameter B. The generic factorization lemma chooses B
large enough to put its conjugated components into this regime; because
M is polylogarithmic in N, the lower bound delta>=N^(-sigma1) holds for
large N. Constants may depend on H,W throughout.

The interpolation proof uses only the published one-parameter
quantitative Leibman theorem, the elementary binomial coordinate
characterization, and the horizontal-character obstruction proved in
the norm-transfer note. Frei–Tinkova's spreading lemma motivated this
step but is not an assumed theorem here.
