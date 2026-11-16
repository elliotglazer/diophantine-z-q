# Gaussian norm transfer from the published one-parameter theorem

Date: 2026-11-06. This is an explicit proof of the unweighted Gaussian
norm-transfer estimate needed in the Type I/II argument. It is not a proof
of the progression main terms, the factorization step, or the complete
replacement of Frei–Tinkova. Independent review is still required.

## Statement

Fix the Gaussian ray modulus H and m,d, all positive integers. Put
E=Q(i). Extend a finite-order ray character chi of modulus H*Z[i] by zero on
ideals not coprime to H. The trivial character on all ideals is also allowed,
by taking H=1.

There exist constants kappa,sigma>0 depending only on m,d and constants
delta0>0, X0, C depending on H,m,d with the following property. Let

    X >= X0,             X^(-sigma) <= delta <= delta0,
    1 <= Q <= delta^(-kappa), 1 <= q <= delta^(-kappa), q integral.

Use the Green–Tao convention: G is connected, simply connected, and nilpotent,
Gamma is a discrete cocompact subgroup, and G/Gamma is m-dimensional.
Equip it with a degree-d filtration of closed connected rational subgroups, a Q-rational adapted Mal'cev
basis, and its associated metric.
Let g be in poly(Z,G_bullet) and suppose (g(n)Gamma) for 1<=n<=X is
totally delta-equidistributed. Let F be Lipschitz and have integral zero. For every real
0<=A<B<=X and every integer b,

    | sum_{A<N(a)<=B, N(a)=b mod q} chi(a) F(g(N(a))Gamma) |
        <= C X delta^kappa ||F||_Lip.                    (NT)

There is no lower bound on B-A or on the number of points in the progression.
The estimate is uniform in the interval endpoints and the residue b.
In dimension zero the assertion is immediate because mean-zero F vanishes.
Partial summation gives the same bound with an extra factor log(2X) if the
summand includes log N(a).

The assertion also applies with m replaced by 2m and F replaced by
F1 tensor conjugate(F2), provided both F1 and F2 have mean zero and the
entire product orbit is totally delta-equidistributed on the product
nilmanifold. Mean-zero factors do not imply that product-orbit hypothesis.
The product function has integral zero. Choose the smaller kappa,sigma of
the two dimension bounds when using (NT) in Type II.

## Published input and conventions

The only non-elementary distribution input in this proof is Green–Tao,
*The quantitative behaviour of polynomial orbits on nilmanifolds*, Annals
175 (2012), 465–540, Theorem 2.9. It is the one-parameter quantitative
Leibman theorem, with the degree doubled below. The elementary coordinate
and metric estimates in its Appendix A are also used.

Official paper: https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf

Local pinned source:
`work/quartic-version5-release/sun-proof/sources/GT-orbits-published.pdf`.
Theorem 2.9 is on printed page 480 and local text lines 747–754.
The metric estimates are Lemmas A.4 and A.14–A.16.

This proof uses no multiparameter equidistribution theorem. In particular,
it does not use the multiparameter assertion addressed by the later erratum.

For a scalar polynomial p(n)=sum_j alpha_j binom(n,j), use exactly

    ||p||_(C-infinity[X]) = max_{1<=j<=deg p} X^j ||alpha_j||_(R/Z).

Total delta-equidistribution means that the normalized average over every
arithmetic progression of length at least delta*X differs from Haar average
by at most delta times the Lipschitz norm. We never replace normalized
averages by unnormalized sums without multiplying by their number of terms.

## A quadratic coefficient lemma

Let P(t)=a0+a1*t+a2*t^2 be in Z[t], a2 nonzero, and suppose

    |ai| <= B0 X^(1-i/2),       L >= X^(1/2)/B0,       B0>=2.

For any degree-d scalar polynomial p, there is a positive integer k such
that

    k <= C_d B0^(C_d),
    ||k*p||_(C-infinity[X])
         <= C_d B0^(C_d) ||p composed P||_(C-infinity[L]).       (QE)

Here all constants depend only on d. No equidistribution assertion is an
input to this lemma.

Proof. Write

    binom(P(t),j) = sum_l s[j,l] binom(t,l).

All s[j,l] are integers because the left side is integer-valued at every
integer t. The degree is 2j and

    s[j,2j] = (2j)!/j! * a2^j != 0,
    |s[j,l]| <= C_d B0^j X^(j-l/2).

The bound follows by expanding P(t)^h and changing between the monomial
and binomial bases; the change-of-basis matrices have fixed rational
coefficients depending only on d. In the expansion for a coefficient of
degree l, the weighted sum of input exponents is at least l. The stated
bound also follows directly by descending induction in l.

If p=sum_j alpha_j binom(n,j) and p(P(t))=sum_l beta_l binom(t,l), the even
rows of the composition matrix give

    beta_(2j) = sum_{h=j}^d s[h,2j] alpha_h.

Set k_j=product_{h=j}^d s[h,2h]. Descending induction in j shows

    X^j ||k_j*alpha_j|| <= C_d B0^(C_d) ||p composed P||_C-infinity[L].

For the beta_(2j) term use X^j/L^(2j)<=B0^(2j). For a higher alpha_h term
use |s[h,2j]|<=C_d B0^h X^(h-j), which cancels its X^(-h) error. All
multipliers used to clear higher rows are integers of size B0^O_d(1), so
distance modulo one obeys the same bounds. Finally multiply each row to
the common nonzero integer |k_1|. This proves (QE), including the claimed
bound for k. The constant term alpha_0 is never needed.

## A small horizontal character contradicts total equidistribution

The following quantitative observation is useful. If the basis is
T-rational, a nontrivial horizontal character eta has |eta|<=T, and

    ||eta composed g||_C-infinity[X] <= T,

then g cannot be totally delta-equidistributed whenever T<=delta^(-c0),
delta is sufficiently small, and X is sufficiently large with
delta>=X^(-sigma0). Here c0,sigma0>0 depend only on m,d.

Indeed, choose coefficient representatives alpha_j with
|alpha_j|<=T/X^j. On the initial interval of length floor(X/(100*d*T)),
eta(g(n)) stays in an arc of length less than 1/10 around alpha_0. A
translated Lipschitz bump on R/Z can equal one there, have integral zero,
and have bounded Lipschitz norm. Composing it with eta has Lipschitz norm
at most T^C(m,d), by the published Mal'cev coordinate/metric comparisons.
The resulting test function has Haar integral zero because a nontrivial
horizontal character pushes Haar measure onto Haar measure on R/Z.

Choose c0 so that C*c0<1/4 and c0<1/4. The initial interval is longer
than delta*X, and delta*T^C<1/2 for small delta. Its test-function average
is one, a contradiction. The condition delta>=X^(-sigma0), with a
sufficiently small fixed sigma0, absorbs floors and keeps this interval
nonempty. This proves the observation.

## Pullback estimate with all coefficient scales

Fix a large constant Cstar depending only on m,d which dominates the
exponents and constants in (QE), the degree-2d instance of Theorem 2.9,
and the preceding horizontal-character observation. Increasing Cstar is
allowed before choosing the exponents below. Choose

    0 < kappa < 1/(1000*Cstar^2),
    0 < sigma < min(1/(1000*Cstar^2),sigma0).

Require explicitly as well that 6*Cstar*kappa<c0/2 and
2*kappa*sigma<1/4, where c0 is from the horizontal-character observation.
These are compatible strict inequalities, so the exponents can be fixed
once in terms of m,d before H or X is chosen.

Decrease these further, if necessary, to cover the product nilmanifold.
For the proof of (NT), it is enough that B0<=delta^(-5*kappa) and that
the output error parameter is epsilon=delta^kappa.

If (g(P(t))Gamma) for 1<=t<=L were not epsilon-equidistributed,
Theorem 2.9 would give a nontrivial horizontal character eta with

    |eta| <= C epsilon^(-Cstar),
    ||eta composed g composed P||_C-infinity[L]
          <= C epsilon^(-Cstar).

The input basis is epsilon^(-1)-rational since Q<=delta^(-kappa).
The composed sequence has degree at most 2d with filtration
Gtilde_j=G_ceil(j/2); the original adapted basis remains adapted. This
follows from the elementary one-parameter coordinate characterization in
the published Lemma 6.7: write the second-kind Mal'cev coordinates in the
binomial basis and note that a degree-j coordinate becomes degree at most 2j.

Apply (QE). Both |k*eta| and ||k*eta composed g||_C-infinity[X] are at
most C delta^(-6*Cstar*kappa), after increasing Cstar. The character
k*eta is nontrivial because a nonzero integer multiple of a nontrivial
horizontal character is nontrivial. With the displayed choice of kappa,
the horizontal-character observation contradicts total delta-equidistribution.

Thus every such quadratic pullback is epsilon-equidistributed. This
argument only needs ordinary, not total, equidistribution of the pullback.
Every progression restriction below is absorbed into P before this step.

## Gaussian lattice proof of (NT)

Every nonzero Gaussian ideal has exactly four generators. Moreover
chi((z)) is invariant under units and is periodic in z modulo H*Z[i],
including its zero extension. Therefore the sum in (NT) is exactly

    (1/4) sum_{z=x+iy !=0, A<x²+y²<=B, x²+y²=b mod q}
              chi((z)) F(g(x²+y²)Gamma).                       (G)

This factor 1/4 is essential. It is uniform even for generators on the
axes; no half-open angular sector and no boundary convention are needed.

Set rho=delta^kappa and M=floor(rho*sqrt(X)/H). For every integer y and
every residue class x modulo H, partition its x-values into consecutive
blocks of M points, with step H. The character is constant on each block.
On a horizontal row the annulus A<x²+y²<=B is a union of at most two
intervals. At most four blocks per residue class meet an interval endpoint.
There are O(sqrt(X)) relevant rows. The total number of points in these
boundary blocks is therefore

    O(H*sqrt(X)*M) = O(rho*X).

The zero point, if present in a block, is excluded and contributes nothing;
its removal costs at most one additional bounded summand. This is absorbed
by rho*X. All boundary points can be estimated using ||F||_infinity.

Each remaining block lies wholly inside or wholly outside the annulus.
For an inside block split its index t modulo q. On such a class the
condition x²+y²=b mod q is constant. Each nonempty class is parameterized by

    x=x0+H*q*n,       1<=n<=L,
    P(n)=(x0+H*q*n)^2+y²,
    L >= M/(2q) >= rho*sqrt(X)/(4Hq).

The slight endpoint adjustments in x0 change its magnitude by at most
Hq. Thus |x0|<=2sqrt(X) for our parameter range, and

    |a0| <= C X,     |a1| <= C Hq sqrt(X),     a2=H²q².

By taking delta0 sufficiently small depending on H, all fixed constants
and H-powers can be bounded by delta^(-kappa). Since q<=delta^(-kappa),
these coefficient bounds and sqrt(X)/L fit (QE) with
B0<=delta^(-5*kappa). The lower bound delta>=X^(-sigma) ensures M>=2q
and all floor estimates for X>=X0.

The pullback estimate now bounds the sum on this class by
L*delta^kappa*||F||_Lip. The classes partition the interior points, of
which there are O(X). Their combined contribution is O(X delta^kappa
||F||_Lip). Adding the boundary contribution proves (NT).

This proof handles arbitrary A,B because the number of endpoints on each
row is bounded independently of the annulus width. It handles all residue
classes, including classes not coprime to q. It does not use an ideal
theorem, a prime theorem, or a Hecke L-function estimate.

## Interface with Type I/II and limits of this result

For a Type I progression constraint r*n=b mod q, either it has no solutions
or it is one residue class modulo q/gcd(r,q). For Type II the simultaneous
constraints with r and r' are either inconsistent or a single class modulo
a divisor of q. Restrictions n in a dyadic interval and r*n,r'*n in a
specified interval only change A,B. Consequently (NT) covers every such
restriction without a lower-length assertion.

Take delta=(log X)^(-Bexp), Q,q<=(log X)^Cexp. For any required Aexp, choose

    Bexp*kappa > max(Cexp,Aexp).

Then (NT) gives O_H(X*(log X)^(-Aexp)) for large X. This is the precise
polylogarithmic modulus/complexity interface. In Type I/II the inner scale
is at least N^(1/3)/O(1), so log X and log N are comparable; fixed factors
of three are absorbed by increasing Bexp. Product spaces require the
smaller kappa specified above.

This norm-transfer lemma supplies the missing Gaussian analogue of the
unweighted step, but it alone does not prove the ideal von Mangoldt
estimate. The independent Type I/II derivation must still be checked,
followed by progression main terms and quantitative factorization. No
claim that the full external FT dependency is removed follows from (NT)
in isolation.
