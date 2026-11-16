# Gaussian ideal Type I/II reduction

Status: the algebraic and combinatorial extraction below is proved here. The
nilsequence conclusion uses the separately proved Gaussian norm-transfer lemma
in `../quotient-audit/NORM_TRANSFER.md`, and the published Green--Tao results
listed at the end. It does not assume a theorem of Frei--Tinkova. Independent
review of the combined proof is still required. Attribution to Frei--Tinkova's
strategy is retained.

## 1. Conventions and elementary bounds

All ideals are nonzero integral ideals of Z[i]. Write Na for the absolute norm,
mu(a) for ideal Mobius, and Lambda(a)=log Np if a is a positive power of a prime
ideal p, and zero otherwise. Let chi be completely multiplicative with
|chi|<=1. A ray character extended by zero on ideals not coprime to its fixed
modulus is permitted. Put L=log(2N). Constants in this section are absolute.

Let a(n) count ideals of norm n. Unique factorization of ideals gives

* a(p^k)=k+1 at split rational primes;
* a(p^k)=1 for even k and zero for odd k at inert primes;
* a(2^k)=1.

Consequently a(n)<=tau(n). Moreover tau(n)^2<=d_4(n), since at each prime
(k+1)^2<=binomial(k+3,3). Thus, for X>=1,

    sum_{n<=X} a(n)^2 <= X (1+log X)^3,
    sum_{n<=X} a(n)^2/n <= (1+log X)^4.                 (1)

For the first inequality sum 1 over quadruples with product <=X, perform the
last sum by floor(X/(n1*n2*n3)), and bound three harmonic sums. For the second,
bound each of the four harmonic sums separately. These arguments prove the
moment bounds needed below without a cited divisor estimate.

Every ideal has exactly four Gaussian generators. Covering a disk by unit
squares gives

    A(X):=#{a: Na<=X}=pi X/4+O(sqrt X+1).             (2)

The boundary squares lie in the annulus between radii sqrt(X)-sqrt(2) and
sqrt(X)+sqrt(2), which proves the error estimate. In particular A(X)<=C X
for X>=1, and #{a:B/2<Na<=B} is between cB and CB once B exceeds an absolute
constant. No uniform bound a(n)=O(1) is used.

The convolution identities on ideals are

    mu*1=delta_1,       1*Lambda=log N,       mu*log N=Lambda.       (3)

They follow prime-power by prime-power. In particular
sum_{c|d} Lambda(c)=log Nd, with nonnegative summands.

## 2. Exact Vaughan identity

Let U,V>=1. Split mu=mu_{<=U}+mu_{>U} and
Lambda=Lambda_{<=V}+Lambda_{>V}, using norm cutoffs. From (3),

    Lambda = mu_{<=U}*log N + Lambda_{<=V}
             -mu_{<=U}*1*Lambda_{<=V}
             +mu_{>U}*1*Lambda_{>V}.                         (4)

This is an identity of functions on ideals, including ideals divisible by the
ray modulus before multiplication by chi. On ideals of norm >V the second
term vanishes. Take U=V=N^(1/3), and let f be any complex function with |f|<=1
supported on N/2<n<=N. For N>=8, multiply (4) by chi(a)f(Na) and sum. The result
is exactly T0-T1+T2, where

    T0 = sum_{Nd<=U} mu(d)chi(d)
           sum_b log(Nb)chi(b) f(Nd Nb),

    T1 = sum_{Nd<=UV} alpha_d chi(d)
           sum_b chi(b) f(Nd Nb),

    T2 = sum_{V<Nd<=N/U} beta_d chi(d)
           sum_{Nb>U} mu(b)chi(b) f(Nd Nb),

    alpha_d = sum_{bc=d, Nb<=U, Nc<=V} mu(b)Lambda(c),
    beta_d  = sum_{c|d, Nc>V} Lambda(c).

All sums are finite because of f's support. Equation (3) gives

    |alpha_d|<=log Nd<=L,       0<=beta_d<=log Nd<=L.          (5)

No error or omitted endpoint occurs in these identities. The cutoff Nb>U in
T2 can always be included in its bounded coefficient.

## 3. A quantitative extraction statement

There are absolute c0>0 and N0 such that, if N>=N0, 0<epsilon<=1, and

    |sum_a Lambda(a)chi(a)f(Na)| >= epsilon N L,              (6)

then, with theta=c0 epsilon^4/L^24, at least one of the following holds.

(I0) Some dyadic R<=2N^(1/3) has at least theta R integers r in (R/2,R]
for which

    |sum_b log(Nb)chi(b)f(r Nb)| >= theta N/r.

(I1) The same assertion without log(Nb), for some dyadic R<=2N^(2/3).

(II) There are dyadic R,B satisfying

    N^(1/3)<R<=2N^(2/3),   N/2<RB<4N,

and at least theta R^2 pairs r,r' in (R/2,R] such that

    |sum_{B/2<Nb<=B} f(r Nb) conjugate(f(r' Nb))| >= theta B. (7)

Values of r outside the original Vaughan range are harmless: set their
coefficients to zero. The constants 2 and 4 in the displayed ranges are
intentional. In particular this proof does not use the inconsistent smaller
product range printed in different parts of FT's extraction argument.

### Proof of I0 and I1

At least one Ti has magnitude >=epsilon N L/3. In case I0 define

    G(r)=r/(NL) * |sum_b log(Nb)chi(b)f(r Nb)|.

In case I1 define G(r)=r/N times the analogous unweighted absolute sum.
In either case (2), the support of f, and (5) give G(r)<=C and

    epsilon <= C sum_{r<=N^e} a(r)G(r)/r,

where e=1/3 or 2/3. Cauchy--Schwarz and (1) imply

    sum_{r<=N^e} G(r)^2/r >= c epsilon^2/L^4.

There are at most C L dyadic cells (R/2,R]. On one cell,

    sum_{R/2<r<=R} G(r)^2 >= c R epsilon^2/L^5.

Since G<=C, at least c R epsilon^2/L^5 terms have
G(r)>=c epsilon/L^(5/2). Decreasing c0 in theta makes both the count and the
claimed amplitude weaker than these bounds, including the weighted case.

### Proof of II, with all conjugates

Split Nd and Nb into cells (R/2,R] and (B/2,B]. There are at most C L^2
rectangles. A nonzero term satisfies N/2<Nd Nb<=N; hence its cell satisfies
N/2<RB<4N. Also V<Nd<=N/U and Nb>U imply the stated ranges and
B>=N^(1/3)/4. One rectangle contributes magnitude at least
c epsilon N/L. We use the weaker lower bound c epsilon N/L^2 below.

After grouping d by r=Nd, its contribution is

    T = sum_{R/2<r<=R} A_r sum_{b in Bcell} c_b f(r Nb),

where |A_r|<=L a(r), and |c_b|<=1. The condition Nb>U is in c_b; all product
cutoffs remain in f. Thus the domain is exactly rectangular and no Fourier
truncation lemma is needed. Equation (1) gives

    sum_r |A_r|^2 <= C R L^5.

Writing F_{r,b}=f(r Nb), Cauchy--Schwarz therefore yields

    Tstar:=sum_r |sum_b c_b F_{r,b}|^2
          >= c epsilon^2 R B^2/L^9.                         (8)

Let M be the number of ideals in Bcell. Expansion, then Cauchy--Schwarz in
(b,b'), gives the exact inequality

    Tstar^2
    = |sum_{b,b'} c_b conjugate(c_b')
                 sum_r F_{r,b}conjugate(F_{r,b'})|^2
    <= M^2 sum_{b,b'} |sum_r F_{r,b}conjugate(F_{r,b'})|^2
    = M^2 sum_{r,r'} |sum_b F_{r,b}conjugate(F_{r',b})|^2.

By (2), cB<=M<=CB, and (8) now implies

    average_{r,r'} |average_b F_{r,b}conjugate(F_{r',b})|^2
        >= c epsilon^4/L^18.                                (9)

Each summand is at most one. Thresholding (9), and then using M>=cB, proves
(7) with theta=c0 epsilon^4/L^24. In particular the ray character and Mobius
coefficients have disappeared. The surviving ideal average is untwisted.
This completes the extraction proof.

## 4. Progressions and mean zero

For the analytic application set

    f(n)=1_{N/2<n<=N} 1_{a<n<=b} 1_{n=c (mod q)} F(g(n)Gamma),

and zero elsewhere. No lower bound on b-a is imposed. In I0/I1 the conditions
on n=Nb are an interval and the congruence rn=c (mod q). If solvable, the latter
is one residue class modulo q/gcd(r,q), not necessarily q. In II, the two
conditions rn=c and r'n=c combine, if compatible, into one residue class
modulo lcm(q/gcd(r,q),q/gcd(r',q)), which divides q. The interval is the
intersection of the two scaled intervals and Bcell.

Thus the separate norm-transfer lemma applies directly to every extracted
sum, including arbitrarily short or empty intersections. There is no inference
that an intersection has length comparable to B/q. If the intersection is
empty, it cannot support the extracted large sum.

For II the test function on the product nilmanifold is

    H(x,y)=F(x) conjugate(F(y)).

Its Haar mean is |integral F|^2=0, its sup norm is <=1, and its Lipschitz norm
is at most a fixed multiple of that of F under the sum product metric. For a
general normalization use ||F||Lip^2 and normalize F first. This verifies the
mean-zero hypothesis that is needed for product norm transfer.

## 5. Published horizontal-character recombination

Here is the exact deterministic statement used after norm transfer. Fix m,d.
There are constants H>=2 and K>=2, depending only on m,d, such that the following
holds. Let 0<eta<eta0, N>=eta^(-K), and let g be a polynomial sequence on an
m-dimensional nilmanifold of degree d with an eta^(-1)-rational adapted basis.
Here and below G is connected, simply connected and nilpotent, Gamma is a
cocompact lattice, and the filtration and polynomial sequences have the
standard hypotheses of the cited Green--Tao theorem.

If for at least eta R values of r in (R/2,R], R<=2N^(2/3), the sequence
g(rn), n<=ceil(N/r), fails total eta-equidistribution, then g(n), n<=N, fails
total eta^H-equidistribution. The same conclusion holds if
N^(1/3)/4<=R<=2N^(2/3), N/2<RB<4N, and for at least eta R^2 pairs the sequence
(g(rn),g(r'n)), n<=B, fails total eta-equidistribution on the product.

The constants H,K can be enlarged without invalidating this statement.
They are finite combinations of the exponent constants in published GT
Theorem 2.9 and Lemma 4.5, and elementary degree-d polynomial operations.
The proof below specifies all uses; it does not invoke FT or an unproved
"same argument" extension to ideals. There are no ideals left in this statement.

### 5.1 From failed total equidistribution to coefficients

Failure supplies an arithmetic progression a+q[ell] of length ell>=eta M
inside [M]. Here q<=2/eta and |a|<=2M. GT Theorem 2.9 applied on this progression
gives a nonzero horizontal character with magnitude and smoothness norm
bounded by eta^(-C1), for a fixed C1=C1(m,d). For the product replace m by 2m.

For completeness, removing a large shift does not require treating a as a
bounded-height rational in GT Lemma 8.4. Write p(a+qt) in monomials, multiply
by d! to pass from its binomial coefficients, and use the identity

    p(n)=p(a+q*((n-a)/q)).

Multiplication by q^d clears all denominators q^j. For the coefficient of n^i,
the error terms are bounded by

    C_d eta^(-C1) sum_{j=i}^d q^(d-j)|a|^(j-i) ell^(-j)
       <= eta^(-C2) M^(-i),                                 (10)

after increasing C2; integer coefficient terms are annihilated modulo one.
This proves that a nonzero integer multiple of the character has magnitude
<=eta^(-C2) and C-infinity[M] norm <=eta^(-C2). Degree-d conversion between
monomials and binomial coefficients changes C2 only by a fixed amount.

There are at most eta^(-C3) possible such characters, since the horizontal
character lattice has rank at most 2m. Pigeonholing gives one character for a
set of density at least eta^C4 of r or of (r,r'). These statements hold after
enlarging constants and decreasing eta0 to absorb fixed factors.

### 5.2 Type I recombination

Write psi(g(n))=sum_{j=0}^d beta_j n^j modulo one. For the selected set S,

    ||d! beta_j r^j|| <= eta^(-C5) (R/N)^j,  1<=j<=d.       (11)

If R<=eta^(-C6), choose one r. Multiplication by r^d and d! in (11) immediately
gives a nonzero horizontal character whose magnitude and C-infinity[N] norm
are bounded by a fixed power of eta^(-1). This handles all small dyadic scales,
including R=1, without a recurrence lemma.

Otherwise |S|>=eta^C4 R and R is larger than any fixed inverse power required
in the recurrence argument below. Regard S as a subset of [ceil R]. Apply
published GT-orbits Lemma 4.5 to the polynomial d! beta_j r^j and the interval
of length at most 2 eta^(-C5)(R/N)^j centered at zero. Choose K large enough
that R<=2N^(2/3) and N>=eta^(-K) make this interval at most half the density
eta^C4. Lemma 4.5 yields a nonzero integer t_j of size <=eta^(-C7) with

    ||t_j (d!)^2 beta_j|| <= eta^(-C8) N^(-j).               (12)

The extra d! safely clears leading-coefficient conversion. Multiply psi by
the product of these nonzero integers and by (d!)^2. Equations (12) give
magnitude and C-infinity[N] norm <=eta^(-C9) for this single nonzero character.

### 5.3 Type II recombination and the constant-offset issue

Write the pigeonholed nonzero product character as psi1 plus psi2. Suppose
psi1 is nonzero; otherwise interchange the two coordinates. The coefficient
information is

    ||d!(beta_j r^j + beta'_j r'^j)||
         <= eta^(-C5)(R/N)^j.                               (13)

Choose one r' with at least eta^C4 R partners. For each j, (13) places
d! beta_j r^j in a short interval centered at -d! beta'_j r'^j. Apply the
same published Lemma 4.5 to that interval. The lemma permits an arbitrary
interval center. This proves (12), hence the same small character of g.

There is no assertion that r^j-r0^j=(r-r0)^j. The constant-center recurrence
argument avoids that invalid inference entirely. The lower bound
R>=N^(1/3)/4 ensures R exceeds the inverse density powers when K is large.

### 5.4 Contradiction to total equidistribution

If a nonzero horizontal character Psi has magnitude and C-infinity[N] norm
<=eta^(-C9), then for 1<=n<=c eta^(2C9+4)N its phase differs from Psi(g(0))
by at most 1/10. This follows by summing its binomial expansion; its constant
coefficient is subtracted, not assumed zero. Choose a Lipschitz, mean-zero
circle function that equals one on this arc, and compose it with Psi.
The resulting function has mean zero because a nonzero horizontal character
pushes Haar measure to circle Haar measure. The character's Lipschitz norm
is bounded by a fixed power of eta^(-1), using the adapted-basis metric bounds
in published GT Appendix A. Increase H beyond these exponents. The first
floor(c eta^(2C9+4)N) integers then violate total eta^H-equidistribution.
Increase K so this interval is nonempty. This proves the stated recombination
lemma, with both all-small-scale and product cases covered.

## 6. Explicit exponent bookkeeping for the analytic consequence

Use the separate norm-transfer lemma for dimensions m and 2m, taking the
smaller of its positive exponents kappa,sigma and shrinking kappa to <=1.
Its hypothesis is total zeta-equidistribution on [M], rationality and
progression modulus <=zeta^(-kappa), and zeta>=M^(-sigma). Its conclusion for
arbitrary intervals is O_H(M zeta^kappa). Abel summation gives an additional
factor log(2M) for a log(Nb) weight: every partial interval satisfies the same
unweighted bound, and integral dt/t<=log(2M). No short-interval ideal count
is used for this Abel step.

Let H,K be the recombination constants in Section 5. Choose

    a = 1/(4H),
    c = a*kappa/32,
    s = min(1/100, 1/(4aK), sigma/(12a)).                   (14)

For delta in [N^(-s),delta0(H,modulus)] suppose the shell sum were larger than

    C Q N L^7 delta^c ||F||Lip.                             (15)

Normalize ||F||Lip=1. If Q L^6 delta^c>=1, the elementary bound O(NL)
already proves (15) after increasing C. Otherwise Q<=delta^(-c) and
L<=delta^(-c/6). Apply Section 3 with epsilon=C Q L^6 delta^c, reducing C
to the appropriate fixed factor in (6). It yields density and normalized
amplitude at least a fixed constant times delta^(4c). For delta sufficiently
small these are at least delta^(5c), and a>5c.

If an extracted sequence were totally delta^a-equidistributed, norm transfer
would bound its sum by O(M delta^(a*kappa)L^e), e=0 or 1. This is smaller
than M delta^(5c), because a*kappa=32c and L<=delta^(-c/6). Its rationality
and modulus hypotheses hold since c<a*kappa. For I, M>=N^(1/3)/2; for II,
M=B>=N^(1/3)/4. Equation (14), after enlarging N0, ensures
delta^a>=M^(-sigma). Thus every extracted sequence fails total delta^a
equidistribution. Section 5 applies with eta=delta^a: its size hypothesis
N>=eta^(-K) follows from asK<=1/4. Its conclusion is failure of total
delta^(aH)=delta^(1/4)-equidistribution, contradicting original total delta
equidistribution. This proves (15).

All inequalities have strict exponent slack. The fixed cutoff delta0 absorbs
fixed H- and nilmanifold-dependent constants. For delta>=delta0 the trivial
O(NL) estimate gives (15) with an enlarged implied constant. This is why no
unstated dependence of an exponent on the fixed ray modulus is required.

### All dyadic scales and the full interval

Take exact real upper endpoints M_j=2^(-j)N. Keep shells with
M_j>=2 sqrt(delta) N; all discarded terms have norm <=2 sqrt(delta)N and total
absolute weight O(sqrt(delta) N L) by (2). There are no integer-rounding
differences of endpoints: each shell is exactly M_j/2<Na<=M_j.

On [floor M_j], the sequence inherited from [N] is totally 2sqrt(delta)
equidistributed. Indeed a progression of length >=2sqrt(delta)floor M_j has
length >=delta N for large N, and the original discrepancy bound delta is
stronger. The shell statement applies with this parameter. The original
progression is only intersected with the shell; Section 4 requires its modulus
bound, not a new lower length bound. Its rationality parameter remains Q.
The lower parameter hypothesis in (14) still holds after decreasing s once,
for example replacing it by s/4, since M_j>=N^(1-s/2).

Summing M_j<=2N gives the bound

    |sum_{Na<=N} Lambda(a)chi(a)1_P(Na)F(g(Na)Gamma)|
      <<_{H,m,d} Q N log(2N)^7 delta^(c/2) ||F||Lip.        (16)

For 1/N<delta<N^(-s/4), replace delta by delta^(s/8); total delta
equidistribution implies total delta^(s/8) equidistribution. This new parameter
is at least N^(-s/8), so the proved range applies, with exponent c*s/16
in (16). If delta<=1/N, the singleton progressions give
|F(g(n))|<=delta||F||Lip at every n, and the trivial O(NL) bound suffices.
This covers every delta in (0,1) with one positive exponent depending only on
m,d and the norm-transfer exponents. The progression can have any interval
length, provided its common difference is at most Q.

## 7. Source-verifiable dependencies and corrections

Published parents cached in `work/quartic-version5-release/sun-proof/sources/`:

1. Green--Tao, *The quantitative behaviour of polynomial orbits on
   nilmanifolds*, Annals 175 (2012), 465--540. Theorem 2.9 on p480 gives the
   character after failed equidistribution. Lemma 4.5 on p490 gives strong
   polynomial recurrence. Appendix A supplies the character metric bounds.
   Local text: `GT-orbits-published.txt`, lines 747--753, 1299--1320.
2. Green--Tao, *The Mobius function is strongly orthogonal to nilsequences*,
   Annals 175 (2012), 541--566, Section 3, pp548--553, supplies the published
   Type I/II architecture. Local text: `GT-mobius-published.txt`, lines312--584.
   We prove the ideal extraction ourselves and use Lemma 4.5 above instead of
   an unexplained reuse of those integer calculations.
3. Frei--Tinkova v3, local `FT-v3.tex`, lines1810--2228, is the attributed
   methodological source, not an assumed theorem in this proof. The proof
   here fixes its missing conjugates, dyadic-range mismatch, and asserted
   lower lengths of progression intersections. It also avoids estimating
   ideals on a short progression by the number of rational integers in it.

The present result is a mean-zero ideal-von-Mangoldt estimate. By itself it
does not prove the ray-character main terms, major-arc factorization, the
inverse-theorem transfer to the required cubes, or the manuscript's final
prime-pattern theorem. Those steps need their own completed arguments before
the FT dependency can be removed from the overall construction.

## 8. Ordinary-prime corollary for the centered weight

The same power-form conclusion holds for E=Q, chi=1 and ordinary von Mangoldt
Lambda(n), with a positive exponent c_Q depending only on m,d. This does not
require an unstated extension of Green--Tao's Mobius theorem to Lambda.

Proof: replace ideals throughout Sections 1--3 by positive integers. Then
a_Q(n)=1 and the convolution identity (4) is the ordinary integer identity,
with exactly the same coefficient and moment bounds (or better ones). The
recombination proof in Section 5 is unchanged.

The norm-transfer input is now elementary from total equidistribution. For
any subprogression J of [X], if |J|>=zeta X, total zeta-equidistribution gives

    |sum_{n in J} F(g(n))| <= |J| zeta ||F||Lip
                            <= X zeta ||F||Lip.

If |J|<zeta X the same upper bound follows from ||F||infinity<=||F||Lip.
This covers every truncated progression with no lower-length or modulus
restriction. Abel summation supplies the log weight, and the identical
argument applies to F tensor conjugate(F) on the product nilmanifold.
Thus Section 6 applies with any sufficiently small fixed kappa,sigma, giving

    |sum_{n<=N} Lambda(n)1_P(n)F(g(n))|
       <<_{m,d} Q N log(2N)^7 delta^c_Q ||F||Lip.             (17)

The estimate holds for arbitrary interval progressions P of common difference
at most Q and all delta in (0,1). Shrink c_Q to be less than 1/4.

Let Lambda'(n)=log n on rational primes and zero otherwise. The contribution
of proper prime powers to (17) is at most C sqrt(N)log(2N)^2 ||F||Lip: for
each k>=2 there are at most N^(1/k) integers p, and k<=log_2 N. If delta>1/N,
this is bounded by the right side of (17), since delta^c_Q N>=N^(1-c_Q).
If delta<=1/N, the singleton total-equidistribution estimate
|F(g(n))|<=delta||F||Lip gives (17) for Lambda' directly by the elementary
bound sum_{n<=N}Lambda'(n)<=N log(2N). Hence (17) also holds with Lambda'.

This corollary supplies the ordinary-prime mean-zero term in a centered
W-tricked weight. The separate factorization argument must still track the
affine reparameterization and the resulting progression modulus Wq; no
uniform-in-W assertion about a fixed Dirichlet character has been inserted.
