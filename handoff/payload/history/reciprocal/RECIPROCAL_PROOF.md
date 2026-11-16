# Reciprocal-coordinate logarithms and the precision budget

This is a proposed arithmetic source change. It is not an equal-output
replacement for the pinned logarithm polynomial. No source pin is authorized
by this file or by the accompanying scripts. An independent mathematical
review, source compilation audit, new quadratic lift, and full expansion
remain required.

The baseline is the verified wave11 quartic with 13,609 total variables. Its
source still uses precision 64,24 anchor squarings, and scalar order 48. All
of those parameters remain unchanged in the first proposed experiment.
The beta-only precision 16 variant is a separate second experiment. The
older52/13/26 proposal is included only for comparison.

## Fixed inputs and source locations

Use the exact existing curve and generator theorem:

    K = Q(sqrt(2)), d = 3-sqrt(2), D=d^2=11-6sqrt(2),
    E: y^2=x^3-Dx, 2E(K)=Z P_*.

The unchanged arithmetic proof supplies the five-contact height constant

    H = 2(4608^165888+6^100) (product_{p<=76176} p)^24 +128,
    log2(H)<4783227,

the height estimate h(a)<=H M_5(a)^24, the index lower bound
h(x(nP_*))>=n^2-6, the 41-contact prime pattern, the scalar estimate
h(beta)<=H sqrt(abs(s)), and the Lucas growth lemma. No external theorem is
added here. This review does not independently reprove those unchanged
theorems.

In the current manuscript, the relevant section labels are
`hyp:o8-height`, `eq:o8-indexheight`, `eq:o8-anchor-bound`,
`eq:o8-contacts`, `eq:o8-proxies`, `eq:o8-scalarheight`,
`lem:o8-lucas`, `subsec:o8-common-J-proof`, and `subsec:o8-root-proof`.
The original source builder still places the logarithm at lines 195–227,
the point chart at 253–272, the comparison at 365–384, the scalar orders at 436,
and the module construction at 485. The old source digest remains
6e68a9d39573279e894e29d8913b5ade932aa6526d28a2d40bc713c1cca934a2.

## Exact curve identity

Write f=1/x and z=-x/y. For a nonzero chart point the inverse and parameter
equations give x,y,f,z nonzero. The curve equation gives the exact identity

    z^2 = f/(1-D f^2),       f=z^2(1-D f^2).

On the formal branch, f=z^2+O(z^6). Put w=D f^2. Then

    D z^4 = w/(1-w)^2.

Define rational numbers a_j by

    a_0=1, a_1=-2/5,
    a_j=((4j-5)/(4j+1)) a_(j-1)  for j>=2,

and the formal power series G(w)=sum_{j>=0} a_j w^j. Its defining equation is

    4w(1-w) G'(w)+(1+w)G(w)=1-w.                 (1)

Coefficient comparison proves this: the constant term is a_0=1; the
w coefficient is 5a_1+a_0=-1; all later coefficients are
(4j+1)a_j-(4j-5)a_(j-1)=0. Conversely these equations uniquely determine G.

Differentiating the exact f identity gives

    z dw/dz = 4w(1-w)/(1+w).

Consequently (1) implies

    d(zG(w))/dz = (1-w)/(1+w)
               = (1+4D z^4)^(-1/2).

The last square root is the formal one with constant term 1. Both sides have
the indicated constant term, and their squares agree because
1+4Dz^4=(1+w)^2/(1-w)^2. The normalized formal logarithm has exactly this
invariant differential and zero constant term. Therefore

    log_E(z) = z G(D f^2).                       (2)

This is a formal identity on the curve, not an equality of the two finite
truncation polynomials in arbitrary independent z,f.

An independent formula useful for checking coefficients is

    a_j = sum_{i=0}^j (-1)^i binom(1/2,i)
          binom(2(j-i),j-i) / [4^(j-i)(4(j-i)+1)].

Indeed G(w)=sqrt(1-w) sum_{k>=0} binom(2k,k)w^k/[4^k(4k+1)], which also
satisfies (1). The producer uses the recurrence; the independent circuit
checker uses this binomial-convolution formula.

## Finite truncation and every selected prime

For a required precision e, put m=ceil(e/4), J=m-1, and define

    G_J(w)=sum_{j=0}^J a_j w^j,
    L_e(z,f)=z G_J(D f^2).

The proposed values are e=64,16 and, in a separate experiment,52 or 13.
Thus m<=16 and J>=3. Let p>76176 be any selected split good prime, with
v_p(p)=1, and let r=v_p(z)>=1. The formal curve identity gives
v_p(f)=2r and v_p(D f^2)=4r, since D is a p-unit.

We now bound the entire infinite tail, including coefficients with p in
their denominators. For j>=1 the denominator in the recurrence expression
for a_j divides 5 product_{k=2}^j(4k+1), which divides (4j+1)!. Hence

    v_p(a_j) >= -v_p((4j+1)!) >= -(4j+1)/(p-1).

If 4j+1<p, the sharper bound v_p(a_j)>=0 holds. If 4j+1>=p, then
j>=19044; in particular3j>=4m. Also (4j+1)/(p-1)<=j, so

    v_p(a_j w^j) >=4jr-j >=4mr,

because (4j-4m)r>=j. In the first case the same conclusion holds directly
for every j>=m. These valuations tend to infinity, which proves convergence
and the tail estimate

    v_p(G(w)-G_J(w)) >=4mr.

By (2) and formal logarithm isometry, log_E(z)/z is a unit. Thus

    L_e(z,f)/log_E(z) belongs to 1+p^(4m) Z_p,
    and hence to 1+p^e Z_p.                        (3)

The old primary-point formal tests therefore suffice without being
strengthened. At e=64, use16 coefficients; the error after multiplication
by z has valuation at least65r. At e=16 or 13, use4 coefficients and obtain
valuation at least17r. At e=52, use13 coefficients and obtain at least53r.
No precision is inferred merely from polynomial degree in f.

## Global nonvanishing over the rational coordinate field

This replaces the old finite-logarithm nonvanishing argument and is required
when the private inverse is removed. Let nu be the rational exponent-of-two
valuation, and put

    v(a+b sqrt(2)) = (1/2) nu(a^2-2b^2)
                  = min(nu(a),nu(b)+1/2).

The equality follows from opposite parity of 2nu(a) and 1+2nu(b). Norm
multiplicativity and the rational valuation inequality show that v is a
valuation with values in (1/2)Z, and a finite sum with a unique least
valuation is nonzero. Here v(D)=0.

Every a_j for j>=1 has v(a_j)=1: a_1=-2/5 and every recurrence numerator
and denominator is odd. Let J>=2. We claim

    G_J(D f^2) !=0 for every f in K.               (4)

If f=0 this is 1. If t=v(f)>=0, the constant term has valuation0 and
every other term has valuation1+2jt>=1. If t<0, then t<=-1/2.
Among nonconstant terms the valuation1+2jt strictly decreases with j,
and the last one has valuation1+2Jt<=1-J<0. It is also below the constant
term. This proves (4). All proposed truncations have J>=3.

It follows that L_e(z,f) is nonzero exactly when z is nonzero, even away
from the curve. The retained old chart has xf=1 and yz=-x, which force
z!=0. The already accepted reduced chart has pz=-1 and does the same.
Consequently every old logarithm-inverse removal can be justified for the
new polynomial by (4), after its exact output identity is independently
checked. The old checker, which expects a polynomial in z alone, must
not be reused by altering just its coefficient list or source hash.

At2 this proof is global and does not assume good reduction. At3 and 17,
the pole-completeness argument is unchanged: selected contact primes are
local squares there, and multiplying them by the norm-root square preserves
that condition. No new integrality condition for the private comparison
points at these small primes is imposed. At the selected large primes,
the separate estimate(3) supplies exactly the approximation used by the
arithmetic comparison argument.

## Soundness and completeness of the primary comparisons

Retain the same points, shifts, contacts, common root approximation and
formal tests. At an odd contact outside the exceptional set, the alternate
tests give

    h==4 mod p^K, m_i==4n_i mod p^(e_i),

where K=64 initially, e_1=q is the beta precision, and e_2=e_3=e_4=K.
Here q is 64 or 16. The shared H alternate test still has orderK, so h is
a p-unit. Formal logarithm homomorphism gives log(X_i)/log(X_0)=m_i/h.
Equation (3) then gives integrality and the same congruence for the new
finite-logarithm ratio. The proxy tests imply

    beta==n mod p^q,
    (xi,tau,zeta)==(s,t,z) mod p^64.               (5)

For completeness keep the same orientations and shared integer j, and
choose each private h_p with

    h_p==0 mod d_(p,1), h_p==4 mod d_(p,2),
    h_p==4 mod p^(64+v_p(j)).

The original gcd and p-unit arguments give compatibility. Avoid0,4,-4,
so all points and subtraction denominators are nonzero. The ratio estimate
(3) proves the required high and low tests. Choose the common theta last
to meet the finitely many coefficientwise valuation requirements. The
unchanged norm and pole completeness arguments finish the assignment.
All inverses are defined by the original nonzero chart conditions and(4).

Changing to q=16 changes exactly two field tests: the beta primary ratio
and its alternate shift ratio. In existing field order the list becomes

    [1]*11 + [16,64,64,64,64,16,64,64,64].

The corresponding rational list, including the root-error test, is

    [1]*23 + [16]*2 + [64]*8 + [16]*2 + [64]*6.

The shared denominator always uses precision 64, never16. There are still
five modeled primary points, five shifts, and 41 contacts. The scalar batch
remains[1,1,1,1,48,48].

## Final arithmetic inequalities

First take K=64 and the original24-squaring anchor. It gives

    a=abs(s)>=3^(2^23-1)>(20H)^2,

using log2(3)>3/2 and
3(2^23-1)=25165821>4(5+4783227)=19132928.
Let B=max(abs(n),abs(s),abs(t),abs(z)) and
Delta=t^2-s(s-2)tz+(s-2)^2z^2-1.

The first contradiction uses only the three high congruences in (5), at
every one of the 41 contacts. In particular it still controls all four
points' abscissas, including A=nP_*. If Delta!=0, the unchanged shared-height
argument gives

    B^2-6 <7H abs(Delta)^(3/8)<14H B^(3/2),
    hence B<(14H+6)^2<=(20H)^2.

This contradicts B>=a. Therefore Delta=0, and Lucas growth gives
log(B)>a-3. No use of beta precision 64 occurred in this first step.

If beta!=n, set N=abs(num(beta-n)) in lowest terms. At beta precision q=16,
integrality and congruence give the sixteenth-power radical divisibilities,
so

    B^2<7H N^(3/2)+6,       N<=2 exp(h(beta)) B.

Since B,H>=1, this implies

    B^(1/2)<(7*2^(3/2)+6)H exp(3h(beta)/2)
           <32H exp(3h(beta)/2).

The unchanged scalar bound gives h(beta)<=H sqrt(a)<a/20. Also
log(32H)<a/20. For example20log(40H)<(20H)^2 for H>=1, as follows by
checking H=1 and differentiating the difference. Thus

    log(B)<2log(32H)+3h(beta)<a/4<a-3,

because a>4. This is the second contradiction. Hence beta=n is an integer,
and rational X with X^2=beta-2 is an integer. The completeness construction
is unchanged except for evaluating the new finite polynomials and assigning
their ratios. The old choice of h_p is more than sufficient for q=16.

For uniform q=64 the original second contradiction applies without any
parameter change. Thus the first experiment changes the approximation
polynomial only; the second additionally weakens the beta tests to 16.

For comparison, K=52,q=13,A=26 is also feasible. The general first bound is

    B^(2-96/K)<24H,

so it suffices that a>(24H)^(K/(2K-96)). The26-squaring lower logarithm is
50331646.5>(13/2)*4783232=31091008. For every q>=13 the second bound is

    log(B)<[q/(2q-24)]log(40H)+[24/(2q-24)]h(beta)
          <[(q+24)/(20(2q-24))]a<=37a/40<a-3,

using a>40. These are the exact former52/13 inequalities. They remain
valid for the reciprocal-coordinate truncation by (3). Precision52 alone
does not shorten the new fused G circuit, so there is no predicted gate
advantage over64 for this implementation. At K<=48 or q<=12 the respective
growth exponents cease to give an upper bound, irrespective of a larger
anchor. This identifies a limit of this proof, not extra rational solutions.

## Optional algebraic removal of private primary z coordinates

This is separate from the arithmetic change above. It is an exact rational
equivalence within the new reciprocal-logarithm source.

After the two accepted chart reductions, a private primary point has
coordinates u,v,p,z,f,x and equations

    f=u^2, v^2+df=1, p^2=x-Df, xf=1, pz=-1,
    y=xp as the expression used by its subtraction chart.

Put G_i=G_(J_i)(D f_i^2), where all J_i>=2. These are globally nonzero by (4).
Remove z from each of the five private primary charts and remove pz=-1.
Introduce a shared field pair Lambda and retained ratio pairs C_i with

    Lambda*p_0=G_0,
    A_i=C_i*p_i,      A_i*Lambda=G_i  for 1<=i<=4.  (6)

Every last G definition is fused into its equation in (6): if G_i=F_i is
its quadratic output expression, use Lambda*p_0=F_0 or A_i*Lambda=F_i
without allocating that final G pair. All products and resulting rows
remain quadratic. The four proxy differences are still C_i minus the
same rational proxies; every alternate test and subtraction chart is retained.

For the forward map, keep the point coordinates and C_i, set
Lambda=-L_0=G_0/p_0, and A_i=C_i*p_i. Since z_i=-1/p_i, the old ratios give
C_i=L_i/L_0=G_i/(p_i Lambda), which proves(6). For the reverse map,
Lambda*p_0=G_0!=0 gives Lambda,p_0 nonzero. If p_i=0, then A_i=0 and
A_i Lambda=G_i contradicts(4). Thus every p_i is nonzero. Set

    z_i=-1/p_i, y_i=x_i p_i,
    L_i=z_i G_i, and the former inverse of L_0 to 1/L_0.

Equation(6) gives precisely C_i=L_i/L_0. The reduced charts restore their
original charts by h_i=u_i p_i and w_i=u_i p_i/v_i. The denominator v_i is
nonzero: f_i p_i^2=v_i^2(1+d f_i), and both f_i,p_i are nonzero. This also
proves that allowing the otherwise excluded p_i=0 torsion cases does not
enlarge the solution set. No good-reduction or rank theorem is needed for
this algebraic equivalence.

Every removed primary z component must occur only in its chart inverse
equations and old logarithm circuit. Every removed G output component must
have exactly its defining and ratio uses, or all its other uses must be
substituted and remain quadratic. The shared source uses the primary z
coordinates only in those locations; a new checker must repeat the complete
incidence scan on the actual candidate. Difference parameters z(Y_i) and
the common auxiliary z(J) are retained. Root point parameters are retained.

The optional compressed-source compiler constructs precisely these primary
charts and equations. It supplies y=xp directly as a quadratic expression
to the subtraction row, which becomes x(lambda-p)-nu=0. All other
subtraction equations and their nonzero-abscissa guards are unchanged.

## Fused evaluation and coefficient control

For16 or 13 coefficients, form field targets

    w=D f^2, w2=w^2, w3=w2*w, h=s*w3^2,
    t=(h/s) sum_{j=12}^{15}(a_j/a_12)w^(j-12)
      +(a_10/a_12)w3*w+(a_11/a_12)w3*w2,
    p=(h/s)[(a_12/a_6)t+sum_{j=6}^9(a_j/a_6)w^(j-6)]
      +sum_{j=0}^5(a_j/a_6)w^j.

Set absent coefficients to zero in the 13-term case. Each w^4,w^5 term is
represented as w3*w or w3*w2. Hence all defining rows are quadratic, and
G=a_6 p. A following multiplication by z gives the plain logarithm. In
the compressed version the quadratic expression a_6 p is inserted directly
into(6), so p is not allocated. The scale s is a fixed nonzero rational
constant; the probe tries1,2,3,4 independently.

This construction forms w directly. It does not leave D as a linear
substitution in every later row, which would unnecessarily enlarge those
coefficients. Useful exact checks on the normalization are

    a_6=-418/16575,       a_12/a_6=1195701/3387461,
    a_10/a_12=735/559,    a_11/a_12=49/43,
    a_13/a_12=47/53,     a_14/a_12=799/1007,
    a_15/a_12=43945/61427.

The lower a_j/a_6 coefficients have denominators dividing418. The lcm of
the displayed p-row denominators for s=1 is 128723518. Its constant
coefficient after clearing denominators is-5104287825. These values are
small enough to justify a bounded exact probe, not a claim about the final
quartic coefficient bound. The independently expanded probe and complete
eventual quartic must still enforce the strict2^80 cap.

For four coefficients, form w=D f^2, w2=w^2, and
G=1+a_1w+a_2w2+a_3w2*w. This is a quadratic expression. Binding G and
multiplying by z uses four field pairs; the compressed version needs only
w,w2 before(6).

## What is and is not proved

Proved here, subject to independent review: the exact curve/formal identities,
all selected-prime tail estimates, global nonvanishing, the two arithmetic
contradictions for 64/16/24, unchanged completeness, and the optional exact
chart/ratio solution maps. No new unpublished assumption is used.

The source transformation does not preserve a finite logarithm's output as
a polynomial in independent variables. Both arithmetic sources define the
same rational input set by separate soundness and completeness proofs.
An old rational solution first gives integral X; the destination completeness
construction rebuilds a destination solution with that X. In reverse, apply
the same procedure using the original source. If a fully specified effective
map is desired, enumerate rational witness tuples in a fixed height order
and choose the first destination solution. Completeness proves termination.
These are not claimed to be rational-function maps in the old witness tuple.
Only the optional compressed chart step has the direct rational maps in (6).

Not established: acceptance of this proof by an independent reviewer,
execution of any new script, the new source counts, actual final variable
savings, or the final coefficient bound. The existing source hash is not
changed and the existing arithmetic certificate is not reassigned.
