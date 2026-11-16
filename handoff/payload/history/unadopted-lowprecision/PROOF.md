# Exact low-precision reciprocal polynomials

This packet concerns finite polynomial identities only. It makes no claim
that a Diophantine source may use precision 12, 40, 44, or 48. In particular,
it does not assume acceptance of a revised height constant or precision
budget. There is no changed source pin or measured whole-quartic saving.

Let w=D f^2 in Q(sqrt(2)), with D=11-6sqrt(2), and let

    a0=1, a1=-2/5, aj=((4j-5)/(4j+1))*a(j-1).

For e in {12,40,44,48}, the exact target is

    G_e(w) = sum(a_j w^j, j=0,...,e/4-1).

Every field equality is interpreted as two rational coordinate equalities.
The field product is (a,b)*(c,d)=(ac+2bd,ad+bc), so a quadratic expression
in previously allocated field pairs gives quadratic rational residuals.

## Three coefficients

Allocate only w=D f^2. Return the quadratic expression

    G_12 = 1+a1*w+a2*w^2.

No separate w^2 coordinate is needed. If a consumer needs a bound G pair,
allocate it with its two quadratic defining equations. Otherwise a field
product P*Q=G_12 can be imposed directly in two quadratic equations.

## Ten coefficients with a block of three

Allocate w, w2=w^2, w3=w2*w, and a scaled pair U. Before scaling, set

    U0 = a3+a4*w+a5*w2
         + w3*(a6+a7*w+a8*w2+a9*w3).
    G_40 = a0+a1*w+a2*w2+w3*U0.

Expanding U0 gives coefficients a3 through a9 in degrees zero through six.
Multiplying by w3 and adding the low terms gives exactly G_40.

The producer allocates U=(s/a_k)U0 for k=3 or 6 and s=1 or 2. The returned
expression uses (a_k/s)w3*U, so the output is unchanged. Both a_k and s are
nonzero rational constants. This is an invertible rational rescaling of
one private field pair and introduces no nonvanishing assumption.

## Eleven or twelve coefficients with blocks of three

Allocate w, w2, w3, w6=w3^2, and U=(s/a_k)U0, where

    U0 = a3+a4*w+a5*w2
         +w3*(a6+a7*w+a8*w2)
         +w6*(a9+a10*w+a11*w2).
    G = a0+a1*w+a2*w2+(a_k/s)*w3*U.

For eleven coefficients set the absent a11 term to zero. All definitions
and the final expression remain quadratic in allocated pairs.

## Eleven coefficients with four allocated pairs

The power basis w,w2,w4,w5 is smaller than the preceding block circuit:

    w2=w^2, w4=w2^2, w5=w*w4.

Every exponent from zero through ten is a sum of two elements of
{0,1,2,4,5}. Therefore the exact expression

    a0+a1*w+a2*w2+a3*w*w2+a4*w4+a5*w5
      +a6*w2*w4+a7*w2*w5+a8*w4^2+a9*w4*w5+a10*w5^2

is quadratic in these four pairs and equals G_44. Omitting its a10 term
also gives a four-pair alternative for G_40.

For G_48 the five-pair power basis w,w2,w3,w5,w6 suffices. Allocate w5=w2*w3
and w6=w3^2. The set {0,1,2,3,5,6} has pairwise sums covering every exponent
zero through eleven, so every term of G_48 is available as a quadratic
expression. This packet makes no minimality claim for either construction.

The power-basis trials allocate scaled coordinates s_j*w^j. They use
s_j=1, s_j=a_j, or s_j=1/denominator(a_j), and always divide by s_j when
forming the logical power expression. Every s_j is nonzero. These are
again exact private-coordinate rescalings; the independent checker verifies
the returned polynomial instead of trusting the scaling description.

## Structural target counts

These counts refer to rational internal targets, with the two f inputs
already supplied. They are structural predictions until the packet runs.

| Precision | Direct quadratic output | Bound G output |
| --- | ---: | ---: |
| 12 | 2 | 4 |
| 40, either scheme | 8 | 10 |
| 44, power basis | 8 | 10 |
| 44, block scheme | 10 | 12 |
| 48, either scheme | 10 | 12 |

A direct output is intended for substitution into a following quadratic
field equality, not for discarding an unconstrained G variable. A plain
logarithm z*G generally needs a bound G first unless its particular consumer
has another verified fusion identity.

## Independent verification and coefficients

`check_lowprecision.py` does not import this producer or the source builder.
It computes coefficients from

    G(w)=sqrt(1-w)*sum(binomial(2k,k)w^k/[4^k(4k+1)], k>=0),

expands every acyclic rational-coordinate definition into the two input
variables, and compares both outputs exactly. This proves the finite
polynomial identity for arbitrary f in Q(sqrt(2)); no curve equation is used.

Every candidate also contains two generic field-product equations P*Q=G.
The checker reconstructs these from four fresh external input coordinates
and the supplied output expression. It expands the squared internal rows
alone and again with those final two equations. This includes the output
denominators that an internal-only direct-circuit check would miss.

The strict 2^80 bound is reported for each actual expansion. A profile that
exceeds the bound remains an exact polynomial circuit but is not an eligible
bounded candidate. Neither isolated expansion proves the whole-source bound:
row overlaps, repeated instances, and later substitutions must still be
checked in the complete final artifact.
