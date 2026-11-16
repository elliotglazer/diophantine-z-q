# Independent arithmetic review of beta precision sixteen

Reviewed by the unit-scale search agent on 2026-11-05. This is a static
review of the proposed K=64, q=16, anchor-squarings=24 change and its consumers.
No source package, arithmetic check script, quadratic lift, or final expansion
was executed for this review.

Conclusion: the beta-only precision sixteen change is sufficient for the
existing arithmetic argument. I found no incorrect inequality or missing
precision consumer in that change. The shared logarithm denominator, its
alternate test, the other three proxy comparisons, the 24-squaring anchor,
and scalar order 48 must remain as specified. The proposed compiler does
preserve those parameters by static inspection.

This conclusion uses the existing curve/rank, five-contact height, index-height,
scalar-height, prime-pattern, and Lucas inputs. The separate guards review
covers the new exact reciprocal-log identity, global nonvanishing, and optional
compressed-chart reconstruction. I checked how the proposed local estimate
is consumed, including the estimate's tail bounds. I do not treat a new source
hash alone as a proof of the arithmetic change.

## Reviewed versions

| File | SHA256 |
| --- | --- |
| `RECIPROCAL_PROOF.md` | `be5b08dd9ded743606d5c6a5fc869c4e9764575da49e5d80af13aca09950a98a` |
| `reciprocal_kernel.py` | `c4e94463cd59a2418a6502ac7cdcfd713edf9bc1134fe0b4d4bd84700983b304` |
| `build_reciprocal_source.py` | `d9ec8f4788882f37f3a0b7746f8d19c28968f7bf3f09cc06addab92f787098f6` |
| `degree8-original/source/archive_build.py` | `c7ef798894a106e3c6b02816583be2b6e966e4e701f73ee670c9a0de52a70912` |
| `diophantine_zq.tex` | `b6c125899af3a8f8ba139abad332b8f98805967bab25b0dcf6d9651997f614b7` |

The paths for the last two files are inside the research repository
`work/quartic-variable-search-20261105/remote-repo`.

## Exact order assignment

Use mathematical indices X_0 for H and X_1,...,X_4 for the points comparing
against A,S,T,Z. The source labels the latter `X0`,...,`X3`; this naming
offset does not change the order of the arguments.

| Field-expression positions, zero based | Expressions | Required orders |
| --- | --- | --- |
| 0 through 4 | f(X_0),...,f(X_4) | all 1 |
| 5 | f(J conjugate) | 1 |
| 6 through 10 | f(Y_0 conjugate),...,f(Y_4 conjugate) | all 1 |
| 11 | L_16(X_1)/L_64(X_0) minus beta | 16 |
| 12 through 14 | remaining three primary ratios minus xi,tau,zeta | all 64 |
| 15 | z(Y_0 conjugate)/z(J conjugate) | 64 |
| 16 | z(Y_1 conjugate)/z(J conjugate) | 16 |
| 17 through 19 | remaining three alternate ratios | all 64 |

Each field expression supplies its two existing rational tests. With the
root-error test first, the rational-order list is exactly

    [1]*23 + [16]*2 + [64]*8 + [16]*2 + [64]*6.

The eight consecutive high-order rational tests include the three high
primary ratios and the H alternate ratio. This is the critical distinction
from lowering the shared denominator or all alternate tests to sixteen.

`reciprocal_kernel.install` sets `PELL_PRECISION=64` and
`ANCHOR_SQUARINGS=24` for this experiment. Its batch wrapper replaces only
the `q_batch41` orders. Its plain primary loop uses precision sixteen only
for the first numerator; the denominator explicitly uses `high`. The
compressed loop uses the same indexed choices for G and the high-order
shared denominator equation. The recorded field-order list agrees with
the actual field-expression order and rational batch orders.

In the original builder, the only actual logarithm evaluations are the one
denominator and four numerators in `make_multi_comparison`, lines 377-378.
The default precision in the old method signature is not an additional
consumer because those calls pass precision explicitly. `make_root` has no
logarithm evaluation. It retains the same common proxy tuple and passes it
to all 41 comparisons, which is needed below when passing to one common
integer Delta.

## Local estimate and mixed ratios

At each selected split good prime p>76176, the unchanged order-one f tests
put all primary points in the formal group. In particular r=v_p(z) is an
integer at least one and v_p(f)=2r. Since D has norm 49, D is a unit there.
Thus w=D f^2 has valuation 4r.

The recurrence denominator divides (4j+1)!, so the proposed estimate
v_p(a_j) >= -(4j+1)/(p-1) is valid. For 4j+1<p the coefficient is integral.
For 4j+1>=p, j>=19044; since m is at most 16, 3j>=4m. Also
(4j+1)/(p-1)<=j. Consequently

    v_p(a_j w^j) >= 4jr-j >= 4mr

for every omitted j>=m. The same lower bound in the integral-coefficient
case follows from j>=m. These lower bounds tend to infinity. Therefore the
whole infinite tail, including terms with nonunit denominators, has the
claimed valuation. Assuming the exact reciprocal-log identity, multiplication
by z and division by the formal logarithm give relative errors in
1+p^(4mr) Z_p, hence in 1+p^e Z_p. Four coefficients suffice at e=16,
and sixteen coefficients suffice at e=64. No stronger formal-point condition
is required.

Let e_1=16 and e_2=e_3=e_4=64. The alternate tests and formal isometry give
v_p((m_i-4n_i)/j)>=e_i and v_p((h-4)/j)>=64. Since j is a nonzero integer,
these imply m_i=4n_i mod p^e_i and h=4 mod p^64. Thus h is a p-unit and
m_i/h is integral. Write the relative truncation errors as u_i in
1+p^e_i Z_p and u_0 in 1+p^64 Z_p. Then

    L_e_i(X_i)/L_64(X_0) = (m_i/h) (u_i/u_0)
                         = n_i mod p^e_i.

This also proves integrality of each finite-logarithm ratio. The primary
tests therefore give beta=n mod p^16 and
(xi,tau,zeta)=(s,t,z) mod p^64, with all proxies p-integral. The high
denominator's error does not reduce any high numerator to precision sixteen.

## First contradiction: unchanged precision sixty-four

The source root equation is the Lucas polynomial in xi,tau,zeta; beta
does not occur in it. At every one of the 41 raw contacts, the three high
proxy congruences give p^64 dividing the integer

    Delta = t^2-s(s-2)tz+(s-2)^2 z^2-1.

The original passage from a normalized contact to an odd raw contact is
independent of which coordinate target produced that contact. Hence, if
Delta is nonzero, the sixty-fourth power of every relevant contact radical
divides Delta. This includes the contact radicals used for the abscissa of
A=nP_*. It is not necessary to know beta=n modulo p^64 to bound that
abscissa. Every batch, including those arising from A's coordinates, still
contains the same three high proxy tests.

The retained shared-height theorem with exponent 24/64=3/8 therefore
bounds all four points. For B=max(|n|,|s|,|t|,|z|), the unchanged bounds give

    B^2-6 < 7H |Delta|^(3/8) < 14H B^(3/2).

Here |Delta|<5B^4 and 7*5^(3/8)<14. Since B>=1, division by B^(3/2)
gives sqrt(B)<14H+6, hence B<(14H+6)^2<=(20H)^2 for H>=1.

The 24-squaring anchor still gives a=|s|>=3^(2^23-1)>(20H)^2. Its
numeric comparison is exact:

    3(2^23-1)=25165821 > 19132928=4(5+4783227).

Together with log2(3)>3/2 and log2(20)<5, this proves the stated strict
anchor bound. It contradicts B>=a, so Delta=0. The nonzero chart point Z
still gives z!=0, and a>=7 holds. The existing Lucas lemma thus gives
log B>a-3. No beta precision occurs in this first contradiction.

## Second contradiction: precision sixteen is enough

Suppose beta differs from n and let N be the positive absolute reduced
numerator of beta-n. Local integrality and beta=n mod p^16 imply p^16|N
at each relevant contact prime. The same shared-height theorem, now with
exponent 24/16=3/2, gives

    B^2 < 7H N^(3/2)+6,
    N <= exp(h(beta))(1+|n|) <= 2 exp(h(beta)) B.

After substituting the second inequality and dividing by B^(3/2), use
B>=1, H>=1, and h(beta)>=0 to obtain

    sqrt(B) < (7*2^(3/2)+6)H exp(3h(beta)/2)
            < 32H exp(3h(beta)/2).

The final numerical inequality is strict; for example sqrt(2)<3/2 makes
7*2^(3/2)+6<27<32. Taking logarithms therefore gives

    log B < 2 log(32H)+3h(beta).

The scalar batch is unchanged. Its order-48 parameter ratio still yields
M_5(beta)^48|s, and the original height bound still gives
h(beta)<=H sqrt(a)<a/20. Also log(32H)<a/20: for H>=1 the function
400H^2-20log(40H) is positive at H=1 and has derivative 800H-20/H>0.
Thus 20log(32H)<400H^2<a. It follows that

    log B < a/4 < a-3,

where the last inequality follows from a>4. This contradicts Lucas growth.
Therefore beta=n is integral, and the unchanged reduced-denominator argument
for X^2=beta-2 makes rational X integral. All inequality directions and
strictness needed by the contradiction are correct.

## Other consumers and completeness

The manuscript's norm-tree argument, lines 8079-8117, accepts arbitrary
positive leaf orders. Grouping the new leaves by increasing order remains
within that argument. Its constant all-left leaf remains unchanged, so odd
raw contact valuation still implies positive contact valuation and each
rational test has valuation at least its assigned order. The argument is
not restricted to a list having only orders one and sixty-four.

The common-root argument, lines 8466-8483, chooses theta after all field
tests and accepts an individual order k for each expression. It applies
unchanged to the mixed list. Its converse also transfers each pair of
rational tests to the selected field place at the corresponding order.

For completeness, retain the original shared j and each private h_p with
h_p=4 mod p^(64+v_p(j)). This still supplies every alternate condition,
including the two now-weaker rational tests for A's alternate expression.
Set the proxies to the integer indices. The high and low relative-error
estimates above then supply the primary conditions. The original exclusions
h_p not in {0,4,-4}, common orientations, and choice of theta last are
unchanged. Normalized leaves at the positive prime contacts are integral,
so the same norm-root and parity-completeness arguments apply.

The scalar construction at manuscript lines 8496-8537 and builder lines
418-421 and 485 uses f(J_0), f(S), z(S)/z(J_0), with orders
[1,1,1,1,48,48]. It neither uses the finite logarithm nor reads the beta
comparison precision. The compiler wrapper preserves that separate batch.
The anchor at manuscript lines 7890-7909, builder lines 303-311, and shared
squaring chain at lines 443-445 likewise remains at 24 squarings. The curve,
point doubling, contacts, root equation, and four common proxies are unchanged.

The affected manuscript statements are its uniform-order comparison display
and `eq:o8-proxies`, the mixed-ratio portion of `subsec:o8-common-J-proof`,
and the second contradiction. They must be stated with e_1=16 and the other
e_i=64 for the new source. The first contradiction, shared-height theorem,
scalar bound, anchor, and completeness structure remain valid as above.
The current uniform p^64 statement for beta is not claimed for the new
source. Other manuscript polynomial constructions are outside this change.

## Scope of acceptance

This review supports the arithmetic precision budget 64/16/24 and verifies
its source-level order assignment by inspection. It does not certify generated
module bytes, the optional compressed chart circuit, a fresh quadratic lift,
the final coefficient bound, or a measured variable reduction. Those checks
remain part of completing the authorized source optimization. No additional
user approval is a mathematical premise of this review.
