# Why finitely many rational equations might recognize an integer

This is an explanatory proof architecture for the repository's proposed construction, relative to its stated arithmetic inputs. It is not an elementary replacement for those inputs or an independent verification of the full manuscript. The numerical endpoint remains the frozen 933-variable proposal; the direct-target 909-variable candidate has its own proof note.

## Start with the obstruction

We want rational equations whose solvability says that a rational input x is an integer. Writing x=m/n does not help: the equations have no built-in way to demand that m and n be integers. The construction instead obtains integers from a geometric object whose rational points already carry integer labels.

For the chosen elliptic curve over K=Q(sqrt(2)), the relevant arithmetic theorem says

    2E(K)=Z P*.

Thus a rationally described nonidentity double Q has a unique nonzero integer label n, defined by Q=nP*. The equations quantify the coordinates of Q and an appropriate halfpoint chart. They never quantify n as an integer. The label comes from the theorem about the curve.

The remaining problem is to connect our rational input to one of those hidden integer labels. Put beta=x²+2. If we can force beta=n for a label n, then x² is an integer. Writing x=a/b in lowest terms immediately forces b=1. This explains the otherwise artificial-looking change from x to beta.

## Reading a label locally

The group law is complicated in global coordinates, but close to the identity at a good prime it has a logarithm. That logarithm turns addition of points into addition of numbers. Introduce H=hP* and U=uP*. Where both are sufficiently close to the identity, their logarithm ratio is u/h.

A single ratio does not identify n. Introduce a second observation after translating by the target point Q=nP*. In the direct-target candidate the second ratio is

    (u−n)/(h−1).

If both ratios were exactly the same number L, we would have

    hL=u,      (h−1)L=u−n,

and subtraction would give L=n. This is the basic reason for the two comparisons. In the frozen 933-variable construction the shifts are 2 and 2n; subtraction gives 2L=2n instead.

The equations cannot use an infinite p-adic logarithm. They use explicit truncated polynomials instead. A separate local estimate bounds the truncation errors. At a consumed odd prime, at least one of h and h−1 is a unit. That observation, together with the cross test, makes the approximations integral and turns relative errors into absolute errors. The conclusion is a congruence L=n modulo a controlled prime power, rather than an exact equality.

This calculation is elementary once the formal-logarithm estimates and point-domain facts have been supplied. It is a useful place to begin a blackboard explanation.

## From congruences to equality

A congruence at one prime is much weaker than equality. The construction obtains congruences at every sufficiently large prime occurring to odd order in one of several fixed contact products. The product of those primes is an odd-contact radical M. If the local precision is k, the numerator of a nonzero discrepancy must be divisible by M^k.

The crucial global input is a height theorem: the heights of the relevant contact parameters are bounded by H times M^19. Using several fixed scales transfers this bound to all the elliptic-curve labels. In the refined construction, the resulting comparison principle has the shape

    B² < 7H |N|^(19/k) + 6,

where B is the largest absolute label and N is an integer numerator of a tested discrepancy. This is the bridge from local divisibility to global size. It is not a consequence of the Chinese remainder theorem alone.

The exponents suggest what precision is needed. If N is a polynomial of degree d in labels of size at most B, then roughly |N| is at most a constant times B^d. The displayed bound would force

    B² < constant times B^(19d/k).

When k>19d/2, the right side grows more slowly. A sufficiently large forced label then makes a nonzero discrepancy impossible. This heuristic guides the circuit design; the actual proof retains the constants and the additive term.

## Why there are two contradictions

The first discrepancy is the Lucas polynomial Delta=F(a,t,b), of degree at most four in the labels. Precision 40 is just above the threshold 19·4/2=38. The exact estimates give

    B^(1/10) < 24H

if Delta is nonzero. An anchor forces B≥|a|>(40H)^10, contradicting that inequality. Hence the Lucas equation holds exactly.

The Lucas equation then supplies exponential growth: log B>|a|−3. This is the point of the auxiliary Lucas witnesses. They manufacture a second, much stronger comparison between the size of a label and the size of the whole configuration.

The second discrepancy is beta−n. Its numerator satisfies N≤2 exp(h(beta))B. The scalar conditions bound the logarithmic height h(beta), and the precision-12 tests yield

    log B < (12/5)log(40H)+(19/5)h(beta) < 31|a|/200.

The anchor makes this incompatible with log B>|a|−3. Therefore beta=n, and the original rational x is an integer.

This division of labor explains the design: one set of tests forces a growth equation; that growth equation makes the remaining approximation exact. Neither congruence alone needs to prove the final conclusion directly.

## Why genuine integers have witnesses

The preceding discussion excludes nonintegers. It does not yet show that every integer is admitted. Completeness must arrange all the local tests and all the real conditions at once.

For an integer input, choose beta and the scalar and Lucas data first. Choose local continuity neighborhoods that preserve the scalar conditions; they determine a modulus L. Next the simultaneous-prime theorem selects the contact primes with controlled reduced elliptic-group orders and avoidance of the odd factors of L. The order of these choices matters: L is fixed before the prime theorem is applied.

Because P* is a double, its reduction lies in the doubling image, whose order is one quarter of the full group order. The two families of image orders are coprime. In the direct-target candidate they let us solve

    h=0 modulo M−,   h=1 modulo M+,   h=h0 modulo L.

The remaining overlap is compatible because 16 divides h0. Multiplication by h puts the primary points near the identity at one set of places; multiplication by h−1 does the same for the translated points at the opposite places. Their logarithm ratios are exactly the desired labels before truncation. A real-progression argument supplies the simultaneous real bounds. The pole and norm lemmas then fill the remaining rational witnesses.

The Chinese remainder step is elementary. Producing suitable prime orders, controlling the local predicates, and establishing the real-progression assertion are substantial arithmetic inputs.

## From the argument to one quartic

The arithmetic conditions are expressed by finitely many rational equations. Long polynomial calculations are split into quadratic assignments, for example z=uv. Divisions are encoded by bz=a, but only after proving that every relevant solution forces b nonzero. Clearing denominators without that proof could add unintended rational solutions.

Write the resulting quadratic residuals as R1,...,Rm, with integer coefficients. Over Q,

    R1²+...+Rm²=0   if and only if   R1=...=Rm=0.

This produces one polynomial of degree at most four. Exact coefficient expansion and reversible elimination certificates establish what polynomial the program actually emitted. They do not prove the arithmetic lemmas used to interpret its solutions.

## Map to the full argument

| Explanatory step | Precise source |
|---|---|
| Finite-double chart and nonzero point coordinates | Current manuscript `lem:v5-point-domains`; Version 6 package `PROOF.md`, point chart |
| Recovering labels from two local ratios | Current manuscript `lem:v5-two-anchors`; `DIRECT_TARGETS.md` for shift one |
| Contact radicals and transfer to label heights | Current manuscript `lem:v5-height-transfer`; `research/combined-comparison/ARITHMETIC.md` for exponent 19 |
| Scalar height and anchor inequalities | `ARITHMETIC.md`, sections 2–3 |
| Lucas growth and the two contradictions | Current manuscript `lem:o8-lucas`; `ARITHMETIC.md`, section 4 |
| One common witness | Current manuscript `v5:real-progression-bridge`, `thm:v5-simultaneous-primes`; `DIRECT_TARGETS.md` |
| Quadratic program and quartic expansion | `research/v6-comparison/README.md`, generator and checker |

Here “current manuscript” is upstream `manuscripts/quartic_v8.tex` at commit `5856286a57fba19574a40704571ee70e79738281`. Version 8 preserves Version 7's repaired proof body.

## What can be simplified, and what remains deep

The two-observation calculation and the final sum of squares are already elementary. The direct-target change removes an unnecessary doubling from both the proof and the circuit. The exponent inequality k>19d/2 explains the precision choices more clearly than a list of numerical estimates.

A fully elementary proof has not emerged. Within this architecture, the elliptic-group description, quantitative height theorem, local pole/norm predicates, simultaneous-prime theorem and real-progression statement still do essential work. No claim is made that they are indispensable to every possible proof. A promising conceptual goal is a single abstract comparison lemma that accepts a height-transfer exponent and a polynomial degree, and outputs sufficient precision and anchor bounds. It would organize the constants and expose exactly which stronger input would reduce the circuit further.

This exposition was developed with AI assistance and remains a guide to the proposed argument, not independent human validation of it.
