# Independent mathematical review of the Gaussian Gowers bridge

Reviewer: elimination / Type I--II worker, independent of the bridge author.
Date: 2026-11-06. The accompanying JSON receipt pins the reviewed `bridge.tex`.

Verdict: accept the bridge's mathematical implication, conditional on the
separately accepted centered-nilsequence input and the cited published ordinary
prime transference theorems. The implication is restricted to the fixed Gaussian
ray fields used by the construction. It does not assert the former general
finite-Galois-field statement. This review does not itself establish the Hecke
Siegel--Walfisz input or repeat the independent publication/source audit.

## Two cutoffs and the order of limits

The auxiliary cutoff z proves a fixed-system linear replacement statement.
It is distinct from the appendix cutoff v. For each z the modulus V_z is fixed
before the size limit, so the fixed-modulus nilsequence estimate is used only
within its proved quantifiers. The maximum over unit residue classes is finite
at that stage. The diagonal can include every residue, the finite list of ray
unions, the required norm orders, and the countable inverse thresholds.

The author incorporated the requested stage ordering. First choose z_j so the
limiting majorant error is below the required inverse-theorem tolerances, then
choose L_j for the finitely many nilsequence and majorant tests. In the linear
replacement application, choose the physical threshold N_j so that the inner
scales comparable to N/V_zj, including the fixed factors introduced by normal
form, exceed L_j. Thus there is no circular definition z=z(N/V_z), and no
claim that a majorant at one fixed small cutoff becomes arbitrarily close to
one merely by increasing N.

After the auxiliary diagonal is eliminated from the fixed-system lemma, one
may freeze v and apply that lemma to each appendix cube system. This supplies
a genuine o_v(1) error before the separate ordinary local-factor estimate
O(1/log v). The proof does not mislabel the latter as an o_N error.

## Majorant and inverse theorem hypotheses

The centered function is real and satisfies |h|<=lambda, since its prime
indicator is either zero or one and 0<=mu<=1. A common ordinary-prime majorant
for a fixed number of residues therefore dominates a fixed positive rescaling
of every needed centered factor on [L^(3/5),L]. The rescaling depends on fixed
complexities, not on the number of residue classes modulo V_z.

For target U^s the proof uses full-cyclic U^(2s) pseudorandomness. The centered
2s-cube contains 4^s distinct vertex forms in 2s+1 variables; all subproducts
are among the requested linear-forms tests. Inclusion--exclusion is therefore
legitimate. The requested complexity also dominates the generalized von
Neumann requirements and the ambient prime cyclic group has the required
constant ratio to the interval. This repairs the earlier U^(2s-2) mismatch.

The discarded initial interval has normalized cube count O(L^(-2/5)); the
logarithmic pointwise bound gives the stated vanishing U^s error. Its bounded
nilsequence correlation also vanishes. The inverse theorem supplies a fixed
nilmanifold and Lipschitz bound for each fixed norm threshold; changing from
its fixed smooth metric to a fixed rational Mal'cev metric is permitted before
the size limit.

The extension V_z=E*product_(p<=z)p has fixed E. At primes dividing E, a unit
residue eliminates every divisor term involving that prime. The normalization
phi(V_z)/V_z depends only on the set of prime divisors. Extra fixed powers
therefore introduce no new large-prime local factors. The bridge requests the
ordinary correlation bounds as well as the linear-forms estimates, so it does
not silently remove a hypothesis from the cited generalized von Neumann
statement.

## Fixed-system replacement and normal form

Removing an output <=N^(9/10) costs O(N^(d-1+9/10)log(N)^t), uniformly over
the permitted constant terms: a nonconstant fixed linear form has O(N^(d-1))
integer fibers in the box at each value. Nonunit output residues then give no
prime terms because every remaining output exceeds the primes dividing V_z.

The refined system retains the original linear parts. Dividing its constants
by V_z leaves them bounded at scale N/V_z. The generalized von Neumann bound
is uniform over these bounded normalized offsets and convex regions. Its
small factor is precisely h at the correct inner scale, while all other
factors are bounded by a common ordinary-prime majorant.

The normal-form reduction is now explicit. Integer vectors v_ij annihilate
the jth linear part but not the ith, and have fixed size because the original
parts are fixed and nonproportional. The substitution x -> x+sum y_ij v_ij
is accompanied by the full auxiliary integer box, not a zero section. The
map (x,y) -> (x+sum y_ij v_ij,y) is an integer bijection. The extended sum is
exactly the original sum times the number of points in that box, and its
domain is convex and contained in a fixed enlarged box. Dividing by the exact
box cardinality converts an error o(M^(d+k)) to o(M^d). No unproved recovery
from a higher-dimensional slice is used.
For one form the final text chooses an active direction v with
dot(psi_1)(v) nonzero and uses the same full-box bijection.

## Admissible mass and uniformity

On each admissible residue vector the normalized error is o((N/V_z)^d).
Undoing the weight normalization and summing multiplies its coefficient by

    |R_z|/V_z^d * (V_z/phi(V_z))^t = product_(p|V_z) beta_p.

For all sufficiently large primes the individual output hyperplanes have
density 1/p and pair intersections have density 1/p^2, uniformly in the
constant terms. Hence beta_p=1+O_t(p^-2). The finitely many exceptional primes
have the stated bounded factors; higher powers give the same admissibility
condition modulo p. The product is bounded. This justifies the absence of
any V_z^d or unbounded logarithmic amplification, including mixed products.
It also covers locally obstructed systems: their admissible mass is zero,
not a quantity by which the proof divides.

## Appendix cubes and local factors

For fixed v there are finitely many q<=A^C1 and the interval of J/n has a
positive lower endpoint. The wrap integers are bounded in terms of the cube
order because qJ/n<1. Each region is convex; the vertex forms have pairwise
nonproportional linear parts. Fixed-system replacement gives an error
o_v(n^(2a+1)) uniformly in J and the regions, which becomes o_v(1) after
division by n J^(2a).

All vertex outputs have residue b modulo D. Expanding the centered cube and
replacing each subproduct therefore gives exactly mu(b)^(2^a) times the
centered ordinary-prime cube, plus o_v(1). This is an equality of complete
centered expansions, not merely of their top-degree terms.

At p not dividing Wq the gradients remain pairwise independent, giving
1+O_a(p^-2), independently of the wrap constants. At p dividing q and greater
than v the weaker 1+O_a(p^-1) bound suffices. Since log q=O(v), there are at
most O(v/log v) such primes, giving O(1/log v) in the product. The other tail
is O(1/v). Removing prime powers with the fixed linear-fiber count is
negligible even after the other finitely many logarithmic weights. The
cutoff x<R similarly costs O(log(n)^(2^a) R/n).

## Polynomial transfer and arbitrary rates T=o(sqrt N)

The bridge preserves the established arbitrary-function model route; it does
not replace an Artin weight by the ordinary prime model one. Its input is the
same global/local norm bound used by the appendix, with the same fixed
complexity order. The final CRT main term and residue error normalization are
unchanged.

The boundary step required one correction during review. A chosen stage
counter j(N) cannot require T^2/N<1/j(N) for every T=o(sqrt N). The final text
now retains all boundary tests epsilon in {1,1/2,...,1/j} at stage j. For any
admissible T, fix k first; eventually its boundary width is at most N/k up to
the fixed coefficient factor. The positive polynomial majorant bounds that
strip by O(NT/k)+o(NT). Take limsup_N and then k to infinity. This supplies
the advertised arbitrary decay rate, with no extra logarithmic factor and
no hidden rate imposed on T.

I also checked the final localization repair identified by the independent
source reviewer. The full-group polynomial-forms estimate is not used as if
it already held on every x-subinterval. Instead, the at-most-one constant
shift is an anchor nu_0, and F(x) averages the product of all nonconstant
shifts. Independent m,m' variables in F^2 have nonconstant differences, so
the three polynomial-forms moments give E nu_0(F-1)^2 tending to zero in the
stated two-limit order. Weighted Cauchy--Schwarz localizes to any interval,
and the one-dimensional divisor-sum mean controls E 1_I nu_0. Enlarging and
translating the ambient interval avoids interpreting genuinely larger integer
outputs as wrapped ones. The errors are correctly recorded as a cutoff error
plus a size-limit error, rather than a false fixed-cutoff o_N statement.

The lower threshold omega(N) is chosen independently to cover the transfer
condition 4sqrt(W)/A. The assertion T=o(sqrt N) is imposed only along the
final diagonal, not at a fixed v where that would conflict with the positive
lower size ratio. The interval [N/2,N] can be used directly, avoiding any
uncontrolled change of omega under subtraction.

## Scope and review provenance

The author made the scale-diagonal, explicit normal-form, and cumulative
boundary-test corrections in response to this review, and the weighted-L2
localization correction in response to the source reviewer. I did not edit the
author's TeX. The JSON receipt binds the final reviewed bytes and the upstream
interfaces. Exact published source availability and bibliography fidelity are
covered by the separate source reviewer; this document accepts no unpublished
Artin linear-correlation theorem. The remaining integration must retain the
Gaussian-field scope and all separately audited analytic dependencies.
