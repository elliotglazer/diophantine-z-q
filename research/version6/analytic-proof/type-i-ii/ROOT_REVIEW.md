# Independent review of Gaussian ideal Type I/II

Reviewer: root, independent of the author of TYPE_I_II.md. Date: 2026-11-06.

I checked the full proof against the published Green–Tao statements and the current norm-transfer interface. The extraction, recombination and exponent choices are valid, subject to acceptance of that separately reviewed norm-transfer lemma. This does not establish the progression main terms or the full replacement of Frei–Tinková.

## Extraction

The ideal Vaughan identity is exact with the stated cutoffs. On the shell `(N/2,N]`, the small-Lambda term vanishes. The bounds on alpha and beta follow from the nonnegative divisor identity `1*Lambda=log N`, including their support. Complete multiplicativity of a ray character extended by zero suffices.

The ideal-count bound follows from the four-to-one Gaussian generator map. The bound `tau(n)^2<=d_4(n)` holds prime by prime, and the two moment sums have the stated harmonic-sum bounds. Thus the Type I Cauchy–Schwarz argument has no omitted ideal multiplicity.

For Type II, the actual lower bound on a dyadic rectangle is stronger than the deliberately weakened one used. Squaring `epsilon*R*B/L^2` and dividing by `R*L^5` gives `epsilon^2*R*B^2/L^9`. The second Cauchy–Schwarz identity is an exact equality of finite complex sums after taking absolute squares. Its conjugates are correctly placed. Normalizing by the ideal count gives the stated fourth-power density. Both the amplitude and density in the conclusion are weaker than the resulting bounds, so `theta=c0*epsilon^4/L^24` is sufficient.

The modulus after solving `r*n=c mod q` is `q/gcd(r,q)` when solvable. Intersecting two such classes gives either the empty set or one class of modulus dividing q. All product cutoffs remain inside f before Cauchy–Schwarz. Consequently the argument does not require any unjustified lower bound on a truncated interval's length.

## Recombination

I read Theorem 2.9 and Lemma 4.5 in `GT-orbits-published.txt` against their published source. Theorem 2.9 supplies the horizontal character for the one-parameter restricted orbit. Lemma 4.5 permits any interval center and gives the extra interval-length factor in the smoothness bound. That extra factor is essential to obtain `N^(-j)`, rather than merely `R^(-j)`, in equation (12).

The affine shift removal in (10) has the correct scale. Multiplication by fixed factorials and q-powers clears all rational coefficients before using distances modulo one. The shift may be O(M), while the progression length is at least eta*M, so the remaining loss is only a fixed inverse power of eta. Pigeonholing the resulting horizontal characters costs another fixed power because their lattice has bounded rank.

For Type I at small R, multiplying by r^d clears the r^j denominators and costs a bounded inverse power of eta. At large R, Lemma 4.5 applies to the selected r-values in an initial interval containing the dyadic cell. The interval length is small enough relative to density by taking K large; the relation R<=2*N^(2/3) supplies the required N-power saving. For Type II, fix one r-prime with many partners and apply the same lemma to the shifted interval. This avoids the invalid replacement of `r^j-r0^j` by `(r-r0)^j`.

The product orbit is not assumed equidistributed merely because its factors are. Rather, the proof argues that if it were totally equidistributed, the norm-transfer estimate would contradict the extracted correlation. The subsequent horizontal character is a nonzero pair. Interchanging the pair if necessary leaves a nonzero character in the first coordinate.

The final character test is valid on a long initial interval. Its constant phase is subtracted. A nonzero horizontal character pushes Haar measure to Haar measure on the circle, and the adapted-basis metric bounds control the test's Lipschitz norm.

## Parameter check

With `a=1/(4H)` and `c=a*kappa/32`, the extracted density and amplitude are at least delta^(5c) for small delta. Since a>5c, these are sufficient for the recombination input with eta=delta^a. In the nontrivial case `Q*L^6*delta^c<1`, both the rationality and progression-modulus bounds required by norm transfer hold. Its weighted upper bound has exponent at least `32c-c/6`, strictly larger than 5c. The stated s makes inner scales large enough for norm transfer and makes `N>=eta^(-K)` valid. Recombination contradicts total delta-equidistribution because delta^(aH)=delta^(1/4) is larger than delta.

The discarded small shells have total weight O(sqrt(delta)*N*L). Retained shells inherit total `2sqrt(delta)` equidistribution from `[N]`, and geometric summation preserves the bound. Shrinking the admissible s and replacing very small delta by delta^(s/8) removes the lower-delta restriction. Singleton tests handle delta<=1/N. The resulting power c_final is positive, though it is smaller than the shell exponent.

The ordinary-integer corollary repeats the exact same convolution extraction with a(n)=1. Its unweighted progression bound follows directly from total equidistribution for long progressions and cardinality for short ones. It does not assume that the published Möbius theorem is already a von Mangoldt theorem.

## Remaining documentation

Before integration, bind this review and the final norm-transfer review to source hashes. Use a distinct symbol for the recombination exponent H in TeX to avoid confusing it with the Gaussian ray modulus. The numerical value of c_final is not needed by the prime-pattern existence application. Its dependence only on the fixed nilmanifold dimension and degree, with the ray modulus entering constants and thresholds, is needed and is maintained.
