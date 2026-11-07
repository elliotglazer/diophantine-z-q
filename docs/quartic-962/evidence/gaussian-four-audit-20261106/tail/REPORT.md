# Independent Gaussian large-prime tail audit

Status: the large-prime argument is mathematically valid after making its quantifiers and several suppressed justifications explicit. I found no fatal large-prime obstruction and no need for a new arithmetic hypothesis. The replacement retains all labels, the large-divisor estimate, and the weighted error exponent. It does not change the final theorem. This conclusion concerns the tail and its stated medium-prime input, not the separate analytic prime-pattern lower bound.

The substantive statement repair is to quantify a fixed lower cutoff `L_*` and state uniformity for `L >= L_*` in the weighted proposition. The original proposition left the range of `L` unstated, although its medium-prime input requires a sufficiently large cutoff. The other changes expand valid but compressed steps. They should not be described as repairing a false lattice bound or a missing logarithmic saving.

## Baseline and replacement

- Read-only baseline: `work/gaussian-four-audit-20261106/baseline.tex`.
- Whole-file SHA256: `06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c`.
- Read local-count and medium-prime context at lines 16212 through 16387, audited the tail at lines 16389 through 16531, and read its final consumer at lines 18565 through 18611.
- Replace inclusive lines 16389 through 16531 with `replacement-tail.tex`. Leave the following blank line and subsection untouched.
- Exact original interval SHA256: `983c0f233c967ea169d99b487a2338814db720f55e4683bfb397abe46a42819a`.
- `handoff.json` records the replacement hash and label list. `build_fragment.py` checks the baseline hash before extracting or generating anything and writes only in this directory.
- No shared manuscript or repository file was edited. No applicable `AGENTS.md` was found on the directory ancestry. The `unslop` skill was read and applied to this report.

## Source pins and access limit

The BHB inputs are Lemmas 2.1 and 4.1 of T. D. Browning and D. R. Heath-Brown, *The geometric sieve for quadrics*, Forum Mathematicum 33 (2021), 147–165, [DOI](https://doi.org/10.1515/forum-2020-0074). The [Oxford repository record](https://ora.ox.ac.uk/objects/uuid%3A029537a5-f3a1-4ec7-a96f-07533accd494) explicitly identifies its PDF as the accepted manuscript, accepted on 14 September 2020. The inspected file is the cached `work/quartic-version5-release/sun-proof/sources/BHB-accepted.pdf`, SHA256 `1e2a4d3d3f731c0ee67599cfa50f899fe499e51d4a452455a04f2d0a35e7191c`. Its existing line-addressable extraction is `BHB-accepted.txt`, SHA256 `f2dc9444a4aaba553d7d73ad64cb6e103d736e83aa07921240737e5e40d4c169`.

Exact accepted-manuscript pins:

- Lemma 2.1: page 6 continuing onto page 7, extraction lines 242 onward. This is a box sieve for polynomials with no common factor in the integer polynomial ring. It allows unequal side lengths, requires each side parameter, height bound and cutoff to be at least 2, and its constant depends only on degree and dimension. Its bound is `V log(VH)/(M log M) + V log(VH)/B_min`.
- Definition of good primes and Lemma 4.1: page 13, extraction lines 552 through 574. Good means odd and rank-preserving. For a quadratic form in `m` variables of rank at least 3, the covering has at most `(3m)^omega(q) q^(m-2)` lattices, each of determinant `q^(m-1)`. The number with largest Euclidean minimum greater than `T` is at most a constant times `(3m)^omega(q) q^(2m-3) T^(-m)`.
- The lattice definition at extraction lines 556 through 560 gives `q Z^m` inside each lattice. The basis, inverse-basis and point-count arguments are on accepted pages 16 and 17, extraction lines 692 through 751. The coefficient-content argument and the box-sieve application are on pages 17 and 18, extraction lines 769 through 832. These were read as proof, not inferred from the theorem title.

The medium-prime context uses Theorem 4.1 of T. Browning and D. Loughran, *Sieving rational points on varieties*, Transactions of the AMS 371 (2019), 5757–5785, [DOI](https://doi.org/10.1090/tran/7514). Its inspected institutional accepted copy is `work/quartic-version5-release/sun-proof/sources/BL-accepted.pdf`, SHA256 `94411c88a12ad369896d58b43a9f943b88ff11d816f6c97a9f0d308936d2c4cb`. The extraction `BL-accepted.txt` has SHA256 `249535d02bdfa82e9695d613cbfbfe70ccfc13392661dc3e39d61b57be3d0726`. Section 4 starts on manuscript page 16; Theorem 4.1 is on page 17, PDF page 18, extraction lines 1015 through 1034. It explicitly permits `n >= 5`, arbitrary nonempty nonzero residue subsets as in (4.1), and a smooth compactly supported nonnegative weight with gradient of the form bounded away from zero on its support. Its error is `O(B^(n/2+epsilon) M^(n/2+epsilon))`, uniform in the modulus and residue subsets.

The publisher's BHB HTML verifies publication and its revised date, but says that the full text is inaccessible. Its PDF endpoint was inaccessible on this check. The BL publisher landing page returned 403 and its final PDF request timed out. The cached files named `BHB-published.pdf` and `BHB-published*.xml` have zero bytes and were not treated as sources. Thus this audit checks the accepted versions of published papers, not a newly obtained final typeset edition. The existing bibliography's disclosure remains accurate. No unpublished strengthening is used.

## Why the inhomogeneous argument applies

The main homogeneous BHB quadric theorem is not a direct citation for the adjacent norms `(a+epsilon)^2+b^2`. Homogenizing by adding a variable and then forgetting that it equals 1 would introduce a dimension and lose a power of `B`. The manuscript instead reconstructs BHB's fixed-coordinate argument from its two lemmas. This is legitimate, and the replacement states that route explicitly.

The form `Q_kappa` has rank 5. Its projective quadric in `P^4` is smooth. The affine cone has its sole singularity at the origin, which is excluded from the BL weight support. The matrix of `R= kappa w^2-xz` has determinant `-kappa/4`, so the ternary form has rank 3 at every odd prime not dividing `kappa`. These are exactly the primes put into the squarefree lattice modulus. The locus cut out by `G=H=0` has dimension 2 inside the dimension-4 affine quadric at the good primes; the local count is at most `4 ell^2`. No smoothness assumption on that intersection is needed for either BHB lemma used here.

After changing signs to make both shifts +1, set `x0=a+c`, `x1=a-c`, `x=b-d`, `z=b+d`. Then `x0 x1=R`. For fixed nonzero `t=x0` or `t=x1`, the triple `(x,z,w)` determines the missing coordinate uniquely. Discarding parity and the missing coordinate's box condition increases the count and does not introduce multiplicity.

For a fixed integer `v`, the number of triples with `R=v` is `O(B^(1+epsilon))`: for each of `O(B)` choices of `w`, a nonzero product `xz=kappa w^2-v` has a divisor-bound number of factorizations. Its zero value can occur for at most two values of `w`, with `O(B)` pairs each. This includes `v=0`. Consequently all `R=0`, `x0 x1=0` points contribute `O(B^(2+epsilon))`.

If an odd prime divides both `x0` and `x1`, it squares into a nonzero `R`. For each prime the nonzero multiples in range number `O(B^2/ell^2)`. Each such `R` contributes `O(B^(1+2epsilon))` after counting triples and the factorizations `x0 x1=R`. Summing the prime reciprocal squares gives the first tail term. A prime larger than a constant times `B` cannot square into the nonzero `R` in this range. Zero values have already been removed.

Otherwise at least one chart has `ell` not dividing `2t`. In the `t=x1` chart, `G-H=P=kappa w^2+2t` and `4t^2 G=K`. The exact identity in the manuscript reduces to the pair `P,(t^2+x^2)(t^2+z^2)`. For fixed nonzero `t`, the first polynomial is nonconstant in `w` alone and the other is independent of `w`; they have no common nonconstant factor. The second has coefficient 1 on `x^2 z^2`, so their contents have no common prime.

In the `t=x0` chart, `t(G-H)=P'=kappa(t+2)w^2-2xz` and again `4t^2 G=K`. For `t` other than 0 and -2, `P'` is an irreducible rank-3 homogeneous quadratic and `K` has nonzero constant term `t^2(t+2)^2`. Thus it cannot divide `K`. The chart has already excluded `t=0`. At `t=-2`, `P'=-2xz`, while setting `x=0` or `z=0` in `K` gives respectively `kappa^2 w^4+4z^2` or `kappa^2 w^4+4x^2`, both nonzero polynomials. This also proves coprimality. The coefficient of `x^2z^2` in `K` is 1, so there is no common content prime in this chart either.

## Lattice count and coefficient uniformity

Take `q` to be the product of primes dividing `t` outside the fixed set of divisors of `2kappa`. All are good for `R`. The number of eligible nonzero `t` for a fixed `q` is `O(B^epsilon)` for any fixed epsilon. The replacement supplies Rankin's bound and explicitly absorbs the finite small-prime factors and `2^omega(q)`; `q` is at most a fixed multiple of `B`.

For `m=3`, the source gives at most `9^omega(q) q` lattices of determinant `q^2`. Their largest minima are at most `q`; hence each has `O(B^3/q^2)` points in the box, including when one minimum is comparable to `B`. The bad lattices, with largest minimum greater than `T`, contribute

`B^epsilon sum_(q <= C B) 9^omega(q) q^3 T^(-3) B^3/q^2 = O(B^(5+2epsilon) T^(-3))`.

For the others, a basis comparable to the successive minima and its inverse give side bounds `O(B/lambda_i)`. Their product is `O(B^3/q^2)` and their minimum is at least a constant times `B/T`. Enlarging all side parameters to 2 costs only a constant factor. The substitution has determinant of absolute value `q^2`, invertible at every prime counted in that chart. It preserves rational polynomial coprimality, and any common content newly acquired is supported on `q`, hence on `2t`. Dividing off that content preserves divisibility by the primes being counted. Coefficient heights are bounded by a fixed power of `B`, since `t=O(B)`, the degrees are at most 4 and the basis entries are `O(B)`.

Thus the affine box sieve is genuinely uniform in the varying chart parameter and lattice. Summing its two terms gives `O(B^(3+3epsilon)/(L log L)+B^(2+3epsilon)T)`. Balancing with the bad-lattice estimate at `T=B^(3/4)` gives `B^(11/4+epsilon)` after renaming epsilon. No prime upper bound or short-range restriction is imposed in the box sieve, so primes larger than `B` are covered too.

## Medium input, weights and final consumer

For the BL input, `Q_kappa` is isotropic and has nonzero discriminant, the gradient is bounded away from zero on any fixed compact support away from the origin, and the moduli avoid `2kappa`. Primitive inclusion-exclusion changes the main factor to the ratio with denominator `ell^4-1`, as written. Its error sum converges because the scale has exponent `5/2+epsilon`. These checks establish that the tail's source interface uses the five-variable theorem in its stated range. The independent local/medium audit should remain the primary review for all of that preceding lemma.

The weighted tail only needs the medium estimate's leading term `C tau B^3/((log B)^k L log L)` and its power-saving error. Its constant is independent of `L` and `tau`; its derivative-dependent error may depend on fixed `tau`. The medium proof's error sum is bounded by the full range up to `B^(1/100)`, so is uniform in a lower cutoff above the fixed exceptional primes. The replacement makes that fact and the empty medium interval for larger `L` explicit.

With `L0=B^(1/100)` and `alpha=1/1000`, the large-divisor first exponent is `2.991`, and its second is `2.751`. Allowing `B^(1/1000)` for all fixed logarithmic weights still leaves both below `3-1/200=2.995`. At one position the pair `a,b^2+1` is coprime in three variables and the same box sieve gives `O(B^3 log B/(L0 log L0)+B^2 log B)` before weights. Its weighted exponent is also below 2.995. The medium error `B^2.7 (log B)^k` is smaller still. Weakening to `B^(3-1/400)` gives exactly `N^(3/2-1/800)`.

The vector-to-pattern map recovers `u` from a chosen prime norm and `w`, so it loses no power. A split prime has eight Gaussian elements of that norm, and all finitely many positions, signs and generator choices can be absorbed into a constant. A vector with prime norm is primitive. The large tail needs no leading `tau` factor because it contributes solely to the power-saving error.

The final proof first fixes a sufficiently large `L`, then the ray field, then each fixed `tau`. This respects the replacement's `L >= L_*` condition. The error's dependence on `tau` is compatible with its diagonal selection of `N_j`. Comparing `1/(L log L)` with `(log L)^(-4k)` is valid with the cutoff-independent leading constant. This audit does not assert the separate prime-pattern lower-bound proposition.

## Validation

`build_fragment.py` verifies the complete baseline hash and preserves every existing tail label. `check_tail.py` checks both chart identities and congruence equivalences over four small prime fields and five values of `kappa`, including bad primes as an extra algebraic check. It also checks the exact rational exponent arithmetic and balances TeX labels, environments and braces. These are supporting checks; the source-level derivation above is the proof review. A full manuscript TeX build belongs to integration and was not performed in this isolated directory.
