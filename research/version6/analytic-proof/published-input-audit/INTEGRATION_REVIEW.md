# Independent end-to-end compatibility review

**Decision: accept the removal of the assumed Frei–Tinková theorem for the stated fixed Gaussian ray-field application in the candidate identified below. No unresolved mathematical interface gap was found.** This is a review of the replacement chain and its actual consumers, not a claim that local review receipts alone prove the chain, nor a new certification of every theorem elsewhere in the manuscript.

Reviewed on 2026-11-06 by the detector/source-audit worker. The candidate is `work/quartic-version6-preparation/manuscript/quartic_962-analytic-candidate.tex`, SHA256 `b43f096ba3a4b1a979778ae1593ce3ad89048a2d28016e5ee9f35b124238dce7`. The accompanying machine-readable dependency inventory is `INTEGRATION_DEPENDENCIES.json`. The decision is bound to these bytes; later mathematical edits require review of their affected consumers.

## Scope and independence

I read the complete norm-transfer, Type I/II, affine-interpolation, factorization, progression, and Gowers-bridge fragments, then checked their connections in the assembled candidate. I also read the retained obstruction, ray-class lower-bound, and final diagonal arguments to check that their inputs are supplied by the narrower replacement.

The new Siegel–Walfisz component is my own work. It is therefore **not independently certified by this review**. I use its separately accepted statement, as independently checked by the quotients worker in `sw-independent-review/REVIEW.md` and `receipt.json`. That component's corrected TeX hash is `56c7d6a62678123d2fd89bfc473f6934e75bd1da04233b292bda4cc9be77262e`. This review checks how its output is used in the progression and later arguments.

The published Green–Tao, Dodos–Kanellopoulos, Tao–Ziegler, Bienvenu, and ray-class theorems remain external mathematical inputs. Their exact-source reviews are separate evidence. Here I checked their required interfaces in the assembled chain; I do not replace source qualifications by blanket acceptance. In particular, DK Theorem 5.1 was checked in arXiv v4 and its final typeset statement was not compared. The candidate preserves that qualification in its bibliography. The unchanged Browning–Loughran and Browning–Heath-Brown source qualifications are also preserved. The accepted conclusion is removal of an **assumed FT theorem**, not a claim that all cited final publisher bytes were inspected.

## The arithmetic domain is exactly the one proved

The integrated polynomial-count setup at `subsec:v5-artin-transfer` now requires K to be the ray class field of E=Q(i) for H Z[i], with 16 dividing H. Every C_j is a conjugation-invariant subset of Gal(K/E), viewed inside Gal(K/Q). This is strictly the split-prime portion of the rational Galois group. The proof is not asserted for arbitrary finite Galois fields or for classes in the other coset.

For this domain every nonzero Gaussian ideal has four generators, including ideals generated on an axis. The norm-transfer proof sums the entire lattice and divides by four, so there is no exceptional angular-boundary convention. The finite ray-character weight is constant modulo H and invariant under units. The quadratic slicing argument uses ordinary one-parameter equidistribution after composition, not an unproved multiparameter theorem.

At an eligible split rational prime there are two conjugate norm-p prime ideals. Conjugation invariance of C gives the exact factor T_C(p)=2 Lambda'_C(p). Other discrepancies lie at proper prime powers or the finitely many excluded primes, whose total is O_H(sqrt X log^2(2X)). This is why the factor 1/2 in the affine centered-prime corollary is correct and why the split-prime restriction cannot be silently removed.

The Fourier coefficients and arithmetic Frobenius convention in the progression proof agree. The finite character average over Gal(K Q(zeta_q)/E) counts the fiber compatible with the chosen cyclotomic residue. Dividing the ideal coefficient by two changes [K Q(zeta_q):E] to [K Q(zeta_q):Q]. No inverse-Frobenius reinterpretation is used. Since W contains the conductor of K^ab, K intersect Q(zeta_(Wq)) equals K^ab. The resulting progression coefficient is exactly mu_C(b)/phi(Wq), matching the ordinary-prime coefficient after multiplication by mu_C(b).

## From norm transfer to the centered nilsequence estimate

The norm-transfer lemma initially has a restricted power regime: delta>=X^(-sigma), and basis height and progression modulus at most delta^(-kappa). The final Type I/II proposition does **not** leave those restrictions as assumptions. Its proof uses the trivial bound when Q log(2N)^6 delta^c is large, so the nontrivial case supplies the missing height/modulus restrictions. Extraction gives densities and amplitudes bounded below by fixed powers of delta. All extracted scales are at least a constant times N^(1/3). The exponent choice puts the transfer lower-parameter and recombination length requirements in range.

The Type II extraction removes the character and Möbius coefficients by the stated two Cauchy–Schwarz steps. Its transfer is on the whole product orbit; the proof does not infer product equidistribution merely from mean-zero factors. The test function F tensor conjugate(F) has zero product Haar mean, and the failure of product equidistribution is recombined using a nonzero component of the resulting product horizontal character. The proof separately handles small Type I dilation scales and large recurrence scales. Shift removal clears denominators before using recurrence, so a large progression shift is not being treated as bounded.

The shell argument and larger-parameter substitution then give the final power estimate for every delta and every Q. Thus the affine step can apply it at X=WN+b, eta=delta^a, and Q_1=max(Q,Wq,2). There is no surviving requirement Q_1<=eta^(-kappa) to be supplied there. An early concern based on the restricted norm-transfer regime was withdrawn after reading this complete final proof.

Affine interpolation constructs a polynomial sequence on all integer arguments, including those outside the residue class b modulo W, by real polynomial Mal'cev-coordinate interpolation. Its total equidistribution is proved through a horizontal-character obstruction; fractional-argument equidistribution is not assumed. The original and interpolated degree and rational-filtration conventions match the Type I/II proposition. Fixed W-dependent constants are allowed. Prime-power errors are absorbed after choosing the affine lower-regime exponent sufficiently small.

For the actual weight h=(phi(W)/W)(Lambda'_C(Wn+b)-mu_C(b)Lambda'(Wn+b)), the factorization proposition's three hypotheses are all supplied:

1. Pointwise control: 0<=mu_C<=1 and 0<=Lambda'_C<=Lambda' imply |h|<=lambda_(b,W)=O_W(log N), so K_w=1 is valid.
2. Constant terms on cells: the centered-progression corollary controls every interval progression. It first handles very large modulus by cardinality and then uses the fixed-field progression theorem. There is no minimum cell length condition to violate.
3. Mean-zero terms: the affine centered-prime corollary gives N delta^c Q log(2N)^7, with fixed positive c and a lower power regime. This is the required fixed-power shape, rather than a family of unspecified logarithmic estimates.

The factorization proof keeps every cell when summing the minor-arc bound. It chooses B after the fixed losses but before using the factorization upper exponent E(B). The later choice of arbitrary logarithmic saving for the progression bound absorbs the cell count. Thus B is not required to dominate its own unknown upper exponent. Rational conjugation is handled with finite-index/lattice and metric losses; it is not assumed isometric. The Haar mean is subtracted on the new subgroup quotient, including the dimension-zero case.

These steps supply the bridge's centered nilsequence estimate uniformly in polynomial orbit and bounded test-function complexity for each **fixed** field, ray modulus, and W. The assembly maps the affine notation Lambda_(b,W) to the already defined lambda_(b,W); this is a notational identity, not a change in normalization.

## The two analytic cutoffs and the inverse theorem

The bridge first uses an auxiliary cutoff z and V_z=D times the primes not dividing D up to z. It does not insert a varying V directly into the fixed-V nilsequence estimate. At each stage it fixes V_z, takes thresholds for the finite list of residues and inverse-theorem tests, and only then raises the stage. Physical thresholds are chosen at the refined scale N/V_z, avoiding an implicit equation for z. The growth restriction V_z=N^(o(1)) also supports the initial-segment discard.

DK is applied to a real function after a fixed positive rescaling, dominated by the ordinary-prime majorant. Its target U^s interval norm has a majorant hypothesis in U^(2s) on the **full prime cyclic group**, not on the interval alone. The bridge requests enough ordinary linear-forms complexity for every subproduct of the 2s-cube (at most 4^s forms). The majorant is not zero-extended outside the working interval. The inverse theorem supplies a fixed-complexity linear nilsequence; that is included in the polynomial-orbit estimate, with a fixed metric comparison. The truncation at L^(3/5) costs o(1) both in the interval Gowers norm and in bounded correlations.

The resulting fixed-system linear replacement theorem uses nonzero, pairwise nonproportional linear parts. Its explicit normal-form extension is an integer change of variables with a full auxiliary box; division by that box's cardinality returns the original sum. It does not replace a high-dimensional estimate by its value on a thin diagonal. Bounded normalized constant terms and convex regions remain within the external generalized von Neumann interface. The error is uniform over the finitely many residue vectors at each stage. After restoring normalization, their admissible mass is bounded by the convergent local product, so a growing power of V_z is not lost.

This theorem contains no z in its conclusion. Only after it is established does the proof fix the different polynomial cutoff v, with W=D times the primes up to v and A=W^(1/rho). This separation is essential and is present in the candidate.

## Local cubes and polynomial transfer

For fixed v the steps q and scale ratios J/n range over fixed compact data. The wrap-around decomposition gives O_a(1) convex regions because qJ/n<1. Every nonempty cube subproduct has nonzero, pairwise nonproportional gradients. The fixed-system replacement theorem applies on each region, with its normalized constant terms bounded; division by n J^(2a) preserves the o_v(1) error. Every output is b modulo D, so the replacement of a centered ray cube gives mu_C(b)^(2^a) times the centered ordinary cube, not a mixture of unrelated densities.

The ordinary local factors are 1+O_a(p^-2) away from Wq and 1+O_a(p^-1) at p dividing q but larger than v. Since log q=O(v), the latter give O(1/log v). Factors at primes dividing W cancel normalization. This supplies the precise global norm used by the retained polynomial proof.

The dense-model use is for arbitrary functions dominated by the ordinary prime majorant. It does not assert that a ray-prime weight has model one. Subtracting its own conditional density from the bounded model gives the centered function to which concatenation and polynomial generalized von Neumann apply. The choice of local complexity, coefficient bound, B_0, global order a, and finally rho precedes v. The recorded M_0, M_1 and J inequalities place every requested global norm in the range just proved.

The candidate includes an explicit fixed enlargement and translation of the ambient interval for actual boundary outputs. Its localization proof anchors the at-most-one constant polynomial by nu_0 and applies the ordinary polynomial-forms theorem to nu_0 F, nu_0 F^2 and nu_0. In the square, independent polynomial variables prevent coincident nonconstant shifts. Weighted Cauchy–Schwarz then controls any fixed-width strip by its relative width, with the prescribed iterated errors. The final diagonal preserves all earlier epsilon-strip tests. For an arbitrary T=o(sqrt N), fixing epsilon first and letting N tend to infinity avoids assuming T^2/N decreases at the stage rate. Therefore the discarded output strips do not incur a spurious log(N)^k loss.

There is no circular dependence between the bridge and the following polynomial-count proposition: the fixed-system replacement and local-cube estimate are proved first; the bridge's completion paragraphs explain the external polynomial machinery used in the subsequent proposition. They do not use that proposition as an input to the linear replacement.

## The retained lower bound and obstruction comparison

The actual consumer uses K_L, the ray field of H_0 T_L Z[i], after choosing one fixed sufficiently large L. Its modulus is divisible by 16. The set C_L lies above C_0 inside Gal(K_L/Q(i)); its adjacent-norm conditions are invariant under conjugation. Thus it satisfies exactly the narrowed polynomial-count hypotheses. There is no consumer here requiring arbitrary conjugacy classes in all of Gal(K_L/Q).

The ray-fiber calculation supplies mu_L(b)>=mu_0 times the product of (1-4/(ell-1)) and hence the singular-series lower bound c(log L)^(-4k), with c independent of L. Its conductor and cyclotomic factors match the mu used by the new progression proof. The norm-fiber denominators cancel; a field-degree loss is not reintroduced by the new analytic route.

The obstruction estimate is uniform in L in its leading term and allows an error depending on the fixed tau. The final order is: coefficients and base modulus, then L large enough to compare leading constants, then K_L and C_L, then each fixed tau_j and its threshold. The asymptotic polynomial theorem is only invoked after the field is fixed. The separate v-diagonal supplies omega(N); the final tau-diagonal arranges T>=omega(N)sqrt N and T=o(sqrt N). Rounding T down preserves the required bound. Its weighted lower count exceeds the weighted obstruction tail with the constants stated in the proof.

Conjugating a generator above the conjugate base class gives the prescribed base residue without changing adjacent norms. Small odd primes are excluded by the fixed ray conditions, the remaining common odd divisors by the tail comparison, and the two-adic valuations remain the exact retained calculation. Coefficient dilation for the user's divisibility q|w is performed before all these fixed-data choices. Negative coefficients are permitted because the retained u in [N/2,N] and sufficiently small tau force all outputs to positive comparable sizes. No stronger uniformity in the coefficient data is used.

## Assembly and remaining qualifications

An independent line diff against `quartic_962-preparation.tex` found edits only in the announced analytic replacement, its scope statements, and added bibliography entries. The local/medium/large obstruction block is unchanged (trimmed-block SHA256 `16056ce425c15e0fbd603a41a8e7cc848949166a02de27448f9867ab04be5835`). The retained ray-density through final-diagonal block is unchanged (trimmed-block SHA256 `4b1fcb78f3cc4945e58b0a68ce922a6a75754dd1907714a7e2867b91cd901a9d`). The new proof replaces the old FT invocation and removes its imported-proof repair remark. FT remains methodological attribution and bibliography provenance, not an assumed analytic theorem.

The citation maps GTMobius2012 to `moebius` and v6gtlinear to `greentao` preserve the cited works. The SW source gate is discharged by the inserted lemma and its independently reviewed proof. The candidate correctly narrows the formerly arbitrary-Galois polynomial proposition. No broader arbitrary-Galois consequence is accepted by this review.

**Remaining mathematical interface gaps: none found in this pinned replacement chain.** Remaining limitations are evidential and scoped: the cited external theorems remain assumptions of the mathematical proof; this reviewer does not independently certify the self-authored SW component; DK and certain unchanged sieve inputs retain explicit author/accepted-version qualifications; and this review does not certify unrelated parts of the quartic construction or its machine-generated polynomial. The candidate remains a preparation artifact, not a publication authorization.

Two nonblocking textual remnants can be removed during later editorial cleanup: inserted source comments still say “working fragment/not integrated”, and the affine corollary calls its already-defined centering “proposed”. They do not affect mathematical assertions. Any cleanup should preserve the reviewed mathematical text or be recorded in the final assembly map.
