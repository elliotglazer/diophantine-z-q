# Independent review of affine interpolation and factorization

Verdict: accept both revised analytic implications under their stated input hypotheses. I found no remaining mathematical gap. The affine interpolation is proved rather than assumed; the factorization parameter choice is not circular. This review does not prove the arithmetic progression main terms or the finite ray-character expansion assumed by the application.

Reviewed files:

* `factorization/AFFINE_PULLBACK.md`, SHA256 `a7849af9a4c44af44e8bfecd4f4e94fdee58c36f5ccfef3b20dca032ee1126a1`.
* `factorization/FACTORIZATION.md`, SHA256 `93eaf841621c852ae89b0447051f9773a89f3a31e44bd75dcf0e2666878cf559`.

I did not author these files. I requested the two affine precision repairs below and checked their incorporation.

## Sources checked

The published [Green–Tao polynomial-orbit paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf) supplies Theorems 1.19 and 2.9 and the one-parameter case of the coordinate characterization in Lemma 6.7. Its local PDF SHA256 is `8c7ea5eced84dc5da97508f4eda39fa84c958d3e659a797ab402645c1c207c8f`.

The published [Green–Tao Möbius paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p03-p.pdf), printed pages 545–547, supplies the rational representative and conjugation argument. The Claim on page 547 explicitly gives an adapted basis on the conjugated subgroup with its intersection lattice, a power-loss total-equidistribution bound, and a polynomial Lipschitz bound. Its local PDF SHA256 is `5259dbc9ee73df46edd765ca27c8b3c0ec466f6b78abafa5f54237b11d44a314`.

The use here is the published one-parameter factorization and conjugation argument. It does not require the later multiparameter equidistribution assertion.

## Affine interpolation

The construction is valid in the stated connected, simply connected nilpotent convention. The second-kind coordinate polynomials of the actual G-valued sequence have real coefficients and the degree restrictions furnished by the adapted filtration. Evaluating those polynomials at real arguments and applying the inverse Mal'cev coordinate map is well-defined. Composing with (t-b)/W preserves the degree restrictions, so Lemma 6.7 gives a polynomial sequence on Z. It agrees exactly with g at t=Wn+b. This does not infer equidistribution by replacing integer arguments with fractional ones.

The first repair was to require both u and v to be integers in the linear coefficient lemma (A2). That integrality is needed: otherwise p modulo one cannot be composed by an arbitrary real shift without choosing lifts, and the binomial matrix need not have integer entries. The actual progression application always has integer u,v. The revised lemma now states the correct condition.

With that repair, the coefficient argument is correct. For a degree-j binomial polynomial composed with u+vt, the diagonal coefficient is v^j and the coefficient in row l has size O_d((C+E)^j X^(j-l)). Clearing the triangular system uses only products of v^j, so the clearing integer has size at most a fixed power of E. Higher-row errors contribute X^(h-j) times X^(-h), exactly the required X^(-j). Integer multiplication, rather than rational division of distances modulo one, justifies the inference.

If total epsilon-equidistribution fails on [X], a witnessing progression has at least epsilon X points. Once epsilon X is large, its common difference is at most 2/epsilon and its shift has magnitude at most 2X. Theorem 2.9 applies to the restricted polynomial sequence with the same rational basis. The linear coefficient lemma recovers a small smoothness norm for a nonzero integer multiple of the character on the entire interpolated sequence. Forward composition with Wn+b uses another integer binomial matrix. Since W and b are fixed and X=WN+b, it gives the asserted smoothness bound on the original scale N. Character magnitude is also bounded by a fixed inverse power of epsilon.

The second repair makes the exponent choice explicit. The revised text names C_aff, depending only on m,d, which dominates all inverse-epsilon exponents, and chooses

    a < min(1,c0/(2*C_aff)),
    sigma < min(sigma0,1/(2*a)).

Thus the resulting character is small enough for the already reviewed total-equidistribution obstruction. Fixed W-dependent constants are absorbed by delta0. Also epsilon X is bounded below by a constant times N^(1-a*sigma), hence grows at least like sqrt(N), so the witnessing progression and all floor manipulations are justified. This proves total equidistribution on the full interval [WN+b], including progressions outside the residue b modulo W.

The use of the ideal estimate is exact. An interval progression in n with step q maps to an interval progression in t with step Wq. Taking Q1=max(Q,Wq,2) costs only a fixed W-dependent factor. The interpolated sequence retains the same nilmanifold, filtration and Lipschitz function. Therefore the input mean-zero estimate (A5) gives (A6) with exponent a*c_E. This application uses the all-progression-length version of (A5), which is the version stated in the independently reviewed Type I/II file.

The finite character expansion and its error are explicitly hypotheses, not proved by interpolation. Given them, the triangle inequality introduces only fixed constants. The condition sigma1*a*min(c_E,c_Q)<1/4 makes the available N*delta^c term dominate the square-root prime-power error. Thus (A8) is a valid conditional mean-zero bound for the stated fixed-modulus weights.

## Factorization, lattices, and metrics

Theorem 1.19 applies with M0=(log(2N))^max(1,Cinit). It gives the factorization, rational subgroup, smooth factor, and periodic cosets as used. The initial basis has rationality at most M, since M is at least M0. Consequently the polynomial rationality estimates in the published page-547 argument remain uniform when the initial exponent Cinit is arbitrary but fixed. Their exponents depend only on m,d, not on B or the eventual upper exponent E(B).

The conjugated group H_j=gamma_j^(-1)G'gamma_j must use Lambda_j=H_j intersect Gamma. It is not legitimate to identify this with the conjugate of G' intersect Gamma without a lattice comparison. The draft does not make that identification. It invokes exactly the published Claim for this intersection lattice and records its power loss. The representative gamma_j has bounded rational coordinates by the same published reduction argument. The frozen smooth element has bounded coordinates because its ambient metric distance from the identity is at most M. These facts give the stated rational basis and Lipschitz estimates. The polynomial property of h_j follows by conjugating the filtration.

The function F_cell is well-defined on H_j/Lambda_j: replacing x by x*lambda, for lambda in Lambda_j, changes the argument in G only by right multiplication by an element of Gamma. Its supremum is bounded by the original supremum. Its Haar mean need not equal the original Haar mean. The draft correctly subtracts a separate mean on every translated subgroup cell; zero-dimensional factors therefore contribute constants only.

## Cell count and errors

Cutting each of the q residue classes into ceil(M*(log(2N))^D) balanced blocks gives at most O(M^2*(log(2N))^D) cells. Their diameters are O(N/(M*(log(2N))^D)), and their cardinalities are at least N divided by a fixed constant times M^2*(log(2N))^D. Since B is eventually fixed and M is polylogarithmic, all these blocks are nonempty for sufficiently large N.

Right invariance of the group metric removes the factor g'(n)*gamma_j from the comparison when epsilon is frozen. Smoothness therefore gives a pointwise error O((log(2N))^(-D)); no unbounded coordinate norm of g'(n) is introduced. The total weighted error is O(N*(log(2N))^(K-D)), which has the required saving for D=A+K+3.

Qstar=M^U with U=C2+D+5 dominates the new basis rationality, each cell modulus, and N divided by the cell size. The minor-arc estimate is applied with its global N normalization to each cell. The draft then multiplies by the full cell count. It does not replace N by the cell cardinality without justification.

The resulting bound is exactly the one recorded as (M). Choosing b=aB-C2 with

    b*c >= C1*U+C2+2+D+A+K1+4

makes it at most O(N*(log(2N))^(-A-4)), using only M at least log(2N). In the restricted parameter regime, b*kappa>=U+1 gives Qstar<=delta^(-kappa). The lower bound delta>=N^(-sigma) follows later from M being polylogarithmic after B is fixed. Any fixed upper smallness cutoff on delta is also eventually met, since b>1 and M grows.

Only after choosing B does the proof invoke M<=C*(log(2N))^E. It uses this E to select the arbitrary-power progression-saving parameters in (SW). Summing the cell means then gives the required bound with no circular condition that B dominate E(B). The progression hypothesis is strong enough to cover every cell, including short cells, exactly as stated.

## Scope of acceptance

The interpolation lemma and the generic implication (Growth)+(SW)+(MA) => (F) are accepted. The W-tricked application is accepted conditional on its displayed ideal/ordinary mean-zero estimates, finite character expansion, and prime-power error. This review uses the existing independent Type I/II review as the status of that separate input; it is not a new full Type I/II audit.

The centered progression hypothesis (SW), the exact arithmetic centering constant, conjugation invariance of the selected ray condition, and the final prime-pattern application remain separate obligations. Neither reviewed file claims to have silently discharged them. No conclusion that the full Frei–Tinková dependency has been removed follows from these two files alone.
