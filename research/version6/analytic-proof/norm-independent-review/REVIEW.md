# Independent audit of Gaussian norm transfer

Verdict: accept the revised unweighted norm-transfer lemma (NT) as proved, subject to its stated hypotheses and with the explicit scope limits below. The original draft needed precision repairs before signoff. The author incorporated them during this review. I found no remaining mathematical gap in (NT).

The accepted `quotient-audit/NORM_TRANSFER.md` has SHA256 `2fda5cb7119a00dbd8815a108e9ba4cdfc06a6ab1fe10ad2d1f657522c059380`. I did not author that proof. I reviewed its argument independently, supplied the repairs below, and checked the revised text.

## Published input

I checked [the published Green–Tao paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf), especially Theorem 2.9, Definitions 1.1–1.2 and 2.2–2.7, and the one-parameter case of Lemma 6.7. The pinned local PDF has SHA256 `8c7ea5eced84dc5da97508f4eda39fa84c958d3e659a797ab402645c1c207c8f`.

Theorem 2.9 supplies precisely the horizontal-character obstruction to failure of ordinary equidistribution that the draft uses, with polynomial dependence on the inverse error and an adapted rational basis. The binomial smoothness norm in the draft matches Definition 2.7. The proof does not invoke the multiparameter equidistribution theorem. The cited coordinate characterization is a structural polynomial-sequence fact; its one-parameter use is sufficient here.

## Repairs required and incorporated

The revised statement explicitly uses the published ambient convention: G is connected, simply connected, and nilpotent; Gamma is discrete and cocompact; the filtration consists of closed connected rational subgroups; the basis is adapted; g is a polynomial sequence for that filtration; and F is Lipschitz. It takes positive m,d and q at least one integral, with the zero-dimensional case handled separately.

The product-space clause now requires total delta-equidistribution of the entire product orbit. Mean-zero factors, or even separately equidistributed factors, do not imply that hypothesis. The diagonal orbit is a basic counterexample to such an implication. The revised clause is the ordinary application of (NT) to dimension 2m and is valid. It must not later be quoted as a proof that a Type II product orbit is equidistributed.

The parameter choices now explicitly include

    6*Cstar*kappa < c0/2,
    sigma < sigma0,
    2*kappa*sigma < 1/4.

These remove ambiguity in the horizontal-character contradiction and floor estimates. All enlargements of Cstar must occur before kappa and sigma are fixed, as the preceding paragraph of the draft specifies. Fixed multiplicative constants are absorbed by decreasing delta0 and increasing X0, both permitted by the statement.

## Quadratic coefficient lemma

The lemma (QE) is correct with the displayed scales. Here is an explicit check of the two steps most likely to lose a power of X.

Expand binom(P(t),j) as a fixed rational linear combination of P(t)^h, h at most j. In a degree-r coefficient of P(t)^h, a monomial with multiplicities n0,n1,n2 has n0+n1+n2=h and n1+2n2=r. Its magnitude is at most B0^h X^(h-r/2), up to a constant depending on d. Changing t^r to the binomial basis uses only fixed coefficients and contributes to binom(t,l) only for r at least l. Thus the bound C_d B0^j X^(j-l/2) follows for X at least one. This argument includes a0 of size X and a1 of size sqrt(X); it does not silently treat them as bounded constants.

The coefficients s[j,l] are integers because the polynomial is integer-valued on the integers. The top coefficient is D_j=(2j)! a2^j/j!, a nonzero integer of size B0 raised to a bounded power. The even rows form a triangular system. Set K_j=product of D_h for h from j to d. The exact identity used in descending induction is

    K_j*alpha_j = K_(j+1)*beta_(2j)
      - sum_{h>j} s[h,2j]*(K_(j+1)/K_h)*(K_h*alpha_h).

Every displayed multiplier is an integer. The beta term is controlled because X^j/L^(2j) is at most B0^(2j). In a higher-alpha term, the factor X^(h-j) from s[h,2j] cancels the X^(-h) bound on alpha_h. Integer multiplication respects distance modulo one, so choosing nearest representatives is not an illicit division modulo one. Passing to the common positive multiplier |K_1| preserves a polynomial bound in B0. Constant alpha_0 never enters a positive even row. This proves the claimed smoothness bound with a nonzero integer multiplier of the required size.

## Horizontal character and composition

The horizontal-character observation is valid. Representatives of the nonconstant binomial coefficients can be chosen with magnitude at most T/X^j. On an initial interval of length floor(X/(100*d*T)), their sum varies by less than the required fixed arc length. A smooth mean-zero function on the circle can equal one on that arc. A nontrivial horizontal character has full circle image because G is connected, and therefore pushes Haar probability to circle Haar probability.

There is also a direct quantitative check of the Lipschitz estimate, avoiding any unspecified metric-conversion exponent. Write eta(x)=k dot psi(x) modulo one. For every link of a chain defining the published metric, circle distance of the eta values is at most |k|_1 times the minimum of the two coordinate lengths used by that link. Summing and taking the infimum shows

    Lip(eta on G/Gamma) <= |k|_1 <= m*|eta|.

Passing to the quotient is valid because eta annihilates Gamma. This proves the weaker polynomial-in-T bound used by the author, with fixed constants. Taking c0 sufficiently small makes both the initial interval admissible for total delta-equidistribution and delta times the composed test norm less than one. The sigma0 restriction handles its floor.

For P quadratic, the stretched filtration Gtilde_j=G_ceil(j/2) is a valid filtration: the commutator inclusion follows from ceil(i/2)+ceil(j/2) at least ceil((i+j)/2). It has degree at most 2d, is rational, and uses the same adapted basis. The one-parameter coordinate characterization of polynomial sequences shows that composition doubles each relevant degree bound. Thus Theorem 2.9 applies at error epsilon=delta^kappa with the original basis, since Q is at most epsilon^(-1).

Applying (QE) to eta composed with g gives a nonzero integer multiple k*eta whose magnitude and smoothness norm are at most C delta^(-6*Cstar*kappa). Multiplication cannot make this character trivial on connected G. The revised strict inequality involving c0 absorbs C for sufficiently small delta and gives the contradiction to total equidistribution. Only ordinary equidistribution is concluded for each pullback; the proof correctly absorbs every progression restriction into P before invoking this conclusion.

## Lattice, intervals, and residue blocks

The conversion from Gaussian ideals to lattice points is correct. Z[i] is principal, and every nonzero ideal has exactly four generators. A ray character on principal ideals is constant for generators in a fixed invertible residue class modulo H, and its zero extension has the same periodicity for the other residue classes. It is also invariant under units because it is an ideal character. Thus the factor 1/4 is exact, including axis points.

For a fixed horizontal row, the annulus has at most two x-intervals. There are at most four boundary blocks per residue class modulo H. With O(sqrt(X)) relevant rows and M=floor(delta^kappa*sqrt(X)/H), the total discarded point count is O(H*sqrt(X)*M)=O(delta^kappa X). This remains true for an arbitrarily thin annulus: it may have no interior blocks, but the same boundary estimate applies. The point zero costs at most one term and is absorbed because X delta^kappa grows under the stated range.

After splitting a full interior block by its index modulo q, each nonempty class has length at least M/(2q), once M is at least 2q. The polynomial is P(n)=(x0+Hq n)^2+y^2. The norm congruence is constant on this class without requiring gcd(H,q)=1 or coprimality of the selected residue. Its coefficient scales are a0=O(X), a1=O(Hq sqrt(X)), a2=H^2 q^2. Also sqrt(X)/L=O(Hq/delta^kappa). Choosing delta0 depending on H makes all these fit B0 at most delta^(-5*kappa).

The floor and endpoint conditions follow quantitatively: at the smallest allowed delta, the ratio delta^kappa sqrt(X)/(Hq) is at least X^(1/2-2*kappa*sigma)/H, which grows by the revised inequality. The same range gives Hq=o(sqrt(X)), validating |x0| at most 2sqrt(X) after shifting the starting index. Hence each full class has the length and coefficient bounds required by (QE).

Each class contributes at most its own length times delta^kappa times the Lipschitz norm. The classes partition O(X) interior lattice points, so summing introduces no missing number-of-blocks factor. Adding the boundary estimate proves (NT), uniformly in both endpoints and the norm residue. Partial summation introduces only the stated logarithm, with the lower integration endpoint at norm 1.

## What this acceptance does not prove

This audit accepts the unweighted Gaussian norm-transfer estimate and its explicitly conditional product-space version. It does not prove product-orbit equidistribution, the Type I/II decomposition and exceptional-pair estimates, progression prime main terms, or quantitative factorization. The final Type I/II interface is valid as a description of which congruence and interval restrictions (NT) can accept, but applying it still requires all its equidistribution and complexity hypotheses at each inner scale. In particular it does not establish that Frei–Tinková has been removed from the full construction.

No empirical test or sampled computation is used as a substitute for the argument above. The acceptance is based on the exact triangular identities, scale estimates, source theorem hypotheses, and lattice partition count.
