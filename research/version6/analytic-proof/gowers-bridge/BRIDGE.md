# Gaussian nilsequence estimates imply the required polynomial transfer

The existing appendix already supplies the polynomial transference argument. The new work needed at its entrance is a Gaussian linear-replacement lemma and its application to the local Gowers cubes. `bridge.tex` proves these from the separately supplied centered Gaussian nilsequence estimate. It does not assume any theorem of Frei–Tinková.

The bridge is conditional on the precise nilsequence interface stated in its first equation. The preceding norm-transfer, progression, Type I/II and factorization work must establish that interface. This file does not certify those arithmetic arguments or silently replace their hypotheses.

## What changes in the appendix

In `work/quartic-version5-release/sun-proof/sun_appendix.tex`:

1. Replace the FT proof-repair remark at lines 379–411 with the corrected relative-inverse application in `bridge.tex`. The majorant exponent is U^(2s) for target U^s, thus U^(2u+2) for target U^(u+1).
2. Restrict the general-Galois statement preceding `prop:v5-artin-patterns` to the fixed Gaussian ray fields and conjugation-invariant class unions used by the actual application. The new arithmetic estimates do not assert the theorem for every finite Galois extension.
3. Replace the FT Theorem 1.4 invocation and its use in the cube estimate, approximately lines 442–489, by the refined-Gowers and fixed-system linear-replacement lemmas proved here.
4. Keep the proof beginning “We now use the arbitrary-function dense-model theorem” at approximately line 491. The new bridge supplies its exact required `eq:v5-global-gowers`. The bridge's last paragraphs clarify the existing two-cutoff order, boundaries and final diagonal; they may be merged into that proof rather than duplicated.

No new polynomial-prime theorem is needed. In particular the special dense model 1 for the ordinary prime weight is never applied to an Artin weight. The arbitrary-function part of the published Tao–Ziegler theorem is used.

## Why the extra auxiliary cutoff is necessary

For a fixed small-prime cutoff v, the ordinary prime majorant has an error that only becomes small as v increases. A fixed-v relative inverse application does not automatically show a genuine o_N(1) Gowers norm for the centered ray weight. Nor is it safe to multiply an error of size O(1/v) by a constant depending exponentially on v through q or A.

The proof uses a separate auxiliary cutoff z to establish a statement about every fixed finite-complexity affine system. With V_z=D times the product of primes up to z not dividing D, diagonalization of the fixed-modulus nilsequence theorem gives small U^s norms for h_(C,V_z,b), uniformly in the finitely many selected residues at each stage. The published relative generalized von Neumann argument then replaces each ray-prime factor by its conditional-density multiple of the ordinary-prime factor.

Summing the refined residue classes does not multiply the error by V_z^d. The exact normalized mass is

    (number of admissible residue vectors)/V_z^d * (V_z/phi(V_z))^t
      = product_(p|V_z) beta_p(Psi) = O_Psi(1).

Outside the fixed set of primes dividing nonzero minors of the linear-part matrix, beta_p=1+O_t(p^-2), uniformly in moving constant terms. This proves an actual o_N(N^d) replacement theorem for each fixed system, after the auxiliary cutoff disappears from the statement.

Only then freeze the appendix's v and apply the replacement theorem to its finitely many q and wrap-around cube systems. The remaining O(1/log v) is exclusively the explicitly computed ordinary-prime local-factor error. The replacement error is o_v(1), so no growing-in-v constant multiplies a persistent majorant error.

## Exact interfaces and normalization

The input is fixed-modulus orthogonality of

    h_(C,V,b)(n) = phi(V)/V * [Lambda'_C(Vn+b) - mu_C(b)*Lambda'(Vn+b)]

against every bounded-complexity polynomial nilsequence, with every negative power of log N, uniformly in the orbit and bounded Lipschitz functions. The constants may depend on the fixed V. All relevant class unions are a fixed finite set. The ordinary and ray weights are supported on primes; an ideal-von-Mangoldt formulation must first use the established prime-power comparison.

Because 0<=Lambda'_C<=Lambda' and 0<=mu_C<=1, |h|<=lambda_(V,b). A fixed positive rescaling of h restricted to [L^(3/5),L] is dominated by the published ordinary prime majorant. The removed interval has vanishing U^s norm by the crude logarithmic bound and its O(L^-2/5) density. The majorant is defined on the entire cyclic group, not extended by zero outside [L].

Request enough linear-forms complexity for all 4^s vertices of a 2s-dimensional cube, plus the relative generalized von Neumann requirements. Expanding every centered subproduct gives U^(2s)(nu-1)=o(1). A target U^(u+1) therefore uses the 2u+2 cube. The DK nilmanifold, metric, correlation threshold and Lipschitz bound are fixed after choosing s,C,delta, and its linear nilsequence is covered by the polynomial-nilsequence interface.

At stage j first choose z_j large enough for the limiting majorant errors to lie below the DK tolerances for the first j tests. Then choose the size threshold for all residues and those tests. In a linear count at physical scale N, the refined Gowers estimate is applied at L comparable to N/V_(z_j), including fixed multiples from normal form. Choose the physical threshold N_j so all these scales exceed the required L_j. There is no implicit equation z=z(N/V_z).

The normal-form extension is an actual bijective change in a larger lattice, not restriction to a zero section. Choosing v_ij in ker(dot psi_j) outside ker(dot psi_i) gives the extension psi_i(x+sum y_ij v_ij). Its convex region includes a full box in y. The total sum is exactly the original sum times that box's cardinality. Thus the published normal-form estimate returns the claimed original-scale error.

## Published sources and exact locators

- Green and Tao, *Linear equations in primes*, Annals of Mathematics 171 (2010), 1753–1850. [Published PDF](https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf). Lemma 4.4, printed p.1773, and the normal-form reduction pp.1774–1775; Proposition 6.4, p.1780, with the explicit enveloping-sieve construction pp.1839–1842; Proposition 7.1, pp.1781–1782, proved in Appendix C, pp.1818–1827. Only these ordinary-prime majorant and relative functional statements are used for the new linear replacement. They do not require an Artin theorem.
- Dodos and Kanellopoulos, *Uniformity norms, their weaker versions, and applications*, Acta Arithmetica 203 (2022), 251–270, [DOI](https://doi.org/10.4064/aa210728-27-2), Theorem 5.1. The checked text is [arXiv v4](https://arxiv.org/abs/1610.00487v4), pp.12–13, dated 9 June 2022; it states the U^(2s) hypothesis and the full quantifier order. Cached PDF SHA256: `1d71ecfcb7a1970ce3d7a10ac426f8c94e9d1d6a88886cb378ca19a099963508`. The publisher's final PDF was not obtained by the parallel audit. The theorem is published, but equality of the checked author version and final typeset statement has not been verified. This source-version limitation is retained explicitly.
- Bienvenu, *A higher-dimensional Siegel–Walfisz theorem*, Acta Arithmetica 179 (2017), 79–100, [DOI](https://doi.org/10.4064/aa8600-10-2016). Theorem 1.1, pp.79–80, gives the ordinary-prime fixed-coefficient affine correlation asymptotic uniformly over bounded normalized constant terms and convex regions. This is enough after v is fixed. The stronger Theorem 1.3 is not needed. The cached published PDF is in the existing sun-proof sources.
- Tao and Ziegler, *Polynomial patterns in the primes*, Forum of Mathematics, Pi 6 (2018), e1, [published PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B46C46EEC613F34152B7904E83EA0E3F/S2050508617000038a.pdf/polynomial-patterns-in-the-primes.pdf), [DOI](https://doi.org/10.1017/fmp.2017.3). Theorem 9, p.21; Theorem 11, p.28, with the arbitrary-function assertion; Corollary 3, p.38; Proposition 6 and its ordinary local-factor computation, pp.39–40; Theorem 13, p.41. The ordinary majorant is equation (36), p.29, its local pseudorandomness is Proposition 2, p.30, and Appendix A supplies the polynomial-forms estimates. Cached published PDF SHA256: `ba1645db9857dd621e8ea6a280927c1e4b7cef5f6df04a4f19e7ac7782220f43`.

Add bibliography keys `v6gtlinear` and `v6bienvenu`; existing keys `v5dk` and `v5tz` are used by the fragment. The cached published Tao–Ziegler article has 60 pages. The existing bibliography's “73 pp.” should be checked/corrected when integrating; theorem numbering here is the published numbering.

Exact insertion text for the existing `thebibliography` (kept here because this task writes only the three bridge files):

```tex
\bibitem{v6gtlinear}
B. Green and T. Tao, \emph{Linear equations in primes},
Ann. of Math. (2) \textbf{171} (2010), no.~3, 1753--1850.
\url{https://annals.math.princeton.edu/wp-content/uploads/annals-v171-n3-p08-p.pdf}.
Lemma~4.4, Propositions~6.4 and 7.1, Appendices~C and D.

\bibitem{v6bienvenu}
P.-Y. Bienvenu, \emph{A higher-dimensional Siegel--Walfisz theorem},
Acta Arith. \textbf{179} (2017), no.~1, 79--100.
\url{https://doi.org/10.4064/aa8600-10-2016}.
Theorem~1.1, pp.~79--80.
```

## Boundaries and final limits

The local-cube truncation x<R costs O((log n)^(2^a) R/n), with R=n^rho, so it tends to zero for fixed v. Wrap-around integers define finitely many convex regions, and fixed v gives J/n in a positive compact interval. Thus the absolute linear-count error o_v(n^(2a+1)) becomes o_v(1) after division by n*J^(2a), uniformly over all allowed J and the finitely many q.

In the polynomial count, a moving strip of width O(T²) is first enclosed in a fixed epsilon*N strip. Theorem 15 of Tao–Ziegler averages over the full cyclic x domain, so a localization argument is needed. Isolate the possible constant-shift majorant as nu0 and let F(x) be the average of the remaining factors over m. Apply Theorem 15 to nu0*F, nu0*F² (with independent m,m') and nu0: all pairwise shift differences are nonconstant. The resulting weighted L2 bound, followed by weighted Cauchy–Schwarz, reduces any x-strip to the one-dimensional interval mean of nu0. This gives normalized mass O(epsilon)+o_(v→infinity)(1)+o_(v,epsilon)(1). Stage j preserves every boundary estimate for epsilon in {1,1/2,...,1/j}. For any allowed T=o(sqrt N), first fix k: eventually T²/N<1/k, so the strip estimate with epsilon=1/k applies. Take the upper limit in N, then let k increase. No comparison T²/N<1/j(N) is imposed. A crude pointwise log-power bound is not used for this boundary.

The final limit is N to infinity uniformly in the allowed T range at each frozen v, followed by v increasing slowly. One must not simultaneously demand T=o(sqrt N) while holding v fixed and keeping T/sqrt N bounded below by a positive v-dependent constant. The final diagonal supplies omega(N) and then allows every T with omega(N)*sqrt N<=T=o(sqrt N). No rate in the fixed-modulus nilsequence estimate is promoted to uniformity in growing moduli.

This completes the bridge as an implication from the stated Gaussian nilsequence theorem. Both independent reviews accepted bridge.tex at SHA256 `b9284d40889c3d4308fd0c3d532b7d59c792f22894acc6db21c19a2422c307cd`: the mathematical receipt is `../type-i-ii/BRIDGE_REVIEW_RECEIPT.json`, and the source/interface receipt is `../bridge-source-independent-review/receipt.json`. The upstream arithmetic input and the DK publisher-version comparison remain separately tracked. Static checks confirm balanced braces and environments, eight unique labels, and all sixteen references resolved in the integration sources; full manuscript typesetting remains an integration check.
