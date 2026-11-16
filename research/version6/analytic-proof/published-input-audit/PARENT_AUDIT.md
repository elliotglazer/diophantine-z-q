# Published-parent audit

Status, 2026-11-06: exact author-version statements inspected, including page images. Neither the Kane nor the DK final publisher PDF was retrieved. Kane's latest author version still contains two consequential typographical errors in the proof of Proposition 14. Two published replacement inputs have now been retrieved and checked: Fogels 1963, theorem on page 309, equation (8), and Mitsui 1956, Lemmas 14–15 on pages 11–12. See `FOGELS_PUBLISHED_REPAIR.md` for the exceptional-zero input and `MITSUI_SW_DERIVATION.md` for the complete Gaussian and rational Siegel–Walfisz specialization, including all endpoint, prime-power, principal-character, and imprimitive-modulus details. The exact IK book statements remain unverified; the Mitsui route avoids relying on their unseen wording.

## Kane, Proposition 14

Reference: Daniel M. Kane, *An asymptotic for the number of solutions to linear equations in prime numbers from specified Chebotarev classes*, International Journal of Number Theory 9 (2013), 1073–1111, DOI [10.1142/S1793042113500139](https://doi.org/10.1142/S1793042113500139).

The checked version is [arXiv:1009.1368v5](https://arxiv.org/abs/1009.1368v5), dated 5 November 2012. Its 40-page PDF is `../sources/kane-v5.pdf`, SHA256 `e12a76769ca7dc1d91bdd37a335a9cb21a85d678b48dc1cf938565147df8bc51`. The current author-hosted `chebGold.pdf` is an older 34-page version and is not the preferred statement source. World Scientific returned HTTP 403; no claim that the final typeset pages were compared is justified.

Definitions 3 and 4 on page 9 use the ideal von Mangoldt weight Lambda_L(p^k)=log Norm(p), and

    F_{L,xi,Y}(a) = sum_{Norm(ideal)<=Y} Lambda_L(ideal)*xi(ideal)*exp(2*pi*i*a*Norm(ideal)).

The sum is over nonzero integral ideals. In Section 4.1.1, pages 15–16, L and xi are fixed, while chi is a rational Dirichlet character modulo q, pulled back to ideals by chi(ideal)=chi(Norm(ideal)). The restriction q<=log(X)^B is introduced there. The modulus of the product divides q*m, where m is a fixed modulus for xi, so its finite conductor norm is at most Norm(m)*q^[L:Q]. For our finite-order Gaussian ray characters there is no varying archimedean parameter. Imprimitive characters are extended by zero on ideals not coprime to their chosen modulus.

On page 16 Proposition 14 states, for Y<=X and the preceding restriction on q,

    F_{L,xi*chi,Y}(0) = r*Y + O(X*exp(-c*sqrt(log X))),

where r=1 when the associated Hecke character xi*chi is principal, and r=0 otherwise. Constants are uniform in chi, q, X and Y. Although the displayed sentence mentions dependence only on L and xi, the preceding B is fixed; the proof necessarily gives dependence on B through the Siegel parameter. Do not claim uniformity as B varies. Likewise do not claim uniformity as the Gaussian ray modulus or xi varies. A fixed finite set of xi can be handled by taking maxima/minima of their constants after the sieve cutoff is fixed.

Two genuine errors remain in v5. They are visible in `kane-16.png`, not extraction artifacts:

1. Lemma 13 prints beta > 1-c(epsilon)/q^epsilon. The needed Siegel zero-free bound is 1-beta >= c(epsilon)*q^(-epsilon), equivalently beta <= 1-c(epsilon)/q^epsilon. The printed direction gives no usable upper bound for Y^beta.
2. Proposition 14's proof selects epsilon=1-1/(2B). The required choice is epsilon=1/(2B), or any smaller positive number. The printed choice gives q^(-epsilon)>=log(X)^(-B+1/2), which does not yield square-root logarithmic decay for general B.

Unlike the older author PDF, v5 Proposition 14 correctly has sqrt(log X), not sqrt(X), in its conclusion.

There is also a separate defect in the sketch of Lemma 13: the printed character-sum bound O(x^(1-1/d)+max(x,q)) contains an O(x) term. On its own it cannot justify convergence in a half-plane left of Re(s)=1 as claimed in the preceding sentence. This prevents treating the one-paragraph Hecke generalization as a complete checked proof after only two textual corrections.

## Correct final deduction, once the Hecke-Siegel bound is available

Fix B>0. Write psi_{xi*chi}(Y) for the ideal sum above. Equation (6), page 15, is the prime-ideal explicit-formula estimate with principal main term, possible exceptional term -Y^beta/beta, and an error bounded by

    Y * exp(-c*log Y/(sqrt(log Y)+3*log(q^d)+O(1)))
      * (log(Y*q^d)+O(1))^4.

For sqrt(X)<=Y<=X and q<=log(X)^B, the error is O_{L,xi,B}(X exp(-c1 sqrt(log X))). The polynomial logarithmic factor is absorbed by reducing c1. If 1-beta>=c_epsilon*q^(-epsilon), take epsilon=1/(2B). Then log Y>=log X/2 implies Y^beta <= Y exp(-c2 sqrt(log X)); the exceptional zero can be assumed beta>=1/2, so 1/beta is harmless. For Y<sqrt(X), the elementary coefficient bound |a_n|<=d log n gives psi(Y)=O_d(sqrt(X) log X), while rY has the same harmless size. This proves the stated uniform-in-Y conclusion, including endpoints small relative to X.

Passing between primitive and imprimitive Hecke L-functions removes only prime-power terms above primes dividing the selected modulus. The total change through Y is O_{L,xi}(log(q+2)*log(Y+2)), sufficient here. Thus principal means principal after induction to the primitive character; it does not mean the extended-by-zero function equals one at excluded ideals.

## Dodos–Kanellopoulos, Theorem 5.1

Reference: P. Dodos and V. Kanellopoulos, *Uniformity norms, their weaker versions, and applications*, Acta Arithmetica 203 (2022), 251–270, DOI [10.4064/aa210728-27-2](https://doi.org/10.4064/aa210728-27-2). The [publisher page](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/203/3/114682/uniformity-norms-their-weaker-versions-and-applications) reports online publication on 10 May 2022 and says PDF access requires an institutional subscription. Its normal Download link redirected to the institute homepage. No access restriction was bypassed.

The checked source is [arXiv:1610.00487v4](https://arxiv.org/abs/1610.00487v4), dated 9 June 2022, which itself lists the published journal reference. Cached PDF SHA256: `1d71ecfcb7a1970ce3d7a10ac426f8c94e9d1d6a88886cb378ca19a099963508`. Pages 12–13 were visually inspected (`dk-12.png`, `dk-13.png`). Because v4 postdates publication, version equality must not be assumed without the final typeset pages.

The exact quantifier pattern is:

    for every integer s>=2, real C>=20, and 0<delta<=1,
    there exist eta>0, M>0, c>0, and one (s-1)-step nilmanifold G/Gamma,
    equipped with a smooth Riemannian metric,
    such that for every positive integer N and every prime N' in [CN,2CN],
    every nu:Z/N'Z -> R_+ with ||nu-1||_{U^{2s}(Z/N'Z)}<=eta,
    and every real f:[N]->R with |f(n)|<=nu(n),
    if ||f||_{U^s[N]}>=delta, then
    |E_{n in[N]} f(n) F(g^n*x)|>=c
    for some F:G/Gamma->[-1,1] with Lip(F)<=M, g in G, and x in G/Gamma.

The constants and nilmanifold are independent of N, N', nu, and f once s,C,delta are fixed. The group G is connected, simply connected, and nilpotent of step at most s-1, and Gamma is discrete and cocompact. The theorem supplies a linear orbit g^n*x. It does not by itself assert a polynomial-sequence theorem or a complex-valued-f version.

The interval norm is the normalized zero-extension norm

    ||f||_{U^s[N]} = ||f*1_[N]||_{U^s(Z/N'Z)} / ||1_[N]||_{U^s(Z/N'Z)}.

Section 5.1.1 states its independence of the ambient cyclic group when N'>2N. All cyclic and interval averages are normalized averages. The majorant hypothesis is on the full cyclic group, not just its restriction to [N].

For target U^{u+1}, this requires majorant uniformity U^{2u+2}, not U^{2u}. The following paragraph explicitly gives the sufficient linear-forms complexity (4^s,4s,1), with the first entry 4 raised to s. It is not (4s,4s,1); the distinction is visible in the page image. With s=u+1, choose enough complexity to control all 4^{u+1} vertices and all subproducts of the (2u+2)-cube.

## Uncompleted exact-source checks

No local copy of Iwaniec–Kowalski Chapter 5 was found in the targeted project source directories. The author's public `ik-ant-exp-sums.pdf` is only Chapters 11–12. The exact printed statements of IK Theorems 5.13, 5.28, and 5.35 have therefore NOT been independently transcribed or verified in this pass. Kane attributes the explicit formula and zero-free region to 5.13 and 5.35; 5.28 is a Dirichlet Siegel theorem whose adaptation to Hecke characters is part of Kane's own argument, not a direct quoted Hecke theorem.

A direct published alternative is L. J. Goldstein, *A generalization of the Siegel-Walfisz theorem*, Transactions AMS 149 (1970), 417–429, DOI [10.1090/S0002-9947-1970-0274416-6](https://doi.org/10.1090/S0002-9947-1970-0274416-6). Its public AMS route returned HTTP 403 and JSTOR supplied no readable article. Its exact hypotheses have not been checked, so this audit does not promote it to an accepted replacement based on its title or citations alone.
