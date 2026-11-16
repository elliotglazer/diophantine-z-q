# Published Siegel–Walfisz input and exact specialization

## Source and version

Takayoshi Mitsui, *Generalized Prime Number Theorem*, Japanese Journal of Mathematics **26** (1956), 1–42, DOI [10.4099/jjm1924.26.0_1](https://doi.org/10.4099/jjm1924.26.0_1). The [J-STAGE publisher archive](https://www.jstage.jst.go.jp/article/jjm1924/26/0/26_0_1/_article/-char/en) offers the [published PDF](https://www.jstage.jst.go.jp/article/jjm1924/26/0/26_0_1/_pdf) freely. The printed received date is 31 January 1957, although the volume's bibliographic year is 1956; preserve that distinction.

Retrieved file `mitsui1956.pdf`: 2,823,723 bytes, 42 pages, SHA256 `b71fbd5ae9443991479a73a4e7bde68165b0c0e90b290cd0bd94fd9da416f963`. This is the journal's typeset article, not an arXiv or author preprint. Pages 2, 11 and 12 were visually checked (`mitsui-02.png`, `mitsui-11.png`, `mitsui-12.png`). The text extraction has encoding defects; the mathematical statements below are checked against the page images.

This source removes the need to treat the unobserved exact wording of Iwaniec–Kowalski Theorems 5.13/5.28/5.35 as an audited input. Fogels's published theorem separately supplies the exceptional-zero bound, as documented in `FOGELS_PUBLISHED_REPAIR.md`.

## Exact published statements and conventions

Section 1, beginning on page 2, treats Hecke L(s,chi) for an arbitrary fixed number field K of degree n and a character modulo a ray modulus a-tilde consisting of a finite integral ideal a and a selection of infinite primes. Thus the case K=Q is included; no n>=2 restriction is imposed. The notation E(chi) is defined on page 2 to be 1 for the principal character and 0 otherwise. The modulus norm in the bounds is the norm of its finite ideal part. The subsequent discussion explicitly includes imprimitive characters (Lemma 1 starts with the primitive case and then passes to the general case).

Immediately before Lemma 14 on page 11, Mitsui fixes A>0, restricts to characters whose finite modulus norm is at most (log x)^A, and explicitly declares the constants in O-terms independent of these characters and their moduli. K and A remain fixed.

Lemma 14 (pages 11–12) defines

    P(x,chi) = sum_{N(p)<=x} chi(p) log N(p) log(x/N(p))

over prime ideals and proves

    P(x,chi) = E(chi)x + O_{K,A}(x exp(-c1 sqrt(log x))).

Lemma 15 (page 12) states

    theta_K(x,chi) = sum_{N(p)<=x} chi(p) log N(p)
      = E(chi)x + O_{K,A}(x exp(-c8 sqrt(log x))).

The character is extended by zero on ideals not coprime to its modulus. These are prime-ideal sums, not sums restricted to degree-one prime ideals. Lemma 15's printed proof is omitted as elementary; the deduction below supplies it even for complex-valued characters.

## Published contour step and exceptional zero

The explicit contour formula used in the proof of Lemma 14 is printed at the bottom of page 11:

    P(x,chi) = -(1/(2 pi i)) integral_{2-i infinity}^{2+i infinity}
                    x^s/s^2 * L'(s,chi)/L(s,chi) ds
                + O_K(sqrt(x) log^3 x).

The error discards prime powers of exponent at least two. The s^-2 smoothing makes the contour integral convergent. This is an actually inspected published formula, rather than an unverified theorem-number reference. Mitsui attributes the formula to Landau [4], but it also follows by integrating the absolutely convergent logarithmic-derivative Dirichlet series termwise on Re(s)=2 and applying the elementary Mellin kernel for log(x/u) times 1_{u<=x}.

On page 11, Mitsui defines a central contour Re(s)=1-B/(N(a)^epsilon), |Im(s)|<=5, joined to the curves Re(s)=1-B/log(|Im(s)|N(a)) for larger height. Equation (1.13) gives logarithmic-derivative control along this zero-free contour. The proof chooses epsilon=1/(2A). The possible pole at s=1 contributes E(chi)x. Pages 11–12 bound the central integral by

    O(N(a)^epsilon x exp(-c log(x)/N(a)^epsilon))
      = O(x exp(-c' sqrt(log x))).

For the outer integral the s^-2 factor leads to a bound of the form

    x integral_4^infinity exp(-c log(x)/log(t N(a)))
                         polylog(t N(a)) / t^2 dt.

Split at t=exp(sqrt(log x)). Below that height, log(tN(a)) <= sqrt(log x)+A log log x, giving the required exponential saving. Above that height, discard the exponential factor and use the t^-2 tail, again obtaining the saving. Fixed powers of logarithms are absorbed by reducing the positive constant in the exponent. This is precisely the published proof of Lemma 14, with an allowed weaker fixed logarithmic factor in the outer estimate.

If the earlier exceptional-zero treatment is to be replaced explicitly, Fogels 1963, p.309, equation (8), gives 1-beta >>_{K,epsilon} N(a)^(-epsilon), and pp.307–308 give the remaining zero-free region. Those statements justify a central line slightly to the left of 1 but to the right of every zero, as required. The pole is subtracted in (1.13). The elementary logarithmic-derivative lemmas and contour estimates are in Mitsui itself. No reversal of the incorrect inequality in Kane is being treated as a proof.

## Completing the omitted unsmoothing argument

Let Q=N(a), and initially suppose Q<=(log x)^A. For fixed x choose

    h = exp(-c1 sqrt(log x)/2).

Apply Lemma 14 at x and xe^h (the modulus restriction still holds at the latter point). Subtract and divide by h. The resulting left side is

    theta_K(x,chi)
       + sum_{x<N(p)<=xe^h} chi(p)log N(p) * log(xe^h/N(p))/h.

Every weight in the second sum lies between 0 and 1. Above each rational prime there are at most n prime ideals. Consequently the sum of absolute values in any interval of prime-ideal norms (x,x+v] is O_K((v+1)log(x+v)); prime-ideal norms are integer prime powers, with at most n ideals at each integer norm. The second sum is therefore O_K((xh+1)log x).

The main term on the right side is E(chi)x(e^h-1)/h = E(chi)x+O(xh). The error after division by h is O_{K,A}(x exp(-c1 sqrt(log x)/2)). Absorbing log x gives Lemma 15 with a smaller positive exponent constant. This argument uses absolute values for the boundary terms and is valid for complex chi; it does not assume positivity or monotonicity of theta_K(x,chi).

## From prime ideals to ideal von Mangoldt sums

Define Lambda_K(p^j)=log N(p) for prime ideals p and j>=1, and zero otherwise. For any modulus character, complete multiplicativity holds on ideals after zero extension. Hence

    psi_K(x,chi) = sum_{N(b)<=x} Lambda_K(b)chi(b)
       = theta_K(x,chi) + O_K(sqrt(x)log^2 x).

For the error, sum over exponents j>=2 up to log_2 x. The number of prime ideals of norm at most x^(1/j) is O_K(x^(1/j)), and their log weights are at most log x. This elementary upper bound suffices and is uniform in chi and its modulus. Thus Lemma 15 yields the same Siegel–Walfisz estimate for psi_K.

## Gaussian family and uniform endpoint

Fix a finite-order ray character xi on K=Q(i), with finite modulus m, and B>0. Let rho vary over all rational Dirichlet characters modulo q with q<=(log X)^B. Define theta=xi*(rho composed with norm). This is a ray character modulo m(q). Its modulus has norm

    Q = N(m)q^2 <= N(m)(log X)^(2B).

For sqrt(X)<=Y<=X and all sufficiently large X depending only on m and B, this is at most (log Y)^A with the single fixed choice A=2B+1. Indeed log Y>=log X/2 and the extra factor log X absorbs N(m)2^A. Mitsui's estimate, applied at Y, therefore gives

    psi_K(Y,theta)=r_theta Y
          +O_{xi,B}(X exp(-c_{xi,B}sqrt(log X))).

For 1<=Y<sqrt(X), the sum is O_K(Y log^2(Y+2)) by the preceding elementary prime-power count, and r_theta Y obeys the same bound. This is smaller than X exp(-c sqrt(log X)) for all sufficiently large X. Enlarging the implied constant handles the remaining bounded X. Thus the displayed estimate holds uniformly for **every 1<=Y<=X**, all q<=(log X)^B, and every rho modulo q.

Here r_theta=1 precisely if theta is principal, equivalently if its primitive inducing Hecke character is trivial. This does not require theta to equal 1 at ideals excluded by its imprimitive modulus. If one chooses to run the proof on the primitive conductor instead, restoring the excluded prime-power terms costs

    O_xi(log(q+2) log(Y+2)),

since there are O_xi(log(q+2)) prime ideals above the prime divisors of m(q), and each contributes at most log Y in its entire prime-power tower. This error is absorbed. Either the direct imprimitive statement or this primitive reduction gives the same main term.

## Ordinary rational family

For K=Q, let rho be any Dirichlet character modulo q<=(log X)^B. Regard it as a Hecke character with finite modulus q and, if needed, the real infinite place to accommodate odd parity. The finite modulus norm is q. For sqrt(X)<=Y<=X choose A=B+1; the same argument applies. It gives uniformly for 1<=Y<=X

    sum_{n<=Y} Lambda(n)rho(n)
      = r_rho Y + O_B(X exp(-c_B sqrt(log X))),

where r_rho=1 exactly for the principal character modulo q. The prime-power and imprimitive-modulus errors are special cases of those already proved. One may also multiply rho by a fixed rational Dirichlet character, absorbing its fixed conductor in A=B+1 and allowing the constants to depend on that fixed character.

## Scope

This establishes the precise Gaussian and rational Siegel–Walfisz inputs needed for the finite-ray-character replacement, with published parent statements and all specialization steps made explicit. It does not assert a nilsequence estimate, a uniformity statement over varying number fields, or a bound uniform in B or in the fixed ray modulus. The constants are ineffective because of the exceptional-zero input. Kane's and DK's unobserved final typeset versions remain unverified; their author-version status is unchanged.
