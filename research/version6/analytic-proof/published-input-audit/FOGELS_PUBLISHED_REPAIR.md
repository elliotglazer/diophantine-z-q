# Published exceptional-zero input and the Kane repair

Checked 2026-11-06. The primary source is E. Fogels, *Über die Ausnahmenullstelle der Heckeschen L-Funktionen*, Acta Arithmetica **8** (1963), 307–309, DOI [10.4064/aa-8-3-307-309](https://doi.org/10.4064/aa-8-3-307-309). The publisher identifies the download as CC-BY. Its [normal download endpoint](https://www.impan.pl/shop/en/publication/transaction/download/product/95181) returned the published scan using Python urllib, although the web tool returned HTTP 403 for the same endpoint. No authentication or access-control workaround was used.

Local file: `fogels1963.pdf`; 1,219,450 bytes; SHA256 `16ad86d54689add23af0c0c54150e999c52c01bba851c97881a9a285dd8c8570`. The PDF contains two scanned spreads: PDF page 1 contains journal pages 306–307, and PDF page 2 contains pages 308–309. Journal page 306 belongs to the preceding article. All three Fogels pages were inspected visually in `fogels-1.png` and `fogels-2.png`. There is no machine-extractable text layer.

## Exact mathematical content

Fogels uses the notation zeta(s,chi) for a Hecke L-function, not just the Dedekind zeta function. On page 307, k is a number field of degree n, d is its discriminant, f is the ideal modulus of a ray character, and

    D = |d| N(f).

The last display on page 307 and its continuation on page 308 state that there is a positive c1=c1(n) such that the region

    Re(s) > 1 - c1 / log(D(2+|Im(s)|))

contains no zero of the Hecke L-functions for the modulus, except possibly a real simple zero beta'=1-delta belonging to a real character chi'. These are called the exceptional zero, character, and function. Page 308 explicitly notes that chi' may be the principal character when n>1.

The unnumbered **Satz** on page 309, whose conclusion is equation (8), says:

    If beta'=1-delta is that exceptional zero of zeta(s,chi')
    for an exceptional character chi' modulo f in a degree-n field k,
    then for every epsilon>0 there is a positive c(epsilon,n),
    independent of D=|d|N(f), such that

        delta > c(epsilon,n) D^(-epsilon).

The direction is unequivocally a LOWER bound on 1-beta'. The theorem's displayed constant depends on epsilon and n; the statement explicitly says it is independent of D. The proof is ineffective through its Brauer–Siegel input. The source does not provide an effective computable value for this constant.

This is a published theorem about the exact Hecke family needed here. It is not an inference from the title of an inaccessible paper, nor an adaptation of a Dirichlet-only theorem.

## What Fogels actually proves

Page 308 first handles the principal exceptional character using the Dedekind-zeta bound from Fogels's earlier paper [2], Section 21, derived there from Brauer's residue estimate. For a nonprincipal real character he takes its index-two kernel in the ray ideal-class group and the corresponding quadratic class-field extension K/k. If Delta is the discriminant of K and d_rel its relative discriminant, he uses

    |Delta| = d^2 N(d_rel),
    N(d_rel) = N(f_chi') <= N(f),
    zeta_K(s) = zeta_k(s) L(s,chi').

Here f_chi' is the conductor; the character is replaced by its primitive inducing character when needed. Thus the exceptional zero is a zero of zeta_K, and |Delta| <= D^2. The degree-2n Dedekind-zeta estimate gives delta >> D^(-2 epsilon); renaming epsilon yields equation (8). This records the argument in the published source, not a new unproved extension of Kane's lemma.

The principal-character possibility is harmless for fixed k=Q(i), but it should not be omitted from a transcription of Fogels's general statement.

## Application to the Gaussian twists

Fix k=Q(i), a finite-order ray character xi of fixed ideal modulus m, and B>0. For each rational Dirichlet character rho modulo the positive integer q, put

    theta(a) = xi(a) rho(N(a))

on ideals coprime to m(q). The norm pullback is a ray character modulo (q), because alpha congruent to 1 modulo (q) implies N(alpha) congruent to 1 modulo q. The product theta is therefore a ray character modulo m(q). Its primitive conductor f_theta divides m(q), so

    N(f_theta) <= N(m) q^2,
    D_theta = 4 N(f_theta) <= 4 N(m) q^2.

There is no infinite-place sign condition over Q(i), and finite order gives trivial archimedean type. These twists fall within Fogels's family. Applying (8) with exponent epsilon/2 gives

    1-beta >= c_{xi,epsilon} q^(-epsilon)

for any exceptional zero. The constants are uniform in rho and q; dependence on the fixed modulus m is allowed. No uniformity in a changing ray character or in B is claimed. Euler factors removed when passing from the primitive to the imprimitive character only have zeros on Re(s)=0, and do not affect the exceptional zero near 1.

## Correct Siegel–Walfisz deduction

Kane v5 equation (6), on page 15, is the explicit-formula estimate described in `PARENT_AUDIT.md`. Pair that estimate with the published Fogels bound just verified. For q <= (log X)^B, choose epsilon=1/(2B) in the last displayed q-bound. Equivalently, apply Fogels directly with exponent 1/(4B) in D_theta. Then

    1-beta >>_{xi,B} (log X)^(-1/2).

For sqrt(X)<=Y<=X this gives

    Y^beta/beta <<_{xi,B} X exp(-c sqrt(log X)),

where an exceptional beta can be taken at least 1/2. The ordinary zero-free-region contribution in Kane's equation (6) has the same shape, after absorbing its fourth power of the logarithm. For 1<=Y<sqrt(X), the elementary degree-two bound on ideal von Mangoldt coefficients gives O(sqrt(X) log X), also within the displayed error. Consequently

    sum_{N(a)<=Y} Lambda_k(a) theta(a)
      = r_theta Y + O_{xi,B}(X exp(-c_{xi,B} sqrt(log X)))

uniformly for 1<=Y<=X, q<=(log X)^B, and all rho modulo q. Here r_theta is one if the primitive character inducing theta is trivial and zero otherwise. Removing prime ideals dividing the chosen imprimitive modulus costs O_xi(log(q+2)log(Y+2)), which is absorbed.

This repairs both visible errors in Kane v5: Lemma 13's direction of inequality, and Proposition 14's choice epsilon=1-1/(2B). The correct choice is epsilon=1/(2B). The repair does not rely on the problematic character-sum estimate in Kane's Lemma 13 sketch.

## Remaining source qualification

The exceptional-zero input is now verified from a published primary source. The exact printed versions of Iwaniec–Kowalski Theorems 5.13, 5.28 and 5.35 are still unavailable in the public/local material checked here. In particular this note does **not** claim to have verified their wording or silently promote Kane's author-version equation (6) to a checked quotation of those theorems. The subsequently retrieved Mitsui 1956 paper supplies an actually checked published contour formula and uniform prime-sum theorem. See `MITSUI_SW_DERIVATION.md` for the complete replacement route, which does not rely on the unseen IK wording or on Kane's erroneous Lemma 13 sketch.

Goldstein's 1970 article remains bibliographically verified but its article bytes were not retrieved: both ordinary public AMS paths returned HTTP 403. Kane's World Scientific article PDF also returned HTTP 403. The normal DK publisher download continues to redirect to the institute homepage, and the publisher page labels that article as subscription access. None of these unobserved published texts is treated as checked.

## Independent published corroboration

The published PDF of M. Coleman and A. Swallow, *Localised Bombieri–Vinogradov theorems in imaginary quadratic fields*, Acta Arithmetica **120** (2005), 349–377, DOI [10.4064/aa120-4-3](https://doi.org/10.4064/aa120-4-3), was obtained from the [publisher's CC-BY endpoint](https://www.impan.pl/shop/en/publication/transaction/download/product/82013). File `coleman-swallow-published.pdf`, SHA256 `69b420c8aebc65a81eef69fcb4dc97ac38241bde3e2780f1d0a695c190a48282`.

Its page 357 (PDF page 9), in the paragraph beginning “Firstly”, explicitly applies Fogels [7] to primitive Hecke characters over a fixed imaginary quadratic field with modulus norm <=F. It gives the exceptional-zero upper bound beta<=1-c(epsilon)F^(-epsilon), for every epsilon>0. The character class is defined on pages 353–354: C*(m,n) consists of primitive finite-modulus characters, extended to ideals with a class-group character and combined with archimedean factor lambda^m. Setting the angular parameter m=0 contains all finite-order ray characters used above. This independently confirms the direction, modulus norm, and imaginary-quadratic scope of the Fogels input. It is corroboration; the original Fogels theorem has itself now been checked.
