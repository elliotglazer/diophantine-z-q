# Independent review of the published Siegel–Walfisz input and progression terms

Reviewer: `/root/astra_sub1000_quotients`, an agent independent of the
Siegel–Walfisz derivation author and progression-fragment author.
Date: 2026-11-06.

Verdict: accepted for the exact hashes below. No mathematical gap was
found in the stated fixed-field Gaussian and rational Siegel–Walfisz
specializations, or in the progression fragment conditional on that input.
The required analytic input is now an inspected published theorem of
Mitsui; no uninspected statement of Iwaniec–Kowalski or Kane is needed.

This is a review of those steps, not a certification of the entire
nilsequence-to-Gowers or final Diophantine theorem chain.

## Reviewed bytes

| File | SHA256 |
|---|---|
| `published-input-audit/MITSUI_SW_DERIVATION.md` | `b3a14e70ec20a0154642ad062f431e40262c009a0caf496e5afe610156d72b88` |
| `progression_mainterms.tex` | `8564d37de829edff8e0864362b6185f6b44f1ac4c1f053c0a34fe6b16444a35b` |
| `published-input-audit/mitsui1956.pdf` | `b71fbd5ae9443991479a73a4e7bde68165b0c0e90b290cd0bd94fd9da416f963` |
| `published-input-audit/fogels1963.pdf` | `16ad86d54689add23af0c0c54150e999c52c01bba851c97881a9a285dd8c8570` |
| `published-input-audit/gaussian_hecke_sw.tex` | `56c7d6a62678123d2fd89bfc473f6934e75bd1da04233b292bda4cc9be77262e` |
| `published-input-audit/bibliography.tex` | `73bb6ad148114ae79bc204ab18ddf4337658a1b35e392f45c090a2d06c43135b` |
| `published-input-audit/applications.json` | `f9bfb6fd3ba85e8079088ec2389bd72ee7a9e17514edf2a5280f0e3b69d71ab1` |

Paths are relative to `work/frei-tinkova-removal-001`.

## 1. Primary-source inspection

I independently viewed the published Mitsui page images for pages 1, 2,
11, and 12, rather than relying on the defective OCR text. The publisher's
J-STAGE metadata was checked at
https://www.jstage.jst.go.jp/article/jjm1924/26/0/26_0_1/_article/-char/en .
It identifies Japanese Journal of Mathematics volume 26, pages 1–42,
bibliographic year 1956, DOI 10.4099/jjm1924.26.0_1. The article itself
prints a received date of 31 January 1957. The derivation correctly
preserves this bibliographic distinction.

The exact input is Mitsui's Lemma 15 on printed page 12:

    sum_{N(p)<=x} chi(p) log N(p)
       = E(chi) x + O(x exp(-c8 sqrt(log x))).

The symbols refer to prime ideals, not only prime ideals of residue
degree one. Page 2 defines the family as Hecke characters for an arbitrary
fixed number field, modulo a finite ideal together with allowed infinite
places. It defines E(chi)=1 for the principal character and zero otherwise.
The paragraph immediately before Lemma 14 on page 11 fixes A>0, restricts
the finite modulus norm to at most (log x)^A, and explicitly declares the
O-constants independent of characters and their moduli. Thus the needed
uniformity is part of the inspected published statement.

The field is fixed. The statement does not give a bound uniform in a
varying field, varying A, or varying fixed Gaussian ray modulus. None is
needed or claimed by the reviewed derivation.

The proof of Lemma 15 is omitted in the article. This does not hide an
uninspected theorem: Lemma 15 itself is the published input. Moreover,
the derivation supplies a valid elementary deduction from the published
smoothed Lemma 14. That deduction was checked independently below.

## 2. Unsmoothing and prime powers

With h=exp(-c1 sqrt(log x)/2), subtracting the two smoothed sums at x
and xe^h and dividing by h gives theta(x,chi), plus a boundary sum whose
coefficients have absolute value at most one. A fixed degree-n number
field has at most n prime ideals of any given integer norm. Therefore
the boundary interval contributes O_K((xh+1)log x), without any sign
assumption on chi. The main term differs from E(chi)x by O(xh), and the
smoothed errors divided by h retain a square-root-logarithmic exponential
saving. This establishes the asserted complex-character unsmoothing.

Adding prime-ideal powers of exponent at least two costs
O_K(sqrt(x)log^2(2x)). Each prime ideal is counted with weight log N(p),
not log N(p^j). The elementary bound obtained by summing j>=2 is uniform
in the character and chosen modulus. Inert Gaussian prime ideals of norm
p^2 are already included in the prime-ideal sum; they are not incorrectly
discarded as proper powers of another ideal.

## 3. Gaussian twist family and principal pole

For a fixed Gaussian ray character xi of modulus m and a rational
Dirichlet character rho modulo q, the function

    theta(a)=xi(a) rho(N(a))

is a finite-order ray character modulo m(q). Indeed a generator congruent
to one modulo (q) has norm congruent to one modulo q. Its finite modulus
norm is at most N(m)q^2. No archimedean angular parameter varies here.

For q<=(log X)^B and sqrt(X)<=Y<=X, the single choice A=2B+1 gives

    N(m)q^2 <= (log Y)^A

for all sufficiently large X depending only on m and B. The extra power
of log X absorbs the fixed factor N(m)2^A. Mitsui's estimate at Y is then
O_(m,B)(X exp(-c sqrt(log X))), uniformly in Y, q, and rho. For
0<=Y<sqrt(X), the elementary bound O_K(Y log^2(Y+2)), together with the
possible main term Y, is smaller than this error for large X. Bounded X
can be absorbed by the implied constant. The endpoint Y=0 is identically
zero. This gives precisely the input required in progression_mainterms.tex,
since exponential square-root-log decay dominates every fixed log power.

The principal indicator is one exactly when the primitive inducing
Hecke character is trivial. It does not mean that the zero-extended
character equals one at excluded ideals. Mitsui explicitly treats
imprimitive characters; alternatively the difference from the primitive
sum is O_m(log(q+2)log(Y+2)). To see this last bound, count the
O_m(log(q+2)) excluded prime ideals and use at most log Y total weight
from each of their prime-power towers. Thus no hidden main term arises
from an omitted Euler factor.

For K=Q the same published theorem applies. An odd Dirichlet character
uses the real infinite place in its ray modulus, which Mitsui permits.
The finite norm is q, and A=B+1 suffices. Consequently the ordinary
Dirichlet Siegel–Walfisz input used in the progression fragment is covered
by the same inspected theorem, not by an unexamined secondary citation.

## 4. Fogels cross-check and scope

I also independently viewed the two published Fogels spreads containing
pages 307–309. The zero-free region and equation (8) are transcribed with
the correct direction: 1-beta is bounded below by c(epsilon,n)D^(-epsilon),
D=|d|N(f). The possible principal exceptional character for degree greater
than one is explicitly mentioned in the source. The substitution
epsilon=1/(4B) for Gaussian modulus norm O(q^2) gives the claimed
logarithmic gap. These observations validate the earlier repair note.

Fogels is not needed as an additional production input when Mitsui
Lemma 15 is used directly. The reviewed Mitsui route closes the previously
unverified explicit-formula step without promoting Kane's author-version
formula or inaccessible book theorems to inspected published statements.

## 5. Fourier and Frobenius normalization in progression_mainterms.tex

The factor T_C(p)=2 Lambda'_C(p) is correct: an eligible split rational
prime has two conjugate prime ideals, both of norm p and both of weight
log p. Conjugation invariance of C is needed and is stated. The remaining
support consists of rational prime powers and excluded primes, with the
claimed O_H(sqrt(X)log^2(2X)) total error.

The finite Fourier coefficients are

    c_C(chi)=|A|^(-1) sum_{a in C} conjugate(chi(a)).

Thus 1_C=sum c_C(chi)chi, exactly as used. The rational progression
indicator contributes conjugate(rho(a))/phi(q), and the Hecke twist is
chi*(rho composed N), without an unannounced inverse. Averaging each
restricted product character over Gal(K Q(zeta_q)/E) equals its
principal indicator r_(chi,rho). This follows from finite-character
orthogonality and the surjective Artin reciprocity map for the already
defined abelian ray extension over E. It invokes no additional analytic
Chebotarev estimate.

The compatible-pair description of Gal(K Q(zeta_q)/E) is valid even when
E is not contained in Q(zeta_q): requiring g in Gal(K/E) makes the
resulting compatible automorphism fix E. The compatibility on
J_q=K intersect Q(zeta_q) already enforces every necessary restriction
on the cyclotomic component.

The coefficient for T_C is the desired numerator divided by [L:E].
Dividing by two changes this to [L:Q], with no further factor of the
ray-group order or phi(q). Uniform error terms are also correct: the
rho-sum is divided by phi(q), and the remaining finite chi-sum has size
depending only on fixed H.

## 6. W-trick and centered progression sums

Since W contains the conductor of K^ab, one has

    K intersect Q(zeta_(Wq)) = K^ab.

The forward inclusion uses that a cyclotomic subfield is abelian over Q;
the reverse uses K^ab subset Q(zeta_W). Consequently the coefficient for
an admissible residue a modulo Wq is mu_C(b)/phi(Wq), where a=b modulo W.
The ordinary prime coefficient is 1/phi(Wq). The common normalization
phi(W)/W therefore gives equal main terms in the centered difference.
The bound 0<=mu_C(b)<=1 and the pointwise estimate |h|<=lambda are valid.

For progression modulus q>log(N)^(D+3), the pointwise logarithmic bound
and |P|<=N/q+1 give the required small total. For the remaining q,
Wq is polylogarithmic. If the transformed residue is non-coprime to Wq,
every prime on it divides Wq, so its total contribution is polylogarithmic.
For coprime residues, apply the accepted Gaussian and ordinary estimates
at the two interval endpoints. The modulus and size exponents can be
fixed before N tends to infinity. No lower bound on interval length and
no uniformity in changing W is used.

The progression fragment retains source-gate comments and conditional
wording. Those are editorial integration markers. This review accepts
the mathematical implication and the published input which discharges
its displayed analytic hypothesis; it does not itself edit those markers.

## 7. TeX fidelity and source inventory

The final SW TeX fragment faithfully states and proves the accepted
specialization. Its estimate is uniform in X, Y, q and rho, with the
fixed-field and fixed-character dependencies retained. The Gaussian
principal indicator uses the trivial primitive inducing character, and
the rational indicator uses the principal Dirichlet character. I repaired
a malformed TeX escape in that rational indicator; this is a typographic
repair with no mathematical change. The hash above binds the repaired
file. The stated range starts at Y=1; the omitted range 0<=Y<1 is empty
on the sum side and has bounded main term, so the same estimate extends
there immediately when progression endpoints require it.

The bibliography entry agrees with the inspected publisher metadata.
Both source-application inventory entries correctly name Mitsui as the
published input, record the separate Gaussian and rational modulus
checks, and retain the scope of independent review. No Fogels theorem
is silently required in the production proof.

Signed: `/root/astra_sub1000_quotients`, independent review completed
2026-11-06 against the hashes listed above.
