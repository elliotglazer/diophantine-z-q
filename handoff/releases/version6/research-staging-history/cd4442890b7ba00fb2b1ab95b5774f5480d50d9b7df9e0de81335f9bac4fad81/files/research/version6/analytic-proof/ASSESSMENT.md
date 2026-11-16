# Removing the Frei–Tinková input

Date: 2026-11-06. The released Version 5 manuscript and its qualifications are unchanged.

## Current status

The initial assessment below led to a proof of the required Gaussian special case. Its norm-transfer, Type I/II, affine-pullback, and factorization components have passed independent source-level reviews. The progression main terms have also passed review, using the inspected published Lemma 15 of Mitsui (1956), not an uninspected explicit-formula quotation from Kane or Iwaniec–Kowalski. The final nilsequence-to-Gowers and polynomial-transfer bridge is written and undergoing independent review. The full replacement has not yet been accepted or published.

The optimization is separate: the current independently checked candidate has 962 total variables, 919 quadratic residuals, and 55,409 monomials. The historical 1,272-variable counts below describe the starting point, not the candidate release. A Version 6 working source includes the new compiler description and Brox-attributed degree-four lower bound. Publication remains gated on the complete analytic argument, theorem inventory, and final build/repository checks.

Current evidence is in `norm-independent-review/`, `type-i-ii/ROOT_REVIEW.md`, `factorization-independent-review/`, and `sw-independent-review/`. The evolving final bridge is in `gowers-bridge/`. These are scoped reviews, not a proof-assistant certificate or a claim of human peer review.

## Initial assessment retained for research history

## Conclusion of this pass

No verified published replacement has been found for the arithmetic estimate used by the 1,272-variable quartic. The original construction and the retained 4,973-variable quartic do not use this new input. Removing its citation from the 1,272-variable argument now would remove a needed justification.

There is a smaller replacement target than the general theorem of Frei–Tinková: only ray characters of the fixed field Q(i) are needed. The ray modulus grows when the finite sieve cutoff is chosen, but it is fixed before the size parameter tends to infinity. Thus the ideal-norm estimate would need field degree two throughout, rather than arbitrary fields. This observation removes the general-field and character-induction parts of their proof from a prospective reconstruction. It does not prove the remaining analytic estimate.

## Exact point of use

In `quartic_1272.tex`, proposition `prop:v5-artin-patterns` uses FT Theorem 1.4 to bound centered Gowers cube correlations. The remaining polynomial transference is based on published Tao–Ziegler results. Proposition `prop:v5-cutoff-lower` then gives a lower bound proportional to `(log L)^(-4k)`. This must exceed the bad-pattern upper bound proportional to `1/(L log L)`.

A qualitative statement that a positive-density set of primes contains polynomial patterns does not give this comparison. Its constant may depend on the density too severely. One cannot choose L after obtaining that constant without also changing the set of primes and the constant.

## Publication checks and alternative theorem checks

- Frei's current author page still lists *Linear constellations in primes with arithmetic restrictions* as “Mathematika, to appear.” No published replacement version was verified. Source: https://www.math.tugraz.at/~frei/ .
- Kai's *Linear patterns in prime elements in number fields* remains in the preprint section of the author's page. It also concerns linear forms in elements, whereas our constraints are on their rational norms. It is not a published drop-in replacement. Source: https://sites.google.com/view/wataru-kai/ .
- Bienvenu's *Asymptotics for some polynomial patterns in the primes* is published, DOI 10.1017/prm.2018.52. Its Theorem 1.2 combines prime weights and quadratic-form representation weights on pairwise nonproportional linear forms. Requiring the same value to be prime and to have a prescribed representation would repeat the linear form. That violates its hypothesis. The author explicitly excludes such infinite-complexity systems after the theorem. Exact statement inspected at https://arxiv.org/html/1511.07317 , Theorem 1.2 and the following paragraph; publication confirmed at https://research-information.bris.ac.uk/en/publications/asymptotics-for-some-polynomial-patterns-in-the-primes/ . This check rules out the direct application, not every possible new argument using the paper.
- Kane's published one-linear-equation result does not itself supply the many simultaneous relations in the Gowers cube. The existing FT proof-scope report already identifies this restriction.
- Ordinary prime nilsequence estimates of Green–Tao are published, but they do not include a finite-order Gaussian Hecke character evaluated on ideals and a nilsequence evaluated on the ideals' norms. Their Type I/II method is a plausible parent for a proof of that special case, not a theorem that can simply be quoted as already stating it.

## Elementary reduction to the Gaussian field

Let E=Q(i), O=Z[i], and H a fixed integer divisible by 16. Put A_H=(O/HO)^*/O^*. For the ray field K_H/E, complex conjugation acts on A_H by conjugating residues. Let S be a conjugation-invariant subset of A_H, including a union such as the residue conditions used in the manuscript. Let Lambda'_S(p)=log p when p is a rational prime unramified in K_H, split in E, and the class of an ideal above p is in S; set it to zero otherwise. The definition is independent of the ideal above p because S is conjugation invariant.

For ideals coprime to H, define

`T_S(n) = sum_{N(a)=n} Lambda_E(a) 1_S([a])`.

For every rational prime p not dividing 2H,

`T_S(p) = 2 Lambda'_S(p)`.

Proof: a split prime has two conjugate prime ideals of norm p and each has ideal von Mangoldt weight log p. An inert prime has no ideal of norm p. Outside prime arguments, this weight is supported on rational prime powers. Summing these terms through X contributes `O_H(sqrt(X) log^2(X))`, a sufficient elementary bound. The finitely many ramified or excluded primes contribute only logarithmic factors through their powers.

Fourier expansion on the finite abelian group A_H gives the exact identity

`T_S(n) = sum_{chi in dual(A_H)} c_S(chi) T_chi(n)`,

where

`c_S(chi) = |A_H|^(-1) sum_{a in S} conjugate(chi(a))`,

and `T_chi(n) = sum_{N(a)=n} Lambda_E(a) chi([a])` over ideals coprime to H. Every character is a finite-order Gaussian ray character. Since every ideal of Z[i] is principal and has exactly four generators, ideal sums equal one quarter of the corresponding element sums. The character is constant on unit multiples; the factor four cannot be omitted.

This identifies a route avoiding arbitrary number fields. It does not by itself establish cancellation of T_chi against nilsequences or identify all progression main terms. Those are the remaining analytic tasks.

## Why rational congruences alone cannot replace the ray condition

At the split prime 13, the residues z=1 and z=i both have norm 1. Their adjacent norms differ: N(1-1)=0, whereas N(i-1)=N(i+1)=2 modulo 13. Thus specifying the rational norm modulo 13 does not decide the condition used to sieve the adjacent norms.

More generally the kernel of the norm map on (Z[i]/13)^* is generated by commutators with conjugation. In the manuscript's ray extension, this kernel is killed in the maximal abelian quotient over Q. Hence the distinction is precisely information missing from rational congruence conditions. CRT lets this example be inserted while preserving the fixed base residue. This blocks the proposed direct reduction to ordinary primes in arithmetic progressions.

## Remaining proof obligations for the narrow replacement

1. Prove a quantitative mean-zero nilsequence estimate for the Gaussian ideal von Mangoldt function twisted by every fixed ray character. A possible target is the degree-two specialization of FT Theorem 2.4, with all Type I/II steps proved from the published parents.
2. Establish the progression main terms and their compatibility with the finite ray-character expansion. Characters that contribute a congruence main term must not be declared mean-zero indiscriminately.
3. Verify factorization, interval restrictions, coefficient sizes, and every order of limits in passing to the required cube correlations. Preserve the stronger majorant norm exponent already identified in the Version 5 audit if the same relative inverse theorem is used.
4. Substitute the restricted ray-class correlation theorem into the existing polynomial-count proof and repeat the cutoff lower-bound and obstruction-tail comparison.
5. Independently review the replacement and regenerate the manuscript, inventory and handoff pins before claiming the 1,272-variable result uses only published external inputs.

If these steps reproduce the same prime-pattern statement, the polynomial program, 1,272 variables, degree four, and 48,001 symbolic monomials are unchanged. If the arithmetic construction is altered instead, those counts need to be recomputed.

Completing a proof of the special case inside the manuscript would remove FT as an assumed theorem, while retaining citation for the method and provenance. Merely rewriting its unverified steps would not remove the mathematical dependence.

## Pinned starting points

- Released manuscript SHA256: `16033e0471df605093b28210a9f81718c2486b147016ec8afc75d166dff0b90f`.
- Source package manifest SHA256: `aa7f04c54e8b778a419a1be8d24e0b3a9a8540c50202d41815864a156d6985c6`.
- Existing detailed scope: `work/quartic-version5-release/repository/docs/quartic-1272/evidence/FT_PROOF_SCOPE.md`.
- Existing source-node inventory: `work/quartic-version5-release/repository/docs/quartic-1272/evidence/FT_PROOF_DEPENDENCIES.json`.
- Published parent sources are cached under `work/quartic-version5-release/sun-proof/sources/`.
