# Independent bridge source and interface review

Accepted for `gowers-bridge/bridge.tex`, SHA256 `b9284d40889c3d4308fd0c3d532b7d59c792f22894acc6db21c19a2422c307cd`, on 2026-11-06. This review complements the elimination worker's limit, normalization, and polynomial-transfer audit. It checks the exact published inputs and the bridge's interface with the accepted norm, affine, and factorization arguments. It does not independently re-prove the Gaussian Siegel--Walfisz or Type I/II inputs.

## Exact source consumption

The published Green--Tao *Linear equations in primes* PDF was inspected directly. Proposition 6.4 supplies a common majorant for a fixed finite list of ordinary W-tricked prime weights on [N^(3/5),N], after a fixed rescaling. Proposition 7.1 applies to real functions bounded by that majorant, s-normal systems with bounded normalized coefficients, and arbitrary convex regions. Its conclusion is uniform in those regions and coefficients. It does not require an Artin-prime theorem or the paper's then-conjectural prime uniformity theorem. The bridge uses only these unconditional functional and sieve statements.

The fixed factor extension V=E times the small-prime product is valid. For sufficiently large cutoff all prime factors of E are already small. Unit output residues eliminate the divisor terms involving these primes, phi(V)/V is unchanged from the radical, and the remaining local factors and correlation moment estimates are the same. Fixed E changes only fixed constants and coefficient bounds. The Appendix D construction also defines the majorant on the full cyclic group, with value one outside the working interval; the bridge does not mistakenly zero-extend the majorant.

Dodos--Kanellopoulos Theorem 5.1 was checked in the cached arXiv v4, pp.12-13: target U^s[N], prime ambient size in [CN,2CN], C at least 20, and majorant U^(2s) distance to one. The conclusion is a bounded Lipschitz linear nilsequence with fixed nilmanifold and constants depending on s,C,delta. The bridge's rescaling, real function, interval normalization, metric comparison and polynomial-orbit inclusion match that statement. The publisher-typeset statement has not been compared; this qualification is retained in the author's inventory and this receipt.

Bienvenu's published Theorem 1.1, pp.79-80, explicitly permits bounded linear coefficients, constant terms of size O(N), and arbitrary convex K in [-N,N]^d, with error o_(d,t,L)(N^d). It therefore supplies precisely the uniformity needed after the appendix cutoff is fixed. The cube systems have pairwise nonproportional linear parts, including every subproduct. Wrap constants grow only linearly in the scale.

The cached published Tao--Ziegler text confirms the arbitrary-function clause of Theorem 11. No special model-one conclusion is transferred to the ray-prime weights. Theorem 15 in Appendix A, p.57, permits different residue weights, large constant coefficients, and distinct polynomials with nonconstant differences. Its averaging ranges cover the quadratic-parameter ranges here for all sufficiently large N at each fixed cutoff.

## Boundary correction closed

The first draft invoked polynomial-forms estimates on fixed x-subboxes without deriving localization. Theorem 15 averages x over the full cyclic group. The revised fragment closes this gap explicitly.

If a shift polynomial is constant, retain its majorant as an anchor nu_0(x); otherwise take nu_0=1. There is at most one constant polynomial because the quadratic leading coefficients are distinct. Average the product of the other majorants over m to form F(x). Theorem 15 applies to nu_0 F and nu_0 F^2, using independent m,m' in the latter, and to nu_0. Within each copy, polynomial differences are nonconstant by the original hypothesis; between copies, each polynomial depends nontrivially on its own independent variable. Thus the weighted second moment of F-1 tends to zero. Weighted Cauchy--Schwarz localizes to every x-interval, and the one-dimensional divisor-sum mean bounds the anchor's mass there. This gives O(epsilon) plus vanishing error for a strip of width epsilon N.

The revised proof uses an enlarged ambient interval for actual integer outputs near or beyond the old endpoint. Its two-limit notation does not claim fixed-cutoff sieve errors automatically vanish with N. The final diagonal retains all earlier fixed-epsilon tests; taking first a fixed epsilon, then the upper limit in N, then epsilon to zero handles every allowed T=o(sqrt N).

## Interface and remaining qualifications

The bridge's h_(C,V,b) exactly matches the centered weight in the progression fragment. Its bound by the ordinary weight follows from 0<=Lambda'_C<=Lambda' and 0<=mu_C<=1. The centered-prime affine corollary supplies the totally equidistributed, mean-zero minor-arc estimate; the progression corollary supplies the all-progression mean estimate; the factorization proposition then gives the stated all-polynomial-orbit nilsequence input for each fixed V. No varying-V uniform estimate is smuggled into that input.

The linear replacement lemma now explicitly requires nonzero integer linear parts. The normal-form extension is an integer bijection with a full auxiliary box, not a restriction to a lower-dimensional slice. The normalized admissible residue mass prevents amplification when summing residue classes. The auxiliary cutoff is eliminated before the separate fixed-cutoff local-cube computation. These changes agree with the other reviewer's audit.

All references in the bridge resolve against the current supplied fragments and the existing sun appendix; their exact hashes are in `receipt.json`. Bibliography entries `v6gtlinear` and `v6bienvenu` still need to be included by integration as the author specifies. No PDF compilation is claimed. Acceptance is for this Gaussian-ray-field implication, not the old unrestricted arbitrary-Galois formulation; integration must apply the stated scope restriction. It also does not erase the separately recorded source-version qualification for DK.
