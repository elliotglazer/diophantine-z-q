# Candidate explicit 175-variable quartic

## Statement and scope

Relative to the retained arithmetic interfaces below, the polynomial
`F = sum(Q_j^2, j=1..147)`, with the integer quadratic residuals in
[source/computation/projective_contacts_20261126/quadrics.json](source/computation/projective_contacts_20261126/quadrics.json)
specialized at C = 331^21, satisfies

    X in Z iff exists x2,...,x175 in Q with F(X,x2,...,x175)=0.

The input is x1; the count includes it. F has exact total degree 4, content 1,
3,196 monomials, 802-bit maximum absolute coefficient, and a
[73,080-byte canonical decimal expansion](source/computation/projective_contacts_20261126/expanded175.txt)
(no final newline, decimal kB). No abc or (OM) assumption is added.
This is a candidate for the 229-variable explicit record in Version 21,
not an official record or a new unconditional independent proof.

Receiving main: 964d7dd71f253091dbc5eac793b78cc56d1fcc73 (Version 21).
Source snapshot: [6864691d536057574be873667936610da6a4ea99](https://github.com/JoseBrox/diophantine-z-q_improvements/tree/6864691d536057574be873667936610da6a4ea99).
The original source files are copied under source/; Git blob IDs
are listed in source-blobs.json, annex-blobs.json and foundations-blobs.json.
The proof annex is the relevant fixed-route chain; statements about
161-variable and other families are background only. Where an annex cites
an original source not copied, resolve it at the pinned source snapshot,
not a moving branch.

## Proof and dependency map

All residuals are over Q; their sum of squares vanishes iff every residual
vanishes. For the arithmetic argument, use K=Q(sqrt(2)), d=3-sqrt(2),
E:y^2=x^3-d^2 x, R0=(1+sqrt(2),2sqrt(2)), P0=2R0, absolute logarithmic
heights and rational-prime normalized valuations as in v82.

1. [v82, theorem thm:main, lem:scalar, prop:point, eq:radicals and Ordered integer completeness](source/papers/quartic/scalar_point163_179_20261120_v82.tex)
   gives the 179-variable parent, point recovery including torsion, scalar
   extraction, the Lucas label bound, and the simultaneous prime preparation.
   It needs the actual rank-one group description E(K)=Z R0+E[2](K), the
   full allowed finite point domain, good-prime formal logarithm estimate,
   H4.1 on its full domain, the fixed-data Gaussian prime-pattern supplier
   with arbitrary finite avoidance and synchronized depths and real recurrence.
   The normalized torsion-inclusive finite-sum input is given in
   [v62, thm:main and cor:four](source/papers/effective_sums/effective_torsion_sums_20261117_v62.tex).
   Compare Version 21 Part I (in particular v21:effective-soundness,
   v21:local-extraction and v21:completeness) for the receiving context;
   [v68, eq:height-input](source/papers/quartic/quartic229_compact_20261117_v68.tex)
   specifies the five-contact modular height input. This note retains these
   arithmetic interfaces; it does not assert their independent discharge.

2. [BB-native replacement, lem:sound, thm:bb, lem:real, lem:seven and thm:pole](source/papers/quartic/bb_native_quartics_20261124.tex)
   replaces the original native pole, not the detector itself. The consumed
   input is d'=7b/9 with 0<d'<1, square reduced denominator and
   v2(d')>=4, d' in 7 Q_2^{*2}; the real and dyadic preparation and
   additional integrality at 7 are supplied before invoking the congruent-number
   realization. The elementary negative-odd-valuation obstruction applies
   at every rational prime, including 2. The external input is
   Bhargava–Burungale, arXiv:2611.16130v2, Lemma 2.2 and Theorem 2.3,
   as translated in the source proof. No Route K realization theorem is
   imported as a separate input. The current submission does not claim a
   fresh independent reading or validation of that external paper.

3. [Weighted explicit 178, equations (1)–(4), sections 4–5](source/computation/weighted_explicit178_20261124/README.md)
   removes the inverse normalizer via positive weights (1,R,1,1).
   The effective sum estimate on all four finite points, including finite
   torsion, is B^2 < 40 sum h(t_j)+360 h(R)+2500. For true witnesses R>100
   and the doubled scalar point gives positive real sums at both embeddings;
   the three contact lists are fixed before prime selection.

4. [Harmonic scalar, sections 1–5](source/computation/harmonic_scalar_20261125/README.md)
   replaces the scalar block and gives 177 variables. [Depressed scalar,
   sections 1–3](source/computation/depressed_scalar_20261125/README.md)
   improves its anchor. With s=2^20 X^2, u=s/(1+s), r=(2401+2400s)
   (343+375s)(1+s), e=-1081567619/25920000, K0=18536 C^2, the scalar is
   R=K0 r/(r-e)>100. At 331 the two cubic values are units for integral
   local X (331 residue cases); for nonintegral X their common leading
   term forces equality of valuations. Thus v331(R)=2N+1 throughout.
   Local extraction precedes division and yields the nonzero integral a.
   For N=21, |a|>=331^97>2^810 and h(u)<2^301*331^-97*|a|.
   The additional scalar exceptional primes are handled in the cited
   bound, not discarded. Consequently h(beta)<|a|/2 and h(R)<|a|,
   beta=51X^2+2504. The real and dyadic completeness conditions
   for the scalar are checked in the depressed-scalar proof.

5. [Aligned gates, 177 -> 175](source/computation/aligned_gate_20261125/README.md)
   gives an input-preserving Laurent rechart guarded by cu=1 and v=u^2
   (here u denotes the gate unit, not the scalar contact argument).
   Its two affine substitutions for old x72 and x171 make the deleted
   gates consequences of the retained gate. See the pinned certificate
   and parent and child tables. [Reciprocal depressed scalar](source/computation/reciprocal_depressed_scalar_20261126/README.md)
   replaces the two private scalar rows with W T=1 and
   (W-3161163 T)(R-K0)+2163135238 K0 T^2=0; W=36000*2^20 X^2+34981>0.
   Eliminating T recovers the same scalar on the entire domain.

6. [Projective contacts, sections 1–3](source/computation/projective_contacts_20261126/README.md)
   replaces nine quadratic rows only. Its projective change has determinant
   156800 and exceptional set Gamma={2,3,5,7,11,13,17,19,23,37,41,2399}.
   The five image contacts are (-77,23,21,-75,51)/32 and their reflections
   are distinct. The two H4.1 level bounds combine by geometric mean;
   the contact constant is <2^249. Three charts use r=(32t)^2, s=r^2,
   w=1/q and a private combination d, encoding
   (1+w)P(r)=w r^5 for P(r)=product(r-r_i^2).
   The independent checker reconstructs these nine rows, leaving every
   other parent row unchanged. No division by the contact argument is
   introduced, and the existing unit guards remain.

   For soundness, absorb 360h(R)+2500 into B^2/2 by B>=|a|>2^810.
   If the integral Lucas residual Delta is nonzero, the local comparison
   supplies M_j^3 | a Delta and |a Delta|<=14 B^5. The new contact bound
   gives exp((1/3-5/36036)s)<1000*2^249*(54+5s/6) for s=log B.
   At s=810 log 2 this is false, and the exponential-to-linear ratio
   increases thereafter. Thus Delta=0. If J_X=num(beta-n) is nonzero,
   the comparison yields M_j | J_X. The coarse contact bound gives
   log B < 240+|a|, contradicting the Lucas bound
   log B >= (|a|-6) log(|a|-3). Therefore beta=n in (1/2)Z;
   the reduced denominator of X has square dividing 102, so X is integral.
   X=0 is integral directly.

   For completeness fix an integer X, then the scalar, then the
   prepared reference and other labels, then the contact shifts and
   Gaussian primes. The ordered lists stay disjoint since the new
   diameter is <5 and the shifts exceed 13 and 17. The scalar and
   comparison preparation use the same unit guards and parity of
   foreign-prime denominators, and the BB poles retain the local and
   real conditions from item 2. The parent physical coordinates are
   transformed using items 3–5 and the new contact equations. These
   arithmetic implications rely on the source hypotheses above.

## Verification and limitations

Run `python -B check.py` in this directory. This is a newly written
standard-library checker, not the search/generation program.
The separate executed BigInt replay in verification.json checked the final
contact rechart and entire expansion independently. The attached source
blobs also permit reviewing the intervening exact coordinate maps. The
present replay does not independently check every earlier transformation,
prove the full arithmetic inputs, or replace the repository's two-reviewer
process. Previous local checks reported a full-verification manifest
mismatch in the improvements repository's .github/workflows/verify.yml;
it was not repaired or rerun here. No claim of hosted CI, fresh Lean
verification, or human verification is made. No current manuscript,
release, workflow, policy, or review machinery is changed.

The prior locally prepared combined note/PDF was not recoverable in this
session. This package is a reconstruction from pinned public source
material with a focused proof/dependency note and the original proof
annex. A complete integrated current TeX/PDF is an integration/release
task, not claimed here. External BB source access and full inherited
arithmetic audit remain open at this submission scope.

## Attribution

Jose Brox / ZQ Diophantine Project contributors; the underlying reductions
build on Gabe Conant's notes with Astra 6.2 and the earlier three-detector
construction attributed to Gemini 4 Carbon. The copied project research
material is CC BY 4.0; third-party publications are cited, not reproduced.
GPT-6.2 reconstructed the package and executed the final BigInt check;
earlier AI-assisted work is credited in the source annex. No new human
or independent Protocol B approval is asserted.

## Review-round repair

See [REPAIR.md](REPAIR.md) for the disposition of the first-round findings, the now-local parent proof chain, explicit BB witness translation, direct final-pole decoding, and the end-to-end exact replay command `python -B check_all.py`. The final polynomial is unchanged. The author-side replays and the remaining independent review/eligible hosted evidence requirements are distinguished there.
