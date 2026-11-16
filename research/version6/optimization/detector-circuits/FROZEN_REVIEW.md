# Independent review of the 962-coordinate candidate

Verdict: accepted for the reviewed exact algebra, witness maps, and their domain interactions. This does not discharge any inherited arithmetic hypothesis, including the stated Frei–Tinková qualification.

The immutable baseline checker independently reconstructed the sum of squared residuals and compared it to the supplied polynomial table. It checked all 904 raw gate identities, replayed all 894 certificate operations, compared the resulting compiled residuals, and checked the coordinate map. The result has 962 total and active rational coordinates, 919 quadratic residuals, degree four, 55,409 monomials, primitive integer coefficients, and exact coefficient height 64*S². The input remains coordinate zero. S=3^(2^27) remains a fixed coefficient and was not expanded.

The complete receipt is `frozen-independent-check.json`. Its exact inputs include:

| Artifact | SHA256 |
| --- | --- |
| Raw translated IR | cb1295d789c5bb40bd98842b1bd2a51a05c6ff2058a526e7d1d9b177d20da3ae |
| Compiled IR | 244269ada6870d0e2447fd115216844f4ec9c878eba2ddc74303cb12d78b744a |
| Polynomial table | 6b798de7d00ac3c7d725ca0a69d39f1eac1ddb02fee2756cb6323770b952af32 |

`verify_frozen_locals.py` separately checks the actual final emitted circuits, rather than only their abstract proposed formulas. It verifies 18 detector evaluation outputs and their 72 residuals; 18 shared-weight outputs and their 27 residuals; all 20 pole structural formulas and all eight correction-chain factorizations; and all ten logarithm identities, including both final quotient-fused logarithm residual pairs. These are exact polynomial identities with the upstream coordinates independent. The receipt is `frozen-local-checks.json`, bound to the same translated IR hash.

## Domain interactions

The halfpoint chart preserves the domain needed by the removed detector F inverse guards. Write K=Q(sqrt(2)) and D=11-6*sqrt(2), positive under both real embeddings. Its equation is t²(h²-t²/4)=D. Hence t is nonzero. If h were zero, either real embedding would give -t^4/4=D>0, which is impossible. The output point has x=h², so its rational component is h0²+2*h1²>0. Thus every scale A used downstream is nonzero: it is either 1, the square of this positive rational component, or (1+x1²)².

For completeness the chart reconstructs the original halfpoint as x_half=t*(h+t/2), y_half=t*x_half. The equation implies x_half²-t²*x_half=D, so x_half and y_half are nonzero and y_half²=x_half³-D*x_half. Conversely an old admissible halfpoint gives t=y_half/x_half and h=x_half/t-t/2. These denominators are nonzero in the original system. Its old tangent equation excludes y_half=0, and its curve equation then excludes x_half=0. The doubling formulas give exactly x=h² and y=h*(t²/2-h²). Therefore the downstream points and their inherited finite-point domain lemmas are unchanged.

The retained delta inverse gives delta!=0. Together with A!=0, the detector relation F*e=(A*delta)^5 forces both F!=0 and e!=0. Thus the removed F inverse and e inverse can be reconstructed uniquely. The q1 denominator is delta. The regrouped q16 and q52 expressions introduce no divisions. The final-B quotient has denominator e, already proved nonzero.

The retained w0 inverse forces w0!=0. Therefore W!=0 in K and Norm(W)!=0. The norm quotient n=Norm(W)/(2*w0) is nonzero. In the final-B formula v=delta_inverse*n/e and b=n*v, both v and b are nonzero. Hence C=17b is nonzero at all detector poles, exactly as required by the inverse pole map old_e=scaled_e/C. At the scalar pole the explicit b inverse remains.

The scalar n0 and n1 quotient replacements retain the original r inverse, so their denominator is nonzero. The correction chain starts at ±1 and each next entry is either its predecessor or a positive prime times that predecessor. Its inverse Boolean map has no zero denominator. The scalar preparation and its original denominator obligation are unchanged.

For the two fused logarithms, the final exact emitted residual is y*ell+x*P(f)=0. The unchanged point-domain lemma gives y!=0, so it is exactly ell=(-x/y)*P(f). The scalar ratio similarly replaces division by z=-x/y with multiplication by -y followed by division by x. The retained f=1/x equation gives x!=0. Neither fusion introduces a new domain restriction.

All remaining circuit changes are polynomial identities. Their forward maps evaluate the replacement gates and their reverse maps evaluate the old gates on the same semantic inputs. The chart and pole maps described above are the only relevant changed base-coordinate meanings. Every map preserves the input coordinate. No interaction gap was found.
