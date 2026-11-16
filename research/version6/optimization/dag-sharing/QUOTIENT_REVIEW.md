# Independent review of quotient fusion

I reviewed `field-quotients/make_candidate.py`, `EQUIVALENCE.md`, the actual emitted `raw-ir.json`, and the immutable source manuscript at lines 4311–4405. The changes preserve the baseline rational solution projection in both directions. I found no missing denominator condition in the reviewed patch.

The potentially delicate deletion is the F inverse. The unchanged halfpoint curve and doubling-slope equations force the halfpoint ordinate to be nonzero. In each real embedding, D=11±6sqrt(2)>0, and the doubled abscissa is (x²+D)²/(4y²)>0. Thus its rational component, the average of the two embeddings, is positive. Every fixed detector scale A is positive. The retained delta inverse forces delta≠0. Consequently the new equation F*ep=(A*delta)^5 has nonzero right side, so both F and ep are nonzero. The old inverse witnesses are recovered without choosing a new solution branch.

For U 0 and V 0, the original source lemma proves that these finite points of 2E have nonzero ordinate. V 0 remains a finite difference because its abscissa-inequality inverse is retained. Thus the equation y*log=-x*P reconstructs the deleted z=-x/y and forces log=z*P. For the scalar ratio, the emitted equation xH*ratio=-yH*zS is equivalent to zH*ratio=zS. Its two required nonzero values hold: yH by the same source lemma, and xH by the retained fH inverse.

The other quotient fusions retain their required domains explicitly. Delta*di=1 remains; ep*R=di implies the old ep inverse equals R*delta. The trace inverse w 0*wi=1 remains, so the norm quotient cannot admit the w 0=0 branch. Every deleted power or norm assignment reconstructs as its original polynomial value.

`review-quotients.cjs`, written independently of the quotient worker, checks the actual emitted gate numerators and denominators against the saved semantic values. It checks both component records of each changed field quotient, all nine detector weight and norm quotients, and the retained guards. Its 132 semantic equality checks and all 1,165 raw gate identities passed. `quotient-independent-review.json` binds the review to the candidate raw-file hash. The arithmetic source qualifications persist.

## Final B multiplication add-on

The later `field-quotients/final-b/patch.json` is also sound. Replace R=di/ep, s=nw², B=R*s by ep*v=di*nw and B=nw*v. The upstream weight equation still forces ep to be nonzero, independently of the removed R equation. Hence v=di*nw/ep. Recover R=di/ep and s=nw² in the reverse map. This needs no nonzero condition on nw.

`review-final-b.cjs` independently checked the emitted equations, including their output normalization. All 958 raw gate identities and 27 numerator, denominator, and B-output identities passed. `final-b-independent-review.json` binds this review to the add-on candidate's raw-file hash.
