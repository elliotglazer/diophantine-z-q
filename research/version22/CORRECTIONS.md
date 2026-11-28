# Version 21 backlog and PR175 integration notes

Read issue129 and its comments on 27 November 2026. The original selected bodies and IDs are preserved in CORRECTIONS-SOURCES.json. No class A or B entry against Version 21 was found. The following entries are class C or tooling notes.

| ID | Disposition in Version 22 |
| --- | --- |
| 44457437665-1-astra-V21-N1 | The new release manifest uses version 22. The stale version20 field in the frozen V21 packer is not edited; deferred as historical tooling, and that packer is not used for V22. |
| 44457437665-1-fable-N1 | Deferred hosted CI registration to a separate computation PR, as the manuscript guide requires. All 147 new printed rows and the complete final arithmetic interpretation are checked locally; the retained V21 checks pass. No hosted coverage is claimed. |
| 44457437665-1-fable-N2 | Corrected 28 math-mode double-hyphen index ranges in the copied V21 normalization table, using a text-mode separator. Released V21 unchanged. |
| 44457437665-1-fable-N3 | The V22 manifest and current documentation explicitly distinguish draft preparation from published V21. Review/acceptance fields remain pending rather than invented. Final publication wording is deferred until release, as required by policy. |
| 44457437665-1-fable-N4 | Four retained-input explanations are supplied in the new part: scalar point scaling, arbitrary-point duplication, generator-curve scaling and old pole-input normalization. New native pole rows also have their own direct complete interpretation. |
| 44457437665-1-fable-N5 | The new dependency map names the four missing suppliers and states the effective Lucas threshold abs(a)>=8 from its proof. |
| 44457437665-1-fable-N6 | The opening explicitly scopes historical ineffective-threshold language to the earlier construction/method. The new effective parameter is proved separately. |
| 44457437665-1-fable-N7 | The new proof states that the individual bound may be weakened from 3 to 6, and uses distinct symbols for the contact constant, scalar normalizer and label bound. Renaming every historical L is deferred to avoid changing retained notation across unrelated arguments. |
| 45915251550-1-fable-N1-bb-tex-crossref-stale | Corrected in the integrated pole lemma: explicit translation from Theorem2.3; no unsupported density requirement. Original contribution source remains unchanged. |
| 45915251550-1-fable-N2-no-zero-contact-u-unit | Corrected in completeness: prepared primes divide w, selected prime congruences make u a unit there, and the selected-prime size excludes gcd(u,w)>1. |
| 45915251550-1-fable-N3-reference-norm-list | Corrected by printing the five retained norms with support {2,3,7,17,41}. |
| 45915251550-1-fable-N4-inventory-integration | New applications recorded in DEPENDENCIES.md and docs/theorem-application-audit/version22.md. PROJECT.md update deferred because that file belongs to Fable's PR176 and Elliot prohibited editing those files. |

These dispositions do not close another reviewer's findings on their behalf. The contribution's owner override remains part of its history.

## Version 22 class C item carried to the next edition

Fable final-head review, 28 November 2026: in the proof of v22:weighted, the final inequality uses M where the preceding lines renamed the label maximum M_lab. This is a notation inconsistency, not a mathematical change. Deferred to the next edition to preserve the independently rebuilt source/PDF pair. The original observation is in reviews/fable-v22-builder-review.json.
