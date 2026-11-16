# Version 6 research

This directory retains the mathematical research behind the 962-coordinate construction. The [current manuscript](../../quartic_962.pdf), [source inventory](../../docs/quartic-962/README.md), and [independent inventory review](../../docs/quartic-962-validation/inventory-review.md) state the adopted scope.

| Research | Contents |
| --- | --- |
| [Lower-bound audit](lower-bound/independent-review/REVIEW.md) | The single-polynomial total-degree obstruction over the rationals and its source qualifications |
| [Optimization work](optimization/combined/PROOF.md) | The reductions leading to 962 coordinates, with intermediate alternatives and component reviews |
| [Analytic replacement](analytic-proof/ASSESSMENT.md) | The fixed Gaussian ray-field proof and its reviewed connection to the polynomial-pattern argument |

The [frozen 962-coordinate package](../../quartics/quartic-962/README.md) contains the exact source, coefficient table, certificates and accepted transformation evidence. The [portable checker](../../scripts/check_quartic962.py) runs fourteen finite verification stages. The [research manifest](../../handoff/V6_RESEARCH_MANIFEST.json) maps the original source paths to this directory and to that package.

The end-to-end analytic review accepts removal of the assumed Frei-Tinkova theorem for the stated fixed Gaussian ray fields and split-prime classes. The final assembly review preserves this scope through the attribution and display-layout changes. The review does not claim an arbitrary-Galois theorem or inspection of every final publisher version. Dodos-Kanellopoulos and Kollar retain their author-version qualifications; the inherited sieve-source qualifications also remain.

Historical notes and intermediate metadata retain their original status wording. Their presence does not adopt a superseded argument. Downloaded third-party papers and page captures are omitted from this new selection, with source hashes and metadata retained. The [assembly source map](../../handoff/releases/version6/assembly-source/SOURCE_MAP.json) records the reviewed assembly scripts, intermediate manuscript and final component locations.

Contributors: Stefan Baranczuk, Jose Brox, Gabe Conant, Sohail Farhangi, James Freitag, Elliot Glazer, Jennifer Park, and Caroline Terry.

These are source-level mathematical reviews and finite computational checks. They are not a proof-assistant certificate or a claim of human peer review. The main Lean theorem remains unproved.
