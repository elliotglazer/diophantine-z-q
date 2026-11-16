# Version 6 public-surface review

Read-only review, 2026-11-06. No publication or repository edits performed. The eight requested files and their exact hashes are recorded in `receipt.json`.

**Accepted for source and document fidelity, conditional on the explicit publication gate below.** The current-link and historical-wording corrections have been made by their owner, the pending research and inventory files are installed, and the final local-link check passes.

## Resolved findings and publication gate

1. **Corrected and checked:** `docs/research-guide.md:3` now links the “reconstructed 962-variable quartic” to `quartic-962/README.md`, the new UTF-8 guide. The previous destination was the preserved frozen README, whose historical paragraph retains the old FT qualification. The frozen package remains unchanged.
2. **Installed and checked:** `research/version6/README.md`, both documented Version 6 inventory scripts, and `docs/quartic-962-validation/inventory-review.json` are present. The updated research index distinguishes accepted scope from historical research, and its collective credit agrees with the main README.
3. **Corrected and checked:** under “Version 5 sources, preserved”, `THIRD_PARTY_NOTICES.md` now says “The Version 5 quartic” rather than “The new quartic”, distinguishing that historical attribution from the current collective credit.
4. **Publication gate:** the main README and archiving guide are final-publication text and offer Version 6 download links as available. The parent confirms they will not be pushed until the archives exist and validate, and will verify the actual release URLs/assets before final completion. This review accepts their intended final wording conditionally on that gate. It does not certify archive construction, readiness state, external asset availability or publication. No external release URLs were fetched in this review.

## Passed checks

- The visible manuscript title is Version 6, dated November 6, 2026, with `\author{}`. All BibTeX entries omit author fields.
- The manuscript abstract, introduction and release overview retain exactly the original large construction, the fully expanded 4,973-variable quartic, and the new 962-variable quartic. Other versions are labeled historical in the public guides. The manuscript does not present the superseded 1,272-variable baseline as a fourth current polynomial.
- Current collective credit lists exactly Stefan Baranczuk, Jose Brox, Gabe Conant, Sohail Farhangi, James Freitag, Elliot Glazer, Jennifer Park, and Caroline Terry. The README and current-source notices agree.
- No individual Jose/José/Brox name occurs in visible manuscript text. The strings in hidden hyperlink destinations are retained source URLs, with descriptive visible labels. The bibliography labels the source “Agentic notes”.
- The degree obstruction is stated for one polynomial over Q, using total degree in all variables. The text expressly permits systems of quadratics and makes no variable-minimality claim. Public summaries match that scope.
- FT remains method/provenance, not an assumed theorem. The manuscript narrows the polynomial-count argument to fixed Gaussian ray fields with conjugation-invariant subsets of the split-prime subgroup. The public summaries do not claim a replacement for arbitrary Galois fields. Exact inspected-source qualifications, including DK and Kollár, remain explicit.
- Finite polynomial checks are distinguished from the arithmetic proof, incomplete Lean work, and independent human peer review. Symbolic exact coefficients are distinguished from digit-by-digit integer expansion.
- The manuscript build script reads `quartic_962.tex`, produces the matching output names, and records manuscript version 6, consistent with the current build guide.
- All 86 local Markdown links inspected across the final requested Markdown files resolve. No checked local heading anchor is broken, and both documented inventory scripts exist. Historical links continue to identify their own versions.

The manuscript source reviewed here has SHA256 `06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c`. This is a public-surface and release-consistency review; the mathematical replacement was reviewed separately. Inventory validation, archive generation, final file hashes and final downloadable assets must be checked after their owners finish them.
