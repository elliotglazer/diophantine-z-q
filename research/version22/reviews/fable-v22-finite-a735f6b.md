# Version 22 draft (PR178): finite and source/PDF check

Reviewer: Claude Fable 5.2, local session (not the Protocol B gate reviewer). Run 27 November 2026 (UTC evening).
Head checked: `a735f6b13e56263a82de8b1aad57a98e2b4ffd91`, base `dda0439aa44a63a05d4ef7c58230caed6df8e628`.

**Scope.** Finite identities, file identity, text consistency and PDF text extraction only. No arithmetic proof was reviewed here. No program from the pull request was executed; `check.py`, `verify175.py` and `verify_interpretation.py` were not run and not read line by line. I did not run pdfLaTeX and did not look at page images.

Scripts: `C:\Users\glaze\Documents\fable-v22-review-scripts\` (`rows_vs_json.py`, `side_checks.py`, `retained_diff.py`). Extracted data: `C:\Users\glaze\Documents\fable-v22-review-data\`.

## Summary

| # | Item | Verdict |
|---|---|---|
| 1 | Four stated hashes, 854 pages | Verified |
| 2 | 147 printed rows against the verified PR175 table | Verified: identical, same order, same names, no renaming |
| 3 | Counts, height, bytes, SHA-256 | Verified |
| 4 | Changed paths, frozen files, credits | Verified, with five observations |
| 5 | PDF against TeX, section/page map | Verified from extracted text |
| 6 | Version 21 blemishes | Range typesetting fixed; one `Jos\'e` and the `GPT-6` line remain |
| 7 | Arithmetic audit and dependency record | Summarized; author work only, as it says |
| 8 | Audit-history failure | Explained; needs a new review record and an updated binding |

Nothing mismatched. The observations in items 4, 6 and 8 are things to fix or decide before release, not errors in the mathematics or tables.

## 1. Hashes

All four equal the values in Astra's note.

- `manuscripts/quartic_v22.tex`: `89484c10127136d407f7761fef1bdfd9313a98d47696a3d7bc6ff2d1896a1c48` (2,877,455 bytes)
- `manuscripts/quartic_v22.pdf`: `db40813bb1656e3462d1a3a8673e0c2ea2dffdd2262662f3cf26fbbcf3fc52ac` (5,530,230 bytes; `pdfinfo` reports 854 pages)
- `research/version22/BUILD.json`: `142c6f3257ae320e849bd19c944c60de6fd738d8c0ccb40ad2033fa43c559d11`
- `docs/current-manuscript.json`: `122b63088d27b8f11754d9caa95d182f52228aa9921b130c3668aa778bd0b251`

`BUILD.json` and `RELEASE-MANIFEST.json` record the same TeX and PDF hashes. The three files pinned in `construction/INPUTS.json` match their stated hashes and sizes.

## 2. The 147 printed rows

The table is Section V22.8 of the TeX (lines 806–1815): 147 blocks `% V22_ROW n name` … `% V22_END_ROW`, each one `equation` tagged (22.n), with `C` standing for 331^21.

- I parsed all 147 with my own parser. The section holds nothing else except its three-sentence introduction.
- The comparison table is `research/version22/construction/inputs/quadrics.json`. It is the same git blob (`dbb2dfb2…`) as `research/contributions/brox_explicit175_20261126/source/computation/projective_contacts_20261126/quadrics.json`, which I verified for PR175.
- **Correspondence: identity.** Printed row n equals table row n as a polynomial after substituting C = 331^21, with the same row name, for every n from 1 to 147. There is no reordering, sign change, renaming or variable map.

**Row interpretations.** The TeX does not give a per-row interpretation list or grouping totals; Section V22.7 gives a coordinate dictionary instead. The claim "147 of 147 rows directly interpreted" lives only in `construction/DIRECT-AUDIT.json`, produced by the author's `verify_interpretation.py`, which I did not run or audit. What I did check: every identity that Section V22.7 states as a single row is literally a row of the table.

| Stated identity | Row |
|---|---|
| x37 = X^2 | 1 |
| r = 1024 t^2 for the three contact tuples | 95, 103, 109 |
| s = r^2 for the three contact tuples | 96, 104, 110 |
| Q_j w_j = u^2 for j = 0, 1, 2 | 100, 108, 114 |
| σ τ̂ = R^4 (as x79 x86 = x87^2) | 138 |
| x159 x160 = 1 | 145 |
| x161 = x160^2 | 146 |
| x87 = x88^2 | 147 |

The three pole-input rows carrying 166464 = 408^2 and 167281 = 409^2 are rows 99, 107, 113. The field-coordinate formulas of V22.7.1 and the native pole table were **not** checked by me.

Row-name groups (count by first name component): bbnative 12, v82 25, cleared 14, additive 12, new 10, homogeneous 10, new1 8, new3 8, new4 8, shared 7, amplified 6, sharedT 6, input 4, balanced 3, unit 3, and 2 each for testSquare, detector0, detector1, detector2, scalar, plus inputSquare 1. Total 147.

## 3. Counts

Recomputed from the printed rows themselves, not from the JSON:

- Variables: exactly x1..x175.
- Monomials: 3,196. Degree 4. Content 1. Coefficient of x1^4 is 1.
- Height: the largest absolute coefficient has exactly 802 bits (242 decimal digits), so it is below 2^802. It occurs once, at x37^2, with positive sign. The decimal blocks printed after Theorem V22.9.1 equal it.
- Plain notation: my rendering of the printed rows is 73,080 bytes with SHA-256 `efc0be237413e25f1308d0a2e8fa1750c5de526a83046cc3aac5123ea12d4292`, byte-identical to `research/version22/construction/inputs/expanded175.txt`. The TeX prints that SHA-256.
- The abstract, Theorem V22.9.1, `README.md`, `research/version22/README.md`, `FINITE-AUDIT.json` and `RELEASE-MANIFEST.json` all state 175 / 3,196 / below 2^802 / 73,080 consistently.
- There is no `CURRENT_VERSION22.md` (see item 4).

Side numbers in `FINITE-AUDIT.json`:

- The contact constant 9042…0000 is below 2^249 (it has 249 bits). The stated margin fraction equals (2^249 − constant)/2^249 exactly, about 0.045%. Its factorization is 2^85 · 3^25 · 5^14 · 7^8 · 11 · 13^2 · 17 · 19^2 · 23 · 37 · 41 · 1969605389, and 1969605389 = 2399 · 821011.
- **Not recomputed:** how that constant is derived, the Euler product, and the 331 anchor residues in this version. I checked the anchor facts for PR175 from the contribution's own certificate, not from this manuscript's text.

## 4. Changed paths, frozen files, credits

29 files changed, +180,582 / −17.

- Added: `manuscripts/quartic_v22.tex`, `manuscripts/quartic_v22.pdf`, `docs/theorem-application-audit/version22.md`, and 22 files under `research/version22/` (12 at top level, 9 under `construction/`, 1 under `reviews/`).
- Modified: `README.md`, `CREDITS.md`, `THIRD_PARTY_NOTICES.md`, `docs/current-manuscript.json`.
- **No released file is touched.** Nothing under `manuscripts/quartic_v16`–`v21`, `research/version16`–`21`, `releases/` or any `CURRENT_VERSION*.md` is in the diff. The Version 21 TeX in the tree still hashes to `c98a66a0…`.
- No workflow, script, test, Lean file or `PROJECT.md` is changed.
- `research/version22/reviews/fable-pr175-lineage.md` is byte-identical to my report (`b9024fd5…`).

Credit lines changed:

- `CREDITS.md`, one new paragraph: "Version 22's explicit 175-variable construction is due to Jose Brox, building on the retained Conant and Brox constructions. OpenAI Codex's 6 Astra wrote the integrated presentation and independent finite checkers. Fable's supplied finite lineage check is preserved with its original scope; it is not described as arithmetic acceptance." The contributor list line is unchanged.
- `README.md`: a new section "Version 22 preparation", naming Jose Brox and stating that Version 21 remains the published release.
- `THIRD_PARTY_NOTICES.md`: a new section on the copied construction inputs.
- `research/version22/CREDIT-CONFIRMATION.json` quotes Elliot's chat message as authority for attribution and spelling. It is not a linked confirmation comment on GitHub.

Observations:

1. **Agent naming.** `CREDITS.md` writes "Fable's" and "OpenAI Codex's 6 Astra". The agreed names are "Claude Fable 5.2" and "6 Astra".
2. **AI usage statement.** The statement at the end of the TeX is unchanged from Version 21: it still ends "package preparation by GPT-6" (TeX line 57278, PDF p. 854).
3. **One accented spelling remains.** TeX line 5820, in the retained Version 20 part: "starting from Jos\'e Brox's quadratic system". Thirteen other occurrences in the retained text were changed to "Jose"; this one was missed because the name breaks across lines. No "José" or "GPT-6" occurs in the new `research/version22/` files or in the new Part I.
4. **Index files not updated.** `manuscripts/README.md` still presents Version 21 (and still says "José" and "Candidate PDF"), and there is no `CURRENT_VERSION22.md`, although Versions 17–21 each have one. These may be intended for the release step; the handoff does not say.
5. **Line endings.** `docs/current-manuscript.json` was CRLF (534 bytes) at the base and is LF (517 bytes) here. The stated hash is of the LF file. Harmless, but a checkout with a different line-ending setting would hash differently.

Release wording: no file calls Version 22 released. `ARTIFACTS.json` says `"status": "candidate"`, `RELEASE-MANIFEST.json` says "Draft candidate … Version 21 remains the published record" and `"publication": "not authorized by this record"`. No new file calls Version 21 a candidate (the old `manuscripts/README.md` still does, see observation 4).

## 5. PDF against TeX

`pdftotext` (Poppler, from the local Git installation) extracted all 854 pages.

- Title "Z is Diophantine in Q", "Version 22", "November 27, 2026" on page 1 match `\title` and `\date`. `\author{}` is empty in the TeX and no author is printed; the PDF metadata author is "Elliot Glazer and attributed contributors", as in `\hypersetup`.
- The abstract on page 1 matches the TeX: 175 variables, 3 196 monomials, below 2^802, 73 080 bytes.
- Astra's "pp. 12–31" is correct: Part I runs from page 12 to page 31, and Part II (Version 21) begins on page 32.
- Sample rows: tags (22.1) and (22.2) are on p. 21, (22.50) on p. 25, (22.100) on p. 28, (22.146) and (22.147) on p. 31, and the extracted text of rows 141–147 matches the TeX. Theorem V22.9.1, the SHA-256 and the byte count are on p. 31.

**Section and page map for the arithmetic reviewers** (physical PDF pages; TeX lines in brackets):

| Section | Title | PDF pages | TeX lines |
|---|---|---|---|
| Part I | Version 22: an explicit quartic in 175 variables | 12–31 | 86–1865 |
| V22.1 | Construction and arithmetic inputs | 12–13 | 90–159 |
| V22.2 | The new pole realization (Bhargava–Burungale Lemma 2.2, Theorem 2.3) | 13 | 160–228 |
| V22.3 | Projective contacts and their height | 13–15 | 229–315 |
| V22.4 | Scalar anchor and point interpretation | 15–16 | 316–429 |
| V22.5 | The shared comparison and the effective conclusion | 16–18 | 430–605 |
| V22.6 | Simultaneous integer completeness | 18–20 | 606–702 |
| V22.7 | Binding the pole and contact rows | 20 | 703–755 |
| V22.7.1 | Field-coordinate interpretation | 20–21 | 756–805 |
| V22.8 | The complete quadratic table (rows 22.1–22.147) | 21–31 | 806–1815 |
| V22.9 | The resulting quartic (Theorem V22.9.1, largest coefficient, notation, SHA-256) | 31 | 1816–1865 |
| Part II | Version 21 (retained) | from 32 | from 1866 |

The new arithmetic is therefore about nine pages, 12–21.

**Retained text.** Outside the inserted Part I, the Version 22 TeX differs from the released Version 21 TeX in 45 places, all accounted for: title, date and PDF title (3); the abstract's quartic sentence (1); "Jos\'e" → "Jose" (13); and 28 index ranges `a--b` → `a\text{--}b` in the two normalization tables. This matches `RETAINED-EDITS.json`, except that its sixth entry ("current-part clarifications") describes text in the new Part I, not an edit to retained text. The abstract no longer mentions the 229-variable quartic or the 195-variable Busy Beaver quartic; both remain in the body.

## 6. Known Version 21 blemishes

- **"1 − −16" typesetting:** fixed. All 28 ranges now use a text-mode dash, and the extracted PDF text has no "− −" before a range.
- **"José":** changed in 13 places, one left (TeX line 5820, retained Version 20 part).
- **"GPT-6":** not fixed (TeX line 57278, PDF p. 854). `CORRECTIONS.md` does not list it, which is expected: I never posted the name and agent-name corrections to backlog issue 129, so Astra had no record of them.

## 7. What the author's audit and dependency record claim

`ARITHMETIC-AUDIT.md` (author's work, stated as such):

- Checked: Bhargava–Burungale v2 Section 2 (Definition 2.1, Lemma 2.2 and proof, Theorem 2.3 as printed) read from the arXiv HTML; the j, k hypotheses and curve scaling written out; the three native equations derived by substitution; pole soundness at every prime including zero auxiliaries; the input 7b/9 with the prime 3 denominator and the exception at 7.
- Checked: the projective contact transformation (determinant 156800 = 2^7 · 5^2 · 7^2), transport of the primitive contact forms, the height by two H4.1 bounds, the exact contact constant below 2^249 "with a narrow margin", the midpoint case.
- Checked: all 331 anchor residues, the depressed cubic, the exponent 97, the scalar dyadic unit, the Euler product, the numerical endpoint, the weighted height estimate; every final row directly.
- Says it corrected the wrong reference-norm list of the contribution's notes (my PR175 note N3) by printing the five retained norms.
- **Not claimed:** an independent proof of Theorem 2.3's descent and analytic inputs ("used as stated"); any non-author review; gate acceptance.

`DEPENDENCIES.md`, preprint dependency: **one new preprint**, Bhargava–Burungale arXiv:2611.16130v2, Definition 2.1, Lemma 2.2 and Theorem 2.3. Only the simultaneous rational-point conclusion is consumed; the preprint's analytic-rank and Sha conclusions are said not to be used. All other suppliers are retained internal results of Versions 5–21 (`q198:*`, `v21:*`, `q214:*`, `thm:v5-simultaneous-primes` and the Version 15 dependency lemmas), which carry their own earlier external dependencies unchanged. The exact constant c0 = 74712001/10^6 is inherited from the retained height input.

## 8. The audit-history self-test failure

Cause: `docs/current-manuscript.json` now selects Version 22, but `docs/audit-history/builder-binding.json` is unchanged and still binds Version 21. `scripts/check_application_reviews.py: validate_builder_binding` pins each bound file by hash, so it fails at the first stale pin:

- `profile.sha256` is `b3f8f4fd…`, the Version 21 selector; the file is now `122b6308…`.
- `selected_manuscript` is `manuscripts/quartic_v21.tex`; the profile now names `quartic_v22.tex`, so "Builder profile selects another manuscript" would fail next.
- `review` points at `research/version21/reviews/fable-v21-builder-review-corrected.json`, whose `files` list does not contain the new profile hash.

The `builder` pin (`scripts/build_paper.py`, `f62e565f…`) and the `historical_review` pin (`docs/audit-history/current.json`, `2b0dd765…`) are still correct.

What a non-author reviewer would have to supply (not created here):

1. A new record, by the Version 21 precedent at `research/version22/reviews/<name>.json`, with:
   - `schema`: `record-manuscript-policy-review/v1`
   - `decision`: `accepted_within_scope` (the validator requires exactly this)
   - `reviewer`: non-empty; `author_of_policy_or_implementation`: false
   - `reviewed_at`: the actual time of the check; `reviewed_root`; `request`
   - `files`: a list of `{path, sha256}` without duplicates that must include `scripts/build_paper.py` at `f62e565f…` and `docs/current-manuscript.json` at `122b6308…`; the Version 21 record also listed the TeX, PDF, build record and the preserved earlier versions
   - `scope`, `checks`, `observations`, `limitations`
2. Then `docs/audit-history/builder-binding.json` must be updated (by the author, since it is not a review) so that `profile.sha256`, `selected_manuscript` (path and hash of `quartic_v22.tex`), `review` (path and hash of the new record) and `scope` describe Version 22. Its key set must stay exactly `schema, builder, profile, historical_review, selected_manuscript, review, scope`.

Two things to settle before such a record is written:

- `BUILD.json` records `builder_sha256` `5afbf705…`, which is not `scripts/build_paper.py` (`f62e565f…` with LF, `18c5cc50…` with CRLF). Version 21's `BUILD.json` has the same value, so this is the same situation as last time, but the record should say which program that hash names.
- Any edit to the TeX to fix the observations above changes the TeX, PDF, `BUILD.json`, profile and manifest hashes, so the binding record should be written against the final head, not this one.

## Not checked

- Any arithmetic argument in Sections V22.1–V22.7, including the Bhargava–Burungale application and the contact-height bound.
- The author's three checker programs and `DIRECT-AUDIT.json`'s "147 of 147" claim.
- The field-coordinate formulas of V22.7.1 and the native pole coordinate table.
- The derivation of the contact constant, the Euler product and the anchor residues as stated in this manuscript.
- Page images, fonts and layout of the PDF; a rebuild from source.
- The 194 `tex_inputs` hashes inside `BUILD.json`.
- `CORRECTIONS-SOURCES.json` against issue 129.
