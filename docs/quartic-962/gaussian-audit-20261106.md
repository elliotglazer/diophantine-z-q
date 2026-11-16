# Gaussian appendix audit, 6 November 2026

Four Astra agents independently reviewed the large-prime tail, Gaussian prime-weight estimates, transference, and polynomial-pattern application against the pinned source versions. Their proposed changes were integrated, and a separate assembly and interface check verified the resulting TeX.

The reviews report no outstanding mathematical gap within those four scopes after the changes below. This is internal model review, not independent human validation or formal verification. The restricted converse, height theorem, and other Section 15 applications were not re-audited in this pass.

## Changes to the manuscript

- **Large-prime tail:** the weighted proposition now explicitly requires a fixed lower cutoff `L >= L_*`, and its leading constant is uniform in that range and independent of the fixed positive `tau`. The final proof chooses `L >= max(L_1,L_*)`. The proof now supplies the coordinate reconstruction, zero-fibre count, rank and content checks, short lattice-side treatment, and logarithmic-weight estimates.
- **Prime weights:** a new corollary explicitly discharges the factorization hypotheses and states the fixed-modulus centered nilsequence estimate used by transference. Its uniformity is in the orbit and bounded complexity, not in a varying arithmetic modulus.
- **Transference:** the fixed rescalings needed for literal majorant domination and bounded-by-one model hypotheses are explicit. The local-factor proof includes singleton systems. The boundary argument gives positive-coordinate embeddings for negative polynomial coefficients and handles artificial cyclic wraps separately.
- **Polynomial patterns:** the dense-model normalization and parameter order are explicit. The ray-field product quotient is justified by a disjointness and degree argument. Tao–Ziegler's bibliography entry is corrected from 73 to 60 pages.

No finite polynomial data, polynomial bounds, or final theorem statement changed. No new external theorem was introduced.

## Review records

| Scope | Report |
| --- | --- |
| Large-prime tail | [Source checks and derivation](evidence/gaussian-four-audit-20261106/tail/REPORT.md) |
| Prime-weight estimates | [Source checks and derivation](evidence/gaussian-four-audit-20261106/weights/AUDIT.md) |
| Transference | [Source checks and interfaces](evidence/gaussian-four-audit-20261106/transference/AUDIT.md) |
| Polynomial-pattern application | [Source checks and final limits](evidence/gaussian-four-audit-20261106/patterns/audit.txt) |
| Tail-to-final-count interface | [Independent cross-check](evidence/gaussian-four-audit-20261106/patterns/tail-interface-review.txt) |
| Integrated TeX | [Independent assembly review](evidence/gaussian-four-audit-20261106/transference/INTEGRATION_REVIEW.md) |

The [integration receipt](evidence/gaussian-four-audit-20261106/integration-receipt.json) pins the candidate, revised exports, and reports. The previous exports and receipts remain available as historical evidence; the current inventory uses the new exports.

The source-version qualifications remain: the Browning–Heath-Brown and Browning–Loughran checks used accepted manuscripts of published papers, and the Dodos–Kanellopoulos check used arXiv v4. Their final typeset statements were not compared. The other source inspections are identified individually in the reports.
