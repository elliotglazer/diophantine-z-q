# Independent integration review

Accepted for assembly and interface consistency. The reviewed candidate is `../quartic_962.tex`, SHA256 `8ca476687a7ab761f3de4d0c964608a3e7d249a97a6c7647d9057ec5a4638c29`, 912132 bytes. There are no integration findings requiring changes.

This review covers assembly, scope and the handoffs among the four audited components. It does not repeat their full mathematical audits or claim that a complete manuscript compilation was performed. The candidate was not edited.

I read `../integrate.py`, `../changes.diff`, `../assembly.json`, all final replacement fragments, and the relevant joined passages of the candidate. Independently of executing `integrate.py`, `check_integration.py` reconstructs the candidate from the baseline by forward line splicing and two explicit text replacements. Its output is exactly equal to the candidate bytes. It also independently reproduces the unified diff.

The fragment ranges are the expected baseline intervals:

| Component | Baseline lines | Inserted artifact |
|---|---:|---|
| Tail | 16389–16531 | `tail/replacement-tail.tex` |
| Weights | 16533–17940 | `weights/weights_fragment.tex` |
| Transference | 17941–18279 | `transference/replacement.tex` |
| Bounded model | 18387–18392 | `patterns/repair-dense-model.tex` |
| Ray fixed field | 18517–18526 | `patterns/repair-ray-fixed-field.tex` |

The other two changes are the root's explicit final choice `L >= max(L_1,L_*)` and the documented Tao–Ziegler page-count correction at baseline line 18686. Every replacement interval is disjoint. The exact reconstruction proves there are no changes outside these authorized intervals and replacements. The unchanged blank baseline line 16532 remains between the tail and weights replacements.

Every fragment occurs exactly once in the assembled candidate. The weights fragment has CRLF line endings on disk; `integrate.py` reads it as text and inserts its LF-normalized content. The raw and normalized hashes are both recorded in `integration-review.json`. This explains their difference and is not a content discrepancy. All other fragment hashes match their inserted bytes directly.

The new centered-nilsequence corollary is present exactly once and precedes the bridge that consumes it. Its weight normalization, fixed-modulus quantifier and fixed-complexity uniformity match the bridge's displayed input. The bridge's fixed domination factors do not alter the polynomial scale parameters. The bounded model repair uses a fixed `B_*`, applies concatenation at `(calA,M1)`, and applies the polynomial generalized von Neumann theorem at `(A,M0)`, consistently with the bridge. The final ray-field repair preserves the previously used quotient, commutator and density conclusions while supplying their degree argument.

The tail now explicitly supplies a threshold `L_*`. The final proof chooses `L >= max(L_1,L_*)` before fixing the ray field, before invoking the fixed-field asymptotic, and before choosing the sequence of small fixed `tau` values. This meets both the ray-class lower-bound cutoff and the tail estimate's cutoff. It introduces no varying-field invocation of the fixed-field theorem.

All old labels remain, there are no duplicate labels, and the sole new label is `cor:ga-fixed-centered-nilsequence`. Every newly introduced reference resolves. The complete declaration blocks for `thm:v5-simultaneous-primes` and `prop:v5-artin-patterns` are byte-identical to their baseline text. The explicit source-version qualification for Dodos–Kanellopoulos remains in the application and bibliography. This integration review does not upgrade that checked author version to a verified final typeset statement.

Machine-readable checks, exact hashes and limitations are in `integration-review.json`. The reproducible read-only checker is `check_integration.py`; it writes only the review JSON in this directory.
