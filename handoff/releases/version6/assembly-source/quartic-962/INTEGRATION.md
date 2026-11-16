# Version 6 integration

This preparation directory contains no production edits. `construction.tex` replaces the final quadratic-compilation subsection of the Version 5 shared-point section. The preceding arithmetic source and its soundness/completeness proof remain the mathematical specification. The fragment gives exact maps from that source to the new 962-coordinate circuit, so the arithmetic proof need not be rewritten around circuit coordinates.

Retain exactly the three intended polynomial constructions in the final manuscript: the original construction, the existing 4,973-variable fully written quartic, and the new 962-variable quartic. The 1,272-variable quartic is superseded as the third displayed construction. The old builder included in the new package is provenance for the equivalence proof, not a fourth displayed polynomial.

## Frozen artifact

Copy the complete immutable directory `work/quartic-sub1000-20261106/combined/frozen` to the eventual release path `quartics/quartic-962`. It is self-contained and was rebuilt in a fresh directory. Do not regenerate or edit its mathematical artifacts during manuscript integration.

| Artifact | SHA256 |
| --- | --- |
| MANIFEST.json | 36fca72cb0eb126193ffa43d890ff09d5e29cbf1274561d2632ed1e227163787 |
| build_source.cjs | b99b000a57a904328d167a3b3fe9e319e84dc880f03071af9b4face29bc9a570 |
| raw-translated-ir.json | cb1295d789c5bb40bd98842b1bd2a51a05c6ff2058a526e7d1d9b177d20da3ae |
| compiled-ir.json | 244269ada6870d0e2447fd115216844f4ec9c878eba2ddc74303cb12d78b744a |
| polynomial.json | 6b798de7d00ac3c7d725ca0a69d39f1eac1ddb02fee2756cb6323770b952af32 |

There are 962 total active variables, comprising the input and 961 witnesses; 919 quadratic residuals; 55,409 monomials; degree four; primitive coefficient content one; and exact coefficient height 64*S², with S=3^(2^27). Raw counts are 90 base coordinates, 904 arithmetic coordinates, 47 structural equations and 904 gate equations. Exactly 32 coordinates and rows are eliminated.

The S-free coefficients number 55,401 and have maximum bit length 1,526. Seven coefficients have the form c*S with 0<|c|<=768. One coefficient is 64*S², at X79². The coefficient of X0⁴ is one. These facts were read from the frozen table and checked against the independent checker.

## Manuscript edits to prepare

The line numbers below refer only to the immutable file `work/quartic-version5-release/repository/quartic_1272.tex`. Use labels or text when applying after other changes.

1. Change the title's version number at line 39 to Version 6. Replace the abstract's third construction at lines 53 onward by the 962-variable statistics. Preserve the original polynomial and all 4,973-variable assertions.
2. Update the introductory third-polynomial paragraph at lines 113 onward to 962 variables and the new section reference. Do not add a fourth polynomial paragraph for the superseded 1,272-variable construction.
3. Rename the section at lines 10524 onward to “The shared-point quartic in 962 variables.” Use `sec:v6-962`; either update the two old references to `sec:v5-1272` or retain that label as an explicit compatibility alias. Rewrite the opening attribution to distinguish inherited arithmetic from the new circuit transformations.
4. Remove the old `thm:v5-1272-polynomial` statement at lines 10556–10574. The new theorem is `thm:v6-962-polynomial` in the fragment. It can remain at the start of the compilation subsection, or be moved to the section opening without changing its text.
5. Retain the mathematical source and arithmetic argument from `subsec:v5-point-source` through the end of the proof of `thm:v5-source-projection`, approximately lines 10576–11208. Its old halfpoints, poles and finite correction choices define a reference source. Add one sentence that these are the semantic specification and are converted to the implementation coordinates in the new compilation subsection.
6. Replace everything from `subsec:v5-compilation`, starting at line 11210, through the old theorem's final proof immediately before `% End Version 5 main additions`, with `construction.tex`.
7. Update any remaining references to the old polynomial theorem, final-polynomial equation, compiler proposition or table-statistics proposition. New labels are `thm:v6-962-polynomial`, `eq:v6-final-polynomial`, `lem:v6-point-chart`, and the new domain/evaluation equations in the fragment. The older mathematical-source labels intentionally remain.
8. Replace public links and reproduction commands for the advertised third quartic with `quartics/quartic-962`. Search for literal `1272`, `1\,272`, `48001`, `1229`, `1214`, `5339`, and `quartic-1272`, and review each occurrence. Do not mechanically change provenance hashes, bibliography text, unrelated numbers, or historical audit records.

## Statements requiring semantic care

- The retained source says that each point is represented by an old halfpoint. That is the reference predicate. The implementation now stores t,h and uses `eq:v6-point-chart`. Do not silently reinterpret the old halfpoint symbols as the new chart variables.
- Initial correction coordinates are signed partial products, not Booleans. The reverse map recovers Booleans, so the old finite correction set in the source is unchanged.
- At each pole, the implementation stores C*e_old, not e_old. The scalar preparation parameter is still present.
- The F5 inverse is removed from the implementation, but F5!=0 remains a theorem of the implementation equations. Its proof uses positive scales and the retained delta inverse. The w0 trace inverse and subtraction guards remain explicit.
- The two shared logarithms omit their separate local-parameter coordinates. Their fused quotient equations retain the same nonzero ordinate premise. This is not a new global-logarithm theorem.
- The individual optimization savings should not substitute for the final measured count. The final count was computed after all interactions and all 32 eliminations.
- The arithmetic dependence on the simultaneous prime theorem, height estimate, cyclic group and pole-completeness result remains. Root's separate Frei–Tinková replacement must update those inherited proofs and the application inventory. Neither the finite certificate nor the reviews here proves that replacement.

## Validation and release boundary

The frozen package has passed a fresh isolated reproduction and three complementary reviews: complete gate/certificate/table checking; source-domain and witness-map review; and an independent SOS/count/input audit. The preparation fragment is additional exposition and is not itself a substitute for those files.

The preparation JSON parses. The fragment has balanced braces, 13 distinct labels, and all six explicit references resolve against its own labels or the retained manuscript. A standalone `pdflatex` attempt stopped before reading the source: the installed MiKTeX reports a fresh installation and cannot create its user profile directory under `AppData/Roaming/MiKTeX/2.9` with the current filesystem permissions. The TeX fragment has therefore not been typeset in this environment. `validation/fragment-check.tex` is a minimal wrapper for a configured TeX installation.

An independent worker reviewed the fragment against the accepted witness proof and frozen metadata and accepted its mathematical content and integration plan. Its requested clarity improvements were applied: the retained power outputs are explicit, and the scalar norm equation uses the named retained leaf to display a literal quadratic expression.

Root owns the separate degree lower bound, the simultaneous-prime argument, all manuscript-wide application counts, and publication authorization. No production repository, release tag or remote was modified for this preparation.
