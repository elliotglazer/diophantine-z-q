# Research checkpoint — norm sharing and Lucas explanation

7 November 2026. Starting fork head:
`d333532c048086de6648bbc9fe497fbae91aa8be`.
Fresh upstream main check:
`5856286a57fba19574a40704571ee70e79738281`, unchanged from the already
integrated Version 8. Contributor instructions and current research notes
were read. No AGENTS.md was found. An unrelated untracked compiler
temporary file was preserved and excluded from this checkpoint.

## Actual work

Tested replacing N and e*delta in the norm/B block by the scaled norm
M=N/delta², so that B*q1=M². The two-way projection and nonvanishing
implications are proved in README.md. Fresh compilation produced the same
900 variables and 857 residuals but 54,357 monomials, compared with 51,252
in the current candidate. The increase is 3,105 monomials. Coefficient
length remains 3,247 bits. This experiment is rejected and remains isolated.

The compiler and full algebraic checker passed. A separate checker verifies
the nine actual emitted norm blocks and the Laurent identity for B;
all ten logarithm and nine mixed-weight checks also pass. Constant-chain
and arithmetic budgets pass, and the ordinary export matches the checked
polynomial table exactly. A changed norm numerator is rejected by the
new checker. Results, verification reports and source hashes are saved.

Implementation lesson: W0 is an affine expression with multiple coordinates,
not a single coordinate. An initial checker assumption to the contrary
failed and was corrected. verify_norm.py checks the full expressions and
the actual normalized assignment gate. Do not silently seed only one of
W0's component coordinates as the whole norm input.

## Conceptual progress

Proved the eight-gate mixed weight circuit optimal in the class with
nonnegative pure-power exponents, pure gates independent of q1, and only
two q1-dependent gates (the outputs). A relaxed exhaustive final-gate
enumeration supports the argument. This does not establish global
optimality: extra mixed intermediates or negative powers are outside it.

LUCAS_BLACKBOARD.md gives a self-contained elementary proof of upstream's
Lucas growth lemma. It explains the norm-one unit orbit, the recurrence,
and how divisibility forces a large orbit index. It distinguishes this
elementary ingredient from the remaining elliptic, height and prime-pattern
inputs. This is an exposition of an existing lemma, not a new theorem.
Finite exact recurrence checks cover 388 signed parameter examples.

The naive cubic rewrite without divisibility fails: t=a,w=1 solves
t²-a*t*w+w²=1 for every a. Merely writing w=(s-2)z does not fix the
precision argument either, because w then has height weight two and the
discrepancy retains weighted degree four. A new independently controlled
integer label w could change the threshold, but its extra point and
comparison cost and common-witness completeness remain unassessed.

## Endpoint and next pass

The best current variants remain 924 variables with doubled targets and
900 with the separately reviewed direct-target proposal. Their files,
hashes and proposed PR metadata remain unchanged; the frozen 933 package
is preserved. No candidate was promoted in this pass.

Avoid repeating the scaled-norm substitution or a search within the
now-proved eight-gate class. A worthwhile next computational search must
allow extra q1-dependent intermediate values or signed exponents, or
share work outside the isolated weight circuit. Track both variables and
monomial count: normalized affine expressions can substantially increase
quartic support even when gate count is unchanged.

All new proofs and code received AI self-review only. Exact arithmetic
checks are not independent human mathematical review. No upstream merge,
PR comment, message or browser operation was performed. This log records
one completed pass, not execution between passes.
