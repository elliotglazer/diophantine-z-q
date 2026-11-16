# Literal 15,671-witness anchor review

The original anchor passes the local and polynomial checks in this scope. Its seven-witness predicate is exactly the published semilocal predicate from Koenigsmann's Proposition 6. No offset, new variable, altered equation or enlarged constant is needed.

[anchor-proof.tex](anchor-proof.tex) supplies the full specialization and local argument. [source-application-ledger.json](source-application-ledger.json) records publication, edition, theorem locators, byte pins and matched conventions. The original article's reference to a supplied source is replaced by an explicit published application, while keeping the formula unchanged.

The proof establishes the exact nonzero index set

    2 * 3^(2^23-1) Z \ {0}.

At 3, P reduces to a point of order two and z(2P) has valuation one. At 2, P itself lies in the formal branch, so its multiples already have integral reciprocal coordinates. The two rational coefficients are handled separately; no cancellation or unidentified field trace is assumed. The subgroup can meet any additional finite list of index divisibilities and has positive representatives.

The original constant remains C=3^(2^24), represented by 25 shared variables and 25 equations. The anchor keeps 16 private variables and six equations. The exact integer comparison proving |n|>(20H)^2 is verified, conditional on the separate original bound log2(H)<4,783,227. This folder does not certify the geometric H5 input. A failure of that input would remain a failure of the full original construction even though this anchor calculation passes.

The source trace distinguishes three different artifacts. The literal `q_anchor.json` and `shared.json` contain the formula reviewed here. The supplied `focused_diophantine.tex` proves the same local mechanism with a much longer old chain; its exponent is not imported unchanged. The separate `supplied-short-anchor-proof.tex` uses a 409-based chain and is not the literal anchor's specification. Our proof derives the 24-squaring case directly.

## Reproduce the small checks

```console
python check_anchor.py
```

The script checks all six anchor rows, all 25 shared-chain rows, and the actual root call. It verifies that root variables 26 and 27 are the reciprocal of the S abscissa pair 30 and 31 by checking both field-coordinate equations. Exact rational-pair arithmetic verifies the curve change, reduction of P at 3, the displayed z(2P), and the initial 2-adic depth. It prints JSON and writes a report only when `--output PATH` is supplied. The author's original receipt is [reference-anchor-check.json](reference-anchor-check.json). Input paths resolve relative to this package; `--package PATH` can select another copy with the same layout.

This is a small scalar check, not an expansion or build. It never materializes C. The anchor and constant-chain residuals are already primitive, have degree at most two, and their sum-of-squares contribution has coefficient L1 bound 6,956<2^13 and degree at most four. Thus this proof adds no hidden large polynomial coefficient. Verification of the full degree-eight polynomial and its global <2^80 bound belongs to the separate packaging audit.

The completed 20,371-witness repository and its inventory were not edited.
