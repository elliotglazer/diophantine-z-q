# Detector and norm circuits

The candidate has 1,107 total rational coordinates, including the unchanged input, and 1,064 quadratic residuals after the baseline compiler. This saves 165 coordinates against the immutable 1,272-coordinate baseline. Raw counts are 1,139 coordinates and 1,096 residuals. The exact sum of squared, denominator-cleared residuals has integer coefficients and degree four. The large fixed parameter S is never expanded.

`patch_builder.py` exports `patch(text)` for integration with the other workers. `build_candidate.cjs` and `raw-ir.json` give the executable candidate and exact raw residual system. `reduced-ir.json` gives the reduced system, and `reduction-certificate.json` records the baseline compiler's 32 eliminations. `verify.py` checks formal polynomial identities, runs three samples against the immutable source oracle, rebuilds the reduced system, and records `verification.json`. Samples test implementation consistency; the identities and maps below prove equivalence.

## Changes and measured savings

| Change | Total coordinate saving |
| --- | ---: |
| Balanced convolution for symmetric polynomials | 42 |
| Power-basis detector evaluations | 117 |
| Lucas multiplication regrouping | 2 |
| Scalar norm quotient fusion | 4 |
| F5 quintic regrouping | 0 |
| Total | 165 |

The attempted F5 improvement saves zero because the baseline already shares the common t² terms of its two initial factors. It remains an equivalent three-assignment formula in this candidate.

For ten field inputs y_i, compute coefficients of product(1+y_i*T) with a balanced product tree. At each internal node, assign each convolution coefficient as a single quadratic sum in each of the two field components. The linear coefficient is free. A ten-leaf tree uses 25 field assignments instead of 45; four leaves use five instead of six. Two leaves are unchanged. Every input y_i remains the original squared test.

For a degree-n field polynomial with affine coefficients c_k, build scalar powers q² through q^n, using q^k=q^floor(k/2)*q^ceil(k/2). Then assign each of the two components of sum(c_k*q^k) once. The output therefore uses n+1 coordinates, versus 2n for the baseline Horner evaluation. The three degrees are ten, two, and four, so each detector saves 9+1+3=13 coordinates. There are nine detectors.

The original Lucas expression is t²-a(a-2)tb+((a-2)b)²-1 in K=Q(sqrt(2)). Set C=(a-2)b and AT=a*t. The same expression is t²-AT*C+C²-1. This removes one field multiplication. No exact Lucas equation or new proxy predicate is introduced.

For the scalar tree write r=scalar.r and i=scalar.rInverse; the original equation ri=1 remains. Let f=PU[0].f[0], u=PU[0].f[1], and g=PS.f[0]. Replace n0=1+r(fi)² by r*n0=r+f². Replace n1=(ui)²+r(gi)² by r*n1=u²i+g², retaining the existing leaf1=u*i. These equations are quadratic, and r is nonzero. The removed leaf0 and leaf2 aliases remain quadratic expressions for diagnostic evaluation, without allocated coordinates. The exact difference certificates are

    r*(1+r*(f*i)^2)-(r+f^2) = f^2*(r*i-1)*(r*i+1)
    r*((u*i)^2+r*(g*i)^2)-(u^2*i+g^2)
      = (u^2*i+g^2*(r*i+1))*(r*i-1).

## Exact maps on rational zero sets

The maps preserve all 90 original base coordinates, especially the input coordinate 0. They preserve the original inverse and field-quotient guards and all structural equations.

Given a baseline zero, retain the base coordinates and unchanged arithmetic values. Evaluate the new balanced tree, power chains, Lucas intermediates, and three-assignment F5 formula. Set the new scalar n0 and n1 to their baseline values. The displayed identities show every new residual vanishes. All later semantic values, including detector W, B, the scalar tree, and the anchor input, are identical.

Given a candidate zero, recover every baseline arithmetic coordinate by evaluating its original expression in dependency order on the same base coordinates. Polynomial assignment equations uniquely determine their assigned coordinates. All retained division guards are unchanged. The only new divisions have denominator r, which has its retained inverse equation. The identities show the two new norm quotients equal the baseline norm values. Thus all baseline semantic outputs and structural residuals agree and vanish. This produces a baseline zero with exactly the same input.

The compiler's rational affine elimination maps then identify raw and reduced zero sets. These maps are recorded in the reduction certificate. They protect the input.

These changes compose with field-quotient changes, logarithm/DAG changes, and pole/Boolean changes. They do touch `evalSym`, the symmetric coefficient loop, Lucas construction, F5 construction, the scalar leaves declaration, and the scalar n0/n1 declaration. Apply this patch before renaming those blocks. The underlying source's arithmetic hypotheses and qualifications, including Frei–Tinková, are unchanged.

## Optional alternative weight patch

`patch_weights.py` exports a separate `patch(text)` and is not included in the primary patch. Applied after the primary patch, its checked artifacts in `weights/` have 1,079 total compiled coordinates and 1,036 quadratic residuals. It saves another 28 coordinates. The field-quotients worker has a stronger overlapping weight change, so integration should prefer that worker's change and omit this optional patch.

The alternative keeps F's inverse guard. It builds A^5, d2=delta², and the quotient F*q1=A^5*d2, then d3=d2*delta, e=q1*d3, and the inverse R*(e*delta)=1. It drops the old inverse delta and inverse e coordinates. The inverse R equation forces e and delta nonzero. Thus q1 is nonzero. The F inverse and quotient equation then force A nonzero. Conversely, the old guards force these new equations to have unique solutions. Recover the dropped inverse coordinates as 1/delta and 1/e. All downstream weights and R are unchanged. The polynomial identity

    e*F-(A*delta)^5
      = F*(e-q1*delta^3) + delta^3*(F*q1-A^5*delta^2)

is checked exactly in `verify.py`. Unlike the stronger field-worker change, this alternative does not require a separate positivity argument for A. Run its checks with `verify.py path/to/detector-circuits/weights`.
