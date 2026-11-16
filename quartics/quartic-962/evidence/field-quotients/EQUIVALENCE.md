# Quotient fusion and nonzero witnesses

This candidate has 1,255 raw rational coordinates and 1,212 quadratic
residuals. The unchanged compiler leaves 1,223 coordinates and 1,180
residuals. This saves 49 coordinates from the frozen 1,272-coordinate
polynomial. The input remains coordinate 0. The compiled integer polynomial
has degree four and 53,925 monomials. Its large fixed parameter remains
`S=3^(2^27)` and is never expanded.

The patch only changes quotient arithmetic. It preserves every source
predicate and every inherited arithmetic qualification, including the
Frei–Tinkova input. It does not reach the target of 999 coordinates alone.

## The changed equations

Write K=Q(sqrt(2)). Every displayed equation in K means its two rational
component equations. All products below use affine expressions or explicitly
retained quadratic gate outputs, so the actual residuals have degree at most
two.

| Change | Old coordinates removed | New equation | Net saving |
|---|---|---|---|
| U0,V0 logarithms | local parameter z=-x/y | y*log=-x*P(D*f²) | 4 |
| Scalar ratio involving U0 | no further coordinate | xH*ratio=-yH*zS | 0 |
| Each detector weight | terminal Ad⁵ product | F*ep=Ad⁴*Ad | 9 |
| Each detector reciprocal weight | ep inverse | ep*R=di | 9 |
| Each detector q1 | di³ product | delta*q1=ep*di² | 9 |
| Each detector trace quotient | norm coordinate | w0*nw=(w0²-2*w1²)/2 | 9 |
| Each detector F guard | F inverse | already implied by weight equation | 9 |

The candidate retains the `delta*di=1` and `w0*wi=1` guards in every
detector. It retains the U0 abscissa inverse and every other unchanged
nonzero witness. In particular it does not remove the trace guard merely
because the norm quotient equation holds.

`P` in the logarithm row is the same retained polynomial evaluation as in
the baseline. The final evaluation is affine in retained gate coordinates.
The U1 through U4 and V1 through V4 logarithms use the original implementation.
Fusing them does not improve the compiled count because the compiler already
removes their final product coordinates. The two shared denominator logarithms
U0 and V0 retain their final outputs and benefit from fusion.

## Why every fixed scale is nonzero

This is a new elementary deduction from the unchanged point-module
equations, not a new arithmetic assumption.

In either real embedding of K, put D=11-6*sqrt(2), using the corresponding
sign of sqrt(2). Both values of D are strictly positive since 121>72.
For each input halfpoint the equations give

    y²=x³-D*x,       2*y*m=3*x²-D,
    xDouble=m²-2*x.

They force y nonzero. Otherwise the curve equation gives x=0 or x²=D;
the slope equation would respectively give 0=-D or 0=2D.

The exact polynomial identity verified in `verify_identities.py` is

    4*y²*(m²-2*x) - (x²+D)²
      = (2*y*m-(3*x²-D))*(2*y*m+(3*x²-D))
        - 8*x*(y²-x³+D*x).

Consequently xDouble=(x²+D)²/(4*y²)>0 in both real embeddings. Its rational
component is their average, so it too is strictly positive. The nine fixed
scales are 1, the squares of four such rational components, and four values
(1+x1²)². All nine scales A are therefore strictly positive.

The retained delta inverse gives delta nonzero. Thus Ad=A*delta is nonzero
and Ad⁴*Ad is nonzero. The fused equation F*ep=Ad⁴*Ad forces both F and ep
nonzero. The deleted F inverse is recovered as 1/F. There is no new
denominator-zero branch.

## Maps between solutions

All unchanged named semantic values are preserved. Gate coordinates are
the normalized quadratic values specified by their existing gate records.
Their names or numerical ids can change when earlier coordinates disappear;
this is only enumeration. The base coordinates, including the input, are
unchanged.

From a baseline solution to a candidate solution, preserve the base
coordinates and all retained semantic values. Omit the deleted coordinates.
Evaluate the new gate records in their specified order. The old equations
imply each new equation by multiplication and cancellation of the retained
nonzero denominators. In particular ep=(Ad)^5/F, R=1/(ep*delta),
q1=ep/delta³, and nw=(w0²-2*w1²)/(2*w0) retain exactly their old values.

From a candidate solution to a baseline solution, reconstruct the deleted
semantic values as follows.

* For U0 and V0 set z=-x/y in K. Their unchanged finite-double or
  finite-difference construction forces y nonzero by the baseline source
  lemma at Brox lines 4311-4348. The equations y*log=-x*P force log=z*P.
* Set the deleted terminal fifth-power value to Ad⁴*Ad.
* Set each deleted F inverse to 1/F. Nonvanishing was proved above.
* Set each deleted ep inverse to R*delta. Indeed ep*R=di and
  delta*di=1 imply ep*(R*delta)=1.
* Set the deleted inverse-cube value to di²*di. The candidate equation
  delta*q1=ep*di² and delta nonzero imply q1=ep*di³.
* Set the deleted norm value to w0²-2*w1². The retained trace inverse and
  the fused quotient equation imply nw=norm*wi/2.

The scalar ratio equation xH*ratio=-yH*zS is equivalent to
zH*ratio=zS after substituting zH=-xH/yH. Both xH and yH are nonzero:
the candidate retains fH*xH=1, and the same inherited ordinate lemma applies.
This recovers the baseline scalar ratio without changing it.

Restore each deleted normalized quadratic coordinate using its original
definition; normalization only multiplies by a nonzero rational constant
and adds an affine term. Every baseline residual then vanishes. The maps
preserve all retained values and the input exactly. The polynomial in each
system is a sum of squares of nonzero rational multiples of its residuals,
so its rational zero set is exactly the simultaneous residual zero set.

The only imported nonvanishing result used for the new local-parameter
fusion is the same finite-point ordinate lemma already used by the deleted
baseline quotient. The new positivity argument for scales is fully given
above.

## Evidence and reproduction

`make_candidate.py` reads the frozen builder and writes `build_candidate.cjs`
plus `patch-certificate.json`. The certificate records each exact text
replacement and the baseline builder hash. Run the generated builder with
Node. Compile `raw-ir.json` using the frozen `compiler/compile_ir.py`.

`verify_identities.py` independently expands eight formal polynomial
identities over Q with a small standard-library implementation. It also
checks the frozen manifest hash, current coordinate census, degree bounds,
and the retained and deleted guard names. Its receipt is `identity-check.json`.
This test does not substitute sampled numerical evidence for the proof.

`checker-report.json` is the frozen independent JavaScript checker's receipt.
It checked 1,165 raw gate identities, all 1,143 compiler-certificate operations,
the coordinate map, the complete sum-of-squares polynomial, integer
coefficients, specialized support, and primitive content 1. Its source-domain
obligation list remains explicit. The written proof above discharges the new
obligations; the original source obligations remain inherited.

The changes compose with independent symmetric-evaluation and detector
polynomial-circuit changes provided those changes preserve the same semantic
values F, delta, ep, q1, w0, and w1. A different weight circuit should be
compared by actual combined census rather than summing overlapping savings.
