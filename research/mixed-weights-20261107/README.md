# Mixed rational weights: 924 variables, or 900 with direct targets

Research checkpoint, 7 November 2026. The new circuit change is an exact
rational reparameterization on the already established detector domain.
Its proof below is AI-authored and self-reviewed; no independent human
mathematical review is claimed. The direct-target variant additionally
inherits the arithmetic review obligations in
`../overnight-20261106/DIRECT_TARGETS.md`.

| Variant | Variables including input | Residuals | Monomials | Maximum coefficient bits |
| --- | ---: | ---: | ---: | ---: |
| Frozen doubled-target package | 933 | 890 | 51,907 | 3,247 |
| Mixed weights, doubled targets | 924 | 881 | 51,880 | 3,247 |
| Previous direct-target candidate | 909 | 866 | 51,279 | 3,247 |
| Mixed weights, direct targets | 900 | 857 | 51,252 | 3,247 |

Both new outputs are primitive quartics with ordinary integer coefficients.
The 933 artifacts are unchanged. The new outputs are reproducible variants,
not replacements for the archived artifacts or a claim that the complete
number-theoretic argument has been independently certified.

## An eight-gate circuit

Write e for the existing nonzero weight and q for the existing q1.
The required outputs are q12=q*e^22 and q40=q*e^78.
Introduce eight coordinates using only quadratic residuals:

    a=e², b=a², c=b², d=c²,
    a*f=d², g=f²,
    c*q12=q*f,
    b*q40=q12*g.

Thus a,b,c,d have exponents 2,4,8,16; f=e^30 and g=e^60.
The output exponents are 30-8=22 and 22+60-4=78.
This uses one fewer coordinate and residual in each of nine detectors.
The compiler confirms a total saving of nine variables and 27 monomials.

The previous limited lower bound remains correct: it covered positive
powers formed only by multiplication, followed by two output quotients.
This circuit instead uses an intermediate quotient and reuses q12.
No optimality claim is made for the eight-gate circuit.

## Every new denominator is justified

The only new division denominators are e², e⁸ and e⁴. The construction
retains the w0 inverse, the relation

    2*w0*N = w0²-2*w1²,

and the relation

    B*(e*delta)=N².

All these coordinates are rational. If N=0, then w0²=2*w1².
If w1=0 this contradicts w0!=0; otherwise it would make sqrt(2)
rational. Hence N!=0, so B*(e*delta)!=0 and in particular e!=0.
This deduction is a property of every solution of the entire polynomial
system. It does not assume that quotient gates are executed in order.
There is therefore no circular appeal to the new quotient outputs.

For every old solution, the displayed powers and outputs uniquely extend
it to a new solution. For every new solution, nonvanishing permits division
in the displayed equations, forcing exactly the old q12 and q40 values.
The old intermediate e24,e40,e80 can then be reconstructed uniquely.
All other source equations are unchanged. Thus the two systems have
identical projections onto their shared coordinates in both directions.

No new local estimate, prime-pattern theorem, height bound, target shift,
or positivity assertion is needed for the 933-to-924 transformation.
Combining it with shift one gives 900 variables, but does not remove
the separate arithmetic obligations of that shift.

## Reproduce and check

From the repository root, choose fresh output directories:

```sh
python3 -B research/mixed-weights-20261107/explore.py --target-shift 2 --only 4 --out /tmp/mixed-924
python3 -B research/mixed-weights-20261107/explore.py --target-shift 1 --only 4 --out /tmp/mixed-900
python3 -B research/mixed-weights-20261107/verify_run.py /tmp/mixed-924 --target-shift 2
python3 -B research/mixed-weights-20261107/verify_run.py /tmp/mixed-900 --target-shift 1
```

The generator checks inherited pinned inputs, compiles the source, checks
the elimination certificates and full sum-of-squares expansion, and emits
the complete ordinary polynomial. Its inherited output subdirectory is
named `precision40_quotients` for both variants; the target-shift flag and
recorded builder and polynomial hashes distinguish them.

The verification wrapper additionally checks the constant-chain projection,
the arithmetic budgets, all ten emitted logarithm polynomials, and the
actual emitted weight gates in each detector. The weight checker evaluates
Laurent polynomials in independent symbols e,q1, and inspects every
encountered denominator; it does not merely check a handwritten exponent
chain. The full unchanged upstream checker also runs again against the
ordinary polynomial export.

Ordinary polynomial hashes:

- 924: `bff480cc9d5984716cba5e34529dbdd5a1373256acb6452a20a1bf82dab4129b`
- 900: `444f6bee0839d9df052fec4764458245c8b5d81d460c03ecb022c808c4410bad`

RESULTS.json and VERIFICATION.json record both runs. INPUTS.json pins
the additional wrapper and verification dependencies. The underlying
manuscript and compiler pins remain those in
`../v6-comparison/INPUTS.json`, with the existing source relocation map.

## Intuitive explanation and proof map

This improvement changes how the same numbers are computed, not what the
equations assert. Once a quantity is known to be nonzero, a quadratic
equation such as e²*f=e32 can compute e30 as cheaply as a multiplication.
Using that freedom avoids materializing both e40 and e80. The second
output also reuses information already present in the first.

The arithmetic architecture is still described in
`../overnight-20261106/INTUITIVE_PROOF.md`; its two height contradictions
are made precise in `../overnight-20261107/COMPARISON_LEMMA.md`.
The present denominator proof is elementary. The elliptic-curve integer
labels, contact-to-height bound and common-witness prime construction
remain deep inherited inputs, with no new independent certification here.
