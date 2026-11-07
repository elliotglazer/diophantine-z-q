# Norm sharing experiment and elementary proof follow-up

7 November 2026. This pass found no improvement to the 900-variable
candidate. It records an exactly equivalent but larger-monomial experiment
and expands the elementary Lucas argument. All new prose and code are
AI-authored/self-reviewed, not independently human-refereed.

## Rejected scaled-norm circuit

The current detector uses

    N=(w0²-2*w1²)/(2*w0), q1=e/delta³, B=N²/(e*delta).

Since delta² is already available, consider instead

    J=w0*delta²,
    2*J*M=w0²-2*w1²,
    B*q1=M².

These equations give M=N/delta² and the same B. They replace the old
N, e*delta and B gates by J, M and B gates: three coordinates either way.
The w0 inverse and the defining relation delta³*q1=e remain in place.

There are no extra zero-denominator solutions. The inverse gives w0!=0.
Over Q, w0²-2*w1² cannot vanish when w0!=0. Thus the new norm equation
forces J and M nonzero, hence delta!=0. The B equation then forces q1!=0,
and delta³*q1=e forces e!=0. These are implications of the whole system,
not an assumption that gates must be evaluated before proving domains.
Conversely every old solution uniquely determines J,M,B. This establishes
the two-way source projection and all new denominator obligations.

| Circuit | Variables | Residuals | Monomials | Coefficient bits |
| --- | ---: | ---: | ---: | ---: |
| Current mixed weights | 900 | 857 | 51,252 | 3,247 |
| Scaled norm experiment | 900 | 857 | 54,357 | 3,247 |

The experiment is rejected: it adds **3,105 monomials** with no other
reported metric improvement. Multiplying the affine expression for w0
by the affine expression for delta² produces a denser quadratic residual;
its square is expensive. Algebraically similar gate counts do not imply
similar expanded quartic support.

Reproduce in a fresh directory:

```sh
python3 -B research/norm-sharing-20261107/explore.py --only 4 --out /tmp/scaled-norm
python3 -B research/norm-sharing-20261107/verify_norm.py /tmp/scaled-norm/precision40_quotients/parameter-source-ir.json
python3 -B research/norm-sharing-20261107/check_elementary.py
```

The generator runs the inherited pinned compiler and full algebraic
checker. The new checker separately verifies actual emitted norm gate
formulas and the exact Laurent identity for B. The input pin manifest
and verification report record the source and generated hashes.

## Eight weight gates are optimal in a larger, still restricted class

Allow pure powers e^j formed by quadratic monomial quotient gates,
but require j>=0 throughout. Require that pure-power gates depend only
on other pure powers, and that the only two q1-dependent gates are the
two outputs q12 and q40. The existing eight-gate circuit is optimal in
this class, even when the second output may reuse the first.

If there were at most seven gates, at most five could be pure-power gates.
Each such gate has exponent j=a+b-c with nonnegative available exponents;
the largest available exponent can at most double. Starting from e and 1,
all available pure powers have exponent at most 32.

The first q-dependent output must have q-exponent one. Its exponent in
e is a difference of two pure exponents, so cannot be 78. Therefore it
must be q12, with exponent 22. A second gate can either shift an available
q-dependent value by a difference of pure exponents (giving at most
22+32=54), or use three q-dependent factors. In the latter case its
possible exponents are -22,0,22,44, since only q1 and q12 are available.
None yields 78. This proves the lower bound of eight gates in this class.

check_elementary.py exhaustively enumerates the relaxed last-gate exponent
possibilities as a finite cross-check. The universal proof is the preceding
growth argument, not the finite check alone. This does not rule out seven
gates using negative pure exponents, additional q-dependent intermediates,
or interactions with the e/delta/norm equations.

## Elementary growth proof

LUCAS_BLACKBOARD.md gives a self-contained explanation of upstream's
Lucas growth lemma: norm-one solutions lie on a recurrence orbit,
and divisibility forces the orbit index to be large. It also exhibits
the small solutions that defeat the naive cubic replacement when the
divisibility condition is dropped. Merely substituting w=(s-2)z does
not lower the relevant weighted degree, because w can have size B².

This clarifies an elementary ingredient of the intuitive proof. It does
not remove the separate elliptic-curve, height and prime-pattern inputs.
No new arithmetic endpoint or PR metadata change is promoted by this pass.
