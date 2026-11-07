# Research checkpoint — 7 November 2026

## Repository state

Upstream main was checked again through GitHub and remains
`5856286a57fba19574a40704571ee70e79738281`. The branch already contains
the Version 8 integration from the previous pass; there is nothing new
to integrate. Starting fork head was
`772c4adf4a05e21255e4c1784e08e917fda4c68a`. The working tree was clean.
CONTRIBUTING.md was read; no AGENTS.md was found in this checkout.

## Actual progress

COMPARISON_LEMMA.md extracts an exact, parameterized version of both
height contradictions, including the additive constants. It identifies
strict precision thresholds and explains why simply lowering 40 to 36
or 12 to 8 fails with the present exponent 19. It also proves a limited
optimality result: seven power gates plus two quotient outputs is minimal
within the existing positive-power detector architecture. It does not
claim a global lower bound on rational circuits.

The exact numerical specializations and power identities pass
check_bounds.py. A fresh generation of the 909 candidate, including the
unchanged compiler, elimination certificate checker and full quartic
expansion comparison, reproduces the previous polynomial hash:

    326a23b5af8064915013411f24af39e4507c41431c6b783d5a6cae488695b93b

All ten separately expanded logarithm identities pass again. Counts
remain 909 variables, 866 residuals, 51,279 monomials, maximum coefficient
length 3,247 bits, degree four and primitive content one. No new smaller
polynomial was found in this pass. VERIFICATION.json records this replay.

## Fresh direct-target review

Inspection of build_source.cjs shows that the target object `four` is
consumed only by the five-element R array passed to the guarded difference
construction. The wrapper removes target doublings, not the point charts
or difference guards. At a completeness witness, Ui=h*ni*P* and Qi=ni*P*.
Since ni is nonzero and P* has infinite order, equality of their abscissae
is equivalent to h=1 or h=-1. The same assertion holds for H and P*.
Thus h0 a positive multiple of 64 avoids every new difference pole.
The inherited nonzero-logarithm lemma handles the remaining logarithm
denominators, including the changed differences.

The soundness subtraction is an exact identity over any local ring where
the stated congruences are established; it introduces no division by h
or h-1 after those congruences. At least one of these consecutive integers
is a unit at every prime. Integrality propagation still depends on the
inherited cross-test and relative-error lemma, not just this identity.

The finite-group argument uses |2E(Fp)|=|E(Fp)|/4, because all four
two-torsion points are rational at the selected good odd split primes.
With the stated prime-order properties, dividing both orders by four
gives coprime opposite-side moduli. The primary modulus has 2-adic
valuation four, the opposite modulus is odd, and odd factors of L are
avoided. Therefore the only overlap with L requires 16|h0. These checks
support the shift-one argument. They do not independently establish the
simultaneous-prime theorem or the original point-chart characterization.

This was another AI self-review, not an independent mathematical review.
The 909 candidate remains separately labeled; the frozen 933 artifacts
and PR metadata are unchanged. Full generated artifacts are reproducible
by the existing wrapper but are not newly packaged in this checkpoint.

## Failed approaches and next best directions

Do not search again for six positive-power multiplications followed by
the same two output quotients: the exponent bound rules this out.
Do not interpret that as ruling out mixed q1/e intermediate gates,
intermediate quotients, or sharing across the detector residuals.

The next computational direction is a search over such mixed rational
circuits, retaining the norm-derived e!=0 domain proof. The next
conceptual direction is a lower-degree growth relation with controlled
auxiliary heights, or a sharper contact-to-height exponent below 18.
The former must preserve exponential growth and divisible completeness;
the latter needs arithmetic beyond a constant optimization.

For the intuitive proof, use the earlier INTUITIVE_PROOF.md together
with the new comparison lemma. The blackboard argument is now explicit
at both growth contradictions, but the elliptic group calculation,
height theorem and prime-pattern completeness input remain indispensable
to this architecture and have not received independent human review here.

No upstream merge, PR comment, or external message was sent. This log
records one completed research pass, not continuous execution between runs.
