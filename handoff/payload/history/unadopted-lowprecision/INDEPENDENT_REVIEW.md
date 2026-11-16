# Independent review of the low-precision circuit packet

Reviewed 2026-11-05. Scope: static mathematical and code review of `PROOF.md`,
`lowprecision_kernel.py`, `probe_lowprecision.py` and `check_lowprecision.py`.
No producer, test, expansion or other substantive computation was run by this
reviewer. Root owns the pending wave13 execution. Only this review file was
written.

No finite-identity or checker-soundness defect was found. The supplied
circuits compute the advertised polynomials, all required divisions are by
fixed nonzero rational constants, and the independent checker validates the
actual quadratic rows and both output coordinates. Its packet check closes
the empty/subset-index problem found in the earlier reciprocal probe.

This is not a new-source acceptance. Actual run results, complete source
binding, the new source's arithmetic proof, its lift and the full final
coefficient expansion remain separate.

## Reviewed content pins

| File | SHA256 |
| --- | --- |
| `PROOF.md` | `6b5e6e6c42e9cc3e6f8c3e0863c42ec97a165a692d5ce13f71a8aed709169592` |
| `lowprecision_kernel.py` | `66854ff3ee24d8dd6f4b3b54fa5ca627d87b5d0da09cafa35e3d05d47d0d5c31` |
| `probe_lowprecision.py` | `8a6cecd95f140081647ca8252972300e0c801d9863d5bcb4ee4b4bb940ef51c6` |
| `check_lowprecision.py` | `7ac5156871cfc1bc797b1135e58d9e3e7e08af2a187eca50dc1eb83f481dd549` |

The producer requires the already reviewed original builder digest
`c7ef798894a106e3c6b02816583be2b6e966e4e701f73ee670c9a0de52a70912` and explicitly
sets `D=(11,-6)`. It writes an isolated packet rather than changing that
builder or any arithmetic source pin.

## Exact polynomial formulas

The target is `G_e(D f^2)`, where `e` is 12, 40, 44 or 48 and the number of
coefficients is respectively 3, 10, 11 or 12. The recurrence starts with
`a_0=1`, `a_1=-2/5` and multiplies by `(4j-5)/(4j+1)` for `j>=2`.
Every coefficient used as a scaling pivot is nonzero. The independent
convolution formula in the checker produces the coefficients of
`sqrt(1-w) * sum binom(2j,j)w^j/(4^j(4j+1))`, as required.

For the three-term case, only `w=D f^2` is bound; `1+a_1 w+a_2 w^2` is a
quadratic expression in that pair. A bound output adds two scalar
definitions. There is no hidden separate `w^2` allocation.

For the ten-term block circuit, the definition of the unscaled `U` contains
powers 0 through 6 with coefficients `a_3` through `a_9`. Multiplying it by
`w^3` and adding the first three terms gives powers 0 through 9 exactly.
For the eleven- and twelve-term block circuits, the additional `w^6` term
extends the unscaled `U` through powers 7 and 8; the final multiplication
gives powers 10 and 11. The absent twelfth coefficient in the eleven-term
case is omitted, not filled by a nonzero term.

In each block circuit the actual bound pair is `U=(s/a_k)U_unscaled` and
the output uses `(a_k/s)w^3 U`. Both factors are fixed nonzero rational
numbers. They cancel identically and impose no nonvanishing condition on
an input or intermediate value.

For `powers45`, the allocated logical powers are 1, 2, 4 and 5. The missing
powers are supplied by the quadratic products `w*w2`, `w2*w4`, `w2*w5`,
`w4^2`, `w4*w5`, and `w5^2`, with the last one unused at precision 40.
For `powers56`, powers 1, 2, 3, 5 and 6 are allocated; missing powers 4,
7, 8, 9, 10 and 11 can be written as 2+2, 2+5, 3+5, 3+6, 5+5 and 5+6.
The producer's pair-selection rule makes these choices and has no gap.

The scaled power targets equal `s_j w^j`, while the entries retained in
the logical-power dictionary are those targets divided by `s_j`. Thus
subsequent products operate on the correct unscaled powers. Unit,
coefficient and reciprocal-denominator normalizations are all defined;
the relevant `a_j` and integer denominators are nonzero. The extra final
power scale also cancels. These maps are invertible rational coordinate
rescalings within the isolated circuit.

## Degree and target counts

The first `w` definition is quadratic in the supplied input pair. Every
later multiplication uses bound pairs or linear expressions in such pairs.
All block definitions and all direct outputs are therefore quadratic in
the allocated coordinates, despite their higher degrees after substitution
into `f`. Binding the output preserves quadratic degree.

The producer adds four distinct fresh coordinates for a generic field
product `P*Q`, and two integer rows for `P*Q=G`. This covers the direct
output denominators and their cross terms in a real use of the output.
It does not multiply a quadratic direct output by another variable, which
would generally be cubic. A plain logarithm `z*G` needs a bound output or
a separately proved fusion.

The structural rational target counts agree between the proof, producer
and independent contract:

| Profile | Direct output | Bound output |
| --- | --- | --- |
| 12 | 2 | 4 |
| 40, either scheme | 8 | 10 |
| 44, power scheme | 8 | 10 |
| 44, block scheme | 10 | 12 |
| 48, either scheme | 10 | 12 |

These counts exclude the two supplied `f` coordinates and the four generic
product coordinates. They are not claimed final source variable counts.
The contract has two precision-12 profiles and fourteen profiles for each
of 40, 44 and 48, giving exactly 44.

## Independent checker

The checker imports neither the producer, its kernel nor the archive
builder. It has its own coefficient formula and polynomial operations.
Instead of replaying the block or power construction, it substitutes every
definition into the two original input variables and compares both outputs
with repeated field multiplication of `D f^2`. This is an independent
identity check for arbitrary rational input pairs; no curve relation,
sample evaluation or nonvanishing assumption is used.

Targets must be the prescribed contiguous fresh integer coordinates.
Every defining row must be quadratic, have a nonzero constant coefficient
of its own target, use no future coordinate, and contain no other occurrence
of that target. Thus the rows define all targets uniquely over the
rationals, in order, for every input. A quadratic occurrence of the target
cannot masquerade as a constant pivot. Duplicate monomials, negative or
out-of-range coordinates, zero coefficients and invalid rational
denominators are rejected.

Outputs must be quadratic expressions in existing coordinates. For bound
profiles they must be exactly the last two target variables, in order.
The four fusion coordinates must be fresh, distinct and exactly the
expected range. The two supplied fusion rows must equal the independently
constructed real and imaginary equations for `P*Q-G=0`, up to nonzero
rational row scaling. The normalized comparison does not discard an extra
constraint or permit a missing component.

The two expansions use the actual supplied integer rows, first the
definitions and then the definitions plus fusion equations. They collect
all monomials in the sums of squares before taking the maximum absolute
coefficient. Since each input row has degree at most two, these expansions
have degree at most four. Their reported coefficients therefore include
the effects of normalization and overlap within the isolated block.

The checker refuses execution under `python -O`, so its assertions cannot
silently disappear in that mode.

## Packet completeness and negative tests

The independent contract fixes all 44 filenames, parameters and target
counts. Packet validation requires exactly that number of entries, unique
known names, matching target counts and SHA256 digests of the bytes that
are subsequently decoded. It also requires equality with the complete
expected filename set. The main routine reads only those fixed filenames,
not paths taken from the untrusted index. Empty or subset packets, duplicate
cases and path substitutions cannot pass.

Every valid circuit is followed by fifteen negative tests. They exercise
wrong precision/coefficients, overwritten inputs, absent or changed
definitions, duplicate monomials, cubic rows, future dependencies, wrong
or reversed outputs, invalid denominator or coordinate, and missing or
changed fusion data. Seven packet mutations exercise empty, missing,
duplicate and unknown cases, wrong digests/counts and changed bytes.
The edits actually violate the corresponding checked conditions for these
profiles. Static review does not replace executing the tests.

## Scope limits

The strings `scheme`, `normalization` and `hscale` are matched to their
expected profile metadata, but the checker does not independently
reconstruct the particular intermediate rescaling advertised by a label.
An alternative circuit of the same target count, relabeled and rehashed,
can pass if its actual rows satisfy every structural and output check.
This is sound for the stated identity and coefficient claims. It is not
an independent proof that every named search profile uses its advertised
internal layout. The producer's correspondence with those layouts was
checked by source reading in this review.

An overall packet `PASS` means that all finite identities and rejection
tests passed. It does not mean that every profile meets `2^80`. Each actual
expansion reports its strict bound separately; the best-profile selection
only considers a passing `with_generic_field_product` bound and may return
no eligible profile at a precision. This distinction is explicit in the
proof and should remain explicit when reporting wave13.

The generic product expansion is stronger than an internal-only circuit
bound, but it is still isolated. Actual source consumers may share product
coordinates, identify them with existing coordinates, or undergo later
substitutions. Complete source binding and final expansion must include
those effects. No arithmetic source, inverse deletion or compressed chart
is accepted solely from this packet.
