# Independent static review of batch absorption

Reviewed by the unit-scale search agent on 2026-11-05. This review covers the
mathematics and code listed below. No computation or test was run for this
review, and no candidate variable count or full certificate is certified here.

Conclusion: I found no soundness bug in `batch_absorb_expected`, its stated
rational equivalence proof, or the producer's proposed event construction.
The rule is suitable for integration with the existing complete patch checker
and full certificate replay. Runtime tests and the combined candidate's final
expansion remain necessary acceptance steps.

Reviewed SHA256 values:

| File | SHA256 |
| --- | --- |
| `PROOF.md` | `46e1175ac239e2627b1312c5716310d8e316f72fec37b6eae96a1bf3c0bc9a2a` |
| `absorb_batch_error.py` | `ad25d50d21e7ad122eb3e34cd471bf032396b3185eb6ff2d883ed63aa7ca8795` |
| `check_batch_absorb.py` | `f3d14675eb656849c305f0437ca8b733bb3cb0512b92b68e5892f07af638509c` |
| `test_batch_absorb.py` | `26738913874d273d07030066a285d2f49739c4e2ca62bc0298a137ef11e8380e` |

## Nonvanishing and the polynomial identity

The checker validates the exact equations E-theta^2+2=0 and
R F-R-E^2=0 up to multiplication by a nonzero rational constant. The proof
that E is nonzero over Q is valid: a reduced fraction a/b with square two
would make both a and b even. Consequently R(F-1)=E^2 implies R is nonzero.
No premise that R, E, or a field coordinate is nonzero is inferred from a name.

The identity in `PROOF.md` has the correct signs. With
h=R O-P, g=R F-R-E^2, s=Q-B^2, and
f=O N-F Q+Q-T^2, direct symbolic collection gives

    -N h + Q g + E^2 s + R f = P N-E^2 B^2-R T^2.

Thus the old expanded pair equation and the new pair equation are equivalent
when the retained proof equations and the new definitions hold, because R
is nonzero. Neither P nor B needs to be nonzero. The checker does not need
P=R^(2L); its exact definition of O=P/R is sufficient. In the low-order
case, the retained row P-R^2=0 makes the reused O=R valid.

## Definitions and partial deletion

The checker requires distinct definition rows and targets, nonzero constant
linear coefficients on each target, no remaining occurrence of that target
in its right-hand side, and an acyclic order. Therefore each definition
specifies a unique rational-polynomial value. Expanding all those definitions
in an old pair is valid on every assignment satisfying the definition rows.

Deleting only part of the definition list is sound. Let D be the set of
removed targets and C the changed rows. For every d in D, the checker requires
the complete incidence of d to lie in C. A retained definition row is outside
C: the definition indices are distinct, pair rows are disjoint from all
definition indices, and only rows defining targets in D are deleted. Hence
no retained definition row can use a removed target. Its equation continues
to hold unchanged in the new system.

For the reverse map, traverse the supplied acyclic definition order. Keep a
retained target's given value and reconstruct a deleted target from its old
right-hand side. The preceding observation ensures that retaining a target
cannot leave an unsatisfied definition. Induction then proves that every
target, retained or reconstructed, has its fully expanded value. The checked
expanded pair identities therefore imply every original pair equation.

The producer's fixed-point removal search implements the same condition:
once a definition is retained because of an outside use, its dependencies
also become outside uses unless already retained. Its result is checked
directly by the independent checker; the fixed-point search is not trusted.

## Fresh coordinates and complete maps

Fresh identifiers are consecutive and start at the pre-event allocation
limit. Every fresh coordinate has exactly one explicit row. An odd-power
coordinate is uniquely P/R; a square coordinate is uniquely B^2. This is an
equation defining a square value, so it imposes no rational square-root
existence condition. Reusing a square coordinate checks exact equality of
the two square polynomials, which correctly permits signed bases.

The forward map keeps every retained coordinate, discards deleted definition
targets, and assigns the fresh coordinates as above. The reverse map keeps
retained coordinates, discards fresh coordinates, and reconstructs deleted
targets in acyclic order. These maps are mutually inverse on the relevant
solution sets. Coordinate zero cannot be a deleted target, and it is not
changed by either map.

The checker excludes every old pair argument and base coordinate from the
whole definition target set, not only from the deleted subset. It also checks
that no new row mentions any removed target. These conditions are stronger
than needed in some cases and do not create a soundness gap.

## Retained proof rows and patch coverage

The root and first-leaf proof rows are disjoint from all definition and pair
rows. They are excluded from the final expected patch set. Every low-power
proof row is separately required to be outside the changed set. These rows
therefore remain available in both directions of the argument.

The returned expected patch set consists of exactly the pair replacements,
the deleted definition rows, and one appended row per fresh coordinate.
Every returned row is checked to be quadratic and free of removed targets.
The complete supplied patch-key equality and normalized polynomial equality
are essential caller requirements. The standalone command implements these
checks. The existing shared checker's `patch` function also supplies them,
along with variable bounds and incidence updates.

At review time, the shared `verify_certificate.py` did not yet contain the
`batch_absorb` dispatch. The integration must call
`batch_absorb_expected(rows, d, nextvar, incidence)`, retain its returned
allocation count, and pass its expected rows to the existing patch function.
This is pending integration work, not a defect in the reviewed rule.

## Producer and composition

The producer validates the source hash, exact root and first-leaf equations,
the actual alias and lifted-gate rows, and the source bottom-pair identities.
The checker independently verifies the expansion of each actual old pair,
so equivalence does not depend on trusting module labels or allocation maps.
The producer preserves N, upper norm-tree nodes, and parity arguments. No
unproved square-class invariance or leaf permutation is used.

Composition with ratio, logarithm, chart, or parity replacements is valid
when their certificates are replayed in order and this event is generated
against the actual intermediate rows. The source-specific producer may
reject a reordered pipeline whose required rows have changed; that is a
compatibility failure, not permission to bypass a row check. Existing
row identities, complete incidence, and full patch verification must remain
enabled for the combined candidate.

## Test coverage to complete

The supplied tests cover basic high and low cases, signed bases, one rational
sample, malformed equations, outside uses, and fresh-coordinate mistakes.
They do not yet directly exercise a valid partially retained definition
chain or the full caller's missing/extra-patch rejection. Add those cases
before treating the integration as tested. A useful partial case retains
one alias because of a new outside consumer while deleting a dependent
private lift; the reverse-map induction above explains its expected result.
Also reject attempts to delete a prerequisite still used by a retained
definition and attempts to include a retained proof row among changed rows.

These are coverage gaps, not observed acceptance of an invalid event.
