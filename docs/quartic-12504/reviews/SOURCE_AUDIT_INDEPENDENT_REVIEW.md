# Independent review of the source auditor

Status: PASS for the repaired source auditor and mutation harness on static
review. The author addressed the identified timeout, resource-limit, and
test-coverage issues. No blocking issue remains in the reviewed versions.
Execution of the three intended source variants remains pending. No source
generator or checker was executed locally for this review.

## Final reviewed files

| File | SHA256 |
|---|---|
| check_source.py | 495ca32737687fca335704c6bdbabacf8f20a7698839aa680639e8e1b60a948f |
| test_source.py | f6e402489872a7418edd17c7c78a582334df88e954987abe14af13a95b022656 |

The verdict applies to these hashes. It covers plain 64/64, compressed
64/64, and compressed 64/16 at the static level. A successful remote run
must still establish that legitimate expansions fit the resource bounds
and that every malformed-case test executes to the expected result.

## Initial reviewed files

| File | SHA256 |
|---|---|
| check_source.py | ea59490498aa23cc5d26541d2a9bad3934a1972151947564acc9ce295e04a0a4 |
| test_source.py | 605769c0ff878d13d64b86986221ca7db6d704afd14bb4517c4bebfec294e04d |

These are the pre-repair versions. The review covers the plain 64/64,
compressed 64/64, and compressed 64/16 variants requested for wave 13.
The code also handles the stated 52 variants, but they are not needed for
that run. Approval of the changed arithmetic source remains separate.

## Concrete findings sent to the author

1. The initial test harness catches every AssertionError in must_reject.
   The checker reports its elapsed-time limit through AssertionError too.
   Once the shared deadline expires, subsequent invalid cases can therefore
   be counted as rejected solely because they timed out. This can produce
   a false PASS mutation receipt. Resource/deadline failures must propagate
   out of the harness rather than count as semantic rejections.
2. The initial term-count limits do not bound monomial degree before tuple
   concatenation in mul. A short sequence of repeated squarings can create
   exponentially long monomials with only one term. Module also constructs
   range(free) before imposing a small bound on free. Explicit allocation,
   degree, and coefficient-size limits should raise the same nonsemantic
   resource failure. The reviewed intended expansions fit small bounds:
   the norm powers reach degree 128, and the reciprocal G expansions are
   much smaller.
3. The initial mutations cover many altered and omitted equations but do
   not exercise extra core rows, extra calls, external/forward dependencies,
   or corrupted flattened residuals and coordinate mappings. Add those
   cases so the receipt covers the principal risks named in this review.

The first finding blocks relying on an initial-version mutation PASS receipt. The
second concerns bounded execution on malformed inputs, not a discovered
false acceptance of a different mathematical source. The third is a test
coverage gap; the corresponding static checks appear correct.

## Repair review

The revised checker uses CheckerResourceError, a RuntimeError distinct from
AssertionError, for time and resource bounds. must_reject explicitly
re-raises it, checks the deadline before a case, and the harness checks the
deadline again before writing PASS. Five separate resource regressions
require propagation for an expired deadline, oversized free allocation,
oversized product degree, oversized coefficient, and normalization
denominator growth. Those regressions do not count as semantic rejections.

The checker now bounds free/local/shared allocations before constructing
their environments, bounds monomial degree before concatenation, bounds
addition/product term counts, and checks coefficient arithmetic before
large numerator or denominator products. Normalization bounds its running
common denominator and resulting integers. It also bounds aggregate
expanded environments, file hashing, residual line/stream sizes, and
raw/gzip comparison. These checks preserve exact arithmetic within their
limits and fail inconclusively when exceeded.

The new mutations include an extra coherently logged core constraint, an
unlogged residual, an extra call, undeclared/forward/nonlinear-self
arithmetic dependencies, missing/extra/corrupted flattened rows, a corrupted
shared-coordinate mapping, and a corrupted call-argument mapping. They
exercise the full independent flattening pass on temporary files. The
raw/gzip-disagreement case is also covered. A reconstruction-map digest
regression verifies that changing an allocation entry changes the recorded
canonical-map digest.

I re-read these changes and found the tests target actual invalid cases.
The new exception separation prevents the previously identified false
mutation PASS. No producer import or replacement of the independent
mathematical formulas was introduced by the repairs.

## Labels do not replace equation checking

Module treats only a precisely labelled arithmetic allocation followed by
its arithmetic row as a removable definition. Its target must be the next
local coordinate. The row must have a nonzero rational constant coefficient
on that target, must not otherwise contain it, and must be quadratic.
The right side can use only the current environment, which contains free
inputs and already allocated/expanded coordinates. Thus a definition is a
total polynomial assignment, not a new constraint on an input and not a
rational division by a variable.

Core labels select coordinate identities for the independent formulas, but
every resulting core equation is subsequently compared after full exact
expansion, up to a nonzero rational scalar. The set of nonarithmetic equation
labels and each label's multiplicity must match exactly. Relabelling a
constraint as arithmetic cannot hide it unless it actually becomes a valid
total definition of a fresh coordinate, which preserves existential
projection. Relabelling a needed core coordinate loses its required label
or violates the disjoint complete core/definition coverage check.

Extra total arithmetic definitions may pass if they do not change any
checked consumer. That is mathematically valid and only adds existential
witnesses. An extra core constraint, unmatched core witness, or unlogged
row cannot pass. No requirement of circuit minimality is implied.

## External variables and symbolic expansion

Free input identities are fixed to indices 0 through 30 in comparison and
0 through 41 in the batch. Local allocations begin exactly at free and
advance without duplication. Row decoding rejects out-of-range and
unpermitted negative indices. Arithmetic right sides use only the already
defined environment; no future local or external symbol can enter by
label alone. Core variables remain independent symbols in that environment.

The independent expected polynomials use those same checked core symbols
and the fixed input positions. All actual core rows and all 42 ordered
batch arguments are expanded and compared to them. The final union of core
coordinates and definition targets must cover every local coordinate.
I found no variable-capture or hidden-consumer path in these checks.

## Complete comparison and batch constraints

check_compare independently writes all ordinary or compressed primary
chart equations, all six field equations at each subtraction, each scalar
distinct-abscissa inverse, and the plain logarithm inverse or compressed
ratio interfaces. G coefficients come from the binomial convolution rather
than the producer recurrence. The five numerator/denominator precisions
match the intended high/high-or-label order.

The formal tests, primary ratios, and alternate ratios are reconstructed
independently, including both rational components of each field test.
Their 42-element outgoing call includes the contact factor at position zero
and the root-error test immediately after it. Exactly one call to q_batch41
is permitted. The ten rational difference-parameter coordinates are selected
as core variables and constrained by the expected output equations.

check_batch reconstructs the leaf grouping from the rational orders, checks
the nonzero-contact inverse and constant first leaf, every bottom norm,
every upper norm, the final square, and the parity argument. Every row must
be consumed by this comparison or be a total shared-power definition.
The outgoing call dictionary must equal the single expected q_primeparity
call. Shared-power definitions must expand to monic powers of the contact
input, and their actual consumers must have the required exponents.

## Frozen modules and complete flattening

All six original module files are pinned by observed byte hashes. The
height batch and parity source must equal their frozen objects. The root
object must also equal the frozen object except for explicit precision and
anchor metadata. The anchor permits only the documented 24-to-26 change
for high=52, including replacement of the shared index -25 by -27.
This protects the fixed generator, all root charts and their parameters,
all 41 contacts/calls, the scalar order 48, and the original root equations.

flatten_and_check rebuilds the shared squaring chain independently, begins
locals after its allocated coordinates, and visits the root with input
coordinate zero. Negative shared references map to their fixed positive
coordinates; module free inputs map through the current call arguments;
locals map through a fresh contiguous interval. The stack rejects cycles.
The actual call graph has already been fixed by module checks, and its final
visit counts must be exactly 1 root, 1 anchor, 1 height batch, 41 comparisons,
41 comparison batches, and 42 parity instances.

Every generated flattened row is compared exactly and in order to the
provided residual stream. Missing and trailing rows are rejected. Counts,
degree, module totals, shared data, and the polynomial recipe must match
the independently derived objects. I found no off-by-one or free/local
capture error in mapvar or the allocation recurrence.

The optional --write-map output is a newly reconstructed map. The revised
report includes the SHA256 of the same canonical bytes written by that
option. The checker does not validate a separately supplied
construction-certificate.json. Later integration must use the reconstructed,
digest-bound map rather than assume an unrelated existing map was checked.

If both residuals.jsonl and residuals.jsonl.gz exist, the repaired checker
requires their complete decompressed byte streams to agree and records
both file hashes. Thus the initial ambiguity about an unchecked second
encoding has been removed.

## Scope of a passing result

A successful repaired execution would establish exact construction of the
intended proposed source, including full flattened coefficients. It would
not prove the all-prime logarithm estimate, global nonvanishing theorem,
compressed-chart existence theorem, arithmetic source equivalence, a fresh
quadratic lift, or the final coefficient bound. The checker correctly lists
these exclusions and keeps source_pin_authorized false.
