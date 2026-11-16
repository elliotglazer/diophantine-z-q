# Absorbing the root error into bottom norm pairs

All coordinates lie in Q. Write E = theta^2 - 2. Retain this equation and
the first-leaf equation

    R F - R - E^2 = 0.

If theta=a/b is in lowest terms with b positive and theta^2=2, then
a^2=2b^2 forces a even. Substituting a=2c forces b even too, contrary to
coprimality. Thus no rational square equals 2, and E is nonzero. The first-leaf equation gives
R(F-1) = E^2, so R is nonzero.

For every paired field test, the frozen q_compare4 module supplies a test
X = E B and another test T. B is an affine rational polynomial in retained
coordinates. Signs caused by field conjugation are included in B. The
q_batch41 bottom row has the exact form

    P N - X^2 - R T^2 = 0,

where P is the existing even contact power R^(2L), and N is the existing
normalized bottom norm coordinate. This method does not change N.

Introduce O = P/R and Q = B^2. The row is equivalent to

    O N - (F-1) Q - T^2 = 0.

Indeed, multiplying this row by R gives the old row after X = E B and
R(F-1) = E^2. Since R is nonzero, both directions hold. The checker does
not need to reprove P = R^(2L): it keeps every existing equation defining
P, and introduces R O - P = 0. When L = 1, it verifies a retained row
P - R^2 = 0 and reuses O = R without allocating O.

There is also an exact polynomial identity. Let h=R O-P,
g=R F-R-E^2, s=Q-B^2, and f=O N-F Q+Q-T^2. Then

    P N-E^2 B^2-R T^2 = -N h + Q g + E^2 s + R f.

For a low-order pair, h is the negative of the retained row P-R^2.
This identity proves both implications after the stated nonvanishing.

The new rows are quadratic:

    R O - P = 0,
    Q - B^2 = 0,
    O N - F Q + Q - T^2 = 0.

The last row has four monomials when all named quantities are coordinates.
The square row is quadratic because B is affine. The new coefficients are
1 and -1 apart from the inherited coefficients of B and its square. The
current frozen source uses B equal to a coordinate or its negative, so
all new coefficients have magnitude one. Final expanded coefficients
still require the ordinary complete sum-of-squares check.

The fresh odd-power coordinate need not cost a variable after ordinary
simplification. If the highest old even power P has the private definition
P-S^2=0, its old pair consumers have all been replaced. The new equation
R O-P=0 then permits ordinary constant-linear elimination of P, leaving
R O-S^2=0. Both rows stay quadratic. This is an existing elimination rule,
so the absorption event retains the even-power circuit for easier checking.

# Exact maps and complete outside-use conditions

Expand each old lifting definition and each old alias definition in an
acyclic order. Every definition has a nonzero rational constant coefficient
on its defined coordinate and no other occurrence of that coordinate.
The expansion of each old pair row must equal, up to a nonzero rational
constant,

    P N - E^2 B^2 - R T^2.

The event may delete a definition coordinate only when its full incidence
set lies among the changed pair rows and the deleted definition rows.
It cannot delete coordinate zero. Every coordinate used by a new row or
by a retained proof equation must be retained. The producer finds the
largest subset with this property by repeatedly retaining coordinates
with outside consumers. The checker verifies the final incidence claim
directly and does not trust this search.

The forward map preserves all retained old coordinates, drops the deleted
definition coordinates, and sets each fresh O to P/R and each fresh Q to
B^2. All new rows hold by the identity above. Reusing a Q for several
bases is permitted only when their squares are identical polynomials.

The reverse map preserves every retained coordinate and reconstructs each
deleted old coordinate through its old acyclic rational-polynomial
definition. Retained definition rows continue to hold. The transformed
pair equation, the Q definition, and the O definition yield every old
pair row. All rows outside the event remain unchanged by the complete
incidence check. The two maps preserve input coordinate zero, and are
inverse after the uniquely determined fresh coordinates are included.

Upper norm-tree nodes, the final norm value, the parity argument, and every
parity witness remain exactly unchanged. This proof needs no square-class
invariance claim about the parity predicate and no external arithmetic
theorem beyond rational nonsquareness of 2.

# Implementation and integration

`absorb_batch_error.py` matches the pinned source module rows and flattened
coordinate maps. It is intended for the structured norm-base artifact,
before generic elimination or global field scaling. A source mismatch or
changed required identity causes failure. The original lift may already
replace a repeated product E B by an earlier alias Y. The producer checks
the frozen X=E B row, then expands the current X=Y alias chain in a checked
acyclic order and requires its exact value to equal E B. It writes a single `batch_absorb`
event and can export a complete candidate. It never changes the source
hash. For a revised precision source, the algebraic checker is unchanged;
the source-specific producer hash gate and module files must be supplied
by that separately proved source conversion. No revised source is
accepted by merely changing the hash string.

`check_batch_absorb.py` contains independent exact polynomial arithmetic.
Add its function to the existing checker dispatch:

    elif kind == 'batch_absorb':
        expected, nextvar = batch_absorb_expected(rows, d, nextvar, incidence)

Then use the existing patch equality, quadratic degree, variable bound,
source hash, and final full expansion checks. The root obstruction is a
rational-domain rule. It is not valid over Q(sqrt(2)).

`test_batch_absorb.py` exercises high and low denominators, signed bases,
exact sample solutions, and malformed proof rows, aliases, lifts,
incidence claims, duplicate records, fresh coordinates, and square bases.
Root owns test execution and full candidate verification.

# Limits of the search

This rewrite applies to q_batch41 because its first test is E and each
subsequent left leaf is E times a field coordinate. q_height_batch has no
such E-paired layout, so the producer leaves it unchanged.

Arbitrary leaf reordering changes the exact norm value. The parity
predicate in the pinned source is not supplied with a general exact
square-class invariance theorem, so leaf reordering was not accepted as
an exact projection-preserving conversion. Monomial R-rescaling of
ordinary internal norm nodes still leaves an odd power of R on one
square term. No separate internal-node saving is claimed.
