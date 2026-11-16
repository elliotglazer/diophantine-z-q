# Independent reciprocal compiler review

Verdict: mathematical and static compiler review PASS for the pinned files
below. I found no blocking implementation defect in the new chart, ratio,
subtraction, parameter-selection, or source-order code. This is not acceptance
of a new source pin or of a generated quartic. The independent check of the
complete generated modules, flattening map, and final lift remains pending.

I compared the complete new comparison constructor with the frozen original
constructor and q_compare4 module, traced every change installed into the
original builder, and checked the compressed-chart reverse map against the
old seven field equations. I did not run a builder, polynomial expansion,
or other substantive local computation.

## Pinned files

Baseline repository: `work/private-degree8-20261105/repository`.
Proposal directory: `work/quartic-astra-search-20261105/precision-next`.

| File | SHA256 |
|---|---|
| reciprocal_kernel.py | c4e94463cd59a2418a6502ac7cdcfd713edf9bc1134fe0b4d4bd84700983b304 |
| build_reciprocal_source.py | d9ec8f4788882f37f3a0b7746f8d19c28968f7bf3f09cc06addab92f787098f6 |
| RECIPROCAL_PROOF.md | be5b08dd9ded743606d5c6a5fc869c4e9764575da49e5d80af13aca09950a98a |
| degree8-original/source/archive_build.py | c7ef798894a106e3c6b02816583be2b6e966e4e701f73ee670c9a0de52a70912 |
| degree8-original/modules/q_compare4.json | 639574951f42451345b3286a57ca922273567f20a548ee2426939c7a30a07212 |
| degree8-original/modules/Z_definition.json | 75fe909cbd7992c77ec99a2fe18495745362054d20083e4e6a3ff705bb17035e |
| degree8-original/modules/q_batch41.json | 8963245225447a7065b67de902ad27b8820dbeba5562d13756fdf1f71902ae6a |
| degree8-original/modules/q_height_batch.json | 6682b1069de2edb5fe5ef5ffd5d53ac74652699d8166c509bccad63bf741860a |
| degree8-original/modules/q_anchor.json | e4d8f1c9395d254fef83bddefdf304c520af8fee0575926be3aa7189376965cb |
| degree8-original/modules/q_primeparity.json | de1bd279f6ca85b6f4d972c36a4ad079cc9678c47a8672904c168eedbab17478 |

The unchanged source residual digest is
`6e68a9d39573279e894e29d8913b5ade932aa6526d28a2d40bc713c1cca934a2`.

## Changes installed into the builder

The wrapper checks the original builder digest before importing it. Before
installing any replacement, it regenerates the complete original comparison
object, including rows, calls, construction log, and metadata. Its sorted
canonical JSON digest must equal the pinned q_compare4 digest. The temporary
M.save replacement is restored in a finally block. It does not publish that
temporary comparison into MODULES.

The wrapper then passes the following explicit switches to the original main:

```
--chart 10 --parity 7 --base-gates --unit-scale --log-block 2
```

These select the frozen sparse root charts, the same parity variant, the
same two-doubling base-point circuit, d=(3,-1), D=(11,-6), and the literal
scaled generator x=(57/8,-7/2), y=(-165/8,417/32). The switch log-block=2 is
retained for the original source metadata; the new emit_g does not use the
original block evaluator.

The installed changes are limited to Field.logarithm, make_multi_comparison,
the q_batch41 order list, PELL_PRECISION, and ANCHOR_SQUARINGS. The last value
is explicitly 24 for high=64 and 26 for high=52. The wrapper's accepted pairs
are (64,64), (64,16), (52,13), and (52,16), and install repeats that check.
The latter two are separate experiments, not silent changes to a 64 proposal.

For high=64, static tracing predicts identical logical objects for
Z_definition, q_anchor, q_height_batch, q_primeparity, and the shared anchor
rows. The original root constructor never calls Field.logarithm, so changing
that method does not change a root arithmetic gate. The q_batch41 object
also stays identical when label=64. When label=16, only its orders and the
norm/power construction determined by those orders change. For high=52,
the two extra shared squarings, corresponding anchor reference, and root
precision/anchor metadata are intentional.

The original make_root still builds A,S,T,Z, height J, and common comparison
J with Field.gpoint. It retains their z coordinates, their inverse equations,
the scalar order-48 tests, Lucas equation, common theta/error, coordinate
denominator, all contacts, and all 41 calls. The original difference and
doubling methods are not patched.

## Primary chart and nonzero conditions

Only the five private comparison points H,X0,X1,X2,X3 use comparison_point
when compression is requested. Each has independent field pairs u,v,f,x,p
and the exact equations

```
f=u^2
v^2+d*f=1
p^2=x-D*f
x*f=1.
```

The first ratio equation is Lambda*p_H=G_H. Each remaining pair satisfies
A_i=C_i*p_i and A_i*Lambda=G_i. The kernel uses high precision for G_H and
label precision only for X0. Therefore it does not lower the denominator
precision when the beta numerator is lowered.

The global nonvanishing lemma for G in RECIPROCAL_PROOF.md is necessary here.
It applies to every K-valued f, not only points on the curve. All emitted
cases have at least four coefficients, so its J>=2 condition is satisfied.
Its premise is consistent with the compiler: D is fixed to (11,-6), the
coefficient list has a0=1 and valuation two-adic 1 for every other term,
and the fused circuit returns the entire indicated G polynomial.

Consequently Lambda and p_H are nonzero. Each A_i*Lambda=G_i makes A_i
nonzero, and A_i=C_i*p_i makes p_i and C_i nonzero. The retained x*f=1 gives
x,f,u nonzero. Also

```
f*p^2=1-D*f^2=v^2*(1+d*f)
```

proves v nonzero. The reverse assignments

```
z=-1/p, y=x*p, h=u*p, w=u*p/v
```

restore every old chart equation, including z*h=-u and y*z=-x. Thus neither
the p=0 torsion case nor the u=f=0 exceptional component of an unguarded
five-coordinate chart is admitted. The latter is excluded directly by
x*f=1. This audit does not treat the missing p*z=-1 equation as a harmless
deletion; the nonvanishing and reconstruction above supply its replacement.

The omitted primary z values have no other consumer in new_comparison:
formal tests use f, subtraction uses x and x*p, the new logarithm uses f,
and alternates use the difference points. A later change adding a primary-z
consumer would require a new review and an actual incidence check.

## Ratio signs and retained comparison behavior

For each reconstructed primary point, L_i=z_i*G_i=-G_i/p_i. The first
equation gives Lambda=G_H/p_H=-L_H. Therefore

```
C_i=G_i/(p_i*Lambda)=L_i/L_H.
```

This is the old ratio, not its negative or reciprocal. The code subtracts
the same proxy from the real component of C_i and subtracts zero from its
imaginary component. The forward map uses the old C_i and sets
A_i=C_i*p_i, Lambda=-L_H. The reverse map reconstructs the old logarithms
and the old inverse of L_H, which exists by the nonzero argument above.

The plain, uncompressed branch uses the original chart, explicitly computes
the new L_H inverse, and multiplies each new numerator by that inverse.
There is no accidental use of the old finite-logarithm coefficients in
either branch.

## Subtraction equations and guards

The original Field.difference is called with the same pairing
H versus 4P, then X0,X1,X2,X3 versus 4A,4S,4T,4Z. Substituting y=x*p changes
only the expression in the first row. The six field equations are

```
x*(lambda-p)-nu=0
lambda*r+s-nu=0
x_out-lambda^2+x+r=0
lambda*x_out+y_out-nu=0
F_out*x_out=1
Z_out*y_out+x_out=0.
```

In particular, the second line has +s, as required for subtraction of the
second point, and the output line has +y_out. Each equation is still
quadratic. The unchanged scalar guard is

```
((x0-r0)^2-2*(x1-r1)^2)*guard=1.
```

Over Q(sqrt(2)) this excludes precisely x=r. The output reciprocal forces
x_out and F_out nonzero; its formal-parameter equation then forces y_out
and Z_out nonzero. All five difference Z_out pairs remain allocated and are
the inputs to the alternate tests. No difference chart, difference guard,
or root J parameter is removed by primary compression.

The source still contains its preexisting cubic guards/norm nodes and
quartic Lucas residual. The claim that the newly introduced rows are
quadratic does not claim that the whole unlifted source is quadratic.

## Exact free-input and test order

The comparison retains 31 free rational inputs in the original order:

| Zero-based input positions | Meaning |
|---|---|
| 0 through 3 | beta,s,t,z proxies |
| 4 through 7 | x,y pairs for 4P |
| 8 through 11 | x,y pairs for 4A |
| 12 through 15 | x,y pairs for 4S |
| 16 through 19 | x,y pairs for 4T |
| 20 through 23 | x,y pairs for 4Z |
| 24,25 | conjugate f(J) |
| 26,27 | inverse conjugate z(J) |
| 28 | theta |
| 29 | theta^2-2 |
| 30 | contact factor |

There are 20 field expressions. Their zero-based order and corresponding
zero-based rational test positions, after the root-error test at position 0,
are as follows:

| Field expression indices | Rational test positions | Expressions | Orders |
|---|---|---|---|
| 0 through 4 | 1 through 10 | f(H),f(X0),f(X1),f(X2),f(X3) | 1 |
| 5 | 11,12 | supplied conjugate f(J) | 1 |
| 6 through 10 | 13 through 22 | conjugate F_out for the five differences | 1 |
| 11 | 23,24 | C_beta-beta | label |
| 12 through 14 | 25 through 30 | C_s-s,C_t-t,C_z-z | high |
| 15 | 31,32 | conjugate Z(H-4P)/conjugate z(J) | high |
| 16 | 33,34 | conjugate Z(X0-4A)/conjugate z(J) | label |
| 17 through 19 | 35 through 40 | the other three alternate ratios | high |

For each field expression A+B*sqrt(2), the two rational tests remain
error*B and A+B*theta, in that order. Thus the actual construction, not just
its metadata, matches

```
[1]*23 + [label]*2 + [high]*8 + [label]*2 + [high]*6.
```

The contact factor is prepended when calling q_batch41, just as before.
The generic original batch constructor consumes these test positions with
their supplied orders. Its constant leaf still receives the root-error
test; neither a beta component nor an alternate component is substituted
for that leaf.

## Fused G code

I checked the symbolic block layout in emit_g. The bound field targets are
w=D*f^2, w2=w^2, w3=w^3, h=hscale*w^6, and t. The helper low represents
w^4 as w3*w and w^5 as w3*w2. The t expression contributes normalized
degrees 4 through 9; multiplication by h/hscale in the final body places
these at degrees 10 through 15. Its separate middle and low blocks supply
degrees 6 through 9 and 0 through 5. Multiplication by a6 restores the full
G polynomial. Padding the 13-coefficient case with zeros removes only
degrees 13 through 15.

For four coefficients the direct expression is
1+a1*w+a2*w2+a3*w2*w. Every direct output expression is quadratic in its
bound targets. Inserting it into Lambda*p_H=G_H or A_i*Lambda=G_i therefore
keeps the ratio rows quadratic. The generated source must still be matched
against the independent binomial-coefficient expansion; this static
calculation does not substitute for that executable identity check.

## Concrete acceptance limits

No repair to the two reviewed compiler files is requested. The following
checks remain necessary before accepting the proposal as a new source:

1. Verify the complete emitted comparison rows and call arguments, including
   the paired scalar coordinates, against independent formulas. The isolated
   G checker cannot detect a dropped subtraction guard or a reordered test.
2. Compare noncomparison modules with the frozen originals for the intended
   parameter case, and independently flatten the new call DAG and shared
   anchor rows. The author has requested a separate checker for this work.
3. Mutation-test missing ratio equations, wrong ratio signs, wrong input/test
   order, a changed denominator precision, removed difference/root z values,
   and missing nonzero guards. The circuit-only mutations do not cover these.
4. Obtain separate approval of the arithmetic replacement of the old finite
   logarithm and of beta precision 16. The old and new finite polynomials
   are not equal on arbitrary independent f,z inputs. Only the compressed
   chart/ratio step has the direct rational maps checked above.
5. Create and independently check a new source entry and quadratic lift,
   then expand the final quartic and enforce the strict 2^80 coefficient cap.

The wrapper explicitly leaves source_pin_authorized false and records the
compiler copies and their hashes. This matches the proposal's current
status. A successful isolated probe or this static review alone does not
authorize changing the existing source hash.
