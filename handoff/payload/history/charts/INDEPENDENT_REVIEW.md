# Independent review

Reviewer: the ratio-fusion agent, independently of the chart author.
Date: 2026-11-05.

Status: both the `gpoint_chart` replacement and the subsequent
`field_ordinate` elimination pass mathematical and static code review.
No blocking soundness issue was found in the versions listed
below. This is not a report that the scripts ran or that a resulting quartic
passed full verification. The root dispatcher still needs to run the tests,
the source-incidence diagnostic, and the full certificate/expansion checker.

The first-stage review covers the replacement of w,h by p. The second-stage
review at the end covers eliminating y by substituting y=xp in all its
outside uses. Separate version tables identify both reviewed snapshots.

## Exact solution maps

All field products below are in K = Q(sqrt(2)); d = 3-sqrt(2) and D = d².
The old equations are exactly

    f=u², v²+df=1, w²+v²=2, h=vw, zh=-u, xf=1, yz=-x.

The new equations retain f=u², v²+df=1, xf=1, yz=-x and impose

    p=yf, p²=x-Df.

For an old solution, xf=1 gives f and x nonzero and therefore u nonzero.
Then yz=-x gives y and z nonzero. Define p=yf. From zh=-u and yz=-x one
gets xh=yu and hence h=up. Thus

    fp²=h²=v²w²=(1-df)(1+df)=1-Df².

Since f is invertible, p²=x-Df. All retained coordinates stay fixed.

Conversely, p=yf and yz=-x give pz=-1, so p is nonzero. The new equations
give fp²=v²(1+df). If v=0, the right side vanishes but the left side is a
product of nonzero field elements. Thus v is nonzero. Define h=up and
w=up/v. Then h=vw, zh=-u, and dividing fp²=v²(1+df) by v² proves
w²=1+df=2-v². This restores all old equations. On every old solution,
these formulas recover its original h and w, so the solution maps are
inverse and preserve the input projection.

The v=0 exceptional case is therefore excluded by equations that the
checker explicitly retains and verifies. It does not rely on choosing a
branch, adding a guard, or assuming that d is nonsquare. The author's
alternative argument v=0 => df=1 => x=d => p²=0 is also valid.

## Field and inverse conditions

There is no needed nonsquareness assertion about d or D. The coefficient
field is genuinely a field: if a,b are rational and a²-2b²=0, irrationality
of sqrt(2) gives a=b=0. Every nonzero pair therefore has the usual rational
inverse (a,-b)/(a²-2b²). This elementary fact justifies the displayed
division by v. The retained equations establish nonvanishing before that
division is used.

One can also avoid divisions in the reverse witness formula by setting

    h=up, w=-v(1+df)zxu.

Indeed, (up)(-zxu)=1 and (up)²=v²(1+df). This alternative is not required
for acceptance; it confirms that the reverse construction has no hidden
field-extension or square-root choice.

## Checker audit

`chart_expected` verifies all fourteen old scalar equations independently
of the producer. Its hardcoded products use the correct multiplication
(a,b)(c,e)=(ac+2be,ae+bc), and its constants satisfy
(3,-1)²=(11,-6). Comparison up to nonzero rational scaling preserves the
zero sets and does not discard an equation.

The checker requires sixteen distinct existing nonzero coordinate indices,
fourteen distinct valid row indices, and exactly the expected block names.
It excludes input coordinate zero from the old coordinate list. It checks
the complete maintained incidence set of each of the four deleted scalar
coordinates against the six replaced rows. Hence no deleted w or h
coordinate can remain in an outside row. Retained coordinates may have
arbitrary outside uses, and the solution maps preserve their values.

The new coordinates must be exactly nextvar and nextvar+1. The expected
patch set replaces six rows with four quadratic rows and two empty rows;
none contains a removed coordinate. The full base checker independently
compares all supplied patches, rejects duplicate/missing/extra patches,
checks degree and allocated-variable limits, updates incidence, and checks
the final active coordinate map and complete expanded polynomial.

`make_checker.py` advances the allocation counter by exactly two through
the checked handler return. It embeds the reviewed rule source directly
into the output checker, so the output checker hash covers the rule.
The existing source, replay, and expansion checks remain in place.

## Source fidelity and producer audit

The producer uses construction-log labels in the pinned q_compare4 and
Z_definition modules only to locate candidate coordinates and rows. It
checks the actual current rows against the corresponding frozen rows and
checks full deletion incidence. Although it does not regenerate the source
builder, the independent handler verifies every algebraic prerequisite on
the actual certificate state, and the full checker anchors that state to
the pinned source hash. No semantic source assumption is imported through
the labels alone.

The producer's initial incidence table remains sufficient during this
specific sequence: each accepted chart deletes only its private w,h
coordinates, introduces fresh p coordinates, and never changes another
chart's old coordinate uses. The full checker uses updated incidence at
every event regardless.

The expected 211 source charts and gross saving of 422 rational variables
are not measured findings of this review. The diagnostic and full checker
must establish the actual candidate. The four new scalar equations have
coefficient magnitude at most 12 before later transformations, but only
the complete expansion can establish the final global coefficient bound.

## Tests and remaining execution

The static test review found twelve malformed structural/algebraic cases,
including loss of the two essential inverse/parameter equations, outside
uses, aliases, input deletion, bad row lists, and bad freshness. The test
also checks four exact forward/reverse examples and allows outside uses of
retained boundary coordinates. These are sensible tests of the handler.
They remain unexecuted in this independent review. Malformed supplied patch
tests belong to the base checker, which already checks those conditions.

Before counting any saving, run the tests, require all source/incidence
checks to pass, and run the generated full checker on the exported artifact.
After any optimizer pass, recheck the full artifact with the same added rule.

## Reviewed SHA256 versions

| File | SHA256 |
|---|---|
| replace_charts.py | b34e218ebab191d66415d1a99f659318c71018f4a58c3bbb2e704cd1f9f16eb1 |
| check_chart_replacement.py | 57f5e439aaf49182b3fc20dbbc46efb613578fac8fb9ec69dd2d71ebca1ed247 |
| make_checker.py | 2b985a709ac6729b4e945b590ee43c04c5080c472cf098c999e80b32b78a8753 |
| test_chart_replacement.py | 8092dabda1ee2e9031cabd534460d5be700389fc6f1a1ba59bda141cdc477aca |
| PROOF.md | 8a75232dfa1c30347e5c3ffa7f3533399404cf0f9fb610593cdecc0f2ff942bc |

## Second-stage review: ordinate elimination

The additional `field_ordinate` rule passes mathematical and static code
review. No blocking issue was found. The first `chart_expected` handler is
unchanged in the updated checker by text inspection. All execution and
final-count qualifications above continue to apply.

The old proof equations are xf=1, p=yf, and yz=-x. Their scalar residuals
must all match before the handler changes anything. Multiplying p=yf by x
gives y=xp; multiplying yz=-x by f gives pz=-1. Thus restricting an old
solution satisfies the new equation and every outside equation after
substitution. Conversely, from xf=1 and pz=-1 define y=xp. Then yf=p and
yz=-x. Substituted outside equations become exactly their old counterparts.
Both maps preserve all retained coordinates and are inverse. This proof
uses no extra nonvanishing assertion or coefficient-field nonsquareness.

The checker requires ten distinct positive existing scalar coordinate
indices for x,y,z,f,p and six distinct valid proof-row indices. In particular,
neither replacement for a y component can contain either removed y
component. The retained xf=1 rows contain no removed coordinate and remain
untouched. The two p=yf rows become empty. The two yz+x=0 rows become the
correct real and imaginary components of pz+1=0.

The handler derives `affected` itself from the union of both complete
maintained y incidence sets. A certificate cannot omit an outside use by
supplying an incomplete list. It also checks that all four discarded or
replaced proof rows occur in that union. For every other affected row it
substitutes both y coordinates simultaneously into each original monomial,
then sums the resulting exact polynomials. The replacements are the correct
components x0*p0+2*x1*p1 and x0*p1+x1*p0. It rejects any final degree above
two and any residual occurrence of a removed coordinate. The existing full
patch validator rejects missing, extra or altered supplied replacements.

The untrusted producer reads the first-stage certificate records to locate
candidate proof rows, but this history is not a trusted prerequisite of the
rule. The independent handler rechecks the three equations on the actual
current system. The producer updates incidence after each accepted event,
so later candidates see every earlier substitution. It skips a candidate
when a substitution creates degree above two. Its allocation count stays
unchanged, as required for an elimination that introduces no coordinates.

The updated embedding dispatch includes both handlers and embeds their
current source in the standalone full checker. The updated tests add seven
malformed ordinate claims, an exact linear outside-use substitution, and
verification of both stages in the four rational examples. The tests are
still unrun by this reviewer. A linear outside row containing both y
components would be a useful additional test, but the simultaneous
substitution code already handles it correctly by inspection; this is not
a blocking finding.

The claimed 207 eligible ordinate sites and 414 further gross scalar
coordinate removals remain predictions until the full run. The review does
not assume these counts and does not infer optimized savings from them.

### Second-stage reviewed SHA256 versions

| File | SHA256 |
|---|---|
| check_chart_replacement.py | e2a3e2f006b425bdd3a1baba5c9e47f0b498fc5858ed02dcb0886971a99b8fb6 |
| remove_chart_ordinates.py | 0654945ff462e8a158d2f89accb52cf19b34534eed9dba2cea62f393ba19b03b |
| make_checker.py | aca5c4018bbd7ff292b9b94cfb251751d27f4f2d622220d43674f283f9598ec3 |
| test_chart_replacement.py | 67ca12e47382faeb6e68e19334b5edd08dfffa2fed6d285d61d4eb9009c5a61d |
| PROOF.md | f122f0c3b36f78f945a912ebbd2d160e64807699e9766ab2d496fdb371430c0c |
