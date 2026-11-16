# Seven-coordinate chart

The field is K = Q(sqrt(2)). A field coordinate is a pair of rational
coordinates. Write d = 3 - sqrt(2) and D = d^2 = 11 - 6 sqrt(2).

The old chart has eight field coordinates u,v,w,z,f,h,x,y and equations

```
f = u^2
v^2 + d f = 1
w^2 + v^2 = 2
h = v w
z h = -u
x f = 1
y z = -x.
```

Retain u,v,z,f,x,y and replace w,h by a single field coordinate p. Use

```
f = u^2
v^2 + d f = 1
p = y f
p^2 = x - D f
x f = 1
y z = -x.
```

Every equation in rational components has degree at most two. Six field
equations replace seven, and seven field coordinates replace eight.

## Forward map

Keep u,v,z,f,x,y and set p = y f. The equation x f = 1 proves x,f,u nonzero.
The equation y z = -x proves y,z nonzero. Multiplying z h = -u by y and
using y z = -x gives x h = y u. Hence h = y u f = u p. Therefore

```
f p^2 = h^2 = v^2 w^2 = (1-d f)(1+d f) = 1-D f^2.
```

Divide by f and use 1/f = x. This proves p^2 = x-D f.

## Reverse map and all exceptional cases

Keep u,v,z,f,x,y. The new equations imply x,f,u,y,z,p are nonzero, since
x f = 1, y z = -x, and p = y f.

Also v is nonzero. If v were zero, then d f = 1. Thus x = d after
multiplication by x. The equation p^2 = x-D f then gives
p^2 = d-d(d f) = 0, contradicting p nonzero. This argument does not divide
by d and requires no extra guard or arithmetic theorem.

Set

```
h = u p
w = u p / v.
```

Then h = v w and

```
v^2 w^2 = f p^2 = 1-D f^2 = (1-d f)(1+d f) = v^2(1+d f).
```

Divide by v^2 to obtain w^2 = 1+d f = 2-v^2. Finally
z h = z u y f = -u x f = -u. All old equations follow. This reconstructs
the original w,h exactly on every old solution. Thus these are inverse
rational maps, including every case allowed by the old equations.

The only field fact used is that Q(sqrt(2)) is a field. Irrationality of
sqrt(2) proves that a rational pair has zero norm only when both entries
are zero. No elliptic-curve theorem, source arithmetic converse, or
unpublished result is needed.

## Incidence and preservation of the input

The replacement is valid when all eight old coordinate pairs are distinct,
none contains input coordinate zero, all fourteen scalar old equations are
present up to nonzero rational scalar factors, and w,h have no outside
occurrences. The handler scans the complete incidence sets for all four
removed rational coordinates. It does not restrict outside uses of retained
coordinates. The new p pair must be fresh consecutive allocated variables.

The producer locates the five comparison charts and six root charts from
the pinned module construction logs, then uses the pinned flattening map.
The expected total is 41*5+6 = 211, for a raw saving of 422 rational variables.
This is a prediction until the diagnostic and full checker run. Start at
the structured norm-base artifact, since subsequent eliminations and unit
scaling can change the required proof rows.

## Rational equations and coefficients

For p=p0+p1 sqrt(2) and similarly for y,f,x, the four new scalar equations are

```
p0 - y0 f0 - 2 y1 f1 = 0
p1 - y0 f1 - y1 f0 = 0
p0^2 + 2 p1^2 - x0 + 11 f0 - 12 f1 = 0
2 p0 p1 - x1 - 6 f0 + 11 f1 = 0.
```

Their largest coefficient magnitude is 12. Their squared sum has degree
four. This small local coefficient bound does not replace checking the
complete expanded polynomial after later transformations.

## Reproduction and integration

Copy these scripts to the remote research tree, retaining this directory as
CHARTS. Define REPO as the repository root and PARENT as the structured
norm-base artifact directory. Run sequentially:

```
python CHARTS/test_chart_replacement.py --repo REPO
python CHARTS/replace_charts.py --repo REPO --parent PARENT --diagnostic chart-incidence.json --output chart-base
python CHARTS/make_checker.py --base REPO/research/quartic-variables/verify_certificate.py --output verify_with_charts.py
python verify_with_charts.py chart-base
```

The created checker embeds the independent rule source so its own SHA256
covers the added rule. Its ordinary patch validator rejects wrong supplied
rows, extra/missing patches, cubic rows, and unallocated variables. The
standalone rule tests also reject twelve malformed chart claims and allow
outside uses of retained boundary coordinates. Four exact rational examples
test the forward and reverse maps using both signs of u and v.

After full verification, apply the existing elimination and unit-scaling
searches to chart-base and recheck with the same full checker. The producer
does not claim that the raw saving survives those later passes unchanged.

## Removing the ordinate when its consumers stay quadratic

An additional rule removes the field coordinate y after the first replacement.
Check the three retained field equations x f = 1, p = y f, y z = -x. Keep
x f = 1, replace the other two by p z = -1, and replace y by x p in every
outside equation. Reject the transformation if any resulting residual has
degree greater than two. This requires a complete incidence scan of both
rational coordinates of y.

The old equations imply y = x p and p z = -1. Conversely, given the new
equations, define y = x p. Then y f = x p f = p and y z = x p z = -x.
Thus both maps are exact, preserve all boundary variables, and need no
additional guard. The old proof rows must exist and x,y,z,f,p must have
distinct rational coordinates excluding input zero.

At a comparison point the only outside use of y is the first subtraction
line, lambda*x-y-nu=0. It becomes x*(lambda-p)-nu=0, which remains quadratic.
The other difference equations do not change. This should remove 205 field
ordinates in comparisons and the two root J ordinates, for another 414
rational variables. The four main root ordinates have nonlinear consumers;
the producer rejects those when substitution would create degree three.
These counts await the complete remote diagnostic.

The second producer reads the first producer's gpoint_chart records and
computes all current y occurrences. It emits field_ordinate records.
The independent ordinate_expected handler reconstructs the expected patches
from the actual complete incidence table, rather than trusting a supplied
list of affected rows. Tests cover seven malformed ordinate claims plus a
linear outside consumer, and test both stages on four exact rational points.

Run the second producer before generic elimination or unit scaling:

```
python CHARTS/remove_chart_ordinates.py --repo REPO --parent chart-base --output chart-ordinates
python verify_with_charts.py chart-ordinates
```

Regenerate verify_with_charts.py from the updated make_checker.py so it
contains both independent handlers. The predicted combined raw saving is
422+414 = 836 rational variables. Later optimization counts remain unmeasured.
