# Point-module chart saves 18 coordinates

The standalone candidate has 1,254 active rational coordinates and 1,211 quadratic residuals after the unchanged 32 compiler eliminations. Its raw system has 1,286 coordinates and 1,243 residuals. All nine initial point modules save two coordinates each. The patch changes no downstream point values or arithmetic predicates.

Write K=Q(sqrt(2)), D=11-6sqrt(2). For one baseline halfpoint, denote its coordinates by a,b and its doubling slope by m. The baseline equations are

    b² = a³-Da,
    2bm = 3a²-D,
    X = m²-2a,
    Y = m(a-X)-b.

The original gate system implements these equations exactly. Its curve equation together with the slope equation implies b≠0: b=0 would force a=0 or a²=D, making the slope numerator -D or 2D. It also implies a≠0, since a=0 would force b=0.

Introduce base coordinates t,h in K and use the new equations

    u=t²,
    X=h²,
    u(X-u/4)=D,
    Y=h(u/2-X).

Each field element is two rational coordinates. The new module uses four base coordinates t,h and six gate coordinates u,X,Y. The baseline uses four base coordinates a,b and eight gate coordinates. The middle field equation gives two structural quadratic residuals. All other displayed equations use two quadratic assignment residuals each.

## Forward map

Given a baseline solution, put

    t=b/a,
    h=(a²+D)/(2b).

Both denominators are nonzero, as proved above. The curve relation gives

    a=t*h+t²/2,
    m=h+t,
    D=t²(h²-t²/4).

For example, after clearing the nonzero denominator 4a⁴, the new chart equation becomes

    a²(a²+D)²-b⁴-4Da⁴
      = -(b²-a³+Da)(b²+a³-Da)=0.

The slope identity follows after clearing 2ab:

    2abm-a(a²+D)-2b²
      = a(2bm-3a²+D)-2(b²-a³+Da)=0.

Substitute a=t*h+t²/2 and m=h+t into the baseline doubling formula. It gives exactly X=h² and Y=h(t²/2-h²). Thus the new module has the same output point.

## Reverse map

Given a new solution, define

    a=t*h+u/2,
    b=a*t,
    m=h+t.

Since D=u(h²-u/4)≠0, u≠0 and t≠0. Direct expansion gives D=a²-u*a=a(a-u), hence a≠0 and b≠0. Moreover

    b²-a³+Da=0,
    2bm-3a²+D=0,
    m²-2a=h²=X,
    m(a-X)-b=h(u/2-X)=Y.

Reconstruct the baseline x-square, slope-square, and y-product gate coordinates by their original normalized assignment formulas. All baseline point-module rows then hold. The maps are inverse, because b/a=t and (a²+D)/(2b)=h.

Apply this map independently to all nine initial modules. Keep every downstream semantic value and the input coordinate. All original quotient domains remain true through the reconstructed baseline point modules. This proves exact equivalence of rational solution projections.

## Compatibility with the deleted F inverse

In both real embeddings, D=11±6sqrt(2)>0. The chart equation has u=t²>0 and forces h²-u/4>0, so X=h²>0 in both embeddings. Its rational component is positive. Therefore every detector scale A remains strictly positive. This supplies the same positivity fact used by the quotient patch to recover its deleted F inverse.

## Files and verification

`point-replacement.cjs` replaces the single original statement that creates `points` by doubling the nine halfpoints. `prepare_point.py` applies it to the immutable baseline and changes the base-coordinate display names from half.x/half.y to chart.t/chart.h. It writes `point-candidate/build_source.cjs`.

`verify-point.cjs` checked all 1,196 raw gate identities and replayed the compiler certificate. It also checked 81 exact polynomial identities: the forward and reverse algebra above, plus every actual emitted assignment and chart equation in all nine modules. Its receipt is `point-candidate/algebra-check.json`. This is an author-side exact verification; the source integration worker is performing the independent mathematical review.

The exact resulting quartic is the sum of squares of the integer-normalized residuals in `point-candidate/compiled-ir.json`, with S fixed as before. No arithmetic assumption was added or removed, including the existing Frei–Tinková qualification.
