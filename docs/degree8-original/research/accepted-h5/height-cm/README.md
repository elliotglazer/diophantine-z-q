# Original CM height branch

The proof in [cm-height-proof.tex](cm-height-proof.tex) establishes

    h_F(A) < 854 R < 6^100 R^24

for a CM quaternion surface whose geometric endomorphisms are defined over a field L with degree at most 576 and rad(|D_L|) at most R. These hypotheses are stated explicitly and remain the responsibility of the separate field/model audit. This packet does not certify the full H5 estimate.

The two operations that could conceal a field-degree cost are treated separately. Elliptic factors descend by rational idempotents. Maximal-order saturation is the quotient by an explicitly Galois-stable subgroup, so both operations take place over L. A good-reduction extension is used only to evaluate the stable height; the Gaudron--Remond isogeny theorem is applied over L itself.

[source-application-ledger.json](source-application-ledger.json) records the published theorem statements, exact normalizations, URLs and the hypotheses matched in the proof. The full 2023 publisher PDF, rather than merely an author manuscript, was inspected. The 2017 elliptic formula is used before its conversion to a class-group average, avoiding that latter statement's extra Weierstrass-coefficient hypothesis.

The elementary eta estimate and the same-field maximal-order construction are proved in the note. No joint von Kaenel--Kret result is used, and no original witness, polynomial equation or fixed constant changes. There were no heavy computations or builds in this review.
