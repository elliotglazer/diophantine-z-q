# Source compression by 17 coordinates

Status: exact elementary equivalence is proved below and identities are checked by an independent script. This change is pending independent review. It does not remove or strengthen any existing arithmetic qualification, including the current Frei–Tinková input. No release is modified.

The generated system has 1,287 raw coordinates and 1,244 quadratic residuals. Running the baseline compiler's reduction, without expanding the final polynomial, gives 1,255 active total coordinates, including the original input, and 1,212 quadratic residuals. It removes 32 coordinates as before. Thus the saving against the 1,272-coordinate baseline is 17. Multiplying each residual by its rational coefficient denominators gives integer coefficients, and summing their squares gives a polynomial of degree at most four with exactly the same rational zero set. The fixed coefficient S remains a coefficient, never a variable.

## Pole rescaling

Use C=17b. In each baseline pole the equations are

    p² = C(1-e)(1+3e),
    Cq² = (s²-H)(s²+3H),
    H = Ce(C-U²).

The nine coordinate poles have U=b. The scalar pole retains its original preparation parameter and formula for U, including the same denominator domain.

Replace the base witness e by z=Ce. Use the following five intermediate witnesses:

    P=p², F=U², H=z(C-F), V=s², Q=q².

The two structural equations become

    CP=(C-z)(C+3z),
    CQ=(V-H)(V+3H).

Every displayed equation is quadratic in its coordinates because C is an affine form in b. The baseline uses six intermediates for this part, namely (1-e)(1+3e), U², e(C-U²), H, s², q². The replacement uses five. It saves one coordinate and one defining residual at each of the ten poles.

For the forward map retain all unaffected witnesses, put z=Ce, and assign the five intermediates their displayed values. The first new structural residual is C times the first old residual. The second new residual equals the old residual.

For the reverse map set e=z/C, retain p,s,q,U,b, and reconstruct all old intermediates by their definitions. Since C is nonzero, the new first equation divided by C gives the old first equation. The equality H=Ce(C-U²) gives the old second equation. These maps are inverse on the base witnesses. Every auxiliary defining equation has a unique rational solution, so they extend to maps between the complete witness systems.

The nonzero premise is already present. For coordinate poles, the guards for F, delta, the detector weight and w0 give nonzero R and nonzero W. Since Q(sqrt(2)) is a field, W has nonzero norm, and b=R*Norm(W)²/(4*w0²) is nonzero. For the scalar pole, the unchanged inverse equation for b explicitly forces b nonzero. Therefore C=17b is nonzero in every rational solution on either side. The new first equation alone would not establish this premise; the unchanged upstream system is essential.

## Correction chain

The baseline has eight Boolean witnesses and seven gates for their product. Its correction is

    c=(1-2 epsilon_sign) product_p (1+(p-1)epsilon_p),

where p runs through 2,3,5,7,11,13,17. Replace this by eight witnesses c0,...,c7 and the eight quadratic structural equations

    c0²=1,
    ci²-(pi+1)ci*c(i-1)+pi*c(i-1)²=0,  i=1,...,7.

Use c7 as the correction. Each second equation factors as

    (ci-c(i-1))*(ci-pi*c(i-1))=0.

Over Q this gives ci=c(i-1) or ci=pi*c(i-1). Induction from c0=±1 proves that every ci is nonzero and that c7 is exactly one of the original 256 signed squarefree corrections. Conversely each Boolean assignment supplies a chain by successive partial products. For reconstruction, set epsilon_sign=(1-c0)/2 and epsilon_pi=(ci/c(i-1)-1)/(pi-1). These are in {0,1}. All divisions have nonzero denominators, by the induction and pi>1. This saves the seven product coordinates and their equations; the number of structural equations and base witnesses is unchanged.

## Composition and verification

All coordinates outside the ten private pole witness blocks and the correction block keep their meanings. The input is unchanged. The scalar pole's preparation, every detector, the nine halfpoints, all logarithms, the shared height point, and the semilocal anchor are retained. These changes compose with changes to their upstream arithmetic so long as the same nonzero pole inputs and scalar correction meanings are preserved.

Run build_variant.py, then build_source.cjs with Node. Run verify_identities.py for an independent integer-polynomial identity check and all 256 forward correction choices. Run measure.py for the actual coordinate and residual census. The converse correction argument is the displayed factorization, not a sampling claim. The identity verifier imports neither the producer nor the compiler.

## Rejected shortcuts

The nine detector occurrences cannot simply share private pole witnesses. Their inputs differ, and individual existential solvability does not imply a common witness. Likewise one detector at the sum of two coordinate squares would not control both rational heights: rational points on a fixed circle can have arbitrarily large denominators. A new arithmetic height lemma would be necessary.

The source's existing scalar preparation-zero alternative changes the normalization and increases the finite correction set. It is not a free removal of one witness from this system and is not used here. The three-witness anchor retains its original local-solubility condition. No reduction of those witnesses is claimed.
