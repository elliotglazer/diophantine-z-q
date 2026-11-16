# Degree-ten block evaluation

Applied to the combined 1,025-coordinate system, `patch_eval_blocks.py` gives a measured 998-coordinate system with 955 quadratic residuals. The raw system has 1,030 coordinates and 987 residuals. The baseline compiler removes 32 coordinates. The input remains coordinate 0 and is protected.

The exact raw and reduced systems are in `combined-block-eval/`. `verify_eval_blocks.py` expands each of the nine actual emitted evaluation circuits with every upstream coordinate an independent formal variable. All 18 component outputs equal the original polynomial evaluation and all 72 changed gate residuals vanish identically. This is an exact polynomial check over Q, not sampling.

For P(q)=sum from k=0 to10 of c_k q^k over Q(sqrt(2)), use

    B(q) = c5+c6*q+c7*q²+c8*q³+c9*q⁴+c10*q⁵,
    P(q) = c0+c1*q+c2*q²+c3*q³+c4*q⁴+q⁵*B(q).

Compute q²,q³,q⁴,q⁵ in four scalar assignments. Each component of B is one quadratic assignment. Each final component of P is one quadratic assignment, since the low-degree sum is inserted directly into that assignment rather than first assigned to another coordinate. All c_k are affine forms in upstream coordinates. Thus the evaluator uses eight rational coordinates, compared with eleven previously. Nine detectors save 27 coordinates.

Every new gate has the form v=f(previous coordinates), with f quadratic. Given an old-system zero, preserve every base coordinate and unchanged value, evaluate the new gates in order, and use the displayed identity to identify the old and new output P(q). Every downstream value and structural equation agrees. Given a new-system zero, evaluate the old power-basis gates in order on the same q and coefficients. The same identity recovers the identical output and every old downstream equation. These maps use no division. They preserve all original inverse guards, field-quotient domains, the input coordinate, and every arithmetic qualification.

Degree-two and degree-four evaluations are unchanged. The patch touches only `evalSym` and is independent of the optional alternative weight patch `patch_weights.py`. That weight patch is not included in this candidate.

## Shared factor for two weights

`patch_weight_factor.py` is another independent patch. It replaces four assignments

    e30=e24*e6, e102=e96*e6, q16=q1*e30, q52=q1*e102

by three assignments

    common=q1*e6, q16=common*e24, q52=common*e96.

Associativity and commutativity prove both output identities over Q. The forward map computes common; the reverse map computes e30 and e102. Neither direction divides. All original denominator domains are unchanged. Nine detectors save nine coordinates. Applied after block evaluation to the same combined checkpoint, this gives 989 coordinates and 946 quadratic residuals. `verify_weight_factor.py` proves all 18 identities from the actual emitted circuits with upstream symbols independent and checks the 27 actual defining residuals. The checked residual system, compiler certificate, and receipt are in `combined-weight-factor/`. This patch was suggested by the elimination worker and should not be confused with the superseded alternative `patch_weights.py`.

# Review of other workers

`other-workers-review.json` pins the independently reviewed source-compression builder and logarithm patch by SHA256. `review_other_workers.py` expands the actual five gate definitions at each of the ten poles with upstream coordinates independent, verifies all 20 emitted structural pole formulas, and verifies the factorization of all eight emitted correction-chain rows.

The pole maps z=C*e and e=z/C are valid because C=17b is nonzero. For detector poles this follows from the retained meanings of R, W, and the nonzero rational component w0: W is nonzero in Q(sqrt(2)), its norm is nonzero, and b=R*Norm(W)²/(4*w0²) is nonzero. For the scalar pole its explicit inverse enforces b nonzero. The correction-chain factorization implies each next value is either its nonzero predecessor or the relevant prime times that predecessor. This proves the inverse Boolean reconstruction is defined and exactly recovers the original finite choice set. No gap was found in either zero-set map.

`review-log.cjs` reruns the logarithm worker's exact emitted-circuit expansion and baseline checker replay without writing in that worker's directory. All ten logarithm circuits equal the original z*sum(a_j*(D*f²)^j) as exact four-variable polynomials. The square completion uses only division by fixed nonzero rational constants. Its zero-set maps therefore preserve all witness denominator domains. The result is in `review-log-check.json`. No gap was found.
