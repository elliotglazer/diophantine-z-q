# Exact elimination search

The baseline admits a verified reduction from 1,272 to **1,251 total rational
coordinates**, including the unchanged input. The candidate has 1,208 quadratic
residuals. Their sum of squares, after clearing each row's rational coefficient
denominators, is an integer-coefficient polynomial of degree four. The fixed
coefficient S is retained symbolically and is not a coordinate.

This is an algebraic equivalence with the supplied baseline. All qualifications
on that baseline's external arithmetic inputs remain. This result does not yet
meet the target of at most 999 coordinates.

## What changes

One substitution removes `scalar.leaf1.quadratic` (coordinate 1273). Its defining
equation gives `x1273 = x267*x1260`. Substitution into its consumer would initially
produce degree four. Exact polynomial multiples of three retained equations
reduce that consumer to degree two. The complete identity is the first operation
in `modulo-certificate.json`.

Twenty more substitutions follow an invertible linear coordinate change. The
stack of the 1,229 residual Hessians has rank 1,252 over Q, so their common kernel
has dimension 20. Its directions mix final shared symmetric coefficients with
the corresponding Horner coordinates in the nine detectors. A shear in each
direction makes one coordinate occur only linearly in every equation. A constant
pivot then eliminates it. The resulting system has zero common Hessian kernel.

These twenty changes may overlap a redesign of symmetric-coefficient evaluation.
They must not be added to another worker's count without compiling and analyzing
the combined system. The scalar substitution is separate from those twenty.

## Exact correspondence of rational solutions

A shear operation records a coordinate `free` and changes
`old_x[v] = new_x[v] + factor*new_x[free]` for its listed coordinates. All other
coordinates stay fixed. Each elementary shear has determinant one and rational
inverse obtained by subtracting the same multiple. Neither the input nor any
protected coordinate changes.

An elimination operation records a nonzero rational constant pivot coefficient,
a polynomial replacement `q`, and every changed consumer equation. The verifier
checks the pivot becomes identically zero after substituting `x=q`. It also
checks, for every consumer, the exact identity

`new_row = old_row[x := q] + sum(factor_j * retained_row_j)`.

The retained rows do not contain the eliminated coordinate and remain equations
of the new system. Therefore the identity is reversible on their common zero
set. Forward witness maps apply inverse shears and delete eliminated coordinates
in certificate order. Reverse witness maps process the certificate in reverse,
reinsert each eliminated coordinate with its stored polynomial replacement, and
apply the corresponding shears. No variable division, omitted exceptional case,
or new nonzero assumption occurs.

The verifier also checks the exact output rows, active-coordinate census,
degree bound and integer denominator clearing. A sum of rational squares is zero
exactly when every summand is zero. Thus the final quartic has precisely the
baseline's rational zero projection onto the original input.

## Reproduction and artifacts

Run `python verify.py` in this directory for the independent algebraic replay.
It imports none of the search or baseline compiler code. The supplied receipt is
`verification.json`; the integer-coefficient system is
`integer-candidate-ir.json`. The candidate's historical `sourceGates` and `values`
fields are retained metadata and are not asserted to define transformed
coordinates. The authoritative candidate is its coordinate list and residuals.

The search scripts are `modulo_search.py`, `affine_search.py` and `search.py`.
They reuse the baseline compiler's exact polynomial arithmetic. To analyze
another compatible compiled system, use

`python run_pipeline.py PATH_TO_COMPILED_IR PATH_TO_NEW_OUTPUT_DIRECTORY`.

To check that result independently, use

`python verify.py --source PATH_TO_COMPILED_IR --directory PATH_TO_OUTPUT`.

## Search limits

The homogeneous quadratic parts of all 1,229 baseline equations are linearly
independent over Q. No nonzero constant rational linear combination of these
rows is affine. Ordinary direct constant-pivot elimination finds no additional
coordinate before the new transforms.

The modulo-equation pass tries constant-pivot substitutions followed by exact
reduction using unaffected equations. It is a bounded heuristic, not a complete
decision procedure for possible quadratic presentations. The common-Hessian
kernel calculation is exact. A zero common kernel rules out another elimination
by this same affine-direction method on the current presentation; it does not
rule out other presentations or nonlinear rational coordinate changes.

Conic parametrization alone gives no accepted saving here. Its rational inverse
requires a chart condition, and denominator-clearing can admit additional points
on the excluded chart. No such unverified parametrization is included.

## Combined 1,025-coordinate checkpoint

The first merged checkpoint admits one further verified elimination, leaving
1,024 coordinates and 981 quadratic equations. It removes
`detector0.Adelta4.square.quadratic`. Its common Hessian kernel is already zero,
so the baseline's twenty shear savings cannot be added to this merged count.

The immutable input is `combined-1025-source.json` with SHA256
`5198a0dccc3946f4faf2c90aa629183580b593a19e2b4ddc676cb01ae8c7bea4`.
Its certificate, output and verification receipt are in `combined-run/`.
Run `python verify.py --source combined-1025-source.json --directory combined-run`
to replay this separate transformation. Later combined checkpoints supersede
this count and require their own replay.
