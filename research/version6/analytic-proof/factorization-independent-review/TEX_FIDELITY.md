# TeX fidelity review

Accepted, 2026-11-06, for the exact three fragment hashes in `tex-fidelity-static.json`. This is a translation review against the accepted Markdown arguments and the source conventions recorded in `REVIEW.md` and the separate norm-transfer review. It is not a replacement for those mathematical reviews or for the separately reviewed Type I/II and arithmetic progression inputs.

The norm-transfer TeX preserves the integer coefficient descent, ordinary-equidistribution obstruction, stretched filtration, Gaussian row decomposition, residue splitting, endpoint loss, and the explicit parameter inequalities. The affine TeX preserves integer affine parameters, real Mal'cev interpolation, the total-equidistribution implication, fixed-W quantifiers, and the square-root error absorption. The factorization TeX preserves the conjugated lattice, cellwise Haar mean subtraction, cell counts, metric losses, and the choice of B before the upper exponent E(B).

The following precision fixes requested during review are present: b is an integer; X is at least 1 in both coefficient lemmas; C_* is chosen sufficiently large initially; the W-trick conclusion explicitly assumes a Lipschitz Haar-mean-zero F_0; the centered-prime corollary explicitly inherits the group and orbit hypotheses; and that corollary explicitly quantifies every interval progression P in [N] of modulus at most Q. No unreviewed change of parameter regime remains.

The static checker found 52 distinct labels in these fragments plus `type-i-ii/type_i_ii.tex`, no unresolved references, no duplicate labels, and no missing bibliography keys against the supplied harnesses. In particular `gi-minor-arc` and `gi-ordinary-primes` resolve to the Type I/II fragment. The assembled manuscript must include that fragment and the supplied GT bibliography entries.

Accepted TeX hashes:

- norm_transfer.tex: `d2d8fa98291def5007fdd76ee4226acf7f4d77d0dd086d8ce3bc984785b13c16`
- affine_pullback.tex: `10edb90817918605156a7f1193e42fa2777336b063406776129d4233021f2778`
- factorization.tex: `53c1e8b15c0460c5eb4fdcac92f800605fdb846e5b04d13ea847dd7063fa7649`

Source versions and their hashes remain those in the accepted mathematical receipts. No PDF compilation or visual typesetting check is claimed here. This acceptance does not, by itself, assert that the subsequent Gowers/polynomial bridge or the complete removal theorem is proved.
