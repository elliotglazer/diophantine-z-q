# The D210 scalar splitting route

The direct normalizer calculation proves that the fully endomorphism-compatible degree character sends `w_m` to the square class of `m`. It does not become trivial after correcting an unmarked isomorphism: that correction is exactly what produces the norm degree.

With the accepted tame branch model, the resulting sign obstruction at a valuation-one contact with the branch at zero is nonzero at an odd prime p precisely when 105 is nonsquare modulo p. For every scalar splitting cochain, its coefficient field then has degree at least `2^(v_2(p-1)-1)`. The proof gives non-CM rational fibers with this bound arbitrarily large; already `v_2(p-1)=14` forces degree at least8192.

[normalizer-and-local-obstruction.tex](normalizer-and-local-obstruction.tex) gives the proof. [source-application-ledger.json](source-application-ledger.json) records the published uniformization, CM inputs, and accepted family premises. Independent review accepted the result at the stated scalar-splitting scope, including the normalizer degree character, local obstruction, and finite-extension order bound.

Thus a fixed finite central-extension/scalar-coefficient construction cannot deliver the proposed uniform2304 or4608 coefficient degree. Allowing extra ramification does not remove this local lower bound. The baseline six-contact proof allows the coefficient field to grow with the contact product and is not contradicted.

This does not disprove the desired H5 bound or exclude every bounded-dimensional auxiliary construction. An actual repair would need a height estimate that avoids the scalar splitting cost, or a proved restriction on parameters excluding the offending local contacts. Such a restriction is absent from the current universal H5 statement. No literal polynomial, witness count, or fixed constant was changed.

A subsequent positive step allows unbounded character order while bounding local conductor. [SMALL_PRIME_CONDUCTOR_REVIEW.md](SMALL_PRIME_CONDUCTOR_REVIEW.md) independently accepts conductor exponent at most 274 at each of 2, 3, 5, 7 for the proposed scalar lift, including the field, ramification and support arguments. This is compatible with the obstruction above: large tame character order does not force a large wild conductor. The global modularity and height transfer are reviewed separately.
