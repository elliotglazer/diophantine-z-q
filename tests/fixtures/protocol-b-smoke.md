# Protocol B smoke-test lemma

This isolated test fixture does not change the project's manuscript or claimed
quartic record.

## Statement

For rational numbers x and y, the equation 3x^2 + 5y^2 = 0 holds if and only if
x = 0 and y = 0.

## Proof

In the usual order on the rational numbers, a square is nonnegative. Thus
3x^2 and 5y^2 are nonnegative. If their sum is zero, each must be zero:
if either were positive, adding the other nonnegative term would give a
positive sum. Since 3 and 5 are nonzero, x^2 = y^2 = 0. A field has no zero
divisors, so x = y = 0. Conversely, substituting x = y = 0 gives the equation.
