"""Exact small comparisons for the proposed H5 level repair; no theorem certification."""
from fractions import Fraction
from math import prod
import json

if not __debug__:
    raise RuntimeError("Run without -O")

group = prod(11**4 - 11**i for i in range(4))
assert group < 11**16
assert 576 < 2**10
assert 2**10 * 11**16 < 2**66
valuation_bound = 65
extra_two_valuation = 2
upper_break = 2 * (1 + valuation_bound + extra_two_valuation)
conductor = 2 + 2 * upper_break
assert (upper_break, conductor) == (136, 274)
assert conductor < 300
assert 2 * 2 * 576 == 2304
assert Fraction(16,24**4) + (25+3+Fraction(25,16))/288 < 1
assert 13000000 + 1 + 1 < 2**24
budget_exponent = 24 + 12*300*8
assert 210 < 2**8 and 4608 > 2**12
assert budget_exponent == 28824 < 12*165888 == 1990656
print(json.dumps({
    "status": "passed",
    "scope": "Exact arithmetic only; modularity, geometry and ramification are proved in the associated text.",
    "GL4_F11_order": group,
    "Galois_torsion_degree_strict_upper_power_of_two": 66,
    "worst_wild_ramification_valuation_bound": 67,
    "upper_break_bound": upper_break,
    "conductor_bound": conductor,
    "safe_small_prime_level_factor": "210^300",
    "isogeny_field_bound": "2304 R",
    "height_bound": "2^24 210^3600 R^24",
    "height_constant_strict_upper_power_of_two": budget_exponent,
    "original_constant_strict_lower_power_of_two": 1990656,
}, indent=2))
