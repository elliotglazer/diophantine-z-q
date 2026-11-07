"""Exact rational checks of the comparison lemma's numerical specialization.

This checks numerical inequalities, not its inherited arithmetic theorems.
"""
from fractions import Fraction as Q
import json

alpha = Q(19)
assert 2-alpha*4/40 == Q(1,10)
assert 2-alpha/12 == Q(5,12)
assert 5**19 * 2**40 < 5**40  # 5^(19/40) < 5/2
assert 2**19 < 4**12         # 2^(19/12) < 4
assert 7*Q(5,2)+6 < 24
assert 7*4+6 < 40
assert Q(12,5)/40 + Q(19,5)/40 == Q(31,200)
assert Q(31,200)*4 < 4-3
assert all(10*(1-alpha/s)>1 for s in (24,32))
assert not 10*(1-alpha/20)>1
assert Q(50331647,2) > 10*(6+2093966)
assert 2-Q(18)*4/36 == 0
assert 2-Q(16)*4/32 == 0
assert 2-Q(16)/8 == 0
assert 2-alpha*3/32 > 0
powers = [1]
for a,b in [(1,1),(2,2),(4,4),(8,8),(16,8),(24,16),(40,40)]:
    assert a in powers and b in powers
    powers.append(a+b)
assert powers == [1,2,4,8,16,24,40,80]
assert 24-2 == 22 and 80-2 == 78
assert 2**6 < 78
print(json.dumps({'status':'passed_exact_rational_checks',
 'scope':'numerical specialization and restricted power-chain identities; no arithmetic theorem certification',
 'highMargin':str(2-alpha*4/40), 'lowMargin':str(2-alpha/12),
 'powerChain':powers}, indent=2))
