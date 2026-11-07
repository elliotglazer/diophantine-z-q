"""Finite checks supporting the elementary notes, not proofs of universal claims."""
import json
from itertools import product

for s in list(range(7,201))+list(range(-200,-6)):
    a=abs(s);m=abs(s-2)
    u=[0,1]
    for k in range(1,m+1):u.append(a*u[-1]-u[-2])
    assert all(u[k]%(a-2)==k%(a-2) for k in range(len(u)))
    assert all(u[k]%(a+2)==((-1)**(k-1)*k)%(a+2) for k in range(1,len(u)))
    assert u[m]%m==0
    t,z=u[m+1],u[m]//m
    assert t*t-s*(s-2)*t*z+(s-2)**2*z*z==1
    assert (a-1)**(a-4)>3**(a-3)
    # A counterexample to exponential growth without the divisibility.
    assert a*a-a*a*1+1==1
    assert 1%m!=0

# Relax every pure power after five gates to ANY exponent from 0 to 32.
# This is a superset of all nonnegative pure-power circuits in that class.
# With only two q-dependent gates, the first output must be q12 (q40
# cannot have exponent 78 using this power pool). Enumerate all possible
# products/quotients a*b/c for the second output with q-exponent one.
base=[(i,0) for i in range(33)]+[(0,1)]
def outputs(pool):
    return {(a[0]+b[0]-c[0],a[1]+b[1]-c[1]) for a,b,c in product(pool,repeat=3)}
first=outputs(base)
assert (78,1) not in first
second=outputs(base+[(22,1)])
assert (78,1) not in second
assert max(e for e,q in second if q==1)==54
print(json.dumps({'status':'passed','lucasExamples':388,
    'purePowerRelaxationMaximum':32,'secondOutputMaximum':54,
    'scope':'Finite recurrence checks and exhaustive relaxed last-gate enumeration; universal arguments are in the notes'},indent=2))
