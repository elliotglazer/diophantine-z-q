#!/usr/bin/env python3
"""Independent final-stage replay; no generator or third-party package required."""
import hashlib
import json
from collections import defaultdict
from fractions import Fraction
from math import prod
from pathlib import Path

D = Path(__file__).resolve().parent
S = D / "source"
for manifest in ("source-blobs.json", "annex-blobs.json", "foundations-blobs.json"):
    idx = json.loads((D / manifest).read_text())
    for path, sha in idx.items():
        data = (S / path).read_bytes()
        assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == sha, path
f = S / "computation/projective_contacts_20261126"
parent = S / "computation/reciprocal_depressed_scalar_20261126/quartic175.json"
a = json.loads((f / "quadrics.json").read_text())
b = json.loads(parent.read_text())
assert a["input"] == 1 and a["variables"] == 175
assert len(a["residuals"]) == 147
def row(terms):
    d = defaultdict(int)
    for v, e, m in terms:
        d[e, tuple(sorted(m))] += v
    return {k:v for k,v in d.items() if v}
def read(t):
    return row((int(z["coefficient"]), z["parameterPower"], z["monomial"]) for z in t["terms"])
old = {r["name"]:read(r) for r in b["residuals"]}
new = {r["name"]:read(r) for r in a["residuals"]}
assert len(old) == len(new) == 147
p = [1]
radii = [-77,23,21,-75,51]
for r in radii:
    q = [0]*(len(p)+1)
    for i,c in enumerate(p):
        q[i] -= r*r*c
        q[i+1] += c
    p = q
assert p == [-20236648618580625,98933750608581,-151547683050,77366218,-15125,1]
def e(*terms):
    return row((c,0,m) for c,*m in terms)
changes = set()
for i,(t,r,s,d,w) in enumerate([(2,60,61,62,156),(68,69,70,71,157),(162,167,168,169,158)]):
    pref = "additive.detector"+str(i)+"."
    expected = {
        "contactSquare":e((1024,t,t),(-1,r)),
        "contactCombination":e((1,r,s),(p[3],r,w),(p[3],r),(p[4],s,w),(p[4],s),(-1,d)),
        "contactRelation":e((p[1],r,w),(p[1],r),(p[2],s,w),(p[2],s),(p[0],w),(p[0]),(1,s,d))}
    for name, v in expected.items():
        k = pref+name
        assert old[k] != v and new[k] == v
        old[k] = v
        changes.add(k)
assert len(changes) == 9 and old == new
C = 331**21
P = defaultdict(int)
for d in new.values():
    q = defaultdict(int)
    for (k,m),v in d.items():
        assert k >= 0 and len(m) <= 2 and all(1 <= i <= 175 for i in m)
        q[m] += v*C**k
    for m,c in q.items():
        for n,v in q.items():
            P[tuple(sorted(m+n))] += c*v
P = {m:c for m,c in P.items() if c}
assert len(P) == 3196 and max(map(len,P)) == 4
assert P[(1,1,1,1)] == 1
assert {i for m in P for i in m} == set(range(1,176))
assert max(abs(c).bit_length() for c in P.values()) == 802
out = []
for m,c in sorted(P.items()):
    factors = [f"x{i}"+(f"^{m.count(i)}" if m.count(i)>1 else "") for i in sorted(set(m))]
    s = "-" if c<0 else "+" if out else ""
    n = str(abs(c)) if abs(c)!=1 or not factors else ""
    out.append(s+n+("*" if n and factors else "")+"*".join(factors))
literal = "".join(out).encode("ascii")
assert len(literal) == 73080 and literal == (f / "expanded175.txt").read_bytes()
G = [2,3,5,7,11,13,17,19,23,37,41,2399]
J = prod(G)
assert J == 811898089212210
CC = Fraction(74712001,10**6)*2**68*3**16*5**16*7**4*J**2*prod(Fraction(q+1,q) for q in G)
assert 2**68 < CC < 2**249
assert 331**97 > 2**810
assert 2**21*Fraction(36036-2835,36036)>526500
theta = [Fraction(0),Fraction(-1,2),Fraction(-1),Fraction(1,2399),Fraction(-32,407)]
assert [(973*v-77)/(1632*v+32) for v in theta] == [Fraction(x,32) for x in radii]
for x in range(331):
    s=2**20*x*x
    r=(2401+2400*s)*(343+375*s)*(1+s)
    assert r%331 and (25920000*r+1081567619)%331
print("PASS: 175 variables; 147 quadrics; nine replaced contact rows; 3196 monomials; exact degree 4; content 1; 802-bit coefficients; 73080 ASCII bytes; 331 anchor residues.")
