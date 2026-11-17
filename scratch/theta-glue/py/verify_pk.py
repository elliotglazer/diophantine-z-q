# FULL symbolic verification (exact, Q[U0..U3]) of the global identities found by pk.py:
#   e_k(S_m^4 : m even) = P_k(psi4, psi6, chi10, chi12),  k = 3..9,
# where S_m = theta_m^2 in second-order theta constants (duplication formula), psi4 = Sum S^4/4,
# psi6 = Sum_syz eps S_a^2 S_b^2 S_c^2 / 4, chi10 = -Prod S / 2^14, chi12 = Sum_Goepel Prod_{m not in Q} S_m^2/(2^17 3).
# Polynomials: dict packed-exponent -> Fraction; exponents packed base 2^8 (degree <= 72 < 256).
import pickle, sys, time
from fractions import Fraction as F
from dup_sym import S, chars
from igusa import syz, goep
B = 256
def pack(e): return e[0] + B * (e[1] + B * (e[2] + B * e[3]))
def conv(p): return {pack(e): c for e, c in p.d.items()}
def mul(a, b):
    out = {}
    get = out.get
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = k1 + k2; out[k] = get(k, 0) + v1 * v2
    return {k: v for k, v in out.items() if v}
def add(a, b, s=1):
    out = dict(a)
    for k, v in b.items(): out[k] = out.get(k, 0) + s * v
    return {k: v for k, v in out.items() if v}
def smul(a, c): return {k: v * c for k, v in a.items()} if c else {}
ONE = {0: F(1)}
def pw(a, n, cache={}):
    r = ONE
    for _ in range(n): r = mul(r, a)
    return r
eps = pickle.load(open('psi6_signs.pkl', 'rb')); key = lambda t: tuple(sorted(t))
PK = pickle.load(open('pk.pkl', 'rb'))
Sd = {m: conv(S[m]) for m in chars}
S2 = {m: mul(Sd[m], Sd[m]) for m in chars}
S4 = {m: mul(S2[m], S2[m]) for m in chars}
psi4 = {}
for m in chars: psi4 = add(psi4, mul(S4[m], ONE))
psi4 = smul(psi4, F(1, 4))
psi6 = {}
for a, b, c in syz: psi6 = add(psi6, mul(mul(S2[a], S2[b]), S2[c]), eps[key((a, b, c))])
psi6 = smul(psi6, F(1, 4))
chi10 = ONE
for m in chars: chi10 = mul(chi10, Sd[m])
chi10 = smul(chi10, F(-1, 2**14))
chi12 = {}
for q in goep:
    r = ONE
    for m in chars:
        if m not in q: r = mul(r, S2[m])
    chi12 = add(chi12, r)
chi12 = smul(chi12, F(1, 2**17 * 3))
print('terms: psi4 %d psi6 %d chi10 %d chi12 %d' % (len(psi4), len(psi6), len(chi10), len(chi12)), flush=True)
# e_k of y_m = S_m^4 by the recursion e(a::s) = e(s) + a e(s) (shifted), keeping k <= kmax
kmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
kmin = int(sys.argv[2]) if len(sys.argv) > 2 else 3
t0 = time.time()
E = [ONE] + [{} for _ in range(kmax)]
for i, m in enumerate(chars):
    y = S4[m]
    for k in range(min(kmax, i + 1), 0, -1):
        E[k] = add(E[k], mul(E[k - 1], y))
    print('  e-recursion step', i, 'sizes', [len(e) for e in E], '%.0fs' % (time.time() - t0), flush=True)
powc = {}
def P_(f, n):
    if (id(f), n) not in powc: powc[(id(f), n)] = pw(f, n)
    return powc[(id(f), n)]
for k in range(kmin, kmax + 1):
    rhs = {}
    for (a, b, c, d), cf in PK[k].items():
        rhs = add(rhs, smul(mul(mul(P_(psi4, a), P_(psi6, b)), mul(P_(chi10, c), P_(chi12, d))), cf))
    print('k=%d: e_k has %d terms; e_k - P_k == 0: %s  (%.0fs)' % (k, len(E[k]), add(E[k], rhs, -1) == {},
          time.time() - t0), flush=True)
