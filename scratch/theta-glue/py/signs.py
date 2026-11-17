# Signs in Igusa's psi6 = 2^-2 sum_{syzygous} +-(theta theta theta)^4, from the action of generators of
# Sp4(Z) on the ten theta_m^4 (signed permutations; computed exactly in Q(i)[U] with i as a 5th variable).
import itertools, pickle
from fractions import Fraction as F
from poly import P
from dup_sym import S, chars
from igusa import syz
def red(f):
    d = {}
    for e, c in f.d.items():
        ei = e[4]; c2 = c * (-1)**(ei // 2); k = e[:4] + (ei % 2,)
        d[k] = d.get(k, 0) + c2
    return P(d, 5)
V = [P.var(i, 5) for i in range(5)]; Iv = V[4]
S5 = {m: P({e + (0,): c for e, c in S[m].d.items()}, 5) for m in chars}
T4 = {m: red(S5[m] * S5[m]) for m in chars}
h = F(1, 2)
gens = {
  'T1': [V[0], V[1], Iv * V[2], Iv * V[3], Iv],
  'T2': [V[0], Iv * V[1], V[2], Iv * V[3], Iv],
  'T12': [V[0], V[1], V[2], -V[3], Iv],
  'P12': [V[0], V[2], V[1], V[3], Iv],
  'P23': [V[0], V[1], V[3], V[2], Iv],
  'H': [(V[0]+V[1]+V[2]+V[3])*h, (V[0]-V[1]+V[2]-V[3])*h, (V[0]+V[1]-V[2]-V[3])*h, (V[0]-V[1]-V[2]+V[3])*h, Iv],
}
act = {}
for g, L in gens.items():
    act[g] = {}
    for m in chars:
        img = red(T4[m].subst(L))
        hit = [(n, s) for n in chars for s in (1, -1) if (img - T4[n] * s).iszero()]
        assert len(hit) == 1, (g, m, len(hit))
        act[g][m] = hit[0]
# propagate signs eps over syzygous triples: psi6 invariance => eps_{g T} = eps_T * prod sigma
key = lambda t: tuple(sorted(t))
eps = {key(syz[0]): 1}; frontier = [key(syz[0])]
while frontier:
    t = frontier.pop()
    for g in gens:
        img = [act[g][m] for m in t]; t2 = key(n for n, _ in img)
        s = eps[t] * img[0][1] * img[1][1] * img[2][1]
        if t2 in eps: assert eps[t2] == s, 'inconsistent'
        else: eps[t2] = s; frontier.append(t2)
print('#triples reached', len(eps))
# normalize by comparing with 4 psi6
forms = pickle.load(open('igusa_forms.pkl', 'rb'))
psi6 = P(forms['psi6'], 4)
T4r = {m: S[m] * S[m] for m in chars}
h6 = sum((T4r[t[0]] * T4r[t[1]] * T4r[t[2]] * eps[key(t)] for t in syz), P.const(0, 4))
r = None
for c in (1, -1):
    if (h6 * c - psi6 * 4).iszero(): r = c
print('h6 = +-4 psi6 with overall sign', r)
eps = {t: s * r for t, s in eps.items()}
pickle.dump(eps, open('psi6_signs.pkl', 'wb'))
for t in sorted(eps): print(t, eps[t])
