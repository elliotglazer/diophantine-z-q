from fractions import Fraction as F
from pathlib import Path
from itertools import product
import json
import re

HERE = Path(__file__).resolve().parent
checks = 0
# These finite-field checks supplement, and do not replace, the algebraic proof.
for p in [3, 5, 7, 11]:
    for kappa in [1, 2, 3, -1, -2]:
        for a, b, c, d, w in product(range(p), repeat=5):
            if (a*a+b*b-c*c-d*d-kappa*w*w) % p:
                continue
            x0, x1, x, z = a+c, a-c, b-d, b+d
            R = kappa*w*w-x*z
            G = (a+1)**2+b*b
            H = (c+1)**2+d*d
            assert (x0*x1-R) % p == 0
            for chart, t in [(1,x1),(0,x0)]:
                if t % p == 0:
                    continue
                K = (kappa*w*w-x*z+t*t+2*t)**2+t*t*(x+z)**2
                assert (4*t*t*G-K) % p == 0
                if chart == 1:
                    P = kappa*w*w+2*t
                    assert (G-H-P) % p == 0
                    assert (K-(t*t+x*x)*(t*t+z*z)-P*(P+2*t*t-2*x*z)) % p == 0
                else:
                    P = kappa*(t+2)*w*w-2*x*z
                    assert (t*(G-H)-P) % p == 0
                assert ((G % p == H % p == 0) == (P % p == K % p == 0))
                checks += 1

alpha = F(1,1000)
log_loss = F(1,1000)
large_exponent = max(3+alpha-F(1,100),F(11,4)+alpha)+log_loss
assert large_exponent < 3-F(1,200)
assert F(27,10)+log_loss < 3-F(1,200)
assert (3-F(1,400))/2 == F(3,2)-F(1,800)
assert 5-3*F(3,4) == 2+F(3,4) == F(11,4)

old = HERE.joinpath('original-tail.tex').read_text(encoding='utf-8')
new = HERE.joinpath('replacement-tail.tex').read_text(encoding='utf-8')
assert re.findall(r'\\label\{([^}]+)\}',old) == re.findall(r'\\label\{([^}]+)\}',new)
assert new.count(r'\begin{proof}') == new.count(r'\end{proof}') == 2
for env in ['lemma','proposition','equation']:
    assert new.count(r'\begin{'+env+'}') == new.count(r'\end{'+env+'}')
depth = 0
for i,ch in enumerate(new):
    if ch in '{}':
        backslashes = 0
        j=i-1
        while j >= 0 and new[j] == '\\':
            backslashes += 1
            j -= 1
        if backslashes % 2:
            continue
        depth += 1 if ch == '{' else -1
        assert depth >= 0
assert depth == 0
result = {'finite_field_chart_checks':checks,'primes':[3,5,7,11],
          'kappa_values':[1,2,3,-1,-2],
          'exponent_checks':'passed','TeX_labels_environments_braces':'passed',
          'scope':'finite checks supplement the source-level proof audit; no complete manuscript build'}
HERE.joinpath('checks.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
