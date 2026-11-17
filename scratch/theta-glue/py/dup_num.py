# Numerical check (double precision) of the duplication formula in the project's convention:
# theta[a;b](W) = sum_n exp(pi i v.Wv + pi i v.b), v = n + a/2;
# U_c(W) = sum_k exp(2 pi i (k+c/2).W(k+c/2));  theta[a;b]^2 = sum_c (-1)^{((c+a) mod 2).b} U_c U_{c+a}.
import cmath, itertools, random
random.seed(1)
N = 12
def theta(W, a, b, scale=1.0, bfac=1.0):
    s = 0
    for n0 in range(-N, N+1):
        for n1 in range(-N, N+1):
            v = (n0 + a[0]/2, n1 + a[1]/2)
            q = v[0]*(W[0][0]*v[0] + W[0][1]*v[1]) + v[1]*(W[1][0]*v[0] + W[1][1]*v[1])
            s += cmath.exp(cmath.pi*1j*scale*q + cmath.pi*1j*bfac*(v[0]*b[0] + v[1]*b[1]))
    return s
cs = list(itertools.product(range(2), repeat=2))
worst = 0
for trial in range(5):
    x = [random.uniform(-1, 1) for _ in range(3)]
    y11, y22 = random.uniform(.8, 1.5), random.uniform(.8, 1.5); y12 = random.uniform(-.3, .3)
    W = [[x[0] + 1j*y11, x[1] + 1j*y12], [x[1] + 1j*y12, x[2] + 1j*y22]]
    Uc = {c: theta(W, c, (0, 0), scale=2.0) for c in cs}
    for a in cs:
        for b in cs:
            if (a[0]*b[0] + a[1]*b[1]) % 2: continue
            lhs = theta(W, a, b)**2
            rhs = 0
            for c in cs:
                e = ((c[0]+a[0]) % 2, (c[1]+a[1]) % 2)
                rhs += (-1)**(e[0]*b[0] + e[1]*b[1]) * Uc[c] * Uc[e]
            worst = max(worst, abs(lhs - rhs) / max(1, abs(lhs)))
print('worst relative error', worst)
