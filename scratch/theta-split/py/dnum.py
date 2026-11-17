# double-precision version of thnum (pure python), for exploration
import cmath, math, itertools
s2 = math.sqrt(2)
def Omega(tau):
    E = [[tau, s2*tau],[1, -s2]]
    F0 = [[(tau-3)/2, s2*(tau-3)/2],[(tau+1)/2, -s2*(tau+1)/2]]
    P = [[-2,-1],[-1,-1]]
    F = [[sum(F0[r][k]*P[k][c] for k in range(2)) for c in range(2)] for r in range(2)]
    d = F[0][0]*F[1][1]-F[0][1]*F[1][0]
    Fi = [[F[1][1]/d,-F[0][1]/d],[-F[1][0]/d,F[0][0]/d]]
    return [[sum(Fi[r][k]*E[k][c] for k in range(2)) for c in range(2)] for r in range(2)]
chars = [((a0,a1),(b0,b1)) for a0,a1,b0,b1 in itertools.product(range(2),repeat=4) if (a0*b0+a1*b1)%2==0]
def theta(m, Om, N=12):
    (a0,a1),(b0,b1) = m; tot = 0j
    for n0 in range(-N,N+1):
        for n1 in range(-N,N+1):
            v0 = n0+a0/2; v1 = n1+a1/2
            q = v0*v0*Om[0][0] + v0*v1*(Om[0][1]+Om[1][0]) + v1*v1*Om[1][1]
            tot += cmath.exp(math.pi*1j*q + math.pi*1j*(v0*b0+v1*b1))
    return tot
def thetas(tau):
    Om = Omega(tau); return [theta(m,Om) for m in chars]
def esym(xs):
    e = [1]+[0]*len(xs)
    for x in xs:
        for k in range(len(xs),0,-1): e[k] += e[k-1]*x
    return e
def data(tau):
    th = thetas(tau); t8 = [t**8 for t in th]
    E = esym(t8); p = 1
    for t in th: p *= t
    N = 3779136*p**4
    return th, E, N, N/E[1]**5
