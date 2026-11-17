# Numerics for theta-split: theta constants at the Lean Omega(tau) (HDec PkgI1 / BPAnalytic.QM.Omega),
# Lean thetaConst (exp(pi i v^T Omega v + pi i v^T b), v = n + a/2), jTheta = 3779136 (prod th)^4/(sum th^8)^5.
import mpmath as mp, itertools, sys
mp.mp.dps = int(sys.argv[1]) if len(sys.argv) > 1 else 40
s2 = mp.sqrt(2)
def Omega(tau):
    E = mp.matrix([[tau, s2*tau],[1, -s2]])
    F0 = mp.matrix([[(tau-3)/2, s2*(tau-3)/2],[(tau+1)/2, -s2*(tau+1)/2]])
    P = mp.matrix([[-2,-1],[-1,-1]])
    return (F0*P)**-1 * E
chars = [((a0,a1),(b0,b1)) for a0,a1,b0,b1 in itertools.product(range(2),repeat=4) if (a0*b0+a1*b1)%2==0]
def theta(m, Om, N=None):
    (a0,a1),(b0,b1) = m
    if N is None: N = int(mp.mp.dps/3)+6
    tot = mp.mpc(0)
    for n0 in range(-N,N+1):
        for n1 in range(-N,N+1):
            v0 = n0+mp.mpf(a0)/2; v1 = n1+mp.mpf(a1)/2
            q = v0*v0*Om[0,0] + v0*v1*(Om[0,1]+Om[1,0]) + v1*v1*Om[1,1]
            tot += mp.exp(mp.pi*1j*q + mp.pi*1j*(v0*b0+v1*b1))
    return tot
def thetas(tau):
    Om = Omega(tau); return [theta(m,Om) for m in chars]
def jth(th):
    s8 = sum(t**8 for t in th); p = mp.mpf(1)
    for t in th: p *= t
    return 3779136*p**4/s8**5
def jtau(tau): return jth(thetas(tau))
def solve(q, tau0):
    return mp.findroot(lambda t: jtau(t)-q, tau0)
