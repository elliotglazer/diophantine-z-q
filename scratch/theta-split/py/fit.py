import dnum as D, random
from linsolve import solve
random.seed(1)
pts = []
while len(pts) < 30:
    tau = complex(random.uniform(-1,1), random.uniform(0.6,1.8))
    th,E,N,j = D.data(tau)
    pts.append((j,E))
for k in range(3,11):
    for lo,hi in [(-1,1),(-2,1),(-1,2),(-2,2),(-3,2),(-2,3),(-3,3),(-4,4)]:
        n = hi-lo+1
        A = [[j**i for i in range(lo,hi+1)] for j,E in pts]
        b = [E[k]/E[1]**k for j,E in pts]
        x = solve(A[:n], b[:n])
        r = max(abs(sum(a*c for a,c in zip(A[i],x))-b[i])/abs(b[i]) for i in range(n,len(pts)))
        if r < 1e-7:
            print(k,(lo,hi),'relres %.1e'%r, [complex(round(c.real,7),round(c.imag,7)) for c in x]); break
    else: print(k,'no fit', r)
