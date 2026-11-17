import sys; sys.path.insert(0, __file__.rsplit('/',1)[0])
from poly import *
x, yy, a0, a1, a2, a3, s, t = setvars(['x','yy','a0','a1','a2','a3','s','t'])
a = a0 + a1*s; b = -3*a2 - 3*s*a3; c = a2 - s*a3; d = a0 - a1*s
re = a*x + b + t*c*yy; im = a*yy - t*c*x - t*d
n = a0**2 - 2*a1**2 + 3*a2**2 - 6*a3**2
Pp = 4*a1**2 + 12*a3**2; R = a0*a1 - 3*a2*a3; S = a0*a3 + a1*a2
U = x**2 + yy**2 - 3; X = 6*x
Phi = Pp*(U + 6) + 2*s*(R*U - S*X)
E = re**2 + im**2 - n*(x**2 + (yy - t)**2) - Phi
qs, r = reduce(E, 's', 2)
qt, r2 = reduce(r, 't', 3)
print("remainder:", fmt(r2))
print("qs:", fmt(qs)); print("qt:", fmt(qt))
