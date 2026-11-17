from fractions import Fraction as F
def nullspace(rows, n):
    """exact nullspace of the matrix with given rows (lists of Fractions), n columns."""
    M = [list(r) for r in rows]; piv = []; r = 0
    for c in range(n):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; inv = 1 / M[r][c]; M[r] = [x * inv for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        piv.append(c); r += 1
        if r == len(M): break
    free = [c for c in range(n) if c not in piv]
    basis = []
    for fc in free:
        v = [F(0)] * n; v[fc] = F(1)
        for i, pc in enumerate(piv): v[pc] = -M[i][fc]
        basis.append(v)
    return basis
def solve(rows, rhs, n):
    """one exact solution of rows x = rhs (or None)."""
    aug = [list(r) + [b] for r, b in zip(rows, rhs)]
    ns = nullspace(aug, n + 1)
    for v in ns:
        if v[n] != 0: return [-x / v[n] for x in v[:n]]
    return None
