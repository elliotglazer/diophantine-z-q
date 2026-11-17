"""Generate the bundle part of the last new module: OpenResearchLeaves13 / OpenAddedLeaves12 field lists copied from
TailZ19 / TailZ18 (minus r1r2Ab / x6ConicModel) and the conversions' field-by-field lines."""
import re
H = 'ZInQKernel/OneProof/H/'
def struct(path, name):
    L = open(H + path).read().split('\n')
    i = next(k for k, l in enumerate(L) if l.startswith('structure ' + name + ' '))
    j = i + 1
    while L[j].strip(): j += 1
    return L[i + 1:j]
def fields(body):
    return [m.group(1) for l in body for m in [re.match(r'^  ([A-Za-z0-9_]+) :', l)] if m]
def drop(body, f):
    # remove field f and its docstring
    out = []; buf = []
    for l in body:
        if l.startswith('  /--'): buf = [l]
        elif buf and not re.match(r'^  [A-Za-z0-9_]+ :', l): buf.append(l)
        else:
            m = re.match(r'^  ([A-Za-z0-9_]+) :', l)
            if m and m.group(1) == f: buf = []; continue
            out += buf + [l]; buf = []
    return out
R = struct('TailZ19.lean', 'OpenResearchLeaves12'); A = struct('TailZ18.lean', 'OpenAddedLeaves11')
print('R', len(fields(R)), 'A', len(fields(A)))
open('scratch/x6-fold/R12.txt', 'w').write('\n'.join(drop(R, 'r1r2Ab')))
open('scratch/x6-fold/A11.txt', 'w').write('\n'.join(drop(A, 'x6ConicModel')))
open('scratch/x6-fold/R12_fields.txt', 'w').write('\n'.join(fields(R)))
open('scratch/x6-fold/A11_fields.txt', 'w').write('\n'.join(fields(A)))
