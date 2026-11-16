"""Exact common-Hessian-radical test for all affine coordinate directions."""
from search import *

def run():
    equations=[]
    for rid,p in c.rows.items():
        deriv={}
        for (s,m),a in p.items():
            if len(m)!=2:continue
            assert s==0
            i,j=m
            deriv.setdefault(i,{})[j]=deriv.setdefault(i,{}).get(j,F(0))+a
            deriv.setdefault(j,{})[i]=deriv.setdefault(j,{}).get(i,F(0))+a
        equations.extend((rid,i,q) for i,q in deriv.items())
    # Sparse equations first reduce fill, without affecting the exact rank.
    equations.sort(key=lambda x:len(x[2]))
    basis={};pivots=[]
    for rid,i,q in equations:
        q=q.copy()
        while q:
            j=min(q);a=q[j]
            if j not in basis:
                basis[j]={k:v/a for k,v in q.items()};pivots.append([rid,i,j]);break
            for k,v in basis[j].items():
                q[k]=q.get(k,F(0))-a*v
                if not q[k]:del q[k]
    result={'coordinates':len(c.coordinates),'stackedHessianRows':len(equations),
      'stackedHessianRankOverQ':len(basis),'commonRadicalDimension':len(c.coordinates)-len(basis),
      'nonpivotCoordinates':sorted(set(c.coordinates)-set(basis)),
      'interpretation':'A nonzero common radical direction is necessary for eliminating a coordinate after any invertible affine coordinate change by direct constant-pivot substitution without using other equations.'}
    vectors=[]
    for free in sorted(set(c.coordinates)-set(basis)):
        vec={free:F(1)}
        for j,q in sorted(basis.items(),reverse=True):
            val=-sum(a*vec.get(k,F(0)) for k,a in q.items() if k!=j)
            if val:vec[j]=val
        vectors.append({'free':free,'direction':{str(k):str(v) for k,v in vec.items()},
                        'names':{str(k):c.coordinates[k]['name'] for k in vec}})
    result['kernelBasis']=vectors
    (OUT/'affine-obstruction.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':run()
