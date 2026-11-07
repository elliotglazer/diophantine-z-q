"""Independently evaluate actual emitted weight gates as Laurent polynomials.

Input seeds are e and q1. Every encountered quotient denominator must be
a nonzero rational multiple of a power of e, never a new q1 obligation.
The source proof that e != 0 is separate from this algebraic checker.
"""
from fractions import Fraction as Q
import json
import sys
from pathlib import Path

def add(a,b):
    c=a.copy()
    for k,v in b.items():
        c[k]=c.get(k,Q(0))+v
        if not c[k]: del c[k]
    return c

def mul(a,b):
    c={}
    for (i,j),x in a.items():
        for (k,l),y in b.items(): c=add(c,{(i+k,j+l):x*y})
    return c

def verify(raw):
    gates={g['coordinateId']:g for g in raw['gates']}
    values=raw['values']
    checks=[]
    for r in range(9):
        prefix=f'detector{r}.'
        cache={}
        denominators=[]
        for name,power in [('eWeight',(1,0)),('q1',(0,1))]:
            ts=values[prefix+name]['terms']
            assert len(ts)==1 and len(ts[0]['monomial'])==1
            assert Q(ts[0]['coefficient'])==1 and ts[0]['sPower']==0
            cache[ts[0]['monomial'][0]]={power:Q(1)}
        def expr(ts):
            result={}
            for t in ts:
                assert t['sPower']==0
                p={(0,0):Q(t['coefficient'])}
                for i in t['monomial']: p=mul(p,coord(i))
                result=add(result,p)
            return result
        def coord(i):
            if i not in cache:
                g=gates[i]
                if g['operation']=='quadratic_assignment':
                    cache[i]=expr(g['expression'])
                else:
                    assert g['operation']=='rational_quotient'
                    den=expr(g['denominator']); assert len(den)==1
                    (a,b),c=next(iter(den.items()))
                    assert b==0 and c!=0
                    denominators.append({'coordinate':i,'ePower':a,'coefficient':str(c)})
                    cache[i]=mul(expr(g['numerator']),{(-a,-b):1/c})
            return cache[i]
        assert expr(values[prefix+'q12']['terms'])=={(22,1):Q(1)}
        assert expr(values[prefix+'q40']['terms'])=={(78,1):Q(1)}
        assert sorted(d['ePower'] for d in denominators)==[2,4,8]
        checks.append({'detector':r,'q12':[22,1],'q40':[78,1],
                       'denominators':denominators})
    return {'status':'passed_emitted_Laurent_identities', 'detectors':checks,
            'scope':'Actual emitted gate values and denominators; e nonvanishing requires the source norm argument'}

if __name__=='__main__':
    print(json.dumps(verify(json.loads(Path(sys.argv[1]).read_text())),indent=2))
