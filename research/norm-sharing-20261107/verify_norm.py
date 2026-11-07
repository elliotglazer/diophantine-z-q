"""Check actual emitted scaled-norm gate formulas and their Laurent identity.

The compiler represents W0 as an affine expression, not one coordinate.
This checker compares entire expressions rather than treating a component
coordinate as if it were W0.
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

def add(a,b):
    c=a.copy()
    for k,v in b.items():
        c[k]=c.get(k,Q(0))+v
        if not c[k]:del c[k]
    return c

def scale(a,c):return {k:v*c for k,v in a.items() if v*c}
def mul(a,b):
    c={}
    for i,u in a.items():
        for j,v in b.items():c=add(c,{tuple(sorted(i+j)):u*v})
    return c

def decode(ts):
    out={}
    for t in ts:
        assert t['sPower']==0
        out=add(out,{tuple(t['monomial']):Q(t['coefficient'])})
    return out

def verify(raw):
    gates={g['coordinateId']:g for g in raw['gates']};values=raw['values']
    results=[]
    for r in range(9):
        p=f'detector{r}.'
        def value(n):return decode(values[p+n]['terms'])
        def quotient(n):
            x=value(n);assert len(x)==1
            (key,c),=x.items();assert len(key)==1 and c==1
            g=gates[key[0]];assert g['operation']=='rational_quotient'
            return decode(g['numerator']),decode(g['denominator'])
        def expand_last(n):
            x=value(n);i=max(j for m in x for j in m)
            g=gates[i];assert g['operation']=='quadratic_assignment'
            result={}
            for m,c in x.items():
                term={():c}
                for j in m:term=mul(term,decode(g['expression']) if j==i else {(j,):Q(1)})
                result=add(result,term)
            return result
        delta=add(value('t'),{():Q(-1)})
        assert expand_last('delta2')==mul(delta,delta)
        assert expand_last('w0Delta2')==mul(value('W.0'),value('delta2'))
        assert quotient('w0Inverse')==({():Q(1)},value('W.0'))
        numerator=scale(add(mul(value('W.0'),value('W.0')),scale(mul(value('W.1'),value('W.1')),-2)),Q(1,2))
        assert quotient('scaledNorm')==(numerator,value('w0Delta2'))
        assert quotient('Bsemantic')==(mul(value('scaledNorm'),value('scaledNorm')),value('q1'))
        assert expand_last('delta3')==mul(value('delta2'),delta)
        assert quotient('q1')==(value('eWeight'),value('delta3'))
        results.append({'detector':r,'status':'passed_actual_emitted_gate_formulas'})
    # Independent Laurent identity, with exponent order (e,delta,w0,w1).
    n={(0,-2,1,0):Q(1,2),(0,-2,-1,2):Q(-1)}
    b={}
    for i,u in n.items():
        for j,v in n.items():
            power=tuple(x+y+z for x,y,z in zip(i,j,(-1,3,0,0)))
            b=add(b,{power:u*v})
    assert b=={(-1,-1,2,0):Q(1,4),(-1,-1,0,2):Q(-1),(-1,-1,-2,4):Q(1)}
    return {'status':'passed','detectors':results,
        'identity':'B=(w0^2-2*w1^2)^2/(4*w0^2*e*delta)',
        'scope':'Actual gate formulas and exact Laurent identity; nonvanishing follows from the separate global argument'}

if __name__=='__main__':print(json.dumps(verify(json.loads(Path(sys.argv[1]).read_text())),indent=2))
