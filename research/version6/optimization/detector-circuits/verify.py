"""Exact formal identities, source-oracle samples, and quadratic-only census."""
import hashlib, importlib.util, json, sys
from fractions import Fraction
from pathlib import Path
from patch_builder import BASE, HERE
if len(sys.argv)>1:HERE=Path(sys.argv[1]).resolve()

def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
oracle=module('oracle',BASE/'oracle/check_oracle.py')
compiler=module('compiler',BASE/'compiler/compile_ir.py')
P=oracle.Poly

def sym_direct(ys):
    out=[P(1)]
    for y in ys:
        nxt=[P(0)]*(len(out)+1)
        for k,c in enumerate(out):nxt[k]=nxt[k]+c;nxt[k+1]=nxt[k+1]+c*y
        out=nxt
    return out

def sym_balanced(ys):
    if len(ys)==1:return [P(1),ys[0]]
    cut=len(ys)//2;a=sym_balanced(ys[:cut]);b=sym_balanced(ys[cut:]);out=[]
    for k in range(len(a)+len(b)-1):
        out.append(sum((a[i]*b[k-i] for i in range(max(0,k-len(b)+1),min(k,len(a)-1)+1)),P(0)))
    return out

identities=[]
for n in [2,4,10]:
    ys=[P.var('y'+str(i)) for i in range(n)]
    assert sym_direct(ys)==sym_balanced(ys)
    identities.append(f'balanced_product_degree_{n}')
    q=P.var('q');co=[P.var('c'+str(i)) for i in range(n+1)]
    h=co[-1]
    for c in reversed(co[:-1]):h=h*q+c
    powers=[P(1),q]
    for k in range(2,n+1):powers.append(powers[k//2]*powers[(k+1)//2])
    assert h==sum((c*p for c,p in zip(co,powers)),P(0))
    identities.append(f'power_basis_equals_horner_degree_{n}')

a,t,b=[P.var(x) for x in ['a','t','b']]
assert t*t-a*(a-2)*t*b+((a-2)*b)**2-1==t*t-(a*t)*((a-2)*b)+((a-2)*b)**2-1
identities.append('lucas_associative_regrouping')
x=P.var('x');roots=[Fraction(0),Fraction(1,2),Fraction(1),Fraction(-1,2399),Fraction(32,407)]
co=[Fraction(1)]
for root in roots:
    nx=[Fraction(0)]*(len(co)+1)
    for k,c in enumerate(co):nx[k]+=root*c;nx[k+1]+=c
    co=nx
old=P(1)
for root in roots:old=old*(x+root)
assert old==x*x*(x*x*(x+co[4])+co[3]*x+co[2])+co[1]*x+co[0]
identities.append('F5_quintic')

# Ring identities above apply in every commutative Q-algebra, including Q(sqrt(2)).
u,v,w,z=[P.var(x) for x in ['u','v','w','z']]
assert (u+v*P.var('s'))*(w+z*P.var('s'))==u*w+(u*z+v*w)*P.var('s')+v*z*P.var('s')**2
identities.append('field_product_coordinates_before_s_squared_equals_2')
r,i,f,g=[P.var(x) for x in ['r','inverse_r','f','g']]
assert r*(1+r*(f*i)**2)-(r+f*f)==f*f*(r*i-1)*(r*i+1)
assert r*((f*i)**2+r*(g*i)**2)-(f*f*i+g*g)==(f*f*i+g*g*(r*i+1))*(r*i-1)
identities.append('scalar_n0_quotient_modulo_r_inverse')
identities.append('scalar_n1_quotient_modulo_r_inverse')
A,d,F,q,e=[P.var(x) for x in ['scale','delta','F5','q1','e']]
assert e*F-(A*d)**5==F*(e-q*d**3)+d**3*(F*q-A**5*d**2)
identities.append('weight_residual_ideal_identity')

ir=json.loads((HERE/'raw-ir.json').read_text());inventory=json.loads((BASE/'source-review/source_inventory.json').read_text())
samples=[oracle.finite_sample(ir,inventory,1000003,seed) for seed in [7,19,31]]
translated=json.loads((HERE/'raw-translated-ir.json').read_text())
c=compiler.Compiler(translated);stats=c.reduce();c.normalize()
assert all(compiler.degree(p)<=2 for p in c.rows.values())
compiler.write_json(HERE/'reduced-ir.json',c.output())
compiler.write_json(HERE/'reduction-certificate.json',c.certificate)
report={'status':'pass','formal_identities':identities,'sample_checks':samples,'raw_coordinates':len(ir['coordinates']),'raw_residuals':len(ir['residuals']),'reduced_coordinates':len(c.coordinates),'reduced_residuals':len(c.rows),'reduction':stats,'max_residual_degree':max(map(compiler.degree,c.rows.values())),'sum_of_squares_degree_bound':4,'raw_sha256':hashlib.sha256((HERE/'raw-ir.json').read_bytes()).hexdigest()}
(HERE/'verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='sample_checks'},indent=2))
