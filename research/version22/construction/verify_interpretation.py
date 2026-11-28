"""Direct arithmetic interpretation of final rows, using exact Laurent polynomials."""
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
import json
ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
DATA=ROOT/'construction/inputs/quadrics.json'
OUTPUT=REPO/'build/version22'
OUTPUT.mkdir(parents=True,exist_ok=True)
def mon(a=1,c=0,u=0,r=0,m=()):
    return {(c,u,r,tuple(sorted(m))):F(a)} if a else {}
def add(*ps):
    d=defaultdict(F)
    for p in ps:
        for k,a in p.items():d[k]+=a
    return {k:a for k,a in d.items() if a}
def mul(*ps):
    out=mon()
    for p in ps:
        d=defaultdict(F)
        for (c,u,r,m),a in out.items():
            for (cc,uu,rr,mm),b in p.items():d[c+cc,u+uu,r+rr,tuple(sorted(m+mm))]+=a*b
        out={k:a for k,a in d.items() if a}
    return out
def sc(p,a):return mul(mon(a),p)
def sub(p,q):return add(p,sc(q,-1))
def sq(p):return mul(p,p)
def X(j):
    return {159:mon(u=-1),160:mon(u=1),161:mon(u=2),87:mon(r=2),88:mon(r=1)}.get(j,mon(m=(j,)))
def fp(j,a=1):return X(j),sc(X(j+1),a)
def fa(*ps):return tuple(add(*(p[i] for p in ps)) for i in (0,1))
def fs(p,a):return tuple(sc(x,a) for x in p)
def fm(p,q):return tuple(mul(x,q) for x in p)
def fd(p,q):return fa(p,fs(q,-1))
def fx(p,q):return add(mul(p[0],q[0]),sc(mul(p[1],q[1]),2)),add(mul(p[0],q[1]),mul(p[1],q[0]))
def fc(p):return p[0],sc(p[1],-1)
one=mon(); zero={}; fone=(one,zero); u=X(160); R=X(88); K=mon(18536,c=2)
def normal(p):
    assert p
    lower=[min(k[i] for k in p) for i in range(3)]
    d={(c-lower[0],u-lower[1],r-lower[2],m):a for (c,u,r,m),a in p.items()}
    a=d[min(d)];return {k:v/a for k,v in d.items()}
rows=json.loads(DATA.read_text())['residuals']
actual={r['name']:add(*(mul(mon(t['coefficient'],c=t['parameterPower']),*(X(i) for i in t['monomial'])) for t in r['terms'])) for r in rows}
seen=[]
def check(name,p):
    assert normal(actual[name])==normal(p),name
    seen.append(name)
def group(name,p):
    for i in (0,1):
        key=name+'.'+str(i)
        check(key if key in actual else key+'.definition',p[i])

check('inputSquare.definition',sub(sq(X(1)),X(37)))
W=add(sc(X(37),36000*2**20),mon(34981));T=X(76)
check('scalar.depressed.reciprocal',sub(mul(W,T),one))
check('scalar.depressed.linearized',add(mul(sub(W,sc(T,3161163)),sub(R,K)),sc(mul(K,sq(T)),2163135238)))
S=fp(17);TH=fp(101);f=fp(15);f2=fp(50,2);Z=fp(77);Jh=fp(84);L=fd(Jh,f2)
group('v82.scalar.field',fd(fm(L,R),fx(Z,Z)))
check('v82.scalar.partial_trace',sub(mul(X(86),sc(L[0],2)),fx(Jh,fc(Jh))[0]))
U,V,Wp,rr,P,rr2=fp(103),fp(105),fp(107),fp(109),fp(111),fm(fp(113),mon(u=-1))
M=fd(fs(S,-2),Wp);D0=(mon(11),mon(-6));A=fp(27)
for name,res in {
 'product':fd(fx(U,V),fx(L,P)), 'r':fd(fx(P,Wp),fm(rr,R)),
 'sum':fa(fx(rr,fa(U,V,fs(Wp,-1),fs(S,-4))),fm(fx(D0,L),R)),
 'pair':fd(fa(fx(L,P),fx(Wp,fa(U,V))),fx(M,M)),
 'r2':fd(rr2,fx(rr,rr)),
 'fusquare':fd(fx(fm(fp(44,2),u),rr2),fx(U,U)),
 'fvsquare':fd(fx(fm(fp(21,2),u),rr2),fx(V,V)),
 'primary':fd(fx(A,fa(U,M)),fs(fx(S,Z),2))}.items():group('v82.point.'+name,res)
E2=fm(fp(29),mon(u=2))
group('v82.comparison.E2',fd(fd(E2,fx(A,fc(fa(V,M)))),fs(fx(fc(TH),fc(Z)),2)))
charts={1:[fp(115),fp(117),fp(119),fm(fp(121),mon(u=-1)),fp(123),fm(fp(125),mon(u=-1))],
 3:[fp(127),fp(129),fp(131),fm(fp(133),mon(u=-1)),fp(135),fm(fp(137),mon(u=-1))],
 4:[fp(139),fp(141),fm(fp(143),u),fp(145),fp(147),fm(fp(149),u)]}
Es={1:fm(fp(25),u),3:fp(31),4:fp(35)}
aggregate=P
for role,(ss,tt,ff,gg,hh,dd) in charts.items():
    pp=fa(hh,ss,tt)
    for name,res in {'d_piF':fd(dd,fx(pp,ff)),'d_Gh':fd(dd,fx(hh,gg)),
      'sum':fa(fd(fx(D0,fa(ff,gg)),fx(fd(ss,tt),hh)),fx(tt,tt)),
      'unit':fa(fd(fone,fx(dd,fd(ss,tt))),fx(D0,fx(ff,gg)))}.items():group('new'+str(role)+'.'+name,res)
    group('cleared.E'+str(role),fd(Es[role],fd(fx(S,fc(tt)),fx(fc(TH),ss))))
    aggregate=fa(aggregate,fx(hh,pp))
check('new.aggregate',add(sc(sub(X(2),X(68)),2),mon(26),aggregate[0]))
check('new.aggregate_shift',add(sc(sub(add(X(2),X(162)),sc(X(68),2)),2),mon(-8),aggregate[1]))
N=fp(23);beta=add(mon(2504),sc(X(37),51));group('input.cleared',fd(N,fd(S,fm(charts[1][0],beta))))
calC,calP,calQ,H=fp(38),fp(33),fp(40),fm(fp(42,2),u);ss4=charts[4][0]
group('homogeneous.C',fd(calC,fx(fd(A,fone),fa(ss4,fs(S,4)))))
group('homogeneous.Q',fd(calQ,fx(fa(A,fone),calP)))
group('homogeneous.H',fd(H,fd(fd(fa(fx(calP,calP),fx(calC,calC)),fx(calC,calQ)),fx(ss4,ss4))))
group('homogeneous.P.ratio',fd(fx(calP,charts[3][0]),fs(fx(S,ss4),2)))
# Paired registers are explicitly inverted in the text; their determinants are units.
group('cleared.E1.square',fd(fs(fx(Es[1],Es[1]),2),fd(fm(fp(48),mon(u=2)),fm(fp(46),u))))
group('input.cleared.square',fd(fs(fx(N,N),2),fa(fp(46),fm(fp(48),u))))
group('cleared.E2.square',fd(fs(fx(E2,E2),2),fd(fm(fp(54),mon(u=4)),fm(fp(52),mon(u=5)))))
group('cleared.E3.square',fd(fs(fx(Es[3],Es[3]),2),fa(fm(fp(52),mon(u=2)),fm(fp(54),u))))
group('cleared.E4.square',fd(fs(fx(Es[4],Es[4]),2),fa(fm(fp(56),u),fm(fp(58),mon(u=2)))))
group('homogeneous.H.square',fd(fs(fx(H,H),2),fd(fm(fp(56),mon(u=2)),fm(fp(58),mon(u=3)))))
group('shared.partial_pair',fd(fm(fp(174),mon(u=-3)),fa(charts[1][2],fm(charts[4][2],mon(u=-1)))))
# Product rows give W=F0 F1 F2 F3 under the displayed output scales.
group('amplified.det0.product1',fd(fx(fp(89),fp(91)),fm(fp(97),mon(u=2))))
group('amplified.det0.product2',fd(fx(fp(93),fp(97)),fm(fp(99),mon(u=2))))
group('amplified.det0.product3',fd(fx(fp(95),fp(99)),fm(fp(153),mon(u=2))))
Wfield=fm(fp(153),mon(u=-1));D=mul(X(155),mon(u=-1))
check('shared.norm_error',sub(mul(sc(Wfield[0],2),D),fx(fd(Wfield,fone),fc(fd(Wfield,fone)))[0]))
Q=[X(151),X(152),sub(u,add(X(151),X(152)))];B=[X(64),X(72),X(170)]
G=[X(63),add(X(63),sc(sub(add(X(152),X(157)),add(X(151),X(156))),F(1,2))),add(X(63),sc(add(sc(X(151),-2),sc(X(152),-1),X(158),u,sc(X(156),-1)),F(1,2)))]
check('shared.gate0',sub(sc(G[0],2),add(mon(u=2),sq(X(155)),X(156),sc(u,-2),Q[0])))
for j,ids in enumerate([(2,60,61,62,156),(68,69,70,71,157),(162,167,168,169,158)]):
    t,r,s,v,w=map(X,ids);pre='additive.detector'+str(j)+'.'
    for n,p in {'contactSquare':sub(sc(sq(t),1024),r),'contactFourthPower':sub(sq(r),s),
      'contactCombination':sub(add(mul(r,s),mul(add(one,w),add(sc(r,77366218),sc(s,-15125)))),v),
      'contactRelation':add(mul(s,v),mul(add(one,w),add(sc(r,98933750608581),sc(s,-151547683050),mon(-20236648618580625))))}.items():check(pre+n,p)
    check('shared.inverse'+str(j),sub(mul(Q[j],w),mon(u=2)))
    check('balanced.detector'+str(j)+'.poleInput.definition',sub(sc(mul(B[j],add(Q[j],mon(u=2))),167281),sc(sq(G[j]),166464)))
# Native rows are checked without divisions by native witnesses.
for j,(ei,pi,Ui,Vi,qi,ps,qs) in enumerate([(3,5,4,66,6,65,67),(7,9,8,74,10,73,75),(163,165,164,172,166,171,173)]):
    if j<2:
        e=mul(X(ei),mon(r=-2));p=mul(X(pi),mon(u=1,r=-2));a=mul(X(Ui),mon(u=-1,r=-1));b=mul(X(Vi),mon(u=-1,r=-1));q=mul(X(qi),mon(r=-2 if j==0 else -1,u=0 if j==0 else -1))
    else:e=mul(X(ei),mon(u=-2));p=mul(X(pi),mon(u=-1));a=mul(X(Ui),mon(u=-2));b=mul(X(Vi),mon(u=-2));q=mul(X(qi),mon(u=-2))
    # Replace squared auxiliaries using their own literal square-register equations.
    # Comparing the three conics after substitution is performed by elimination below.
    prefix='detector'+str(j)
    native=[sub(add(sq(e),mul(mon(F(7,9),u=-2),B[j],sq(p))),one),sub(mul(a,b),mul(e,sub(one,mul(mon(F(7,9),u=-2),B[j])))),sub(sub(sq(a),sq(b)),mul(mon(F(7,9),u=-2),B[j],sq(q)))]
    # Solve each p2/q2 row for its square-register variable, whose coefficient is a unit monomial.
    env={}
    def subst(poly):
        return add(*(mul(mon(val,c=k[0],u=k[1],r=k[2]),*(env.get(i,X(i)) for i in k[3])) for k,val in poly.items()))
    for reg,n in [(ps,prefix+'.p2.definition'),(qs,prefix+'.q2.definition')]:
        p0=actual[n]; hit=[(k,a0) for k,a0 in p0.items() if reg in k[3]];assert len(hit)==1
        key,aa=hit[0];assert key[3]==(reg,)
        env[reg]=mul(mon(-1/aa,c=-key[0],u=-key[1],r=-key[2]),{k:v for k,v in p0.items() if k!=key});seen.append(n)
    for n,p0 in zip(['firstConic','Bh.definition','secondConic'],native):
        name='bbnative.'+prefix+'.'+n;assert normal(subst(actual[name]))==normal(p0),name;seen.append(name)

# Finish scalar equations without ever making a native witness a unit.
check('testSquare.40.0.0.definition',sub(mul(X(15),X(16)),X(51)))
check('testSquare.40.0.1.definition',sub(add(sq(X(15)),sc(sq(X(16)),2)),X(50)))
check('v82.scalar.inverse',sub(mul(X(79),X(86)),mon(r=4)))
check('v82.scalar.input',sub(mul(X(79),X(80)),add(mon(r=2),mon(9792,r=1))))
check('v82.scalar.p2',sub(mul(X(79),X(81)),sq(X(13))))
check('v82.scalar.q2',sub(mul(X(79),X(83)),sq(X(14))))
check('bbnative.v82.scalar.first',add(sc(sq(X(11)),9),sc(sq(X(79)),-9),sc(mul(X(80),X(81)),7)))
check('bbnative.v82.scalar.middle',add(sc(mul(X(11),X(79)),9),sc(mul(X(11),X(80)),-7),sc(mul(X(12),X(82)),-9)))
check('bbnative.v82.scalar.second',add(sc(sq(X(12)),9),sc(sq(X(82)),-9),sc(mul(X(80),X(83)),-7)))
# Guards are checked before Laurent reduction, since reduction would erase them.
for name,terms in {
 'unit.c_inverse':{():-1,(159,160):1},'unit.c_inverse_square':{(160,160):-1,(161,):1},
 'unit.R_square':{(87,):1,(88,88):-1}}.items():
 r0=next(r for r in rows if r['name']==name)
 assert all(t['parameterPower']==0 for t in r0['terms'])
 assert {tuple(t['monomial']):int(t['coefficient']) for t in r0['terms']}==terms
 seen.append(name)
# The six reference equations literally reduce to the retained 195-source rows.
repo=REPO;source=repo/'research/contributions/brox_explicit175_20261126/source/computation/quartic/seven_units193_v74/source/source195.json'
parent=repo/'research/version21/construction/inputs/brox229/source/quadratic195.json'
assert source.read_bytes()==parent.read_bytes()
old=json.loads(source.read_text())
remap={64:X(50),65:X(51),77:one,78:one,150:X(101),151:X(102)}
for row in old['residuals']:
 if row['name'].startswith('sharedT.reference.'):
  expected=add(*(mul(mon(t['coefficient'],c=t['parameterPower']),*(remap.get(i,X(i)) for i in t['monomial'])) for t in row['terms']))
  check(row['name'],expected)
# Substitute the invertible paired square registers, then check each whole factor.
helper={}
def assign(pair,value):
 helper[pair]=value[0];helper[pair+1]=value[1]
N2=fx(N,N);E12=fx(Es[1],Es[1]);E22=fx(E2,E2);E32=fx(Es[3],Es[3]);E42=fx(Es[4],Es[4]);H2=fx(H,H)
assign(46,fd(N2,fm(E12,mon(u=-1))))
assign(48,fa(fm(N2,mon(u=-1)),fm(E12,mon(u=-2))))
assign(52,fd(fm(E32,mon(u=-2)),fm(E22,mon(u=-5))))
assign(54,fa(fm(E32,mon(u=-1)),fm(E22,mon(u=-4))))
assign(56,fa(fm(E42,mon(u=-1)),fm(H2,mon(u=-2))))
assign(58,fd(fm(E42,mon(u=-2)),fm(H2,mon(u=-3))))
assign(174,fm(fa(charts[1][2],fm(charts[4][2],mon(u=-1))),mon(u=3)))
def substitute(poly):
 return add(*(mul(mon(a,c=c,u=u0,r=r),*(helper.get(i,X(i)) for i in m)) for (c,u0,r,m),a in poly.items()))
def fourth(p):return fx(fx(p,p),fx(p,p))
def scaled(p,n):return fm(p,mon(u=-n))
factors=[
 fa(fone,scaled(fourth(N),5),scaled(fx(fc(charts[1][3]),fc(charts[1][3])),2),fs(scaled(fourth(Es[1]),7),-1),scaled(fx(f2,f2),4)),
 fa(fone,scaled(fourth(Es[4]),5),scaled(fx(charts[3][2],charts[3][2]),2),fs(scaled(fourth(H),7),-1),scaled(fx(fm(fc(fp(21,2)),u),fm(fc(fp(21,2)),u)),4)),
 fa(fone,scaled(fourth(Es[3]),5),scaled(fx(fc(charts[4][3]),fc(charts[4][3])),2),fs(scaled(fourth(E2),11),-1),scaled(fx(fm(fp(44,2),u),fm(fp(44,2),u)),4)),
 fa(fone,scaled(fx(charts[1][2],charts[1][2]),1),scaled(fx(fc(charts[3][3]),fc(charts[3][3])),2),fs(scaled(fx(charts[4][2],charts[4][2]),3),-1),scaled(fx(fc(fp(19,2)),fc(fp(19,2))),4))]
outputs=[fm(fp(89),mon(u=-2)),fp(91),fp(93),fm(fp(95),mon(u=-5))]
for j,(factor,output) in enumerate(zip(factors,outputs)):
 for i in (0,1):
  name='new.det0.factor'+str(j)+'.'+str(i)
  assert normal(substitute(actual[name]))==normal(fd(factor,output)[i]),name
  seen.append(name)
assert len(seen)==147 and len(set(seen))==147

report={'verified_rows':len(seen),'total_rows':len(rows),'remaining_rows':[r['name'] for r in rows if r['name'] not in seen],
 'scope':'Direct finite arithmetic-to-row identities; not proof acceptance.'}
(OUTPUT/'direct-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
