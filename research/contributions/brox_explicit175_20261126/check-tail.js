"use strict";
const fs=require("node:fs"),path=require("node:path");
function verifyTail(data){
 const A=(b,m)=>{if(!b)throw Error(m||"assertion")}, abs=n=>n<0n?-n:n;
 const [q179,q178,q177,qdep,qal,cert,qrec,qfin,txt]=data;
 function key(k,e,m){return [k,e,...m.slice().sort((a,b)=>a-b)].join(",")}
 function decode(k){return k.split(",").map(Number)}
 function put(p,k,a){let b=(p.get(k)||0n)+a;if(b)p.set(k,b);else p.delete(k)}
 function mon(a=1,k=0,e=0,m=[]){return BigInt(a)?new Map([[key(k,e,m),BigInt(a)]]):new Map()}
 function add(...ps){let o=new Map();for(const p of ps)for(const [k,v] of p)put(o,k,v);return o}
 function mul(...ps){let o=mon();for(const p of ps){let r=new Map();for(const [a,x] of o)for(const [b,y] of p){let [k,e,...m]=decode(a),[l,f,...n]=decode(b);put(r,key(k+l,e+f,m.concat(n)),x*y)}o=r}return o}
 const sc=(p,b)=>mul(p,mon(b)),sub=(p,q)=>add(p,sc(q,-1)),sq=p=>mul(p,p),X=i=>mon(1,0,0,[i]),C=mon(1,2);
 function row(r){return add(...r.terms.map(t=>mon(t.coefficient,t.parameterPower,0,t.monomial)))}
 function rows(a){let o=new Map(a.residuals.map(r=>[r.name,row(r)]));A(o.size===a.residuals.length,"duplicate name");return o}
 const eq=(p,q)=>p&&q&&p.size===q.size&&[...p].every(([k,v])=>q.get(k)===v);
 const prop=(p,q)=>{if(!p||!q||!p.size||p.size!==q.size||[...p.keys()].some(k=>!q.has(k)))return false;let k=p.keys().next().value;return [...p].every(([k1,v])=>v*q.get(k)===q.get(k1)*p.get(k))};
 function compare(a,b,msg){A(a.size===b.size,msg+" census");for(const [k,v] of a)A(eq(v,b.get(k)),msg+" "+k)}
 function renum(p,j){return add(...[...p].map(([k,v])=>{let [l,e,...m]=decode(k);A(!m.includes(j),"undeleted coordinate "+j);return mon(v,l,e,m.map(i=>i-(i>j)))}))}
 const one=mon();
 // 179 -> 178: remove R^-1, rescale all native scalar pole coordinates and change the two aggregate rows.
 let old=rows(q179),newr=rows(q178);
 A(q179.variables===179&&q178.variables===178&&old.size===151&&newr.size===150,"179/178");
 A(eq(old.get("unit.R_inverse"),sub(mul(X(90),X(91)),one)),"R inverse guard");
 A(eq(old.get("unit.R_square"),sub(X(89),sq(X(90)))),"R square guard");
 old.delete("unit.R_inverse");
 let scaled=new Set([11,12,13,14,81,82,83,84,85]);
 let affected=[...old].filter(([n,r])=>[...r.keys()].some(k=>decode(k).slice(2).some(i=>scaled.has(i)))).map(([n])=>n).sort();
 let scalarNames=['v82.scalar.inverse','v82.scalar.input','v82.scalar.p2','v82.scalar.q2','bbnative.v82.scalar.first','bbnative.v82.scalar.middle','bbnative.v82.scalar.second'].sort();
 A(JSON.stringify(affected)===JSON.stringify(scalarNames),"weighted scalar support");
 for(let n of affected.filter(n=>!["v82.scalar.inverse","v82.scalar.input"].includes(n)))A([...old.get(n).keys()].every(k=>{let m=decode(k).slice(2);return m.length===2&&m.every(i=>scaled.has(i))}),"homogeneity "+n);
 for(const [name,v] of [["new.aggregate",114],["new.aggregate_shift",115]]){let r=old.get(name);A(r.get(key(0,0,[91,v]))===1n&&!r.has(key(0,0,[v])),"aggregate");r.delete(key(0,0,[91,v]));r.set(key(0,0,[v]),1n)}
 A(eq(old.get("v82.scalar.inverse"),sub(mul(X(81),X(88)),mul(X(89),X(90)))),"old inverse");
 A(eq(old.get("v82.scalar.input"),add(mon(-1),mul(X(81),X(82)),sc(X(91),-9792))),"old input");
 old.set("v82.scalar.inverse",sub(mul(X(81),X(88)),sq(X(89))));
 old.set("v82.scalar.input",add(sc(X(89),-1),mul(X(81),X(82)),sc(X(90),-9792)));
 compare(new Map([...old].map(([n,r])=>[n,renum(r,91)])),newr,"weighted");
 // Harmonic: change the scalar and unscale the retained input-square register.
 old=newr;newr=rows(q177);
 const changed=new Set(["inputSquare.definition","scalar.rPair1.definition","scalar.four_contact_product.definition","scalar.forced_prime.definition","input.cleared.0","input.cleared.1"]);
 for(const [n,r] of old)if([...r.keys()].some(k=>decode(k).slice(2).some(i=>i===37||i===77)))A(changed.has(n),"scalar changed occurrence "+n);
 for(let n of changed)A(old.has(n),"missing old row "+n);
 let exp=new Map([...old].filter(([n])=>!changed.has(n)).map(([n,r])=>[n,renum(r,77)]));
 const k=2n**20n, K=3n*2n**15n*211n;
 exp.set("inputSquare.definition",sub(sq(X(1)),X(37)));
 exp.set("scalar.harmonicA",add(X(77),mon(-2401n*343n),sc(X(37),-k*(2401n*375n+2400n*343n)),sc(sq(X(37)),-k*k*2400n*375n)));
 exp.set("scalar.harmonicR",sub(mul(add(X(77),one,sc(X(37),k)),X(89)),mul(sc(C,K),X(77),add(one,sc(X(37),k)))));
 for(let i=0;i<2;i++)exp.set("input.cleared."+i,add(sc(X(17+i),-1),X(23+i),mul(add(sc(X(37),51),mon(2504)),X(116+i))));
 A(q177.variables===177&&newr.size===149,"177 census");
 compare(exp,newr,"harmonic");
 // Depressed cubic: only two rows change, primitive row proportionality checked.
 old=newr;newr=rows(qdep);exp=new Map([...old].filter(([n])=>!["scalar.harmonicA","scalar.harmonicR"].includes(n)));
 let W=add(sc(X(37),36000n*k),mon(34981)),T=X(77),K0=sc(C,18536),V=sub(X(89),K0),L=sub(sc(T,432000000),sc(V,1053721));
 A(prop(newr.get("scalar.depressed.first"),add(sc(mul(W,L),3),sc(K0,2163135238n))),"depressed first");
 A(prop(newr.get("scalar.depressed.second"),add(sc(mul(T,L),1944000000),sc(mul(K0,W,V),1081567619))),"depressed second");
 for(const n of ["scalar.depressed.first","scalar.depressed.second"])exp.set(n,newr.get(n));
 compare(exp,newr,"depressed");
 // Aligned gates: old variables retained except x72,x171; u powers eliminate c/u/v guards.
 const p=cert.config,drop=p.drop,keep=Array.from({length:177},(_,i)=>i+1).filter(i=>!drop.includes(i)),ix=new Map(keep.map((i,j)=>[i,j+1]));
 A(JSON.stringify(drop)===JSON.stringify([72,171])&&p.c===160&&p.u===161&&p.v===162,"aligned certificate");
 A(!p.chg["1"]&&!drop.includes(1),"input retained");
 const unit=i=>i===p.c?mon(1,0,-1):i===p.u?mon(1,0,1):i===p.v?mon(1,0,2):X(i);
 function subtwo(j){const s=cert.substitutions[String(j)];if(!s)return sc(unit(j),2);
 return add(...s.map(([e,m,a,b])=>{A(e===0&&m.length<=1&&BigInt(b)===2n&&!m.some(i=>drop.includes(i)),"affine substitution");return sc(m.length?unit(m[0]):one,BigInt(a))}))}
 function embed(r,isOld,substitute=true){
 return add(...r.terms.map(t=>{
 let m=t.monomial,fac=mon(BigInt(t.coefficient)*(substitute&&isOld?2n**BigInt(2-m.length):1n),t.parameterPower,isOld?-(p.exps[r.name]||0):0);
 return mul(fac,...m.map(i=>{let j=isOld?i:keep[i-1];return isOld?mul(mon(1,0,p.chg[String(j)]||0),substitute?subtwo(j):unit(j)):unit(j)}))
 }));
 }
 let alrows=new Map(qal.residuals.map(r=>[r.name,r])),drows=new Map(qdep.residuals.map(r=>[r.name,r]));
 const g=["unit.c_inverse","unit.c_inverse_square"];
 for(const n of g){let b=alrows.get(n),a=drows.get(n);A(JSON.stringify(a.terms.map(t=>({...t,monomial:t.monomial.map(i=>ix.get(i))})))===JSON.stringify(b.terms),"aligned literal guard "+n)}
 // Check actual equations before affine substitutions against the three displayed gates, then all remaining pullbacks.
 const uu=unit(161),vv=unit(162),gate0=add(sc(X(63),2),sc(X(152),-1),sc(sq(X(156)),-1),sc(X(157),-1),sc(uu,2),sc(vv,-1)),
 gate1=add(sc(X(72),2),sc(X(153),-1),sc(sq(X(156)),-1),sc(X(158),-1),sc(uu,2),sc(vv,-1)),
 gate2=add(sc(X(171),2),X(152),X(153),sc(sq(X(156)),-1),sc(X(159),-1),uu,sc(vv,-1));
 for(let j=0;j<3;j++)A(prop(embed(drows.get("shared.gate"+j),true,false),[gate0,gate1,gate2][j]),"gate before elimination "+j);
 let removed=[];
 for(const [n,r] of drows){if(g.includes(n))continue;let b=alrows.get(n);if(!b){removed.push(n);b=alrows.get("shared.gate0")}A(prop(embed(r,true),embed(b,false)),"aligned "+n)}
 A(JSON.stringify(removed.sort())===JSON.stringify(["shared.gate1","shared.gate2"]),"removed gates");
 A(qal.variables===175&&alrows.size===147&&alrows.size===drows.size-2,"aligned census");
 // Reciprocal cubic: re-interpret register 76 only; all other rows literally unchanged.
 old=rows(qal);newr=rows(qrec);exp=new Map([...old].filter(([n])=>!["scalar.depressed.first","scalar.depressed.second"].includes(n)));
 A([...exp.values()].every(r=>[...r.keys()].every(m=>!decode(m).slice(2).includes(76))),"reciprocal occurrence");
 W=add(sc(X(37),36000n*k),mon(34981));T=X(76);V=sub(X(88),K0);
 exp.set("scalar.depressed.reciprocal",sub(mul(W,T),one));
 exp.set("scalar.depressed.linearized",add(mul(sub(W,sc(T,3161163)),V),sc(mul(K0,sq(T)),2163135238)));
 compare(exp,newr,"reciprocal");
 // Projective contacts.
 old=newr;newr=rows(qfin);exp=new Map(old);let pp=[1n];for(const r of [77n,23n,21n,75n,51n]){let v=Array(pp.length+1).fill(0n);pp.forEach((c,i)=>{v[i]-=r*r*c;v[i+1]+=c});pp=v}
 A(pp.join(",")==="-20236648618580625,98933750608581,-151547683050,77366218,-15125,1","contact polynomial");
 for(const [i,chart] of [[0,[2,60,61,62,156]],[1,[68,69,70,71,157]],[2,[162,167,168,169,158]]]){
 const [t,r,s,d,w]=chart.map(X),pre="additive.detector"+i+".";
 let repl={contactSquare:sub(sc(sq(t),1024),r),contactCombination:sub(add(mul(r,s),mul(add(one,w),add(sc(r,pp[3]),sc(s,pp[4])))),d),contactRelation:add(mul(s,d),mul(add(one,w),add(sc(r,pp[1]),sc(s,pp[2]),mon(pp[0]))))};
 A(eq(old.get(pre+"contactFourthPower"),sub(sq(r),s))||eq(old.get(pre+"contactFourthPower"),sub(s,sq(r))),"fourth power");
 for(const [n,v] of Object.entries(repl)){A(!eq(old.get(pre+n),v),"replacement unchanged");exp.set(pre+n,v)}
 }
 compare(exp,newr,"projective");
 function expand(q,N){let a=new Map(),C=N===null?1n:331n**BigInt(N);for(const r of q.residuals){
 let p=new Map();for(const t of r.terms){A(t.monomial.length<=2,"degree");put(p,t.monomial.slice().sort((x,y)=>x-y).join(","),BigInt(t.coefficient)*C**BigInt(t.parameterPower))}
 for(let [m,x] of p)for(let [n,y] of p){let a1=m?m.split(",").map(Number):[],b1=n?n.split(",").map(Number):[];put(a,a1.concat(b1).sort((x,y)=>x-y).join(","),x*y)}
 }return a}
 let pol=expand(qfin,21),as=[...pol].map(([k,v])=>[k?k.split(",").map(Number):[],v]).sort(([a],[b])=>{for(let i=0;i<Math.min(a.length,b.length);i++)if(a[i]!==b[i])return a[i]-b[i];return a.length-b.length});
 let literal="",vars=new Set(),height=0,degree=0;
 for(let [m,v] of as){let f=[];for(let i=0;i<m.length;){let j=i+1;while(j<m.length&&m[j]===m[i])j++;f.push("x"+m[i]+(j-i>1?"^"+(j-i):""));vars.add(m[i]);i=j}degree=Math.max(degree,m.length);height=Math.max(height,abs(v).toString(2).length);let a=abs(v)===1n&&f.length?"":abs(v).toString();literal+=(v<0n?"-":literal?"+":"")+a+(a&&f.length?"*":"")+f.join("*")}
 A(qfin.variables===175&&qfin.input===1&&newr.size===147&&pol.size===3196&&height===802&&degree===4&&vars.size===175&&[...vars].every(i=>i>=1&&i<=175)&&pol.get("1,1,1,1")===1n&&literal===txt&&literal.length===73080,"final expansion");
 // Contact and anchor constants, and Euler product outside the exceptional set.
 const S=[2,3,5,7,11,13,17,19,23,37,41,2399],P=S.reduce((a,b)=>a*BigInt(b),1n);
 const numerator=74712001n*2n**68n*3n**16n*5n**16n*7n**4n*P**2n*S.reduce((a,b)=>a*BigInt(b+1),1n),denominator=1000000n*P;
 A(P===811898089212210n&&numerator<denominator*2n**249n&&numerator>denominator*2n**68n,"contact constants");
 function strip(n){n=abs(n);A(n!==0n,"contact zero");for(let p of S.map(BigInt))while(n%p===0n)n/=p;return n}
 const radii=[-77n,23n,21n,-75n,51n];A(radii.every(a=>strip(a)===1n),"radii");for(let i=0;i<5;i++)for(let j=0;j<i;j++)A(strip(radii[i]+radii[j])===1n&&strip(radii[i]-radii[j])===1n,"contact difference");
 let en=1n,ed=1n;for(let p=2;p<=1000;p++){let prime=true;for(let j=2;j*j<=p;j++)if(p%j===0){prime=false;break}if(prime&&!S.includes(p)){en*=BigInt(p+1);ed*=BigInt(p)}}
 A(10n*en<21n*ed,"Euler product");A(331n**97n>2n**810n&&2n**21n*(36036n-2835n)>526500n*36036n,"endpoint");
 const cubic=s=>(2401n+2400n*s)*(343n+375n*s)*(1n+s);
 for(let x=0n;x<331n;x++){let r=cubic(k*x*x);A(r%331n!==0n&&(25920000n*r+1081567619n)%331n!==0n,"331 anchor")}
 // All four evaluations prove the depressed cubic identity, since both expressions have degree <=3.
 for(let s of [0n,1n,-2n,3n]){
 let w=36000n*s+34981n;
 A(25920000n*cubic(s)===-1081567619n+ (w*w*w-3161163n*w)/2n || (2n*25920000n*cubic(s)===-2163135238n+w*w*w-3161163n*w),"depressed identity");
 }
 return {weighted_rows:150,harmonic_rows:149,depressed_rows:149,aligned_rows:147,aligned_deleted:removed,reciprocal_rows:147,projective_rows:147,final_variables:175,monomials:3196,degree:4,content:1,height_bits:802,ascii_bytes:73080,anchor_residues:331,contact_constant_lt_2_pow_249:true,small_prime_Euler_bound:true}
}
const paths=["computation/bb_native_quartic_20261124/quartic179/quadrics.json","computation/weighted_explicit178_20261124/quadrics.json","computation/harmonic_scalar_20261125/quartic177.json","computation/depressed_scalar_20261125/quartic177.json","computation/aligned_gate_20261125/quartic175.json","computation/aligned_gate_20261125/certificate175.json","computation/reciprocal_depressed_scalar_20261126/quartic175.json","computation/projective_contacts_20261126/quadrics.json","computation/projective_contacts_20261126/expanded175.txt"];
const d=paths.map(p=>{const s=fs.readFileSync(path.join(__dirname,"source",p),"utf8");return p.endsWith(".json")?JSON.parse(s):s;});
console.log(JSON.stringify(verifyTail(d)));
