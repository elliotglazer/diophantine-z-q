"use strict";
const fs=require("node:fs"),path=require("node:path");
function arithmetic() {
 const assert=(x,m)=>{if(!x)throw Error(m||"assertion")};
 const abs=x=>x<0n?-x:x;
 const gcd=(x,y)=>{x=abs(x);y=abs(y);while(y){[x,y]=[y,x%y]}return x};
 const F=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);assert(d!==0n,"zero denominator");let g=gcd(n,d)*(d<0n?-1n:1n);return [n/g,d/g]};
 const rat=x=>{let [a,b="1"]=String(x).split("/");return F(a,b)};
 const plus=(a,b)=>F(a[0]*b[1]+b[0]*a[1],a[1]*b[1]);
 const times=(a,b)=>F(a[0]*b[0],a[1]*b[1]);
 const key=(k,e,r,m)=>[k,e,r,...m.slice().sort((a,b)=>a-b)].join(",");
 const unpack=k=>k.split(",").map(Number);
 function put(p,k,v){let a=plus(p.get(k)||F(0),v);if(a[0])p.set(k,a);else p.delete(k)}
 const mon=(a=1,k=0,e=0,r=0,m=[])=>{let v=Array.isArray(a)?a:rat(a);return v[0]?new Map([[key(k,e,r,m),v]]):new Map()};
 function add(...ps){let p=new Map();for(let q of ps)for(let [k,v] of q)put(p,k,v);return p}
 function mul(...ps){let p=mon();for(let q of ps){let z=new Map();for(let [a,x] of p)for(let [b,y] of q){let [k,e,r,...m]=unpack(a),[l,f,s,...n]=unpack(b);put(z,key(k+l,e+f,r+s,m.concat(n)),times(x,y))}p=z}return p}
 const sc=(p,a)=>mul(mon(a),p), sub=(p,q)=>add(p,sc(q,-1)), sq=p=>mul(p,p), X=i=>mon(1,0,0,0,[i]);
 function replace(p,fn){return add(...[...p].map(([k,a])=>{let [l,e,r,...m]=unpack(k);return mul(mon(a,l,e,r),...m.map(i=>fn(i)||X(i)))}))}
 function normal(p){assert(p.size,"zero row");let all=[...p.keys()].map(unpack);let lo=[0,1,2].map(i=>Math.min(...all.map(k=>k[i])));let z=new Map([...p].map(([k,a])=>{let [l,e,r,...m]=unpack(k);return [key(l-lo[0],e-lo[1],r-lo[2],m),a]}));let first=z.get([...z.keys()].sort()[0]);return new Map([...z].map(([k,a])=>[k,F(a[0]*first[1],a[1]*first[0])]))}
 function eq(p,q){return p.size===q.size&&[...p].every(([k,a])=>q.has(k)&&a[0]===q.get(k)[0]&&a[1]===q.get(k)[1])}
 const prop=(p,q)=>eq(normal(p),normal(q));
 const fp=(i,j=1)=>[X(i),sc(X(i+1),j)];
 const fs=(a,b)=>[sc(a[0],b),sc(a[1],b)];
 const fm=(a,b)=>[mul(a[0],b),mul(a[1],b)];
 const fa=(...ps)=>[add(...ps.map(a=>a[0])),add(...ps.map(a=>a[1]))];
 const fd=(a,b)=>fa(a,fs(b,-1));
 const fx=(a,b)=>[add(mul(a[0],b[0]),sc(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))];
 const fc=a=>[a[0],sc(a[1],-1)];
 return {assert,F,rat,mon,add,mul,sc,sub,sq,X,replace,normal,eq,prop,fp,fs,fm,fa,fd,fx,fc,unpack}
}
function verifyV82(data){
 const {assert,F,rat,mon,add,mul,sc,sub,sq,X,replace,normal,eq,prop,fp,fs,fm,fa,fd,fx,fc,unpack}=arithmetic();
 const [q,w,physical,maps,old,bb]=data;
 const lab=new Map(q.coordinates.map(v=>[v.id,v.source_id])),cw=w.weights;
 const units={400:1,401:-1,402:-2};
 const C=mon(1,1),c=mon(1,0,1),R=mon(1,0,0,1);
 const deleted=['inverse_vieta.','cleared.E2.0','cleared.E2.1','scalar.W2.','scalar.b.','scalar.p2.','scalar.firstConic','scalar.Bh.','scalar.q2.','scalar.secondConic','parity_scalar.','scalar.ratio1_unscaled_square.','scalar.r_power_2.','shared.c_unit','shared.c_inverse_square'];
 const map0={112:mon(1,-1,1,2),113:mon(1,-1,1,1),192:mon(1,0,1,-1,[192]),193:mon(1,0,1,-1,[193])};
 const change={};
 for(const [i,j] of [[68,66],[69,67]]){const a=X(i),b=X(j),m=mul(sub(a,b),mon(1,0,-2));change[i]=sc(add(a,b,m),F(1,2));change[j]=sc(sub(add(a,b),m),F(1,2))}
 let want=new Map();
 for(const row of q.residuals){let name=row.name;if(deleted.some(s=>name.startsWith(s)))continue;let p=add(...row.terms.map(t=>mul(mon(t.coefficient,t.parameterPower),...t.monomial.map(j=>{let i=lab.get(j);return i in units?mon(1,0,units[i]):mon(1,0,-cw[i],0,[i])}))));
 p=replace(p,i=>map0[i]);if(!name.startsWith("new.det0.factor2."))p=replace(p,i=>change[i]);want.set(name,p)}
 const f2=fm(fp(64,2),mon(1,0,-1)), S=fm(fp(17),mon(1,0,-1)), TH=fm(fp(150),mon(1,0,-1));
 const A=fm(fp(33),mon(1,1,-1)), FU=fm(fp(54,2),mon(1,1,-1)), FV=fm(fp(23,2),mon(1,1,-1));
 const Z=fp(102),J=fp(109),L=fd(J,f2), D=[mon(11),mon(-6)];
 const [U,V,W,rr,P,rr2]=[182,184,186,190,192,194].map(i=>fp(i));
 const M=fd(fs(S,-2),W),fresh={
 'v82.point.product':fd(fx(U,V),fx(L,P)),
 'v82.point.r':fd(fx(P,W),fm(rr,R)),
 'v82.point.sum':fa(fx(rr,fa(U,V,fs(W,-1),fs(S,-4))),fm(fx(D,L),R)),
 'v82.point.pair':fd(fa(fx(L,P),fx(W,fa(U,V))),fx(M,M)),
 'v82.point.r2':fd(rr2,fx(rr,rr)),
 'v82.point.fusquare':fd(fx(FU,rr2),fx(U,U)),
 'v82.point.fvsquare':fd(fx(FV,rr2),fx(V,V)),
 'v82.point.primary':fd(fx(A,fa(U,M)),fs(fx(S,Z),2)),
 'v82.comparison.E2':fd(fd(fm(fp(35),mon(1,0,-1)),fx(A,fc(fa(V,M)))),fs(fx(fc(TH),fc(Z)),2)),
 'v82.scalar.field':fd(fm(L,R),fx(Z,Z))};
 for(let [name,p] of Object.entries(fresh))for(let i=0;i<2;i++)want.set(name+"."+i,p[i]);
 want.set("v82.scalar.partial_trace",sub(mul(X(111),sc(L[0],2)),fx(J,fc(J))[0]));
 let [sig,B,E,U1,V1,P1,Q1,P2,Q2]=[104,105,11,12,107,13,14,106,108].map(X);
 const nrows={
 'v82.scalar.inverse':sub(mul(X(111),sig),mon(1,0,0,4)),
 'v82.scalar.input':sub(sub(mul(B,sig),sq(R)),sc(R,9792)),
 'v82.scalar.p2':sub(mul(sig,P2),sq(P1)),
 'v82.scalar.q2':sub(mul(sig,Q2),sq(Q1)),
 'v82.scalar.first':add(sc(sq(E),3),sc(mul(E,sig),-34),sc(sq(sig),-289),sc(mul(B,P2),17)),
 'v82.scalar.middle':sub(mul(E,sub(sc(sig,17),B)),sc(mul(U1,V1),17)),
 'v82.scalar.second':add(sq(U1),sc(mul(U1,V1),34),sc(sq(V1),-867),sc(mul(B,Q2),-17))};
 for(let [n,p] of Object.entries(nrows))want.set(n,p);
 // The fixed route specializes formal C=1 and substitutes its actual scalar anchor.
 for(let [n,p] of want){want.set(n,add(...[...p].map(([k,a])=>{let [l,e,r,...m]=unpack(k);return mon(a,0,e,r,m)})))}
 const AP=[23,149,263,337,631,1063,1093,1171,1439,2161,2437,2837,2851,3187,3343,3793].reduce((x,y)=>x*BigInt(y),1n);
 const BP=[263,2161,2437,2837,3793].reduce((x,y)=>x*BigInt(y),1n);
 want.set("scalar.forced_prime.definition",add(mon(),mon(25,0,-1,1,[101]),mon(-AP*BP**4n,0,-1,0,[101])));
 const srcmap=new Map(physical.rows.map(row=>[row.name,row]));
 function raw(row,change=null){return add(...row.terms.map(t=>{let co=change?change[String(t.coefficient)]:t.coefficient;assert(co!==undefined,row.name+" mapping "+t.coefficient);return mul(mon(co,t.parameter_power,t.c_power,t.R_power),...t.monomial.map(i=>i===112?mon(1,0,0,2):X(i)))}))}
 assert(srcmap.size===want.size,"physical row census "+srcmap.size+" "+want.size);
 for(let [n,row] of srcmap){assert(want.has(n)&&prop(raw(row),want.get(n)),"v82 physical "+n)}
 let labels=new Map(Object.entries(maps.source_labels).map(([k,v])=>[v,Number(k)]));
 assert(labels.size===179&&labels.get(1)===1&&maps.c_weights["1"]===0&&maps.R_weights["1"]===0&&maps.parameter_weights["1"]===0,"input");
 const Uvals={400:mon(1,0,1),401:mon(1,0,-1),402:mon(1,0,-2),112:mon(1,0,0,2),113:R,114:mon(1,0,0,-1)};
 function back(row){return add(...row.terms.map(t=>mul(mon(t.coefficient,t.parameterPower),...t.monomial.map(j=>{let i=labels.get(j);assert(i!==undefined,"coordinate");return Uvals[i]||mon(1,0,-maps.c_weights[i],-maps.R_weights[i],[i])}))))}
 const literal=(row)=>add(...row.terms.map(t=>mon(t.coefficient,t.parameterPower,0,0,t.monomial.map(i=>labels.get(i)))));
 const guard={
 'unit.c_inverse':sub(mul(X(400),X(401)),mon()),
 'unit.c_inverse_square':sub(X(402),sq(X(401))),
 'unit.R_square':sub(X(112),sq(X(113))),
 'unit.R_inverse':sub(mul(X(113),X(114)),mon())};
 const oldrows=new Map(old.residuals.map(r=>[r.name,r])),bbrows=new Map(bb.residuals.map(r=>[r.name,r]));
 assert(oldrows.size===151&&bbrows.size===151&&oldrows.size===want.size+4,"compiled row count");
 let changed=0;
 for(let [name,r] of oldrows){
 assert(r.terms.every(t=>t.monomial.length<=2),"degree");
 if(name in guard)assert(eq(literal(r),guard[name]),"guard "+name);else assert(prop(back(r),want.get(name)),"v82 compile "+name);
 let mapping=null;
 if(name.endsWith(".firstConic")||name==="v82.scalar.first")mapping={3:9,"-34":0,"-289":-9,17:7};
 if(name.endsWith(".Bh.definition")||name==="v82.scalar.middle")mapping={17:9,"-1":-7,"-17":-9};
 if(name.endsWith(".secondConic")||name==="v82.scalar.second")mapping={1:9,34:0,"-867":-9,"-17":-7};
 if(mapping){const b=bbrows.get("bbnative."+name);assert(b&&b.terms.every(t=>t.monomial.length<=2)&&prop(back(b),raw(srcmap.get(name),mapping)),"BB row "+name);changed++}
 else {assert(JSON.stringify(r)===JSON.stringify(bbrows.get(name)),"BB unchanged "+name)}
 }
 assert(changed===12,"BB changes");
 return {v82_physical_rows:want.size,v82_compiled_rows:oldrows.size,bb_compiled_rows:bbrows.size,bb_changed_rows:changed,guards:4};
}
const paths=["computation/coauthor_audit_v78/work_general/enhanced/180/quadrics.json","computation/coauthor_audit_v78/work_general/enhanced/180/weights.json","computation/variable_reductions_v82/general/source179.json","computation/variable_reductions_v82/general/quartic179/maps.json","computation/variable_reductions_v82/general/quartic179/quadrics.json","computation/bb_native_quartic_20261124/quartic179/quadrics.json"];
const d=paths.map(p=>JSON.parse(fs.readFileSync(path.join(__dirname,"source",p),"utf8")));
console.log(JSON.stringify(verifyV82(d)));
