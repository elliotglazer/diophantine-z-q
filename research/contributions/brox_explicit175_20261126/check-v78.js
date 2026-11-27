"use strict";
const fs=require("node:fs"),path=require("node:path");
function arithmetic() {
 const assert=(x,m)=>{if(!x)throw Error(m||"assertion")};
 const abs=x=>x<0n?-x:x;
 const gcd=(x,y)=>{x=abs(x);y=abs(y);while(y){[x,y]=[y,x%y]}return x};
 const F=(n,d=1n)=>{n=BigInt(n);d=BigInt(d);assert(d!==0n,"zero denominator");let g=gcd(n,d)*(d<0n?-1n:1n);return [n/g,d/g]};
 const rat=x=>{let [a,b="1"]=String(x).split("/");return F(a,b)};
 const plus=(a,b)=>F(a[0]*b[1]+b[0]*a[1],a[1]*b[1]),times=(a,b)=>F(a[0]*b[0],a[1]*b[1]);
 const key=(k,e,r,m)=>[k,e,r,...m.slice().sort((a,b)=>a-b)].join(","),unpack=k=>k.split(",").map(Number);
 function put(p,k,v){let a=plus(p.get(k)||F(0),v);if(a[0])p.set(k,a);else p.delete(k)}
 const mon=(a=1,k=0,e=0,r=0,m=[])=>{let v=Array.isArray(a)?a:rat(a);return v[0]?new Map([[key(k,e,r,m),v]]):new Map()};
 function add(...ps){let p=new Map();for(let q of ps)for(let [k,v] of q)put(p,k,v);return p}
 function mul(...ps){let p=mon();for(let q of ps){let z=new Map();for(let [a,x] of p)for(let [b,y] of q){let [k,e,r,...m]=unpack(a),[l,f,s,...n]=unpack(b);put(z,key(k+l,e+f,r+s,m.concat(n)),times(x,y))}p=z}return p}
 const sc=(p,a)=>mul(mon(a),p),sub=(p,q)=>add(p,sc(q,-1)),sq=p=>mul(p,p),X=i=>mon(1,0,0,0,[i]);
 function replace(p,fn){return add(...[...p].map(([k,a])=>{let [l,e,r,...m]=unpack(k);return mul(mon(a,l,e,r),...m.map(i=>fn(i)||X(i)))}))}
 function normal(p){assert(p.size,"zero row");let all=[...p.keys()].map(unpack);let lo=[0,1,2].map(i=>Math.min(...all.map(k=>k[i])));let z=new Map([...p].map(([k,a])=>{let [l,e,r,...m]=unpack(k);return [key(l-lo[0],e-lo[1],r-lo[2],m),a]}));let first=z.get([...z.keys()].sort()[0]);return new Map([...z].map(([k,a])=>[k,F(a[0]*first[1],a[1]*first[0])]))}
 function eq(p,q){return p.size===q.size&&[...p].every(([k,a])=>q.has(k)&&a[0]===q.get(k)[0]&&a[1]===q.get(k)[1])}
 const prop=(p,q)=>eq(normal(p),normal(q));
 const fp=(i,j=1)=>[X(i),sc(X(i+1),j)],fs=(a,b)=>[sc(a[0],b),sc(a[1],b)],fm=(a,b)=>[mul(a[0],b),mul(a[1],b)],fa=(...ps)=>[add(...ps.map(a=>a[0])),add(...ps.map(a=>a[1]))],fd=(a,b)=>fa(a,fs(b,-1)),fx=(a,b)=>[add(mul(a[0],b[0]),sc(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))],fc=a=>[a[0],sc(a[1],-1)];
 return {assert,F,rat,plus,times,mon,add,mul,sc,sub,sq,X,replace,normal,eq,prop,fp,fs,fm,fa,fd,fx,fc,unpack}
}
function verifyV78(data){
 const {assert,F,rat,plus,times,mon,add,mul,sc,sub,sq,X,replace,eq,prop,fp,fs,fm,fa,fd,fx,fc,unpack}=arithmetic();
 const [archive,old,ow,assignment,enh,nw,common,explicit]=data;
 const c=mon(1,0,1),ci=mon(1,0,-1),C=mon(1,1);
 const base={77:[1,0],78:[-1,0],90:[0,1],91:[0,-1],92:[-1,-2]};
 function lift(row){return add(...row.terms.map(t=>mul(mon(t.coefficient,t.parameterPower),...t.monomial.map(i=>base[i]?mon(1,0,...base[i]):X(i)))))}
 function arch(row){return add(...row.terms.map(t=>mon(t.coefficient,t.parameterPower,t.unitPower[0],t.unitPower[1],t.monomial)))}
 const co=new Map(common.residuals.map(r=>[r.name,r])),ex=new Map(explicit.residuals.map(r=>[r.name,r]));
 const pref=["inputSquare.","testSquare.40.0.","scalar.","parity_scalar.","sharedT.reference.","inverse_vieta."];
 let matched=0, matchedNames=new Set();
 for(const row of archive.rows){if(pref.some(s=>row.name.startsWith(s))){assert(co.has(row.name)&&ex.has(row.name)&&eq(lift(co.get(row.name)),arch(row))&&eq(lift(ex.get(row.name)),arch(row)),"v74 common scalar "+row.name);matched++;matchedNames.add(row.name)}}
 assert(matched===41,"scalar rows "+matched);
 const omitted=[...co.keys()].filter(n=>n.startsWith("inverse_vieta.")&&!matchedNames.has(n));
 assert(JSON.stringify(omitted)===JSON.stringify(["inverse_vieta.alternate.0","inverse_vieta.alternate.1","inverse_vieta.unweighted.aggregate"]),"omitted scalar");
 // Independently derive the new physical comparison packing from the v74 Laurent source.
 let want=new Map();
 const drop=["additive.detector","balanced.detector","detector0.normOver","detector1.normOver","new.det1.factor","amplified.det1.product"];
 for(let row of archive.rows){let name=row.name;if(drop.some(x=>name.startsWith(x)))continue;
 let p=add(...row.terms.map(t=>mul(mon(t.coefficient,t.parameterPower,t.unitPower[0]),...t.monomial.map(i=>name.startsWith("amplified.det0.product4.")&&(i===79||i===80)?mon(1,-1,-1,0,[302+i-79]):X(i)))));
 want.set(name,p)}
 const third={3:503,4:504,5:505,6:506,81:581,82:582,83:583,84:584,85:585};
 for(let [n,p] of [...want])if(n.startsWith("detector0."))want.set(n.replace("detector0","detector2"),replace(p,i=>third[i]?X(third[i]):null));
 let S=fm(fp(192),ci);
 for(const i of [201,213,225])S=fa(S,fx(fp(i+8),fa(fp(i+8),fp(i),fp(i+2))));
 const [T0,T1,T2]=[2,86,502].map(i=>mul(ci,X(i)));
 want.set("new.aggregate",add(sc(sub(T0,T1),2),mon(26),S[0]));
 want.set("new.aggregate_shift",add(sc(sub(add(T0,T2),sc(T1,2)),2),mon(-8),S[1]));
 const q0=X(300),q1=X(301),W=fp(302),D=X(305);
 const q=[q0,q1,sub(c,add(q0,q1))];
 const contacts=[[2,74,75,76,82,81],[86,87,88,89,96,95],[502,574,575,576,582,581]];
 // Five reflected roots, exact rational coefficients of P5.
 let es=[F(1)];
 for(let z of [F(0),F(-1,2),F(-1),F(1,2399),F(-32,407)]){
 const t=plus(times(F(22),z),F(-3)),r=times(t,t);
 let ne=Array.from({length:es.length+1},()=>F(0));
 for(let i=0;i<es.length;i++){ne[i]=plus(ne[i],es[i]);ne[i+1]=plus(ne[i+1],times(es[i],r))}
 es=ne;
 }
 const gcd=(a,b)=>{while(b){[a,b]=[b,a%b]}return a<0n?-a:a};
 const den=es.reduce((a,b)=>a/gcd(a,b[1])*b[1],1n);
 for(let j=0;j<3;j++){let [t,r,s,v,b,nr]=contacts[j],T=mul(ci,X(t)),R=mul(ci,X(r)),S=mul(ci,X(s)),V=mul(ci,X(v));if(j===0)V=mul(C,V);V=sc(V,F(1,den));
 const inv=X(310+j),oneplus=add(mon(),mul(ci,inv)),tau=mul(c,X(nr)),n="additive.detector"+j+".";
 want.set(n+"contactSquare",sub(sq(sub(sc(T,22),mon(3))),R));
 want.set(n+"contactFourthPower",sub(sq(R),S));
 want.set(n+"contactCombination",sub(add(mul(R,S),mul(oneplus,add(sc(S,F(-es[1][0],es[1][1])),sc(R,es[2])))),V));
 want.set(n+"contactRelation",sub(mul(S,V),mul(oneplus,add(sc(S,es[3]),sc(R,F(-es[4][0],es[4][1])),mon(es[5])))));
 want.set("balanced.detector"+j+".poleInput.definition",sub(sc(mul(c,X(b),add(mon(),q[j])),167281),sc(sq(tau),166464)));
 want.set("shared.inverse"+j,sub(c,mul(q[j],inv)));
 const E=fd(W,[mon(),mon(0)]);
 want.set("shared.norm_error",sub(sc(mul(W[0],D),2),fx(E,fc(E))[0]));
 want.set("shared.gate"+j,sub(sc(tau,2),add(mon(),sq(D),mul(c,inv),sc(c,-2),q[j])));
 }
 const G=assignment.groups,hy=assignment.hyperbolic,part=assignment.partial,high=assignment.high;
 assert(G.length===4&&hy.length===3&&part===3&&assignment.kept.length===0,"assignment");
 for(let [name,p] of [...want]){if(name.startsWith("new.det0.factor4.")||name.startsWith("amplified.det0.product4."))want.delete(name);
 else if(name.startsWith("amplified.det0.product3."))want.set(name,replace(p,i=>i===132||i===133?mon(1,-3,-1,0,[302+i-132]):null))}
 const native={C1:[60,1,-1,2],C2:[66,1,-1,2],C3:[68,1,-1,2],C4:[70,1,-1,2],H:[72,0,-1,4],A1:[205,0,0,1],B1:[207,0,0,-1],A3:[217,0,0,1],B3:[219,0,0,-1],A4:[229,0,0,1],B4:[231,0,0,-1],N:[62,0,-1,2]};
 const linear={DH:[64,0,-1,2],B0:[19,0,-1,-2],A2:[54,1,-1,2],B2:[23,0,-1,-2]};
 assert(JSON.stringify([...G.flat(),...high].sort())===JSON.stringify([...Object.keys(native),...Object.keys(linear)].sort()),"all tests");
 let subst={};
 for(let j of hy){const [i,k,e,h]=native[G[j][0]],[l,t,u,g]=native[G[j][2]];for(let b=0;b<2;b++){
 subst[i+b]=mul(mon(F(1,2*(b?h:1)),-k,-e),add(X(i+b),X(l+b)));
 subst[l+b]=mul(mon(F(1,2*(b?g:1)),-t,-u-1),sub(X(i+b),X(l+b)));
 }}
 for(let [n] of want)if(["new.square.237.","new.square.239.","amplified.C1.power4.","input.cleared.fourth."].some(s=>n.startsWith(s)))want.delete(n);
 const physicalField=(label)=>{let [i,k,e,h]=(native[label]||linear[label]);return fm(fp(i,h),mon(1,k,e))};
 for(let j=0;j<4;j++){
 let E=fd([mon(),mon(0)],fm(fp(118+2*j),mon(1,[1,1,1,0][j],1)));
 E=fa(E,fm(fx(physicalField(high[j]),physicalField(high[j])),mon(1,0,4)));
 for(let power=1;power<=3;power++){
 const label=G[j][power-1];
 if(j===part&&(power===1||power===3)){
 if(power===3)continue;
 const A=physicalField(G[j][0]),B=physicalField(G[j][2]),U=fp(610),v=fd(A,fm(B,c)),u=fa(A,fm(B,c));
 for(let k=0;k<2;k++)want.set("shared.partial_pair."+k,fd(U,u)[k]);
 assert(eq(fx(u,v)[0],fd(fx(A,A),fm(fx(B,B),sq(c)))[0])&&eq(fx(u,v)[1],fd(fx(A,A),fm(fx(B,B),sq(c)))[1]),"partial");
 E=fa(E,fm(fx(U,v),c));continue;
 }
 let term=physicalField(label);if(!(label in linear))term=fx(term,term);
 if(hy.includes(j)&&power===3)term=fs(term,-1);
 E=fa(E,fm(term,mon(1,0,power)));
 }
 for(let k=0;k<2;k++)want.set("new.det0.factor"+j+"."+k,E[k]);
 }
 for(let [n,p] of want)want.set(n,replace(p,i=>subst[i]));
 function uncompile(q,w){
 const labels=new Map(q.coordinates.map(x=>[x.id,x.source_id])),units={400:1,401:-1,402:-2},rows=new Map(),gs=new Set();
 assert(labels.size===180&&new Set(labels.values()).size===180&&labels.get(q.inputCoordinate)===1&&w.weights["1"]===0,"input");
 for(let r of q.residuals){
 assert(r.terms.every(t=>t.monomial.length<=2),"quadratic");
 if(r.name==="shared.c_unit"||r.name==="shared.c_inverse_square"){
 const expected=r.name==="shared.c_unit"?sub(mul(X(400),X(401)),mon()):sub(X(402),sq(X(401)));
 assert(eq(expected,add(...r.terms.map(t=>mon(t.coefficient,t.parameterPower,0,0,t.monomial.map(i=>labels.get(i)))))),"guard "+r.name);gs.add(r.name);continue;
 }
 assert(!rows.has(r.name),"duplicate");
 rows.set(r.name,add(...r.terms.map(t=>mul(mon(t.coefficient,t.parameterPower),...t.monomial.map(j=>{let i=labels.get(j);return i in units?mon(1,0,units[i]):mon(1,0,-w.weights[i],0,[i])})))));
 }
 assert(gs.size===2,"unit guards");
 return rows;
 }
 const physical=uncompile(old,ow);
 assert(physical.size===want.size,"v78 physical census "+physical.size+" "+want.size);
 for(let [name,p] of want)assert(physical.has(name)&&prop(p,physical.get(name)),"v78 physical "+name);
 const newphys=uncompile(enh,nw);
 assert(JSON.stringify(old.coordinates)===JSON.stringify(enh.coordinates)&&newphys.size===physical.size,"coordinates");
 let changed=0;
 const pairs=[[60,61,62,63],[70,71,72,73],[66,67,68,69]];
 for(let [name,p] of physical){
 let m=name.match(/^new\.det0\.factor([012])\.[01]$/);
 if(m){let [a,b,d,e]=pairs[Number(m[1])],left=[a,b],right=[d,e],count=0;
 p=add(...[...p].map(([k,v])=>{let [l,f,r,...i]=unpack(k),hit=i.length===2&&((left.includes(i[0])&&right.includes(i[1]))||(left.includes(i[1])&&right.includes(i[0])));if(hit)count++;return mon(v,l,f+(hit?4:0),r,i)}));
 assert(count===2,"enhanced pair "+name);changed++;
 }
 assert(newphys.has(name)&&prop(p,newphys.get(name)),"enhanced "+name);
 }
 assert(changed===6,"enhanced changed");
 return {matched_v74_v62_v195_rows:matched,v78_physical_rows:physical.size,v78_compiled_rows:old.residuals.length,enhanced_rows:enh.residuals.length,enhanced_changed:changed};
}
const paths=["computation/quartic/seven_units193_v74/primitive/laurent-source.json","computation/coauthor_audit_v78/H10-quartics/quartics/explicit-physical/quadrics.json","computation/coauthor_audit_v78/H10-quartics/quartics/explicit-physical/weights.json","computation/coauthor_audit_v78/H10-quartics/quartics/explicit-physical/assignment.json","computation/coauthor_audit_v78/work_general/enhanced/180/quadrics.json","computation/coauthor_audit_v78/work_general/enhanced/180/weights.json","computation/quartic/seven_units193_v74/source/source195.json","computation/quartic/explicit229_v62/quadratic.json"];
console.log(JSON.stringify(verifyV78(paths.map(p=>JSON.parse(fs.readFileSync(path.join(__dirname,"source",p),"utf8"))))));
