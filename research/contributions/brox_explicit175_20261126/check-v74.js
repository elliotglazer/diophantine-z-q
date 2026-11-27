"use strict";
const fs=require("node:fs"),path=require("node:path");
function verifyV74(data){
 const [archive,source,cert]=data;
 const A=(b,m)=>{if(!b)throw Error(m||"assertion")};
 const key=(k,e,f,m)=>[k,e,f,...m.slice().sort((a,b)=>a-b)].join(","),dec=k=>k.split(",").map(Number);
 function put(p,k,c){let a=(p.get(k)||0n)+c;if(a)p.set(k,a);else p.delete(k)}
 const mon=(a=1,k=0,e=0,f=0,m=[])=>BigInt(a)?new Map([[key(k,e,f,m),BigInt(a)]]):new Map();
 function add(...ps){let o=new Map();for(let p of ps)for(let [k,c] of p)put(o,k,c);return o}
 function mul(...ps){let o=mon();for(let p of ps){let r=new Map();for(let [a,c] of o)for(let [b,d] of p){let [k,e,f,...m]=dec(a),[l,g,h,...n]=dec(b);put(r,key(k+l,e+g,f+h,m.concat(n)),c*d)}o=r}return o}
 const sc=(p,a)=>mul(mon(a),p),sub=(p,q)=>add(p,sc(q,-1)),sq=p=>mul(p,p),X=i=>mon(1,0,0,0,[i]);
 const eq=(p,q)=>p&&q&&p.size===q.size&&[...p].every(([k,c])=>q.get(k)===c);
 const fp=(i,j=1)=>[X(i),sc(X(i+1),j)],fs=(a,b)=>[sc(a[0],b),sc(a[1],b)],fm=(a,b)=>[mul(a[0],b),mul(a[1],b)],fa=(...ps)=>[add(...ps.map(a=>a[0])),add(...ps.map(a=>a[1]))],fd=(a,b)=>fa(a,fs(b,-1)),fx=(a,b)=>[add(mul(a[0],b[0]),sc(mul(a[1],b[1]),2)),add(mul(a[0],b[1]),mul(a[1],b[0]))],fc=a=>[a[0],sc(a[1],-1)],f2=a=>fx(a,a);
 const u=mon(1,0,1),ui=mon(1,0,-1),one=mon(),fone=[one,mon(0)],D=[mon(11),mon(-6)];
 const S=fm(fp(17),ui),TH=fm(fp(150),ui);
 let expected=new Map(),raw={},pairs={1:[201,203,205,207,209,211],3:[213,215,217,219,221,223],4:[225,227,229,231,233,235]};
 function group(n,z){for(let i=0;i<2;i++)expected.set(n+"."+i,z[i])}
 let aggregate=add(sc(X(2),2),sc(X(86),-2),sc(u,14),X(192));
 for(let [role,ids] of Object.entries(pairs)){
 const [s,t,F,G,h,d]=ids.map(i=>fp(i)),p=fa(h,s,t);
 group("new"+role+".d_piF",fd(d,fx(p,F)));
 group("new"+role+".d_Gh",fd(d,fx(h,G)));
 group("new"+role+".sum",fa(fd(fx(D,fa(F,G)),fx(fd(s,t),h)),f2(t)));
 group("new"+role+".unit",fa(fd(fone,fx(d,fd(s,t))),fx(D,fx(F,G))));
 raw["A"+role]=F;raw["B"+role]=fc(G);
 const E={1:31,3:39,4:43}[role];
 const physical=fd(fx(S,fc(t)),fx(fc(TH),s));
 group("cleared.E"+role,fm(fd(fm(fp(E),ui),physical),u));
 aggregate=add(aggregate,mul(u,fx(h,p)[0]));
 }
 expected.set("new.aggregate",aggregate);
 // Clear s2,t2 by R before comparison (no division by a variable).
 const z2=fd(fs(fx(S,fc(fa(fp(184),fp(188)))),-1),fx(fc(TH),fa(fp(182),fp(188))));
 group("cleared.E2",fd(fm(fp(35),X(113)),fm(z2,u)));
 for(let [role,E,J] of [[1,31,60],[2,35,66],[3,39,68],[4,43,70]])group("cleared.E"+role+".square",fm(fd(fm(fp(J,2),mon(1,1,-1)),f2(fm(fp(E),ui))),sq(u)));
 group("new.square.237",fd(fp(237),f2(raw.A4)));
 group("new.square.239",fd(fp(239),f2(fp(231))));
 const beta=add(mon(2504),sc(mul(X(45),ui),51)),N=fd(S,fm(fp(201),beta));
 group("input.cleared",fm(fd(fm(fp(29),ui),N),u));
 group("input.cleared.square",fm(fd(fm(fp(62,2),ui),f2(fm(fp(29),ui))),sq(u)));
 group("input.cleared.fourth",fm(fd(fm(fp(116),ui),f2(fm(fp(62,2),ui))),sq(u)));
 const aa=fm(fp(33),mon(1,1,-1)),w=fp(225),calC=fm(fp(46),ui),calP=fm(fp(41),ui),calQ=fm(fp(48),ui),H=fm(fp(50,2),ui);
 group("homogeneous.C",fm(fd(calC,fx(fd(aa,fone),fa(w,fs(S,4)))),u));
 group("homogeneous.Q",fm(fd(calQ,fx(fa(aa,fone),calP)),sq(u)));
 const hv=fd(fd(fa(f2(calP),f2(calC)),fx(calC,calQ)),f2(w));
 group("homogeneous.H",fm(fd(H,hv),sq(u)));
 group("homogeneous.H.square",fm(fd(fm(fp(72,4),ui),f2(H)),sq(u)));
 group("homogeneous.P.ratio",fm(fd(fx(calP,fp(213)),fs(fx(S,w),2)),u));
 const quadratic={C2:fm(fp(66,2),mon(1,1,-1)),C3:fm(fp(68,2),mon(1,1,-1)),C4:fm(fp(70,2),mon(1,1,-1)),GL:fm(fp(72,4),ui),A1:raw.A1,B1:raw.B1,A3:raw.A3,B3:raw.B3};
 const linear={DH:fm(fp(64,2),ui),B0:fm(fc(fp(19,2)),ui),A2:fm(fp(54,2),mon(1,1,-1)),B2:fm(fc(fp(23,2)),ui),A4:fp(237),B4:fc(fp(239)),C1:fm(fp(114),mon(1,1,-1))};
 for(let det of [0,1]){
 let assign=cert.assignments[String(det)];A(new Set(Object.values(assign.quadratic)).size===8&&new Set(Object.values(assign.linear)).size===7,"assignments");
 for(let i=0;i<5;i++){
 let output=fm(fp(118+16*det+2*i),mon(1,[1,1,1,0,-1][i],1,2*det)),res=fd(fone,output);
 if(i===4)res=fa(res,fm(f2(fm(fp(116),ui)),mon(1,0,4,4*det)));
 for(let [lab,j] of Object.entries(assign.quadratic))if(Math.floor(j/2)===i){let p=1+2*(j%2);res=fa(res,fm(f2(quadratic[lab]),mon(1,0,p,p*det)))}
 for(let [lab,j] of Object.entries(assign.linear))if((j<4?j:4)===i){let p=j<4?2:j-3;res=fa(res,fm(linear[lab],mon(1,0,p,p*det)))}
 group("new.det"+det+".factor"+i,res);
 }
 }
 const base={77:[1,0],78:[-1,0],90:[0,1],91:[0,-1],92:[-1,-2],901:[0,-3],902:[1,-1],903:[-1,-1]};
 const lift=r=>add(...r.terms.map(t=>mul(mon(t.coefficient,t.parameterPower),...t.monomial.map(i=>base[i]?mon(1,0,...base[i]):X(i)))));
 const obs=r=>add(...r.terms.map(t=>mon(t.coefficient,t.parameterPower,t.unitPower[0],t.unitPower[1],t.monomial)));
 let retained=new Map(source.residuals.map(r=>[r.name,lift(r)])),count=0,supplied=0;
 let seen=new Set();
 for(let row of archive.rows){let n=row.name;A(!seen.has(n),"duplicate "+n);seen.add(n);let p=expected.get(n);
 if(p){supplied++;}else{p=retained.get(n);count++}
 A(p&&eq(p,obs(row)),"v74 physical "+n);
 }
 A(supplied===expected.size&&count+supplied===162,"complete coverage "+supplied+" "+count);
 return {v74_physical_rows:162,rederived_field_and_detector_rows:supplied,retained_source195_rows:count};
}
const paths=["computation/quartic/seven_units193_v74/primitive/laurent-source.json","computation/quartic/seven_units193_v74/source/source195.json","computation/quartic/seven_units193_v74/laurent-certificate.json"];
console.log(JSON.stringify(verifyV74(paths.map(p=>JSON.parse(fs.readFileSync(path.join(__dirname,"source",p),"utf8"))))));
