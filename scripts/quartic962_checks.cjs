'use strict';
// Portable replays of the frozen component reviews. Uses the bundled checker,
// never the builder or compiler implementation. Domain proofs remain in PROOF.md.
const fs=require('node:fs'),path=require('node:path');
const [mode,packageArg,workArg,outputArg]=process.argv.slice(2);
if(!mode||!packageArg||!workArg||!outputArg)throw Error('usage: mode package work output');
const pack=path.resolve(packageArg),work=path.resolve(workArg),C=require(path.join(pack,'checker/checker.cjs')),{Poly,Q}=C;
const bytes=fs.readFileSync(path.join(work,'raw-translated-ir.json')),data=JSON.parse(bytes),ir=C.readIR(data);
const zero=()=>Poly.constant(new Q(0)),cn=(n,d=1)=>Poly.constant(new Q(n,d)),v=i=>Poly.coordinate(i);
const scale=(p,n,d=1)=>p.scale(new Q(n,d)),pow=(p,n)=>{let q=cn(1);for(let i=0;i<n;i++)q=q.mul(p);return q;};
const fm=(a,b)=>[a[0].mul(b[0]).add(scale(a[1].mul(b[1]),2)),a[0].mul(b[1]).add(a[1].mul(b[0]))];
const fa=(a,b)=>a.map((x,i)=>x.add(b[i])),fsub=(a,b)=>a.map((x,i)=>x.sub(b[i])),fscl=(a,n,d=1)=>a.map(x=>scale(x,n,d));
const rows=new Map(data.residuals.map(r=>[r.name,r])),coords=new Map(data.coordinates.map(c=>[c.name,c.id]));
const byname=new Map(data.gates.map(g=>[data.coordinates.find(c=>c.id===g.coordinateId).name,g]));
const p=t=>Poly.from(t),value=n=>{if(!data.values[n])throw Error('missing alias '+n);return p(data.values[n].terms);},pair=n=>[value(n+'.0'),value(n+'.1')];
const tests=[];function eq(a,b,label){if(!a.equals(b))throw Error('identity failed: '+label);tests.push(label);}
function environment(){return new Map(data.coordinates.map(c=>[c.id,v(c.id)]));}
function ev(terms,env){let out=zero();for(const t of terms){let z=new Poly().put([],t.sPower,Q.parse(t.coefficient));for(const x of t.monomial)z=z.mul(env.get(x));out=out.add(z);}return out;}
function val(n,env){return ev(data.values[n].terms,env);}
function fld(n,env){return[val(n+'.0',env),val(n+'.1',env)];}
function execute(gates,env,label){for(const g of gates){if(g.operation!=='quadratic_assignment')throw Error('nonassignment in '+label);env.set(g.coordinateId,ev(g.expression,env));eq(ev(data.residuals.find(r=>r.id===g.definitionResidualId).terms,env),zero(),label+' residual '+g.coordinateId);}}

if(mode==='quotients'){
 function fq(n,num,den){for(let j=0;j<2;j++){const g=byname.get(n+'.'+j);if(!g||g.operation!=='field_quotient_component')throw Error(n);for(let k=0;k<2;k++){eq(p(g.numerator[k]),num[k],n+' numerator '+j+'/'+k);eq(p(g.denominator[k]),den[k],n+' denominator '+j+'/'+k);}}}
 function rq(n,num,den){const g=byname.get(n);if(!g||g.operation!=='rational_quotient')throw Error(n);eq(p(g.numerator),num,n+' numerator');eq(p(g.denominator),den,n+' denominator');}
 for(const side of ['U','V']){const n='log'+side+'0',point=side==='U'?'H':'V0';fq(n,fscl(fm(pair(point+'.x'),pair(n+'.polynomial')),-1),pair(point+'.y'));}
 fq('scalar.zRatio',fscl(fm(pair('Sscalar.z'),pair('H.y')),-1),pair('H.x'));
 for(let i=0;i<9;i++){
  const n='detector'+i,delta=value(n+'.t').sub(cn(1)),di=value(n+'.deltaInverse'),ep=value(n+'.eWeight'),w=pair(n+'.W'),nw=value(n+'.normOver2w0');
  rq(n+'.deltaInverse',cn(1),delta);rq(n+'.eWeight',value(n+'.Adelta4.square').mul(value(n+'.Adelta')),value(n+'.F'));
  rq(n+'.q1',ep.mul(value(n+'.deltaInverse2')),delta);rq(n+'.w0Inverse',cn(1),w[0]);
  rq(n+'.normOver2w0',scale(w[0].square().sub(scale(w[1].square(),2)),1,2),w[0]);rq(n+'.Rnorm',di.mul(nw),ep);
 }
 rq('scalar.n0',value('scalar.r').add(value('U0.f.0').square()),value('scalar.r'));
 rq('scalar.n1',value('scalar.leaf1').mul(value('U0.f.1')).add(value('Sscalar.f.0').square()),value('scalar.r'));
 if(tests.length!==136)throw Error('quotient coverage changed');
}else if(mode==='points'){
 const t=v(0),h=v(1),D=v(2),u=t.square(),x=t.mul(h).add(scale(u,1,2)),y=x.mul(t),m=h.add(t),dmap=u.mul(h.square().sub(scale(u,1,4))),error=D.sub(dmap);
 eq(x.square().sub(x.mul(u)),dmap,'reverse D identity');eq(y.square().sub(pow(x,3)).add(D.mul(x)),x.mul(error),'reverse curve identity');
 eq(scale(y.mul(m),2).sub(scale(x.square(),3)).add(D),error,'reverse tangent identity');eq(m.square().sub(scale(x,2)),h.square(),'reverse doubled x');
 eq(m.mul(x.sub(h.square())).sub(y),h.mul(scale(u,1,2).sub(h.square())),'reverse doubled y');eq(x.square().add(dmap),scale(x.mul(t).mul(h),2),'reverse inverse h');
 const a=v(0),b=v(1),s=v(3),curve=b.square().sub(pow(a,3)).add(D.mul(a)),slope=scale(b.mul(s),2).sub(scale(a.square(),3)).add(D);
 eq(a.square().mul(a.square().add(D).square()).sub(pow(b,4)).sub(scale(D.mul(pow(a,4)),4)),scale(curve.mul(b.square().add(pow(a,3)).sub(D.mul(a))),-1),'forward cleared chart');
 eq(scale(a.mul(b).mul(s),2).sub(a.mul(a.square().add(D))).sub(scale(b.square(),2)),a.mul(slope).sub(scale(curve,2)),'forward cleared slope');
 eq(scale(pow(a,3),2).sub(a.mul(a.square().add(D))).sub(b.square()),scale(curve,-1),'forward cleared inverse x');
 const env=environment();execute(data.gates.filter(g=>g.block==='point_modules'),env,'point chart');
 for(const n of ['A','S','T','Z','H','UA','US','UT','UZ']){
  const tt=[v(coords.get(n+'.chart.t0')),v(coords.get(n+'.chart.t1'))],hh=[v(coords.get(n+'.chart.h0')),v(coords.get(n+'.chart.h1'))],uu=fm(tt,tt),xx=fm(hh,hh),yy=fm(hh,fsub(fscl(uu,1,2),xx));
  for(let j=0;j<2;j++){eq(fld(n+'.chart.tSquare',env)[j],uu[j],n+' t square '+j);eq(fld(n+'.x',env)[j],xx[j],n+' output x '+j);eq(fld(n+'.y',env)[j],yy[j],n+' output y '+j);eq(ev(rows.get(n+'.chart.equation.'+j).terms,env),fm(uu,fsub(xx,fscl(uu,1,4)))[j].sub(cn(j===0?11:-6)),n+' chart equation '+j);}
 }
}else if(mode==='circuits'){
 // Each test leaves all upstream coordinates independent and executes only its local assignments.
 function coefficientTree(order,count,start,prefix){
  if(count===1)return [[cn(1),zero()],pair('testSquare.'+order+'.'+start)];
  const cut=Math.floor(count/2),left=coefficientTree(order,cut,start,prefix+'.left'),right=coefficientTree(order,count-cut,start+cut,prefix+'.right'),env=environment();
  execute(data.gates.filter(g=>data.coordinates[g.coordinateId].name.startsWith(prefix+'.co')),env,prefix+' coefficient convolution');
  const out=[[cn(1),zero()]];
  for(let k=1;k<=count;k++){
   let want=[zero(),zero()];
   for(let i=Math.max(0,k-right.length+1);i<=Math.min(k,left.length-1);i++)want=fa(want,fm(left[i],right[k-i]));
   for(let j=0;j<2;j++)eq(fld(prefix+'.co'+k,env)[j],want[j],prefix+' coefficient '+k+'/'+j);
   out.push(pair(prefix+'.co'+k));
  }
  return out;
 }
 for(const [order,count]of [[1,10],[16,2],[52,4]])coefficientTree(order,count,0,'symmetric.'+order);
 {
  const env=environment(),a=fld('L2',env),t=fld('L3',env),b=fld('L4',env),am2=fsub(a,[cn(2),zero()]);
  const want=fsub(fa(fsub(fm(t,t),fm(fm(a,am2),fm(t,b))),fm(fm(am2,b),fm(am2,b))),[cn(1),zero()]);
  execute(data.gates.filter(g=>data.coordinates[g.coordinateId].name.startsWith('Lucas.')),env,'Lucas reassociation');
  for(let j=0;j<2;j++)eq(val('Lucas.F'+j,env),want[j],'Lucas polynomial '+j);
 }
 for(let i=0;i<9;i++)for(const [order,length,qname]of [[1,11,'q1'],[16,3,'q16'],[52,5,'q52']]){
  const env=environment(),n='detector'+i+'.E'+order,q=val('detector'+i+'.'+qname,env),co=[[cn(1),zero()]];
  for(let k=1;k<length;k++)co.push(fld('symmetric.'+order+'.co'+k,env));
  const gs=data.gates.filter(g=>data.coordinates[g.coordinateId].name.startsWith(n+'.'));execute(gs,env,n);
  for(let j=0;j<2;j++){let want=zero();for(let k=0;k<length;k++)want=want.add(co[k][j].mul(pow(q,k)));eq(val(n+'.'+j,env),want,n+' direct power sum '+j);}
 }
 for(let i=0;i<9;i++){
  const env=environment(),n='detector'+i,q=val(n+'.q1',env),e6=val(n+'.e6',env),e24=val(n+'.e24',env),e96=val(n+'.e96',env);
  const names=new Set(['q1e6','q16','q52'].map(s=>n+'.'+s+'.quadratic'));const gs=data.gates.filter(g=>names.has(data.coordinates[g.coordinateId].name));if(gs.length!==3)throw Error('weight coverage');execute(gs,env,n+' shared weights');
  eq(val(n+'.q16',env),q.mul(e6).mul(e24),n+' q16');eq(val(n+'.q52',env),q.mul(e6).mul(e96),n+' q52');
  const envF=environment(),t=val(n+'.t',envF);let f=cn(1);for(const [a,b]of [[0,1],[1,2],[1,1],[-1,2399],[32,407]])f=f.mul(t.add(cn(a,b)));
  execute(data.gates.filter(g=>data.coordinates[g.coordinateId].name.startsWith(n+'.F')),envF,n+' quintic');eq(val(n+'.F',envF),f,n+' contact quintic');
 }
 const coeff=[new Q(1),new Q(-2,5)];for(let j=2;j<=12;j++)coeff.push(coeff[j-1].mul(new Q(4*j-5,4*j+1)));
 for(const side of ['U','V'])for(let i=0;i<5;i++){
  const env=environment(),pre=side+i,n='log'+pre,f=fld(pre+'.f',env),w=fm([cn(11),cn(-6)],fm(f,f));let power=[cn(1),zero()],want=[zero(),zero()];
  for(const c of coeff.slice(0,i===1?4:13)){want=fa(want,power.map(x=>x.scale(c)));power=fm(power,w);}
  const gs=data.gates.filter(g=>data.coordinates[g.coordinateId].name.startsWith(n+'.')&&g.operation==='quadratic_assignment');execute(gs,env,n);
  for(let j=0;j<2;j++)eq(fld(n+'.polynomial',env)[j],want[j],n+' logarithm polynomial '+j);
  if(i)for(let j=0;j<2;j++)eq(fld(n,env)[j],fm(fld(pre+'.z',env),want)[j],n+' output '+j);
 }
 for(const n of Array.from({length:9},(_,i)=>'detector'+i).concat(['scalar'])){
  const env=environment(),b=val(n+(n==='scalar'?'.b':'.Bsemantic'),env),B=scale(b,17),z=v(coords.get(n+'.scaled_e')),p0=v(coords.get(n+'.p')),s0=v(coords.get(n+'.s')),q0=v(coords.get(n+'.q')),U=n==='scalar'?val('scalar.U',env):b;
  const targets=new Set(['p2','U2','Bh','s2','q2'].map(s=>n+'.'+s+'.quadratic'));const gs=data.gates.filter(g=>targets.has(data.coordinates[g.coordinateId].name));if(gs.length!==5)throw Error('pole coverage');execute(gs,env,n+' pole');
  const H=z.mul(B.sub(U.square()));eq(ev(rows.get(n+'.firstConic').terms,env),B.mul(p0.square()).sub(B.sub(z).mul(B.add(scale(z,3)))),n+' first pole');eq(ev(rows.get(n+'.secondConic').terms,env),B.mul(q0.square()).sub(s0.square().sub(H).mul(s0.square().add(scale(H,3)))),n+' second pole');
 }
 const chain=[2,3,5,7,11,13,17,'sign'].map(x=>v(coords.get('correction.partial.'+x)));
 eq(p(rows.get('correction.initialSign').terms),chain[0].square().sub(cn(1)),'correction initial sign');
 [2,3,5,7,11,13,17].forEach((prime,j)=>eq(p(rows.get('correction.partialProduct'+(j+1)).terms),chain[j+1].sub(chain[j]).mul(chain[j+1].sub(scale(chain[j],prime))),'correction factor '+j));
}else if(mode==='anchor'){
 const a=C.readIR(JSON.parse(fs.readFileSync(path.join(work,'raw-ir.json')))),ids=a.data.anchor.privateCoordinateIds,[u,v0,w]=ids.map(v),S=new Poly().put([],1,new Q(1));
 if(JSON.stringify(ids)!==JSON.stringify(data.anchor.privateCoordinateIds)||a.data.anchor.rowId!==data.anchor.rowId)throw Error('anchor metadata');
 const forward=new Map([[ids[0],S.add(scale(u.sub(scale(v0,3)).add(scale(w,3)),1,4))],[ids[1],scale(S,1,2).add(scale(v0,1,4))],[ids[2],scale(S,3,2).add(scale(w,1,4))]]);
 const inverse=new Map([[ids[0],scale(u,4).add(scale(v0,12)).sub(scale(w,12)).add(scale(S,8))],[ids[1],scale(v0,4).sub(scale(S,2))],[ids[2],scale(w,4).sub(scale(S,6))]]);
 function sub(p,map){let out=zero();for(const t of p.terms.values()){let x=new Poly().put([],t.s,t.c);for(const id of t.m)x=x.mul(map.get(id)||v(id));out=out.add(x);}return out;}
 for(const id of ids){eq(sub(forward.get(id),inverse),v(id),'forward inverse '+id);eq(sub(inverse.get(id),forward),v(id),'inverse forward '+id);}
 for(const[id,row]of a.residuals){if(id===a.data.anchor.rowId)eq(scale(sub(row,forward),16),ir.residuals.get(id),'anchor row scale');else{for(const v0 of ids)if(row.uses(v0))throw Error('private anchor leakage');eq(row,ir.residuals.get(id),'unchanged nonanchor '+id);}}
}else throw Error('unknown mode '+mode);
const report={schema:'quartic-962-local-check-v1',mode,status:'PASS',rawSha256:C.hashBytes(bytes),assertions:tests.length,tests,scope:'Exact emitted algebra and cleared witness-map identities. Nonzero premises and external arithmetic are justified by the separately pinned proofs.'};
fs.writeFileSync(outputArg,JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({mode,status:report.status,assertions:tests.length}));
