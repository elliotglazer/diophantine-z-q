'use strict';
const fs=require('node:fs'),path=require('node:path');
const base=path.resolve(__dirname,'../../quartic-version5-release/repository/quartics/quartic-1272');
const K=require(path.join(base,'checker/checker.cjs')),{Poly,Q}=K;
const dir=path.join(__dirname,'point-candidate'),bytes=fs.readFileSync(path.join(dir,'raw-translated-ir.json')),data=JSON.parse(bytes),raw=K.readIR(data);
const gates=K.checkGates(raw),replay=K.replay(raw,JSON.parse(fs.readFileSync(path.join(dir,'reduction-certificate.json'))),K.hashBytes(bytes));
K.compareIR(K.readIR(JSON.parse(fs.readFileSync(path.join(dir,'compiled-ir.json')))),replay);
const c=n=>Poly.constant(new Q(n)),v=i=>Poly.coordinate(i),scale=(p,n,d=1)=>p.scale(new Q(n,d)),pow=(p,n)=>{let a=c(1);while(n--)a=a.mul(p);return a;};
let checks=[];function eq(a,b,label){if(!a.equals(b))throw Error(label);checks.push(label);}
let t=v(0),h=v(1),D=v(2),u=t.square(),x=t.mul(h).add(scale(u,1,2)),y=x.mul(t),m=h.add(t),dmap=u.mul(h.square().sub(scale(u,1,4))),error=D.sub(dmap);
eq(x.square().sub(x.mul(u)),dmap,'reverse D identity');
eq(y.square().sub(pow(x,3)).add(D.mul(x)),x.mul(error),'reverse curve identity');
eq(scale(y.mul(m),2).sub(scale(x.square(),3)).add(D),error,'reverse tangent identity');
eq(m.square().sub(scale(x,2)),h.square(),'reverse doubled x');
eq(m.mul(x.sub(h.square())).sub(y),h.mul(scale(u,1,2).sub(h.square())),'reverse doubled y');
eq(x.square().add(dmap),scale(x.mul(t).mul(h),2),'reverse inverse-map h');
let a=v(0),b=v(1),s=v(3),curve=b.square().sub(pow(a,3)).add(D.mul(a)),slope=scale(b.mul(s),2).sub(scale(a.square(),3)).add(D);
eq(a.square().mul(a.square().add(D).square()).sub(pow(b,4)).sub(scale(D.mul(pow(a,4)),4)),scale(curve.mul(b.square().add(pow(a,3)).sub(D.mul(a))),-1),'forward cleared chart identity');
eq(scale(a.mul(b).mul(s),2).sub(a.mul(a.square().add(D))).sub(scale(b.square(),2)),a.mul(slope).sub(scale(curve,2)),'forward cleared slope identity');
eq(scale(pow(a,3),2).sub(a.mul(a.square().add(D))).sub(b.square()),scale(curve,-1),'forward cleared inverse x');
const fmul=(a,b)=>[a[0].mul(b[0]).add(scale(a[1].mul(b[1]),2)),a[0].mul(b[1]).add(a[1].mul(b[0]))],fsub=(a,b)=>a.map((p,j)=>p.sub(b[j])),fscale=(a,n,d=1)=>a.map(p=>scale(p,n,d)),value=n=>Poly.from(data.values[n].terms),pair=n=>[value(n+'.0'),value(n+'.1')];
for(let name of ['A','S','T','Z','H','UA','US','UT','UZ']){
 let cs=data.coordinates.filter(p=>p.name.startsWith(name+'.chart.'));
 const tt=[v(cs.find(p=>p.name===name+'.chart.t0').id),v(cs.find(p=>p.name===name+'.chart.t1').id)],hh=[v(cs.find(p=>p.name===name+'.chart.h0').id),v(cs.find(p=>p.name===name+'.chart.h1').id)];
 let uu=pair(name+'.chart.tSquare'),xx=pair(name+'.x'),yy=pair(name+'.y');
 // Verify the assignments after substituting the gate definitions, which have already been checked.
 let env=new Map(data.gates.filter(g=>g.block==='point_modules').map(g=>[g.coordinateId,Poly.from(g.expression)]));
 function expand(p){for(let [id,q]of [...env].reverse())if(p.uses(id))p=p.substitute(id,q);return p;}
 for(let j=0;j<2;j++){
  eq(expand(uu[j]),fmul(tt,tt)[j],name+' actual t square '+j);
  eq(expand(xx[j]),fmul(hh,hh)[j],name+' actual output x '+j);
  eq(expand(yy[j]),fmul(hh,fsub(fscale(fmul(tt,tt),1,2),fmul(hh,hh)))[j],name+' actual output y '+j);
  let row=raw.residuals.get(data.residuals.find(r=>r.name===name+'.chart.equation.'+j).id);
  eq(row,fmul(uu,fsub(xx,fscale(uu,1,4)))[j].sub(c(j===0?11:-6)),name+' actual chart row '+j);
 }
}
let report={status:'passed',rawSha256:K.hashBytes(bytes),gateIdentities:gates.checked,compilerOperations:replay.trace.length,symbolicChecks:checks.length,checks};
fs.writeFileSync(path.join(dir,'algebra-check.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({status:'passed',gateIdentities:gates.checked,symbolicChecks:checks.length}));
