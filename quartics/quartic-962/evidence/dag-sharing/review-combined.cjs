'use strict';
const fs=require('node:fs'),path=require('node:path');
const base=path.resolve(__dirname,'../../quartic-version5-release/repository/quartics/quartic-1272');
const C=require(path.join(base,'checker/checker.cjs')),{Poly,Q}=C;
const dir=path.resolve(__dirname,'../combined'),bytes=fs.readFileSync(path.join(dir,'raw-translated-ir.json')),data=JSON.parse(bytes),ir=C.readIR(data);
if(C.hashBytes(bytes)!=='cb1295d789c5bb40bd98842b1bd2a51a05c6ff2058a526e7d1d9b177d20da3ae')throw Error('not the frozen reviewed candidate');
const checked=C.checkGates(ir),replay=C.replay(ir,JSON.parse(fs.readFileSync(path.join(dir,'reduction-certificate.json'))),C.hashBytes(bytes));
C.compareIR(C.readIR(JSON.parse(fs.readFileSync(path.join(dir,'compiled-ir.json')))),replay);
const p=ts=>Poly.from(ts),v=n=>p(data.values[n].terms),fp=n=>[v(n+'.0'),v(n+'.1')],cn=n=>Poly.constant(new Q(n));
const fm=(a,b)=>[a[0].mul(b[0]).add(a[1].mul(b[1]).scale(new Q(2))),a[0].mul(b[1]).add(a[1].mul(b[0]))],neg=a=>a.map(p=>p.scale(new Q(-1)));
const byname=new Map(data.gates.map(g=>[data.coordinates[g.coordinateId].name,g]));let tests=[];
function eq(a,b,label){if(!a.equals(b))throw Error(label);tests.push(label);}
function fq(n,num,den){for(let j=0;j<2;j++){let g=byname.get(n+'.'+j);if(g.operation!=='field_quotient_component')throw Error(n);for(let k=0;k<2;k++){eq(p(g.numerator[k]),num[k],n+' numerator '+j+'/'+k);eq(p(g.denominator[k]),den[k],n+' denominator '+j+'/'+k);}}}
function rq(n,num,den){let g=byname.get(n);if(g.operation!=='rational_quotient')throw Error(n);eq(p(g.numerator),num,n+' numerator');eq(p(g.denominator),den,n+' denominator');}
for(let side of ['U','V']){let n='log'+side+'0',point=side==='U'?'H':'V0';fq(n,neg(fm(fp(point+'.x'),fp(n+'.polynomial'))),fp(point+'.y'));}
fq('scalar.zRatio',neg(fm(fp('Sscalar.z'),fp('H.y'))),fp('H.x'));
for(let i=0;i<9;i++){
 let n='detector'+i,delta=v(n+'.t').sub(cn(1)),di=v(n+'.deltaInverse'),ep=v(n+'.eWeight'),w=fp(n+'.W'),nw=v(n+'.normOver2w0');
 rq(n+'.deltaInverse',cn(1),delta);
 rq(n+'.eWeight',v(n+'.Adelta4.square').mul(v(n+'.Adelta')),v(n+'.F'));
 rq(n+'.q1',ep.mul(v(n+'.deltaInverse2')),delta);
 rq(n+'.w0Inverse',cn(1),w[0]);
 rq(n+'.normOver2w0',w[0].square().sub(w[1].square().scale(new Q(2))).scale(new Q(1,2)),w[0]);
 rq(n+'.Rnorm',di.mul(nw),ep);
}
rq('scalar.n0',v('scalar.r').add(v('U0.f.0').square()),v('scalar.r'));
rq('scalar.n1',v('scalar.leaf1').mul(v('U0.f.1')).add(v('Sscalar.f.0').square()),v('scalar.r'));
let report={status:'passed',rawSha256:C.hashBytes(bytes),gateIdentities:checked.checked,compilerOperations:replay.trace.length,semanticAssertions:tests.length,tests,scope:'Final integration of local log quotients, scalar ratio and norm quotients, detector weight/trace/final-B quotients. Point chart and log polynomial are author-side components separately checked; independent review of those is assigned to source worker.'};
fs.writeFileSync(path.join(__dirname,'combined-integration-check.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({status:report.status,rawSha256:report.rawSha256,gateIdentities:report.gateIdentities,semanticAssertions:report.semanticAssertions}));
