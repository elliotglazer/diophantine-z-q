'use strict';
const fs=require('node:fs'),path=require('node:path');
const base=path.resolve(__dirname,'../../quartic-version5-release/repository/quartics/quartic-1272');
const target=path.resolve(__dirname,'../field-quotients');
const C=require(path.join(base,'checker/checker.cjs')),{Poly,Q}=C;
const bytes=fs.readFileSync(path.join(target,'raw-ir.json')),data=JSON.parse(bytes),ir=C.readIR(data);
const checked=C.checkGates(ir);
const parse=ts=>Poly.from(ts),v=n=>parse(data.values[n].terms),fp=n=>[v(n+'.0'),v(n+'.1')];
const cn=n=>Poly.constant(new Q(n)),add=(a,b)=>a.map((x,i)=>x.add(b[i]));
const mul=(a,b)=>[a[0].mul(b[0]).add(a[1].mul(b[1]).scale(new Q(2))),a[0].mul(b[1]).add(a[1].mul(b[0]))];
const scale=(a,c)=>a.map(x=>x.scale(c));
let checks=[];
function eq(a,b,label){if(!a.equals(b))throw Error(label);checks.push(label);}
const byname=new Map(data.gates.map(g=>[data.coordinates[g.coordinateId].name,g]));
function quotient(name,num,den){let g=byname.get(name);if(!g||g.operation!=='rational_quotient')throw Error(name);eq(parse(g.numerator),num,name+' numerator');eq(parse(g.denominator),den,name+' denominator');}
function fieldquotient(name,num,den){for(let j=0;j<2;j++){let g=byname.get(name+'.'+j);if(!g||g.operation!=='field_quotient_component')throw Error(name);for(let k=0;k<2;k++){eq(parse(g.numerator[k]),num[k],name+' numerator '+j+'/'+k);eq(parse(g.denominator[k]),den[k],name+' denominator '+j+'/'+k);}}}
for(let side of ['U','V']){
 let name='log'+side+'0',point=side==='U'?'H':'V0';
 let pol=add(fp(name+'.horner1'),add([cn(1),cn(0)],add(scale(fp(name+'.w'),new Q(-2,5)),scale(fp(name+'.wPower2'),new Q(-2,15)))));
 fieldquotient(name,scale(mul(fp(point+'.x'),pol),new Q(-1)),fp(point+'.y'));
}
fieldquotient('scalar.zRatio',scale(mul(fp('Sscalar.z'),fp('H.y')),new Q(-1)),fp('H.x'));
for(let r=0;r<9;r++){
 let n='detector'+r,d=v(n+'.t').sub(cn(1)),di=v(n+'.deltaInverse'),ep=v(n+'.eWeight'),w=fp(n+'.W');
 quotient(n+'.deltaInverse',cn(1),d);
 quotient(n+'.eWeight',v(n+'.Adelta4.square').mul(v(n+'.Adelta')),v(n+'.F'));
 quotient(n+'.R',di,ep);
 quotient(n+'.q1',ep.mul(v(n+'.deltaInverse2')),d);
 quotient(n+'.w0Inverse',cn(1),w[0]);
 quotient(n+'.normOver2w0',w[0].square().sub(w[1].square().scale(new Q(2))).scale(new Q(1,2)),w[0]);
 if(byname.has(n+'.FInverse'))throw Error('unexpected F guard retained');
}
const report={status:'passed',reviewer:'dag-sharing worker, independent of quotient author',candidateRawSha256:C.hashBytes(bytes),gateIdentities:checked.checked,semanticAssertions:checks.length,checks};
fs.writeFileSync(path.join(__dirname,'quotient-independent-review.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({status:report.status,gateIdentities:report.gateIdentities,semanticAssertions:report.semanticAssertions}));
