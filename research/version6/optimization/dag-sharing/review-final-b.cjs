'use strict';
const fs=require('node:fs'),path=require('node:path');
const base=path.resolve(__dirname,'../../quartic-version5-release/repository/quartics/quartic-1272');
const C=require(path.join(base,'checker/checker.cjs'));
const file=path.resolve(__dirname,'../field-quotients/final-b/raw-translated-ir.json');
const bytes=fs.readFileSync(file),data=JSON.parse(bytes),raw=C.readIR(data),gateResult=C.checkGates(raw);
const p=ts=>C.Poly.from(ts),v=name=>p(data.values[name].terms);
let checks=0;function eq(a,b){if(!a.equals(b))throw Error('final B identity');checks++;}
for(let i=0;i<9;i++){
 let n='detector'+i,g=data.gates.find(g=>data.coordinates[g.coordinateId].name===n+'.Rnorm');
 if(g.operation!=='rational_quotient')throw Error('operation');
 eq(p(g.numerator),v(n+'.deltaInverse').mul(v(n+'.normOver2w0')));
 eq(p(g.denominator),v(n+'.eWeight'));
 let out=v(n+'.B'),def=new Map(data.gates.map(g=>[g.coordinateId,g]));
 for(let t of [...out.terms.values()])for(let id of t.m){let h=def.get(id);if(h?.operation==='quadratic_assignment')out=out.substitute(id,p(h.expression));}
 eq(out,v(n+'.Rnorm').mul(v(n+'.normOver2w0')));
}
let report={status:'passed',reviewer:'dag-sharing worker independent of final-B author',inputSha256:C.hashBytes(bytes),rawGateIdentities:gateResult.checked,semanticAssertions:checks};
fs.writeFileSync(path.join(__dirname,'final-b-independent-review.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));
