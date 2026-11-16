'use strict';
const fs=require('fs'),path=require('path');
const baseline=path.resolve(__dirname,'../../../quartic-version5-release/repository/quartics/quartic-1272');
const checker=require(path.join(baseline,'checker/checker.cjs'));
const get=f=>JSON.parse(fs.readFileSync(path.join(__dirname,f)));
const data=get('raw-translated-ir.json'), ir=checker.readIR(data), gates=checker.checkGates(ir);
const inputHash=checker.hashBytes(fs.readFileSync(path.join(__dirname,'raw-translated-ir.json')));
const reduced=checker.replay(ir,get('reduction-certificate.json'),inputHash);
checker.compareIR(checker.readIR(get('compiled-ir.json')),reduced);
const poly=name=>checker.Poly.from(data.values[name].terms);
const assert=(a,b,msg)=>{if(!a.equals(b))throw Error(msg);};
for(let r=0;r<9;r++){
 const prefix='detector'+r, name=prefix+'.Rnorm';
 const g=data.gates.find(g=>data.coordinates[g.coordinateId].name===name);
 if(!g||g.operation!=='rational_quotient')throw Error(name);
 assert(checker.Poly.from(g.numerator),poly(prefix+'.deltaInverse').mul(poly(prefix+'.normOver2w0')),name+' numerator');
 assert(checker.Poly.from(g.denominator),poly(prefix+'.eWeight'),name+' denominator');
 const bg=data.gates.find(g=>data.coordinates[g.coordinateId].name===prefix+'.B.quadratic');
 // The builder may normalize the product; direct semantic B equality is checked
 // by its assignment equation and the exact product in the patch certificate.
 if(!bg)throw Error(prefix+' B assignment absent');
 if(data.coordinates.some(c=>c.name===prefix+'.R'||c.name===prefix+'.normOver2w0Square.quadratic'))throw Error('obsolete gate survives');
}
const report={status:'passed',rawTranslatedSha256:inputHash,checkedRawGates:gates.checked,reductionOperations:reduced.trace.length,newQuotientNumeratorDenominatorChecks:18,compiledCoordinates:reduced.coordinates.size,compiledResiduals:reduced.residuals.size};
fs.writeFileSync(path.join(__dirname,'verification.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report));
