'use strict';
const fs=require('node:fs'),path=require('node:path');
const here=path.resolve(__dirname,'../dag-sharing'),base=path.resolve(here,'../../quartic-version5-release/repository/quartics/quartic-1272');
const chk=require(path.join(base,'checker/checker.cjs')),{Poly,Q}=chk;
const dir=path.join(here,'log-candidate'),rawBytes=fs.readFileSync(path.join(dir,'raw-translated-ir.json'));
const data=JSON.parse(rawBytes),raw=chk.readIR(data),gateResult=chk.checkGates(raw);
const cert=JSON.parse(fs.readFileSync(path.join(dir,'reduction-certificate.json')));
const result=chk.replay(raw,cert,chk.hashBytes(rawBytes));
chk.compareIR(chk.readIR(JSON.parse(fs.readFileSync(path.join(dir,'compiled-ir.json')))),result);
const zero=()=>Poly.constant(new Q(0)),constant=n=>Poly.constant(new Q(n));
const fmul=(a,b)=>[a[0].mul(b[0]).add(a[1].mul(b[1]).scale(new Q(2))),a[0].mul(b[1]).add(a[1].mul(b[0]))];
const fscale=(a,q)=>a.map(p=>p.scale(q));
const fadd=(a,b)=>a.map((p,i)=>p.add(b[i]));
const coeffs=[new Q(1),new Q(-2,5)];for(let j=2;j<=12;j++)coeffs.push(coeffs[j-1].mul(new Q(4*j-5,4*j+1)));
function evaluate(terms,env){let p=zero();for(let t of terms){if(t.sPower)throw Error('unexpected S');let v=Poly.constant(Q.parse(t.coefficient));for(let i of t.monomial){if(!env.has(i))throw Error('unbound '+i);v=v.mul(env.get(i));}p=p.add(v);}return p;}
function bind(terms,v,env){if(terms.length!==1||terms[0].monomial.length!==1||terms[0].coefficient!=='1/1')throw Error('nontrivial input');env.set(terms[0].monomial[0],v);}
let checked=[];
for(let side of ['U','V'])for(let i=0;i<5;i++){
 const name='log'+side+i,env=new Map(),f=[Poly.coordinate(0),Poly.coordinate(1)],z=[Poly.coordinate(2),Poly.coordinate(3)];
 for(let j=0;j<2;j++){bind(data.values[side+i+'.f.'+j].terms,f[j],env);bind(data.values[side+i+'.z.'+j].terms,z[j],env);}
 const gates=data.gates.filter(g=>data.coordinates[g.coordinateId].name.startsWith(name+'.'));
 for(let g of gates){if(g.operation!=='quadratic_assignment')throw Error('unexpected log division');env.set(g.coordinateId,evaluate(g.expression,env));}
 const w=fmul([constant(11),constant(-6)],fmul(f,f));let expected=[zero(),zero()];
 const degree=i===1?3:12;
 for(let j=degree;j>=0;j--)expected=fadd(fmul(expected,w),[Poly.constant(coeffs[j]),zero()]);
 expected=fmul(z,expected);
 for(let j=0;j<2;j++){let actual=evaluate(data.values[name+'.'+j].terms,env);if(!actual.equals(expected[j]))throw Error(name+' component'+j+' failed');}
 checked.push({name,degree,gateCoordinates:gates.length});
}
const out={status:'passed',scope:'All ten emitted log circuits equal z*sum(a_j*(D*f^2)^j) as exact four-variable polynomials over Q(sqrt(2)); all raw gates and compiler reductions independently checked.',gateIdentities:gateResult.checked,compilerOperations:result.trace.length,logs:checked,rawSha256:chk.hashBytes(rawBytes)};
fs.writeFileSync(path.join(__dirname,'review-log-check.json'),JSON.stringify(out,null,2)+'\n');console.log(JSON.stringify(out));

