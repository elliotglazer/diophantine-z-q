// Exact direct binding of the final four BB poles, using integer polynomial arithmetic.
const fs=require('fs');const path=require('path');
function verifyPoles(q){
  const poly=(...terms)=>{const m=new Map();for(const [c,...ids] of terms){const k=ids.sort((a,b)=>a-b).join(",");m.set(k,(m.get(k)||0n)+BigInt(c))}for(const [k,v] of m)if(!v)m.delete(k);return m};
  const sum=(...ps)=>poly(...ps.flatMap(p=>[...p].map(([k,c])=>[c,...(k?k.split(",").map(Number):[])])));
  const times=(a,p)=>poly(...[...p].map(([k,c])=>[BigInt(a)*c,...(k?k.split(",").map(Number):[])]));
  const mul=(p,q)=>poly(...[...p].flatMap(([k,c])=>[...q].map(([l,d])=>[c*d,...(k?k.split(",").map(Number):[]),...(l?l.split(",").map(Number):[])])));
  const x=i=>poly([1,i]); const sq=p=>mul(p,p);
  const actual=n=>{const a=q.residuals.find(r=>r.name===n);if(!a||a.terms.some(t=>t.parameterPower!==0))throw Error(n+" missing/nonconstant");return poly(...a.terms.map(t=>[t.coefficient,...t.monomial]))};
  let count=0;
  function check(n,expected,scale=1){const a=times(scale,actual(n));if(a.size!==expected.size||[...a].some(([k,v])=>expected.get(k)!==v))throw Error("bad row "+n);count++}
  check("unit.c_inverse",poly([-1],[1,159,160]));
  check("unit.c_inverse_square",poly([-1,160,160],[1,161]));
  check("unit.R_square",poly([1,87],[-1,88,88]));
  check("shared.norm_error",poly([-1,153,153],[2,153,155],[2,153,160],[2,154,154],[-1,161]));
  check("shared.gate0",poly([2,63],[-1,151],[-1,155,155],[-1,156],[2,160],[-1,161]));
  const Q=[x(151),x(152),poly([1,160],[-1,151],[-1,152])];
  const g2=[poly([2,63]),poly([2,63],[1,152],[1,157],[-1,151],[-1,156]),poly([2,63],[-2,151],[-1,152],[1,158],[1,160],[-1,156])];
  const b=[64,72,170];
  for(let j=0;j<3;j++){check("shared.inverse"+j,sum(x(161),times(-1,mul(Q[j],x(156+j)))));check(`balanced.detector${j}.poleInput.definition`,sum(times(4*167281,mul(x(b[j]),sum(Q[j],x(161)))),times(-166464,sq(g2[j]))),4)}
  const rows=[[3,4,5,6,64,65,66,67,87,87],[7,8,9,10,72,73,74,75,87,161],[163,164,165,166,170,171,172,173,161,161]];
  for(let j=0;j<3;j++){const [e,U,p,z,B,P,V,Z,Eden,Qden]=rows[j];const d=`detector${j}`;check(d+".p2.definition",poly([1,p,p],[-1,P]));check("bbnative."+d+".firstConic",poly([9,e,e],[7,B,P],[-9,Eden,Eden]));check("bbnative."+d+".Bh.definition",poly([9,e,161],[-7,e,B],[-9,U,V]));check(d+".q2.definition",times(j===1?-1:1,poly([-1,z,z],[1,Z,Qden])));check("bbnative."+d+".secondConic",poly([9,U,U],[-7,B,Z],[-9,V,V]))}
  check("v82.scalar.inverse",poly([1,79,86],[-1,87,87]));check("v82.scalar.input",poly([1,79,80],[-1,87],[-9792,88]));
  check("v82.scalar.p2",poly([-1,13,13],[1,79,81]));check("v82.scalar.q2",poly([-1,14,14],[1,79,83]));
  check("bbnative.v82.scalar.first",poly([9,11,11],[-9,79,79],[7,80,81]));
  check("bbnative.v82.scalar.middle",poly([9,11,79],[-7,11,80],[-9,12,82]));
  check("bbnative.v82.scalar.second",poly([9,12,12],[-7,80,83],[-9,82,82]));
  return {rows:count,comparison_poles:3,scalar_poles:1,status:"PASS"};
}
console.log(JSON.stringify(verifyPoles(JSON.parse(fs.readFileSync(path.join(__dirname,'source/computation/projective_contacts_20261126/quadrics.json'),'utf8')))));
