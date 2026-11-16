from pathlib import Path
import hashlib

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'
text=(BASE/'builder/build_source.cjs').read_text()
old="let coeffs={};for(let m of [1,16,52]){let es=[fc(1)],j=0;for(let t of tests.filter(t=>t.order===m)){let y=fsq('testSquare.'+m+'.'+j,t.value),next=[fc(1)];for(let k=1;k<=es.length;k++)next[k]=fadd(k<es.length?es[k]:fc(0),fmul('symmetric.'+m+'.'+j+'.'+k,es[k-1],y));es=next;j++;}coeffs[m]=es;}"
new=r'''
// Product trees with exact rational interpolation. Every factor has constant 1.
// The dynamic program chooses direct convolution when it uses fewer products.
function polyEval(p,x){let v=fc(0),power=Q(1);for(let a of p){v=fadd(v,fscale(a,power));power=qmul(power,Q(x));}return v;}
function interpBasis(n){let basis=[];for(let i=0;i<=n;i++){
 let p=[Q(1)],den=Q(1);for(let j=0;j<=n;j++)if(i!==j){
  let next=Array.from({length:p.length+1},()=>Q(0));
  for(let k=0;k<p.length;k++){next[k]=qadd(next[k],qmul(p[k],Q(-j)));next[k+1]=qadd(next[k+1],p[k]);}
  p=next;den=qmul(den,Q(i-j));
 }basis.push(p.map(c=>qmul(c,qinv(den))));}return basis;}
let treeSerial=0;
function polyProduct(a,b,label){let m=a.length-1,n=b.length-1,d=m+n;
 let name=label+'.product'+treeSerial++;
 if(m*n<=d){let out=Array.from({length:d+1},()=>fc(0));
  for(let i=0;i<=m;i++)for(let j=0;j<=n;j++)out[i+j]=fadd(out[i+j],i===0?b[j]:j===0?a[i]:fmul(name+'.'+i+'.'+j,a[i],b[j]));
  return out;
 }
 let vals=[fc(1)];for(let x=1;x<=d;x++)vals.push(fmul(name+'.evaluation'+x,polyEval(a,x),polyEval(b,x)));
 let basis=interpBasis(d),out=[];for(let k=0;k<=d;k++){let v=fc(0);for(let x=0;x<=d;x++)v=fadd(v,fscale(vals[x],basis[x][k]));out.push(v);}return out;
}
let costs=[0,0],splits=[0,0];for(let n=2;n<=16;n++){costs[n]=Infinity;for(let k=1;k<n;k++){let c=costs[k]+costs[n-k]+Math.min(k*(n-k),n);if(c<costs[n]){costs[n]=c;splits[n]=k;}}}
function productTree(leaves,label){if(leaves.length===1)return [fc(1),leaves[0]];let k=splits[leaves.length];return polyProduct(productTree(leaves.slice(0,k),label),productTree(leaves.slice(k),label),label);}
let coeffs={};for(let m of [1,16,52]){let leaves=tests.filter(t=>t.order===m).map((t,j)=>fsq('testSquare.'+m+'.'+j,t.value));coeffs[m]=productTree(leaves,'symmetric.'+m);}
'''
assert old in text
text=text.replace(old,new)
text=text.replace("const inputSource=path.resolve(__dirname,'..',sourceName);",f"const inputSource={str(BASE/'sources/diophantine_optimization_20261106_v3.tex')!r};")
(HERE/'build_source.cjs').write_text(text)
(HERE/'symmetric-replacement.cjs').write_text(new)
print('prepared',hashlib.sha256(text.encode()).hexdigest())
