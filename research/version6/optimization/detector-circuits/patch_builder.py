"""Exact polynomial circuit replacements; accepts other workers' builder text."""
from pathlib import Path
import argparse

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'

def patch(text):
    start=text.index("const AA=fmul('Lucas.A'")
    end=text.index('const tests=',start)
    text=text[:start]+'''const CC=fmul('Lucas.C',fsub(L[2],fc(2)),L[4]), AT=fmul('Lucas.AT',L[2],L[3]);
const FF=[assign('Lucas.F0',add(sq(L[3][0]),scale(sq(L[3][1]),2),scale(mul(AT[0],CC[0]),-1),scale(mul(AT[1],CC[1]),-2),sq(CC[0]),scale(sq(CC[1]),2),C(-1))),assign('Lucas.F1',add(scale(mul(L[3][0],L[3][1]),2),scale(mul(AT[0],CC[1]),-1),scale(mul(AT[1],CC[0]),-1),scale(mul(CC[0],CC[1]),2)))];
'''+text[end:]
    start=text.index('let coeffs={};')
    end=text.index("start('fixed_height_scales'",start)
    text=text[:start]+'''function polyProduct(name, ys) {
 if(ys.length===1)return [fc(1),ys[0]];
 let cut=Math.floor(ys.length/2),a=polyProduct(name+'.left',ys.slice(0,cut)),b=polyProduct(name+'.right',ys.slice(cut)),out=[fc(1)];
 for(let k=1;k<a.length+b.length-1;k++){
  let c=[zero,zero];
  for(let i=Math.max(0,k-b.length+1);i<=Math.min(k,a.length-1);i++){
   let u=a[i],v=b[k-i];
   c[0]=add(c[0],mul(u[0],v[0]),scale(mul(u[1],v[1]),2));
   c[1]=add(c[1],mul(u[0],v[1]),mul(u[1],v[0]));
  }
  out[k]=[assign(name+'.co'+k+'.0',c[0]),assign(name+'.co'+k+'.1',c[1])];
 }
 return out;
}
let coeffs={};for(let m of [1,16,52])coeffs[m]=polyProduct('symmetric.'+m,tests.filter(t=>t.order===m).map((t,j)=>fsq('testSquare.'+m+'.'+j,t.value)));
'''+text[end:]
    start=text.index('function evalSym(')
    end=text.index('function pole(',start)
    text=text[:start]+'''function evalSym(name,co,q){
 let powers=[one,q];for(let k=2;k<co.length;k++)powers[k]=rm(name+'.power'+k,powers[Math.floor(k/2)],powers[Math.ceil(k/2)]);
 let out=[zero,zero];for(let k=0;k<co.length;k++)for(let j=0;j<2;j++)out[j]=add(out[j],mul(co[k][j],powers[k]));
 return saveF(name,[assign(name+'.sum.0',out[0]),assign(name+'.sum.1',out[1])]);
}
'''+text[end:]
    start=text.index(" let f1=rm('detector'+r+'.Fpair1'")
    end=text.index(" let fi=inv(",start)
    # F=t(t+1/2)(t+1)(t-1/2399)(t+32/407).
    # Coefficients are computed exactly in Q once, without expanded huge S.
    text=text[:start]+''' let roots=[Q(0),Q(1,2),Q(1),Q(-1,2399),Q(32,407)],cs=[Q(1)];
 for(let root of roots){let nx=Array(cs.length+1).fill(null).map(()=>Q(0));for(let k=0;k<cs.length;k++){nx[k]=qadd(nx[k],qmul(root,cs[k]));nx[k+1]=qadd(nx[k+1],cs[k]);}cs=nx;}
 let t2=rsq('detector'+r+'.Fsquare',t),middle=assign('detector'+r+'.Fmiddle',add(mul(t2,add(t,term(cs[4]))),scale(t,cs[3]),term(cs[2]))),Fv=assign('detector'+r+'.F',add(mul(t2,middle),scale(t,cs[1]),term(cs[0])));
'''+text[end:]
    text=text.replace("let leaves=[...PU[0].f,...PS.f,...zRatio].map((v,i)=>rm('scalar.leaf'+i,v,i<4?ri:ri32));", "let leaves=[...PU[0].f,...PS.f,...zRatio].map((v,i)=>i===0||i===2?save('scalar.leaf'+i,mul(v,ri)):rm('scalar.leaf'+i,v,i<4?ri:ri32));")
    text=text.replace("let n0=normTree('scalar.n0',one,leaves[0]),n1=normTree('scalar.n1',leaves[1],leaves[2]),n3=normTree('scalar.n3',leaves[4],leaves[5]);", "let n0=rquot('scalar.n0',add(rr,sq(PU[0].f[0])),rr,'existing_scalar_r_inverse'),n1=rquot('scalar.n1',add(mul(leaves[1],PU[0].f[1]),sq(PS.f[0])),rr,'existing_scalar_r_inverse'),n3=normTree('scalar.n3',leaves[4],leaves[5]);")
    return text

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,default=BASE/'builder/build_source.cjs');p.add_argument('--output',type=Path,default=HERE/'build_candidate.cjs');a=p.parse_args()
    source=patch(a.input.read_text())
    # All writes stay beside the selected output. Source provenance reads immutable baseline.
    source=source.replace("path.resolve(__dirname,'..',sourceName)","path.resolve("+repr(str(BASE).replace('\\','/'))+",sourceName)")
    a.output.write_text(source)
