"""Apply two exact source changes to the immutable baseline builder."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[1] / 'quartic-version5-release/repository/quartics/quartic-1272'
s = (BASE / 'builder/build_source.cjs').read_text()
s = s.replace("const inputSource=path.resolve(__dirname,'..',sourceName);", "const inputSource=" + repr(str(BASE / 'sources/diophantine_optimization_20261106_v3.tex').replace('\\','/')) + ";")
old = """ const B=scale(b,17), ee=assign(name+'.ePolynomial',mul(sub(one,p.e),add(one,scale(p.e,3))));
 residual(name+'.firstConic',sub(sq(p.p),mul(B,ee)));"""
new = """ // p.e now stores C*old_e, where C=17*b is nonzero.
 const B=scale(b,17), pp=rsq(name+'.p2',p.p);
 residual(name+'.firstConic',sub(mul(B,pp),mul(sub(B,p.e),add(B,scale(p.e,3)))));"""
assert old in s
s = s.replace(old,new)
old = "let h=rm(name+'.h',p.e,sub(B,rsq(name+'.U2',Up))),Bh=rm(name+'.Bh',B,h),ss="
new = "let Bh=rm(name+'.Bh',p.e,sub(B,rsq(name+'.U2',Up))),ss="
assert old in s
s = s.replace(old,new)
old = """let correction=sub(one,scale(booleans[7],2));for(let i=0;i<7;i++)correction=rm('correction.product'+i,correction,add(one,scale(booleans[i],[2,3,5,7,11,13,17][i]-1)));
for(let i=0;i<8;i++)residual('correction.boolean'+i,sub(sq(booleans[i]),booleans[i]));"""
new = """// These eight base variables are now signed partial products, not Booleans.
residual('correction.initialSign',sub(sq(booleans[0]),one));
for(let i=1;i<8;i++){
 const p=[2,3,5,7,11,13,17][i-1];
 residual('correction.partialProduct'+i,add(sq(booleans[i]),scale(mul(booleans[i],booleans[i-1]),-p-1),scale(sq(booleans[i-1]),p)));
}
let correction=booleans[7];"""
assert old in s
s = s.replace(old,new)
s = s.replace("fresh('correction.'+p,'base')", "fresh('correction.partial.'+p,'base')")
s = s.replace("e:fresh('detector'+r+'.e','base')", "e:fresh('detector'+r+'.scaled_e','base')")
s = s.replace("e:fresh('scalar.e','base')", "e:fresh('scalar.scaled_e','base')")
s = s.replace("fs.writeFileSync(path.join(OUT,'raw-ir.json')", "data.variant={name:'source_compression_17',baseline:'quartic-1272',changes:['pole_e_rescaled_by_17b','signed_partial_product_correction_chain'],proof:'PROOF.md',status:'pending_independent_review'};\nfs.writeFileSync(path.join(OUT,'raw-ir.json')", 1)
(HERE/'build_source.cjs').write_text(s)
print(HERE/'build_source.cjs')
