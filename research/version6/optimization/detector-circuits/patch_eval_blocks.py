"""Split degree-ten evaluation in half; fuse the low block into the output."""
from pathlib import Path
def patch(text):
    start=text.index('function evalSym(');end=text.index('function pole(',start)
    return text[:start]+'''function evalSym(name,co,q){
 let split=co.length===11?5:co.length-1;
 let powers=[one,q];for(let k=2;k<=split;k++)powers[k]=rm(name+'.power'+k,powers[Math.floor(k/2)],powers[Math.ceil(k/2)]);
 let out=[zero,zero];
 if(co.length===11){
  let high=[zero,zero];for(let k=5;k<co.length;k++)for(let j=0;j<2;j++)high[j]=add(high[j],mul(co[k][j],powers[k-5]));
  let block=[assign(name+'.high.0',high[0]),assign(name+'.high.1',high[1])];
  for(let j=0;j<2;j++)out[j]=mul(powers[5],block[j]);
  for(let k=0;k<5;k++)for(let j=0;j<2;j++)out[j]=add(out[j],mul(co[k][j],powers[k]));
 }else for(let k=0;k<co.length;k++)for(let j=0;j<2;j++)out[j]=add(out[j],mul(co[k][j],powers[k]));
 return saveF(name,[assign(name+'.sum.0',out[0]),assign(name+'.sum.1',out[1])]);
}
'''+text[end:]
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    a.output.write_text(patch(a.input.read_text()))
