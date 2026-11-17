"""Generate X6Glue.lean = scratch/shimura-glue/RowsGlue.lean (verbatim, over TailK; contains
shimura-split's Rows.lean and shimura-glue's Adelic/Deligne/Mobius/RayClass parts) + this task's parts
EvalAffine, Charts, ConicProof, X6New (imports merged)."""
d='scratch/x6-glue/'
def split(path):
    s=open(path).read()
    imports=[l for l in s.splitlines() if l.startswith('import ')]
    body='\n'.join(l for l in s.splitlines() if not l.startswith('import '))
    return imports, body
ir, br = split('scratch/shimura-glue/RowsGlue.lean')
parts=['EvalAffine','Charts','ConicProof','X6New']
out='\n'.join(ir)+'\n'+br
for p in parts:
    _, b = split(d+'parts/'+p+'.lean')
    out+='\n\n/-! # x6-glue part: parts/'+p+'.lean -/\n'+b+'\n'
open(d+'X6Glue.lean','w').write(out)
print('ok', out.count('\n'))
