"""Additional nine-coordinate reduction applied to the combined candidate."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
OUT=HERE/'final-b'
OUT.mkdir(exist_ok=True)
s=(HERE.parent/'combined/build_source.cjs').read_text()
changes=[]
def patch(old,new):
    global s
    assert s.count(old)==1,s.count(old)
    s=s.replace(old,new);changes.append({'old':old,'new':new})
patch(",Rv=rquot('detector'+r+'.R',di,ep,'nonzero_numerator_di_enforces_denominator')","")
patch("bv=rm('detector'+r+'.B',Rv,rsq('detector'+r+'.normOver2w0Square',nw))",
      "bv=rm('detector'+r+'.B',nw,rquot('detector'+r+'.Rnorm',mul(di,nw),ep,'positive_scale_weight_enforces_nonzero_ep'))")
(OUT/'build_source.cjs').write_text(s,newline='\n')
(OUT/'patch.json').write_text(json.dumps(changes,indent=2)+'\n')
print(OUT)
