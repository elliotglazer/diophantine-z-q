"""Independent replay of frozen962 compiler reductions and polynomial table."""
from verify import *
import collections

ROOT=HERE.parent/'combined'
rawpath=ROOT/'raw-translated-ir.json'
raw=json.loads(rawpath.read_text());cert=json.loads((ROOT/'frozen/reduction-certificate.json').read_text())
assert hashlib.sha256(rawpath.read_bytes()).hexdigest()==cert['inputSha256']
rows={r['id']:readpoly(r['terms']) for r in raw['residuals']}
coords={x['id']:x for x in raw['coordinates']};counts=collections.Counter()
for step in cert['operations']:
    kind=step['kind'];counts[kind]+=1
    if kind=='normalize':
        r=step['residual'];a=Q(step['multiplier']);assert a
        rows[r]={k:a*v for k,v in rows[r].items()}
    elif kind=='row_add':
        r,s=step['target'],step['source'];assert r!=s
        rows[r]=add(rows[r],mul({(0,()):Q(step['factor'])},rows[s]))
    elif kind=='eliminate':
        x,r=step['coordinate'],step['pivot'];p=rows[r];q=readpoly(step['replacement'])
        assert x!=0 and not coords[x].get('protected')
        assert p.get((0,(x,)))==Q(step['coefficient'])!=0
        assert all(x not in m or (s,m)==(0,(x,)) for s,m in p)
        assert x not in variables(q) and subst(p,x,q)=={}
        affected={t for t,f in rows.items() if x in variables(f)}-{r}
        assert affected==set(step['affected'])
        for t in affected:
            rows[t]=subst(rows[t],x,q);assert degree(rows[t])<=2
        del rows[r];del coords[x]
    else:raise AssertionError(kind)
candidate=json.loads((ROOT/'frozen/compiled-ir.json').read_text())
assert rows=={r['id']:readpoly(r['terms']) for r in candidate['residuals']}
assert coords=={x['id']:x for x in candidate['coordinates']}
assert set(coords)==set.union(*(variables(p) for p in rows.values()))
assert coords[0]==raw['coordinates'][0]
poly=json.loads((ROOT/'frozen/polynomial.json').read_text())
# The polynomial table reindexes stable IDs to contiguous coordinate indices.
mapping={x['sourceId']:x['id'] for x in poly['coordinates']}
assert set(mapping)==set(coords) and mapping[0]==0
sos={}
for p in rows.values():
    q={(s,tuple(sorted(mapping[x] for x in m))):a for (s,m),a in p.items()}
    sos=add(sos,mul(q,q))
assert sos==readpoly(poly['terms'])
assert all(a.denominator==1 for a in sos.values())
result={'verified':True,'rawCoordinates':len(raw['coordinates']),'coordinates':len(coords),
  'residuals':len(rows),'monomials':len(sos),'quarticDegree':degree(sos),'operations':dict(counts),
  'inputPreserved':True,'unusedCoordinates':0,'rawSha256':cert['inputSha256'],
  'scope':'Exact compiler replay and sum-of-squares table, including every removal. Does not independently prove source-level analytic equivalence.'}
(HERE/'frozen-962-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
