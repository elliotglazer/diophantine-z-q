from pathlib import Path
import hashlib
import json
import urllib.request
from pypdf import PdfReader

D=Path(__file__).resolve().parent/'sources'
D.mkdir(parents=True,exist_ok=True)
sources=[
('kollar-published.pdf','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/057467F70BBCC44C91A42896700A1353/S1474748002000117a.pdf/unirationality_of_cubic_hypersurfaces.pdf'),
('muller-published.pdf','https://www.numdam.org/article/AIF_2002__52_4_983_0.pdf')]
rows=[]
for name,url in sources:
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'})
        with urllib.request.urlopen(req,timeout=30) as r:
            raw=r.read(); final=r.url
        assert raw.startswith(b'%PDF'),raw[:40]
        p=D/name;p.write_bytes(raw)
        reader=PdfReader(p)
        p.with_suffix('.txt').write_text('\n\n'.join('PDF PAGE '+str(i+1)+'\n'+page.extract_text() for i,page in enumerate(reader.pages)),encoding='utf-8')
        rows.append({'file':name,'url':url,'resolved_url':final,'sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'pages':len(reader.pages)})
    except Exception as e:
        rows.append({'file':name,'url':url,'error':str(e)})
(D/'SOURCES.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
print(json.dumps(rows,indent=2))
