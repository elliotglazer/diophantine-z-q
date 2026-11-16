"""Static TeX fragment checks; this does not replace a TeX compilation."""
from pathlib import Path
import hashlib,json,re
here=Path(__file__).resolve().parent
paths=[here.parent/'quotient-audit/norm_transfer.tex',here/'affine_pullback.tex',here/'factorization.tex',here.parent/'type-i-ii/type_i_ii.tex']
labels={};refs=[];files=[]
for path in paths:
    source=path.read_text()
    text=re.sub(r'(?<!\\)%[^\n]*','',source)
    depth=0
    for char in re.sub(r'\\[{}]','',text):
        depth+=(char=='{')-(char=='}')
        assert depth>=0,('unbalanced braces',path)
    assert depth==0,('unbalanced braces',path,depth)
    stack=[]
    for kind,name in re.findall(r'\\(begin|end)\{([^}]+)\}',text):
        if kind=='begin':stack.append(name)
        else:assert stack and stack.pop()==name,('environment mismatch',path,name)
    assert not stack,('unclosed environments',path,stack)
    for label in re.findall(r'\\label\{([^}]+)\}',text):
        assert label not in labels,('duplicate label',label)
        labels[label]=str(path)
    refs.extend(re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',text))
    files.append({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'braceAndEnvironmentCheck':'passed'})
missing=sorted(set(refs)-set(labels))
assert not missing,missing
out={'status':'static checks passed','files':files,'labelCount':len(labels),'referenceCount':len(refs),'unresolvedReferences':missing,
     'texCompilation':'not completed: installed MiKTeX needs first-run setup in nonwritable AppData/Roaming/MiKTeX/2.9; no system setup changed'}
(here/'TEX_CHECK.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
