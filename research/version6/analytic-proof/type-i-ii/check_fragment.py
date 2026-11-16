"""Static TeX cross-reference checks and a hash-bound handoff receipt."""
import hashlib,json,re
from pathlib import Path

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parents[1]/'quartic-version5-release/sun-proof/sources'

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def clean(s):return re.sub(r'(?<!\\)%[^\n]*','',s)
def check_braces(s):
    depth=0
    for m in re.finditer(r'(?<!\\)[{}]',s):
        depth+=1 if m.group()=='{' else -1
        assert depth>=0,('closing brace',m.start())
    assert depth==0,depth
def check_envs(s):
    stack=[]
    for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',s):
        kind,name=m.groups()
        if kind=='begin':stack.append(name)
        else:assert stack.pop()==name,name
    assert not stack

files=[HERE/'type_i_ii.tex',HERE.parent/'quotient-audit/norm_transfer.tex']
content='\n'.join(clean(p.read_text()) for p in files)
for p in files:
    s=clean(p.read_text());check_braces(s);check_envs(s)
labels=re.findall(r'\\label\{([^}]+)\}',content)
assert len(labels)==len(set(labels))
refs=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',content)
assert set(refs)<=set(labels),set(refs)-set(labels)
citations=set()
for item in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',content):citations.update(item.split(','))
assert citations<={'GTOrbits2012','GTMobius2012'}
own=clean(files[0].read_text())
assert all(x.startswith('gi-') for x in re.findall(r'\\label\{([^}]+)\}',own))
receipt={'status':'Proof fragment prepared; static checks pass; TeX engine unavailable in sandbox configuration',
 'proof':{'path':str(files[0]),'sha256':digest(files[0])},
 'normTransfer':{'path':str(files[1]),'sha256':digest(files[1]),'label':'lem:gn-norm-transfer'},
 'argumentReview':{'path':str(HERE/'ROOT_REVIEW.md'),'sha256':digest(HERE/'ROOT_REVIEW.md'),
   'scope':'Independent review of TYPE_I_II.md argument before TeX transcription'},
 'reviewedArgument':{'path':str(HERE/'TYPE_I_II.md'),'sha256':digest(HERE/'TYPE_I_II.md')},
 'publishedSources':[{'path':str(SOURCE/n),'sha256':digest(SOURCE/n)} for n in ['GT-orbits-published.pdf','GT-mobius-published.pdf']],
 'staticChecks':{'balancedBraces':True,'balancedEnvironments':True,'uniqueLabels':True,
   'resolvedCrossReferencesIncludingNormTransfer':True,'ownLabels':len(re.findall(r'\\label\{([^}]+)\}',own)),
   'citationKeys':sorted(citations)},
 'latexCompile':{'attempted':True,'passed':False,'reason':'MiKTeX fresh setup attempts forbidden creation of C:/Users/glaze/AppData/Roaming/MiKTeX/2.9 before reading the document. No TeX syntax diagnostic was produced.'},
 'mathematicalScope':'Gaussian and ordinary-prime mean-zero minor-arc estimates. Hecke Siegel-Walfisz, progression main terms, factorization and final counting remain separately audited. No integration or publication.'}
(HERE/'TEX_HANDOFF.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
