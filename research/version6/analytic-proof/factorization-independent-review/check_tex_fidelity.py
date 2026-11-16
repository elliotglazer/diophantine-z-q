from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
paths=[ROOT/'quotient-audit/norm_transfer.tex',ROOT/'factorization/affine_pullback.tex',ROOT/'factorization/factorization.tex']
contexts=paths+[ROOT/'type-i-ii/type_i_ii.tex']
data={str(p.relative_to(ROOT)):p.read_text(encoding='utf-8') for p in contexts}
labels={}
for name,text in data.items():
 for label in re.findall(r'\\label\{([^}]+)\}',text): labels.setdefault(label,[]).append(name)
references={name:sorted(set(re.findall(r'\\(?:eqref|ref|autoref)\{([^}]+)\}',text))) for name,text in data.items()}
unresolved={name:[label for label in refs if label not in labels] for name,refs in references.items()}
duplicates={label:names for label,names in labels.items() if len(names)>1}
bib=set()
for p in (ROOT/'type-i-ii/check_fragment.tex',ROOT/'factorization/tex-qa/check.tex'):
 if p.exists(): bib.update(re.findall(r'\\bibitem\{([^}]+)\}',p.read_text(encoding='utf-8')))
cites={}
for name,text in data.items():
 keys={key.strip() for match in re.findall(r'\\cite(?:\[[^\]]*\])?\{([^}]+)\}',text) for key in match.split(',')}
 cites[name]=sorted(keys-bib)
report={'status':'passed_static_labels' if not any(unresolved.values()) and not duplicates and not any(cites.values()) else 'needs_attention','fragments':[{'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in paths],'context':{'path':'type-i-ii/type_i_ii.tex','sha256':hashlib.sha256(contexts[-1].read_bytes()).hexdigest()},'labelCount':len(labels),'unresolvedReferences':unresolved,'duplicateLabels':duplicates,'missingBibliographyKeysAgainstProvidedHarness':cites,'note':'Static reference and source-hash check only. Mathematical fidelity is assessed in TEX_FIDELITY.md. A full manuscript must include the provided GT bibliography keys. No PDF compilation is claimed.'}
(HERE/'tex-fidelity-static.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
