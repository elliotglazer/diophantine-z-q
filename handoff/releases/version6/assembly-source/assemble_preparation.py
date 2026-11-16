"""Build an unpublished Version 6 working source from the frozen Version 5.

This does not remove the FT qualification or publish any artifact.  The
replacement analytic fragments have their own unfinished acceptance gate.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT / 'work/quartic-version5-release/repository/quartic_1272.tex'
EXPECTED = '16033e0471df605093b28210a9f81718c2486b147016ec8afc75d166dff0b90f'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

assert sha(BASE) == EXPECTED, 'Version 5 source changed; inspect before rebasing'
s = BASE.read_text(encoding='utf-8')
edits = []

def once(old, new, note):
    global s
    assert s.count(old) == 1, (note, s.count(old))
    s = s.replace(old, new, 1)
    edits.append(note)

once(r'\large Version 5.', r'\large Version 6.', 'Version number')
once('integer coefficient table. We also specify a quartic in $1\\,272$ variables\n'
     'with $48\\,001$ nonzero monomials and maximum coefficient magnitude',
     'integer coefficient table. We also specify a quartic in $962$ variables\n'
     'with $55\\,409$ nonzero monomials and maximum coefficient magnitude',
     'Third abstract polynomial only')
once('A third polynomial, in $1\\,272$ variables, is constructed in\n'
     'Section~\\ref{sec:v5-1272}.',
     'A third polynomial, in $962$ variables, is constructed in\n'
     'Section~\\ref{sec:v6-962}.', 'Third introductory polynomial')
once('The $4\\,973$-variable polynomial\n'
     'is retained with its ordinary, fully expanded integer coefficients.',
     'The $4\\,973$-variable polynomial\n'
     'is retained with its ordinary, fully expanded integer coefficients.\n'
     'Section~\\ref{sec:degree-lower-bound} proves that a single polynomial\n'
     'defining $\\Z$ in $\\Q$ must have total degree at least four, following\n'
     'Brox. Thus the degree of a quartic definition is optimal.',
     'Introductory degree lower bound')
once('\\section{The shared-point quartic in 1272 variables}\n'
     '\\label{sec:v5-1272}',
     '\\section{The shared-point quartic in 962 variables}\n'
     '\\label{sec:v6-962}', 'Third construction section')
once('Our contribution here is an\n'
     'independently specified gate program, its source verification, and the\n'
     'complete polynomial obtained after 32 certified eliminations.',
     'Our contribution here is an\n'
     'independently specified gate program, its source verification, and\n'
     'further changes of coordinates and circuit identities leading to a\n'
     '962-variable polynomial after 32 certified eliminations.',
     'Circuit attribution')
start = s.index('\\begin{theorem}[The new quartic]\\label{thm:v5-1272-polynomial}')
end = s.index('\\subsection{Points, local parameters, and quotient domains}', start)
s = s[:start] + ('The point, pole, and correction variables below specify the\n'
                  'arithmetic source predicate. The final compilation subsection\n'
                  'gives explicit maps to its implementation coordinates.\n\n') + s[end:]
edits.append('Remove superseded 1272 theorem, preserve semantic source')
start = s.index('\\subsection{Exact quadratic compilation and the complete table}')
end = s.index('% End Version 5 main additions', start)
fragment = HERE / 'quartic-962/construction.tex'
s = s[:start] + fragment.read_text(encoding='utf-8') + '\n\n' + s[end:]
edits.append('Replace full compilation subsection with reviewed 962 fragment')
lower = HERE / 'lower-bound/degree_lower_bound.tex'
once('\\appendix', lower.read_text(encoding='utf-8') + '\n\n\\appendix',
     'Insert independently reviewed degree lower bound')
bib = HERE / 'lower-bound/bibliography.tex'
once('\\begin{thebibliography}{99}',
     '\\begin{thebibliography}{99}\n' + bib.read_text(encoding='utf-8'),
     'Add published lower-bound bibliography')

labels = re.findall(r'\\label\{([^}]+)\}', s)
refs = re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', s)
duplicates = sorted({x for x in labels if labels.count(x) > 1})
missing = sorted(set(refs) - set(labels))
assert not duplicates, duplicates
assert not missing, missing
OUT = HERE / 'manuscript'
OUT.mkdir(exist_ok=True)
target = OUT / 'quartic_962-preparation.tex'
target.write_text(s, encoding='utf-8', newline='\n')
report = dict(status='unpublished_preparation_FT_dependency_still_present',
              source=str(BASE), source_sha256=sha(BASE), output=str(target),
              output_sha256=sha(target), edits=edits,
              inputs=[dict(path=str(p), sha256=sha(p)) for p in (fragment, lower, bib)],
              labels=len(labels), references=len(refs),
              missing_references=missing, duplicate_labels=duplicates,
              publication_authorized_after_full_goal_verified=True)
(OUT / 'PREPARATION.json').write_text(json.dumps(report, indent=2) + '\n',
                                     encoding='utf-8')
print(json.dumps(report, indent=2))
