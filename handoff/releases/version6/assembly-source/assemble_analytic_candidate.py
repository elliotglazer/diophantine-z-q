"""Assemble the complete Version 6 candidate for review, without publication."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
A = ROOT / 'work/frei-tinkova-removal-001'
base = HERE / 'manuscript/quartic_962-preparation.tex'
s = base.read_text(encoding='utf-8')
inputs = [base]
edits = []
key_map = {'GTMobius2012': 'moebius', 'v6gtlinear': 'greentao'}

def load(path):
    inputs.append(path)
    text = path.read_text(encoding='utf-8')
    for old, new in key_map.items():
        text = text.replace('{' + old + '}', '{' + new + '}')
    return text

def once(old, new, note):
    global s
    assert s.count(old) == 1, (note, s.count(old))
    s = s.replace(old, new, 1)
    edits.append(note)

old_intro = '''and the order in which the parameters are chosen. One input has a different
publication status from the others. The Artin-symbol linear-forms theorem
of Frei and Tinkov\\'a~\\cite{v5ft}, Theorem~1.4 of arXiv version~3, is
unconditional and is listed by an author as accepted by \\emph{Mathematika}.
We have not verified a final published version. We use that exact theorem
as an external input, and do not claim that the following proof has only
published external inputs. In particular, the proof below does not replace
their ideal-norm nilsequence argument.'''
new_intro = r'''and the order in which the parameters are chosen. For the analytic input
we prove the special case for fixed ray class fields of $\Q(i)$ directly.
The ideal-norm method follows Frei and Tinkov\'a~\cite{v5ft}; no theorem
from that work is assumed. The proof uses the published fixed-field prime
estimate of Mitsui, the one-parameter equidistribution and factorization
results of Green--Tao, and published ordinary-prime transference results.
The field and its ray modulus are fixed before every asymptotic limit.
The exact source versions checked are identified in the bibliography
and the accompanying theorem-application inventory.'''
once(old_intro, new_intro, 'Replace external FT assumption by internal Gaussian proof scope')

progression = load(A / 'progression_mainterms.tex')
sw = load(A / 'published-input-audit/gaussian_hecke_sw.tex')
start = progression.index('% Working replacement fragment.')
end = progression.index(r'\subsection{')
progression = progression[end:]
marker = 'The progression input needed below is the following fixed-field Hecke\nSiegel--Walfisz assertion.'
assert progression.count(marker) == 1
progression = progression.replace(marker, sw + '\n\n' +
    r'The preceding lemma gives the following consequence, including $Y=0$ by the empty-sum convention.' + '\n', 1)
progression = progression.replace('% SOURCE GATE: insert the independently checked published source and\n% explicit correction proof before integrating this fragment.\n', '')
progression = progression.replace(r'Assume \eqref{eq:gaussian-hecke-sw-input}.  For', 'For')
progression = progression.replace(r'Assume \eqref{eq:gaussian-hecke-sw-input}.  For every', 'For every')
assert 'SOURCE GATE' not in progression
old_display = r'''\[
 \mu_C(b)=
 \frac{\#\{g\in C:g|_{K^{\mathrm{ab}}}=\sigma_b|_{K^{\mathrm{ab}}}\}}
      {[K:K^{\mathrm{ab}}]},\quad
 f_{C,b,W}(n)=\frac{\varphi(W)}W\Lambda'_C(Wn+b),\quad
 \lambda_{b,W}(n)=\frac{\varphi(W)}W\Lambda'(Wn+b).
\]'''
new_display = r'''\[
\begin{aligned}
 \mu_C(b)&=
 \frac{\#\{g\in C:g|_{K^{\mathrm{ab}}}=\sigma_b|_{K^{\mathrm{ab}}}\}}
      {[K:K^{\mathrm{ab}}]},\\
 f_{C,b,W}(n)&=\frac{\varphi(W)}W\Lambda'_C(Wn+b),\\
 \lambda_{b,W}(n)&=\frac{\varphi(W)}W\Lambda'(Wn+b).
\end{aligned}
\]'''
assert progression.count(old_display) == 1
progression = progression.replace(old_display, new_display)

parts = [progression]
for path in ['quotient-audit/norm_transfer.tex', 'type-i-ii/type_i_ii.tex',
             'factorization/affine_pullback.tex', 'factorization/factorization.tex',
             'gowers-bridge/bridge.tex']:
    text = load(A / path)
    # The two components used distinct names for the same explicitly normalized weight.
    if path == 'factorization/affine_pullback.tex':
        text = text.replace(r'\Lambda_{b,W}', r'\lambda_{b,W}')
    if path == 'gowers-bridge/bridge.tex':
        old_display = r'''\begin{equation}\label{eq:gaussian-centered-nil-input}
 \left|\mathbb E_{n\leq L}h_{C,V,b}(n)F(g(n)\Gamma)\right|
 \ll_{V,B,\mathrm{complexity}}(\log L)^{-B},\qquad
 h_{C,V,b}(n)=\frac{\varphi(V)}V
 \bigl(\Lambda'_C(Vn+b)-\mu_C(b)\Lambda'(Vn+b)\bigr).
\end{equation}'''
        new_display = r'''\begin{equation}\label{eq:gaussian-centered-nil-input}
\begin{aligned}
 \left|\mathbb E_{n\leq L}h_{C,V,b}(n)F(g(n)\Gamma)\right|
 &\ll_{V,B,\mathrm{complexity}}(\log L)^{-B},\\
 h_{C,V,b}(n)&=\frac{\varphi(V)}V
 \bigl(\Lambda'_C(Vn+b)-\mu_C(b)\Lambda'(Vn+b)\bigr).
\end{aligned}
\end{equation}'''
        assert text.count(old_display) == 1
        text = text.replace(old_display, new_display)
    parts.append(text)
analytic = '\n\n'.join(parts)
once(r'\subsection{Fixed Artin conditions in quadratic patterns}',
     analytic + '\n\n' + r'\subsection{Fixed Artin conditions in quadratic patterns}',
     'Insert full reviewed analytic components and bridge candidate')
start = s.index(r'\begin{remark}[A norm exponent in the imported proof]')
end = s.index(r'\end{remark}', start) + len(r'\end{remark}')
s = s[:start] + s[end:]
edits.append('Remove superseded FT proof-repair remark; replacement states correct inverse norm')
once('Here the field is fixed throughout the limiting argument. Let $K/\\mathbb Q$\n'
     'be finite Galois, put $G=\\operatorname{Gal}(K/\\mathbb Q)$, and let\n'
     '$C_1,\\ldots,C_k$ be conjugacy-invariant subsets of $G$.',
     'Here the field is fixed throughout the limiting argument. Let $K$ be the\n'
     'ray class field of $\\Q(i)$ for $H\\Z[i]$, where $16\\mid H$. Put\n'
     '$G=\\operatorname{Gal}(K/\\Q)$, and let $C_1,\\ldots,C_k$ be\n'
     'conjugation-invariant subsets of $\\operatorname{Gal}(K/\\Q(i))$,\n'
     'regarded as conjugacy-invariant subsets of $G$.', 'Specialize polynomial count to exactly proved Gaussian fields')
start = s.index('We specify how the linear Artin theorem and the published polynomial')
end = s.index('Choose a small positive', start)
s = s[:start] + r'''The Gaussian linear replacement of
Lemma~\ref{lem:gaussian-linear-replacement} and its local-cube consequence
\eqref{eq:gaussian-global-gowers} supply the analytic input. We record
the normalization and polynomial-transfer parameters here.

''' + s[end:]
start = s.index('View these functions on $\\mathbb Z/n\\mathbb Z$')
end = s.index('We now use the arbitrary-function dense-model theorem', start)
s = s[:start] + r'''View these functions on $\mathbb Z/n\mathbb Z$, with representatives
$1,\ldots,n$. If $a\geq2$ and $C_1<C_2<C_3$ are fixed,
\eqref{eq:gaussian-global-gowers} gives
\begin{equation}\label{eq:v5-global-gowers}
 \|g_{j,b}\|_{U^a_{q[J]}}^{2^a}
       \ll_a(\log v)^{-1}+o_v(1),
 \quad q\leq A^{C_1},\quad
 nA^{-C_3}\leq J\leq nA^{-C_2}.
\end{equation}
The implicit constant may also depend on the other fixed complexities
and the fixed ray field. The norm, wrap-around regions, conditional
densities, and order of the auxiliary cutoff are all treated explicitly
in Section~\ref{subsec:gaussian-gowers-bridge}.

''' + s[end:]
edits.append('Replace FT linear invocation and imported cube argument')
once('End intervals of length $O(T^2)=o(N)$\nare harmless by the ordinary majorant.',
     'End intervals of length $O(T^2)=o(N)$\nare controlled by the weighted second-moment localization and the\n'
     'fixed-strip argument in Section~\\ref{subsec:gaussian-gowers-bridge}.',
     'Bind boundary treatment to explicit localization proof')

bib = load(A / 'published-input-audit/bibliography.tex') + r'''
\bibitem{GTOrbits2012}
B. Green and T. Tao, \emph{The quantitative behaviour of polynomial
orbits on nilmanifolds}, Annals of Mathematics \textbf{175} (2012), 465--540.
\url{https://doi.org/10.4007/annals.2012.175.2.2}.
\bibitem{v6bienvenu}
P.-Y. Bienvenu, \emph{A higher-dimensional Siegel--Walfisz theorem},
Acta Arithmetica \textbf{179} (2017), 79--100.
\url{https://doi.org/10.4064/aa8600-10-2016}.
'''
once(r'\begin{thebibliography}{99}', r'\begin{thebibliography}{99}' + '\n' + bib,
     'Add published analytic references; reuse existing Green--Tao bibliography keys')
once('Brox. Thus the degree of a quartic definition is optimal.',
     'the agentic notes cited there. Thus the degree of a quartic definition is optimal.',
     'Use collective attribution in the introduction')
once("construction in Jos\\'e Brox's public manuscript~\\cite{Brox2026}.",
     'construction in the public agentic notes~\\cite{Brox2026}.',
     'Use collective attribution for the shared-point construction')
once("scales, direct Lucas test, and affine anchor change are Brox's arithmetic\nand algebraic improvements.",
     'scales, direct Lucas test, and affine anchor change are arithmetic\nand algebraic improvements recorded in those notes.',
     'Preserve source credit without individual manuscript attribution')
once("The public source passages are Brox's", 'The relevant passages in the public notes are',
     'Retain exact linked source passages')
once("The argument in this section is due to Jos\\'e Brox\n\\cite[section on unconditional lower bounds]{Brox2026}.",
     'The argument in this section comes from the agentic notes\n\\cite[section on unconditional lower bounds]{Brox2026}.',
     'Use collective attribution for the degree obstruction')
once(r'\begin{theorem}[Degree obstruction, following Brox]',
     r'\begin{theorem}[Degree obstruction]', 'Remove individual name from theorem title')
once(r'\bibitem{Brox2026} J. Brox,', r'\bibitem{Brox2026} Agentic notes,',
     'Use collective bibliography credit')
source_url = 'https://github.com/JoseBrox/diophantine-z-q_improvements/blob/f4d1b5e6c23d4adeb3ae1f986ab0bf87884bdff6/paper/diophantine_optimization_20261106_v3.tex'
once(r'\url{' + source_url + '}.', r'\href{' + source_url + '}{Public source at the pinned revision}.',
     'Keep the real source URL with a neutral visible link label')
s = s.replace('{Brox2026}', '{agentic-improvements}')
key_map['Brox2026'] = 'agentic-improvements'
labels = re.findall(r'\\label\{([^}]+)\}', s)
refs = re.findall(r'\\(?:ref|eqref|pageref)\{([^}]+)\}', s)
assert len(labels) == len(set(labels)), 'Duplicate labels'
assert not set(refs) - set(labels), sorted(set(refs) - set(labels))
assert 'We use that exact theorem\nas an external input' not in s
out = HERE / 'manuscript/quartic_962-analytic-candidate.tex'
out.write_text(s, encoding='utf-8', newline='\n')
components = HERE / 'assembled-components'
components.mkdir(exist_ok=True)
(components / 'gaussian-analytic.tex').write_text(analytic.strip() + '\n', encoding='utf-8', newline='\n')
section_start = s.index('\\section{The shared-point quartic in 962 variables}')
section_end = s.index('% End Version 5 main additions', section_start)
(components / 'source962.tex').write_text(s[section_start:section_end].strip() + '\n', encoding='utf-8', newline='\n')
lower_start = s.index('\\section{Why a single defining polynomial must have degree at least four}')
lower_end = s.index('\\appendix', lower_start)
(components / 'degree-lower-bound.tex').write_text(s[lower_start:lower_end].strip() + '\n', encoding='utf-8', newline='\n')
sun_start = s.index('\\section{Simultaneous primes with coprime adjacent norms}')
sun_end = s.index('\\begin{thebibliography}', sun_start)
(components / 'sun-completed.tex').write_text(s[sun_start:sun_end].strip() + '\n', encoding='utf-8', newline='\n')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
report = {'status': 'candidate_requires_final_integrated_review_not_published',
          'source_sha256': sha(out), 'edits': edits, 'citation_key_map': key_map,
          'ordinary_weight_notation_map': {'\\Lambda_{b,W}': '\\lambda_{b,W}'},
          'display_layout_edits': ['Split the density and two normalized weights into three aligned rows',
                                   'Split the centered nilsequence estimate and weight definition into two aligned rows'],
          'inputs': [{'path': str(p.relative_to(ROOT)), 'sha256': sha(p)} for p in inputs],
          'labels': len(labels), 'references': len(refs),
          'components': [{'path': str(p.relative_to(ROOT)), 'sha256': sha(p)} for p in sorted(components.glob('*.tex'))]}
(out.parent / 'ANALYTIC_CANDIDATE.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
print(json.dumps(report, indent=2))
