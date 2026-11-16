from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
candidate = ROOT / 'work/quartic-version6-preparation/manuscript/quartic_962-analytic-candidate.tex'
baseline = ROOT / 'work/quartic-version6-preparation/manuscript/quartic_962-preparation.tex'
expected = 'b43f096ba3a4b1a979778ae1593ce3ad89048a2d28016e5ee9f35b124238dce7'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(candidate) == expected
text = candidate.read_text(encoding='utf8')
old = baseline.read_text(encoding='utf8')

def pin(p):
    p = ROOT / p
    return {'path': p.relative_to(ROOT).as_posix(), 'sha256': sha(p), 'bytes': p.stat().st_size}

def loc(label):
    needle = '\\label{' + label + '}'
    assert text.count(needle) == 1, label
    return {'label': label, 'line': text[:text.index(needle)].count('\n') + 1}

nodes = []
def node(id, labels, deps, inputs, output, qualification='Internal proof and interface inspected in the pinned candidate.'):
    nodes.append({'id': id, 'current_labels': labels, 'locations': [loc(x) for x in labels],
                  'dependencies': deps, 'critical_hypotheses': inputs, 'supplied_conclusion': output,
                  'review_scope': qualification, 'status': 'accepted_for_stated_consumer'})

node('sw', ['lem:gaussian-hecke-sw'], [],
     'Fixed Gaussian ray character and fixed B; varying rational Dirichlet character q<=log(X)^B; 1<=Y<=X. Also K=Q.',
     'Uniform ideal/rational von Mangoldt sums with primitive-principal main term and every logarithmic saving.',
     'Self-authored component excluded from this independent proof review. Accepted through sw-independent-review, corrected TeX hash 56c7d6a62678123d2fd89bfc473f6934e75bd1da04233b292bda4cc9be77262e; only consumption audited here.')
node('progression', ['lem:gaussian-ray-progression', 'cor:gaussian-centered-progressions'], ['sw'],
     'K/Q(i) fixed ray field, 16|H, C subset Gal(K/Q(i)) invariant under conjugation; W fixed and contains conductor(K^ab).',
     'Exact conditional density mu_C; centered h has arbitrary logarithmic cancellation on every interval progression.')
node('norm', ['lem:gn-norm-transfer'], [],
     'Fixed ray modulus; mean-zero Lipschitz test; total delta equidistribution; restricted power regime for delta, basis and progression modulus.',
     'Gaussian ideal norm sums O(X delta^kappa), arbitrary interval endpoints; logarithmic weights and mean-zero product tests covered.')
node('minor', ['gi-vaughan', 'gi-extraction', 'gi-recombination', 'gi-minor-arc', 'gi-ordinary-primes'], ['norm'],
     'Fixed dimensions, filtration and ray modulus; total delta equidistribution; mean-zero Lipschitz test.',
     'All-delta/all-Q Gaussian and rational von Mangoldt minor-arc bounds QN log(2N)^7 delta^c, arbitrary interval progressions.')
node('affine', ['lem:ga-affine-interpolation', 'lem:ga-wtrick-ma', 'cor:ga-centered-primes'], ['minor', 'norm'],
     'Fixed W,b; mean-zero test; small delta in a lower power regime; bounded basis rationality; finite ray Fourier expansion with factor one-half.',
     'Centered W-tricked ray/ordinary prime weight satisfies fixed-power minor-arc hypothesis, with proper-prime-power errors absorbed.')
node('factorization', ['prop:gf-factorization'], ['progression', 'affine'],
     'Pointwise log bound, all-progression mean cancellation, fixed-power mean-zero estimate; fixed W; B chosen before E(B).',
     'Uniform correlation cancellation with all polynomial nilsequences of bounded complexity for each fixed W.')
node('refined_gowers', ['eq:gaussian-centered-nil-input', 'eq:gaussian-refined-gowers'], ['factorization'],
     'Real centered weight dominated after fixed rescaling by common ordinary-prime majorant; full cyclic U^(2s) uniformity; prime ambient size; fixed-V thresholds before diagonal.',
     'Interval U^s uniformity on a sufficiently slow auxiliary modulus V_z, with physical-scale stage thresholds.')
node('linear', ['lem:gaussian-linear-replacement'], ['refined_gowers'],
     'Fixed nonzero pairwise nonproportional linear parts, bounded normalized constant terms, convex region; full normal-form auxiliary box.',
     'Replace ray-prime factors by mu_C times ordinary-prime factors with o(N^d), including mixed products; no auxiliary cutoff in conclusion.')
node('cube', ['eq:gaussian-global-gowers'], ['linear'],
     'New polynomial cutoff v fixed; wrap-around cube forms, q<=A^C1, nA^-C3<=J<=nA^-C2 with C1<C2<C3.',
     'Centered local-step global cube bounded by O(1/log v)+o_v(1).')
node('polynomial', ['prop:v5-artin-patterns'], ['cube'],
     'Same fixed Gaussian ray field and conjugation-invariant split classes; distinct fixed coefficients; external arbitrary-function model, concatenation and polynomial von Neumann results.',
     'Uniform polynomial count for omega(N)sqrtN<=T=o(sqrtN), singular series with conditional densities, and half-interval version; boundary via anchored second moment and fixed-epsilon diagonal.')
node('ray_lower', ['lem:v5-ray-fibres', 'prop:v5-cutoff-lower'], ['polynomial'],
     'Fix base modulus and coefficients; K_L is ray field for H0*T_L; C_L lies above C0 in split subgroup; L fixed before asymptotics.',
     'Singular series lower bound c(log L)^(-4k) with c independent of L; no leftover reciprocal field degree.',
     'Retained proof read for interface and source-domain compatibility; exact text unchanged from preparation source. External ray-class and Mertens inputs remain.')
node('obstruction', ['prop:v5-obstruction-tail'], [],
     'Fixed coefficient data; leading constant uniform in L,tau; each tau fixed when taking its error threshold.',
     'Weighted forbidden-tail upper bound C*tau*N^(3/2)/(L log L)+O_tau(N^(3/2-1/800)).',
     'Retained local/sieve proof read for consumer interface; exact text unchanged. This is not a new independent source audit of the two external sieve theorems.')
node('final', ['thm:v5-simultaneous-primes', 'subsec:v5-diagonal'], ['polynomial', 'ray_lower', 'obstruction'],
     'Choose L once to beat tail, then fixed K_L,C_L, then tau thresholds; omega condition and rounded T maintained; coefficient dilation first.',
     'Required simultaneous split primes with Gaussian residues, adjacent-norm coprimality, exact two-adic valuations, divisibility of w and arbitrarily large u/w^2.')

seen = set()
def visit(id, active):
    assert id not in active, f'cycle at {id}'
    if id in seen: return
    n = next(n for n in nodes if n['id'] == id)
    for d in n['dependencies']: visit(d, active | {id})
    seen.add(id)
for n in nodes: visit(n['id'], set())

def section(s, start, end):
    i=s.index(start); return s[i:s.index(end,i)].strip()
old_sieve=section(old,'\\label{subsec:v5-local-sieve}', '\\subsection{Fixed Artin conditions')
new_sieve=section(text,'\\label{subsec:v5-local-sieve}', '\\subsection{Gaussian ray weights')
old_tail=section(old,'\\label{subsec:v5-ray-density}', '\\begin{thebibliography}')
new_tail=section(text,'\\label{subsec:v5-ray-density}', '\\begin{thebibliography}')
assert old_sieve==new_sieve
assert old_tail==new_tail

fragments=['quotient-audit/norm_transfer.tex','type-i-ii/type_i_ii.tex',
           'factorization/affine_pullback.tex','factorization/factorization.tex',
           'progression_mainterms.tex','gowers-bridge/bridge.tex',
           'published-input-audit/gaussian_hecke_sw.tex']
record={'schema':'ft-replacement-integration-dependencies-v1','date':'2026-11-06',
 'decision':'accepted_scoped_replacement_no_unresolved_interface_gap_found',
 'candidate':pin(candidate.relative_to(ROOT)), 'baseline':pin(baseline.relative_to(ROOT)),
 'fragments':[pin('work/frei-tinkova-removal-001/'+p) for p in fragments],
 'review':pin(OUT.relative_to(ROOT)/'INTEGRATION_REVIEW.md'),
 'nodes':nodes,'acyclic':True,'unresolved_mathematical_interface_gaps':[],
 'retained_text_checks':{'local_and_obstruction_exact':True,'ray_lower_and_final_diagonal_exact':True,
     'local_obstruction_sha256':hashlib.sha256(old_sieve.encode()).hexdigest(),
     'ray_final_sha256':hashlib.sha256(old_tail.encode()).hexdigest()},
 'external_inputs_retained':['Mitsui1956: independently reviewed SW interface',
 'GTOrbits2012: one-parameter quantitative Leibman, polynomial coordinates, recurrence, factorization, rational-subgroup metric comparisons',
 'moebius: rational conjugation claim with lattice/metric losses',
 'greentao: common ordinary-prime majorant, generalized von Neumann, normal form',
 'v5dk: relative inverse Theorem5.1, checked in arxivv4; finaltypeset not compared',
 'v6bienvenu: ordinary linear prime correlations with normalized constants and convex regions',
 'v5tz: arbitrary-function dense model, concatenation, polynomial von Neumann, polynomial-forms majorant',
 'v5kl: ray-class existence/reciprocity and modulus exact sequence',
 'v5williams: fixed-modulus Mertens theorem',
 'v5bl and v5bhb: unchanged sieve inputs with retained version qualifications'],
 'FT_status':'provenance_and_methodological_attribution_only_no_assumed_theorem',
 'limitations':['No self-certification of SW component','No new source-level proof of all external inputs',
 'No assertion for arbitrary Galois fields or non-split cosets','No blanket certificate for unrelated quartic construction',
 'No publication authorization; current candidate only'],
 'editorial_maps':{'GTMobius2012':'moebius','v6gtlinear':'greentao','\\Lambda_{b,W}':'\\lambda_{b,W}'}}
(OUT/'INTEGRATION_DEPENDENCIES.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
print(json.dumps({'candidate_sha256':expected,'review_sha256':sha(OUT/'INTEGRATION_REVIEW.md'),
                  'inventory_sha256':sha(OUT/'INTEGRATION_DEPENDENCIES.json'),
                  'nodes':len(nodes),'acyclic':True,'unchanged_blocks':2},indent=2))
