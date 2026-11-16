"""Build scoped V5-format analytic inputs; this is not a proof checker."""
from pathlib import Path
import hashlib, importlib.util, json, re

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
REPO=BASE.parents[1]
M=REPO/'work/quartic-version6-preparation/manuscript/quartic_962-analytic-candidate.tex'
P=REPO/'work/quartic-version5-release/repository/docs/quartic-1272/inventory.py'
spec=importlib.util.spec_from_file_location('v5inventory',P)
v5=importlib.util.module_from_spec(spec); spec.loader.exec_module(v5)
doc=v5.Tex(M.read_bytes(),str(M.relative_to(REPO)).replace('\\','/'))
def pin(p):
    b=p.read_bytes()
    return {'path':str(p.relative_to(REPO)).replace('\\','/'),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def write(name,obj):
    (BASE/name).write_text(json.dumps(obj,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')

fragment_files=['quotient-audit/norm_transfer.tex','type-i-ii/type_i_ii.tex','factorization/affine_pullback.tex','factorization/factorization.tex']
fragments=[]
for name in fragment_files:
    p=BASE/name
    body=v5.tex_text(p.read_bytes())
    body=body[body.index('\\subsection'):].strip()
    integrated=body.replace('GTMobius2012','moebius')
    if name.endswith('affine_pullback.tex'):
        integrated=integrated.replace('\\Lambda_{b,W}','\\lambda_{b,W}')
    assert doc.text.count(integrated)==1,name
    a=doc.text.index(integrated);z=a+len(integrated)
    fragments.append({'source':pin(p),'current':doc.span(a,z),'integration_changes':['GTMobius2012 citation key renamed moebius','Header comments excluded from body binding']+(['Ordinary-prime symbol Lambda_{b,W} renamed lambda_{b,W} to match progression definition'] if name.endswith('affine_pullback.tex') else [])})
scope_start=min(f['current']['start_character'] for f in fragments)
scope_end=max(f['current']['end_character'] for f in fragments)
reviewed_fragment_path=BASE/'analytic-reviewed-fragment.tex'
reviewed_fragment_path.write_text(doc.text[scope_start:scope_end],encoding='utf-8',newline='\n')

srcdir=REPO/'work/quartic-version5-release/sun-proof/sources'
orbits={'id':'GT-ORBITS-2012-PUBLISHED','bibliography':'B. Green and T. Tao, The quantitative behaviour of polynomial orbits on nilmanifolds, Annals of Mathematics 175 (2012), 465–540.','version':'Published journal PDF','url':'https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf','files':[pin(srcdir/'GT-orbits-published.pdf')],'inspection':'Published one-parameter Theorems 1.19 and 2.9, Lemmas 4.5 and 6.7, definitions and Appendix A checked in the cited review receipts. No multiparameter equidistribution theorem is used.'}
mobius={'id':'GT-MOBIUS-2012-PUBLISHED','bibliography':'B. Green and T. Tao, The Möbius function is strongly orthogonal to nilsequences, Annals of Mathematics 175 (2012), 541–566.','version':'Published journal PDF','url':'https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p03-p.pdf','files':[pin(srcdir/'GT-mobius-published.pdf')],'inspection':'The quantitative conjugation claim on printed p.547 is used; Section 3 is methodological attribution. The Möbius orthogonality theorem is not silently applied to Gaussian or ordinary von Mangoldt weights.'}
common='G connected, simply connected and nilpotent; Gamma discrete cocompact; filtration by closed connected rational subgroups; adapted rational Malcev basis; C-infinity norm in the binomial basis modulo one; Lipschitz norm includes supremum norm. Nontrivial horizontal characters are integer-lattice characters annihilating commutators and Gamma.'
apps=[]
def app(id,labels,keys,locator,objects,hyp,translation,sources=None,conventions=common):
    apps.append({'id':id,'kind':'new_external_application','reviewed_fragment':'gaussian-analytic','citation_keys':keys,'current_labels':labels,'exact_source_versions':sources or [orbits],'theorem_or_source_locator':locator,'objects_and_maps':objects,'hypotheses_and_discharge':hyp,'conventions':conventions,'translation':translation,'status':'published_source_inspected_application_reviewed_relative_to_listed_inputs','review_limit':'Application inventory and cited human reviews; not a proof-assistant certificate or an independent truth decision for the complete manuscript.'})
app('V6-GN-LEIBMAN',['lem:gn-norm-transfer','eq:gn-transfer'],['GTOrbits2012'],'Theorem 2.9, printed p.480, one-parameter case',
    'Apply to t -> g(P(t)) Gamma on [L], with P an integer quadratic from a horizontal Gaussian-norm row. Target discrepancy epsilon=delta^kappa; dimension m and filtration degree at most 2d.',
    'Q<=delta^(-kappa)=epsilon^(-1); the stretched filtration and unchanged basis are supplied by V6-GN-COORDINATES. Failure of ordinary epsilon-equidistribution gives a nonzero horizontal character with epsilon-power size and smoothness bounds. L>=sqrt(X)/B0, B0<=delta^(-5kappa).',
    'Internal integer coefficient extrapolation returns k*eta on the original orbit. Choose C_* first, then 6*C_*kappa<c0/2, sigma<sigma0 and 2*kappa*sigma<1/4. The internal horizontal-character obstruction contradicts total delta-equidistribution. Only ordinary distribution is deduced for each row pullback.')
app('V6-GN-COORDINATES',['lem:gn-norm-transfer'],['GTOrbits2012'],'Lemma 6.7, printed pp.501–502, t=1',
    'Second-kind Malcev coordinates of g(P(t)); replace G_j by G_ceil(j/2).',
    'P has degree two. Each coordinate degree at most j becomes at most 2j; the stretched groups still form a closed connected rational filtration and retain the adapted basis.',
    'Provides polynomiality and degree 2d for the one-parameter Leibman invocation, without a multiparameter theorem or any inference from pointwise fractional arguments.')
app('V6-GN-HORIZONTAL-METRIC',['lem:gn-horizontal-obstruction'],['GTOrbits2012'],'Definitions 2.2 and 2.6 and Appendix A metric comparisons',
    'Compose a fixed mean-zero circle bump with a nonzero horizontal character eta of magnitude at most T.',
    'T-rational adapted basis and character smoothness at most T. Character pushes Haar probability to circle Haar probability; the initial interval of length floor(X/(100dT)) is long when T<=delta^(-c0).',
    'Metric comparison bounds the test Lip norm by T^C. Choose C*c0<1/4 and c0<1/4, then small sigma0 handles floors. The obstruction itself is proved internally; no external converse-equidistribution theorem is assumed.')
app('V6-GI-LEIBMAN-I',['gi-recombination','gi-shift-removal','gi-one-coefficients'],['GTOrbits2012'],'Theorem 2.9, printed p.480, dimension m',
    'For many integer dilations r, restrict n -> g(rn) to a progression a+q[ell] witnessing failure of total eta-equidistribution.',
    'ell>=eta*M, q<=2/eta, |a|<=2M, eta^(-1)-rational basis; polynomial degree d. Fixed factors are absorbed by reducing eta0.',
    'Internal d! and q^d clearing removes the possibly O(M) shift; character-lattice pigeonholing fixes one nonzero character on eta-power density of r. No bounded-height assumption on the shift is made.')
app('V6-GI-LEIBMAN-II',['gi-recombination','gi-shift-removal','gi-two-coefficients'],['GTOrbits2012'],'Theorem 2.9, printed p.480, dimension 2m',
    'For many pairs r,r-prime, restrict n -> (g(rn),g(r-prime*n)) in (G/Gamma)^2 to a bad progression.',
    'Use the product filtration, product lattice and concatenated adapted basis. Product orbit failure is obtained by contraposition of norm transfer; equidistribution of separate factors is never asserted to imply product equidistribution.',
    'Obtain a nonzero pair of horizontal characters, clear shift denominators and pigeonhole. Interchange coordinates if needed to ensure the first character is nonzero; fix one r-prime with many partners.')
app('V6-GI-RECURRENCE-I',['gi-recombination','gi-recurrent-coefficients'],['GTOrbits2012'],'Lemma 4.5, printed p.490',
    'Polynomial r -> d!*beta_j*r^j modulo one on [ceil(R)] for each 1<=j<=d.',
    'Selected r have eta-power density. Values lie in an arc of length <=2*eta^(-C5)*(R/N)^j. R<=2*N^(2/3), sufficiently large K_rec, and the large-R branch ensure arc length at most half density. Small R is treated internally by multiplying by r^d.',
    'Retain the arc-length factor in the published smoothness conclusion; the leading coefficient then has N^(-j), not merely R^(-j), accuracy. Additional factorial and product of nonzero bounded integers yield one character.')
app('V6-GI-RECURRENCE-II',['gi-recombination','gi-two-coefficients','gi-recurrent-coefficients'],['GTOrbits2012'],'Lemma 4.5, printed p.490, arbitrary interval centre',
    'After fixing r-prime, apply to r -> d!*beta_j*r^j in the arc centred at -d!*beta-prime_j*(r-prime)^j.',
    'N^(1/3)/4<=R<=2*N^(2/3); many partners supply eta-power density and the same short-arc inequality. The first horizontal character is nonzero.',
    'Gives the same N^(-j) coefficient control as Type I. Does not replace r^j-r0^j by (r-r0)^j, and does not require the arc to be centred at zero.')
app('V6-GI-HORIZONTAL-METRIC',['gi-recombination'],['GTOrbits2012'],'Definitions 2.2 and 2.6; Appendix A metric comparisons',
    'Mean-zero circle bump composed with the recombined nonzero character Psi.',
    'Character magnitude and C-infinity[N] norm are bounded by eta^(-C9); on an initial interval c*eta^(2C9+4)*N its phase stays in a fixed short arc.',
    'Lip norm is an eta-power and Haar mean is zero. Choose C_rec beyond length and Lip losses, then K_rec for floors, to contradict total eta^C_rec-equidistribution.')
app('V6-GA-COORDINATES',['lem:ga-affine-interpolation'],['GTOrbits2012'],'Lemma 6.7, printed pp.501–502, t=1',
    'Extend the coordinate polynomials of g(n) to real t, form g_R(t), then tilde-g(t)=g_R((t-b)/W).',
    'W>=1 and b are fixed integers, 0<=b<W. Affine composition preserves every coordinate degree constraint for the original filtration; real exponential coordinates exist in connected simply connected nilpotent G.',
    'tilde-g is a polynomial sequence on the same nilmanifold and tilde-g(Wn+b)=g(n). This is an algebraic interpolation statement, not assumed fractional-argument equidistribution.')
app('V6-GA-LEIBMAN',['lem:ga-affine-interpolation'],['GTOrbits2012'],'Theorem 2.9, printed p.480, one-parameter case',
    'Restrict tilde-g to a bad progression u+v[L] in [X], X=WN+b, epsilon=delta^a.',
    'Q<=delta^(-a)=epsilon^(-1); u,v integers, 1<=v<=2/epsilon, |u|<=2X, L>=epsilon*X. Same rational filtration and dimension m.',
    'Internal linear extrapolation and forward composition with integer Wn+b give a small nonzero character on g. a<C0/(2*C_aff) with C0=c0 and sigma<min(sigma0,1/(2a)) permit the norm-section obstruction. Total delta on [N] implies total delta^a on the full expanded interval, for fixed W.')
app('V6-GF-FACTORIZATION',['prop:gf-factorization','eq:gf-cells'],['GTOrbits2012'],'Theorem 1.19, printed p.476',
    'Initial polynomial g on G/Gamma, M0=log(2N)^max(1,C_init), external exponent A renamed B; g=epsilon*g-prime*gamma.',
    'Initial basis is log(2N)^C_init-rational, hence M0-rational; fixed dimension m, degree d. Output M0<=M<=C*M0^E(B), rational subgroup G-prime and Gamma-prime=G-prime intersect Gamma.',
    'epsilon is (M,N)-smooth, g-prime totally M^(-B)-equidistributed, gamma rational with coset period q<=M. B is chosen using lower M>=log(2N) before E(B) is used for the later progression threshold; no circular comparison B>E(B).')
app('V6-GF-CONJUGATED-QUOTIENT',['prop:gf-factorization'],['moebius'],'Quantitative Claim and proof on printed p.547, within Section 2',
    'H_j=gamma_j^(-1)*G-prime*gamma_j; Lambda_j=H_j intersect Gamma; h_j=gamma_j^(-1)*g-prime*gamma_j. F_jk(x Lambda_j)=F(a_jk*gamma_j*x Gamma).',
    'Reduced gamma_j has rational coordinates of height M^O(1); a_jk=epsilon(n_jk) has bounded M-power coordinates. The output subgroup basis and lattice satisfy the published claim.',
    'Obtain basis rationality M^C2, total M^(-aB+C2)-equidistribution and Lip norm M^C2. Account for commensurable lattices and finite-index losses; conjugation is not an isometry of the original quotients. Subtract each new quotient Haar mean, including the dimension-zero case. The claim is used for a general weight through separate mean/minor-arc hypotheses, not by extending the Möbius theorem.',sources=[mobius,orbits])
app('V6-GF-RATIONAL-METRIC-SUPPORT',['prop:gf-factorization'],['GTOrbits2012'],'Appendix A: Proposition A.9, Lemmas A.13, A.5 and A.17, as explicitly used in the published p.547 Claim',
    'Rational conjugation of G-prime, an adapted basis on H_j/Lambda_j, and translated test functions F_jk.',
    'All rational coordinate heights and translation coordinates are M-power bounded. Use the changed lattice Lambda_j=H_j intersect Gamma rather than silently identifying quotients.',
    'Supports the p.547 Claim with exponents depending only on m,d and not B. Records the scoped support chain; does not declare every Appendix A result independently applied.',sources=[orbits,mobius])

internal_specs={
'lem:gn-norm-transfer':('Gaussian ideal norm sum on every norm interval and residue class is <=C*X*delta^kappa*Lip(F), with optional logarithmic weight.','Fixed Gaussian ray modulus, character extended by zero; four generators per nonzero ideal; total delta on [X]; X^(-sigma)<=delta<=delta0 and Q,q<=delta^(-kappa). Product version requires total distribution of the entire product orbit.',['V6-GN-LEIBMAN','V6-GN-COORDINATES','lem:gn-quadratic-coefficients','lem:gn-horizontal-obstruction']),
'lem:gn-quadratic-coefficients':('Integer quadratic pullback smoothness extrapolates to original coefficients after a nonzero integer multiplier of B0-power size.','X>=1; integer quadratic with positive leading coefficient; coefficient scale B0*X^(1-i/2); L>=sqrt(X)/B0. Integer-valued binomial expansion, triangular descent and integer clearing preserve modulo-one estimates.',[]),
'lem:gn-horizontal-obstruction':('A nonzero character with small magnitude and C-infinity norm obstructs total distribution.','T-rational basis, T<=delta^(-c0), delta>=X^(-sigma0); initial interval and Haar-mean-zero bump.',['V6-GN-HORIZONTAL-METRIC']),
'rem:gn-product-and-progression':('Product-orbit and progression uses of norm transfer; logarithmic specialization.','Mean-zero factors do not imply product-orbit distribution. Solve simultaneous residue conditions modulo a divisor of q; arbitrary interval endpoints allowed.',['lem:gn-norm-transfer']),
'gi-moments':('Gaussian ideal multiplicity and first/second moment bounds.','a_E<=tau, tau^2<=d4, harmonic sums, and four-to-one generator disk count.',[]),
'gi-vaughan':('Exact three-term Gaussian ideal Vaughan identity on a dyadic shell.','U=V=N^(1/3); ideal convolution and completely multiplicative character extended by zero; small-Lambda term vanishes and coefficients bounded by log(2N).',[]),
'gi-extraction':('Large weighted shell correlation yields many large Type I or Type II correlations with explicit power density.','Dyadic splitting, partial summation and two Cauchy–Schwarz steps retain ideal multiplicities; all interval/progression indicators remain in f.',['gi-moments','gi-vaughan']),
'gi-recombination':('Many badly distributed integer dilations or dilation pairs force failure of total distribution of the original orbit.','Integer parameters, correct shift removal, arbitrary-centre strong recurrence, nonzero product character coordinate; small R treated separately.',['V6-GI-LEIBMAN-I','V6-GI-LEIBMAN-II','V6-GI-RECURRENCE-I','V6-GI-RECURRENCE-II','V6-GI-HORIZONTAL-METRIC']),
'gi-minor-arc':('Gaussian ideal von Mangoldt minor-arc estimate Q*N*log(2N)^7*delta^c_G*Lip(F).','Every delta in (0,1), Q>=2 and every interval progression of modulus <=Q, with no lower length bound. Intermediate delta/complexity restrictions are removed by shell and small-delta arguments.',['gi-extraction','gi-recombination','lem:gn-norm-transfer']),
'gi-ordinary-primes':('Analogous ordinary-integer von Mangoldt and prime-only minor-arc estimate.','Repeat convolution with multiplicity one and direct unweighted total-distribution bound; prime powers handled explicitly. No Möbius-to-von-Mangoldt black box.',['gi-minor-arc','gi-recombination']),
'lem:ga-linear-coefficients':('Integer affine coefficient extrapolation with integer multiplier bounded by an E-power.','X>=1, u,v integers, v nonzero, |u|<=CX, |v|<=E, L>=X/E; integral triangular binomial coefficient matrix.',['lem:gn-quadratic-coefficients']),
'lem:ga-affine-interpolation':('Fixed-W real-coordinate interpolation preserves quantitative total distribution on [WN+b].','Fixed integer W,b; same filtration and quotient; delta>=N^(-sigma), Q<=delta^(-a); parameters chosen before factorization exponent.',['V6-GA-COORDINATES','V6-GA-LEIBMAN','lem:ga-linear-coefficients','lem:gn-horizontal-obstruction']),
'lem:ga-wtrick-ma':('Transfer ideal minor-arc sum to the fixed-W arithmetic subsequence.','N(a)=Wn+b is exact; progression modulus becomes Wq and endpoints become O_W(N); W fixed; F0 Lipschitz and Haar mean zero.',['lem:ga-affine-interpolation','gi-minor-arc']),
'cor:ga-centered-primes':('Finite linear combinations of fixed-W ray and ordinary prime weights satisfy the mean-zero minor-arc bound.','Conditional on checked finite-character expansion and both minor-arc inputs; Gaussian factor 1/2, prime-power O(sqrt(N)log^2 N), sigma1*cW<1/4; every progression P of modulus <=Q. Ordinary weight symbol is lambda_{b,W} after integration.',['lem:ga-wtrick-ma','gi-ordinary-primes']),
'rem:ga-choice-order':('Arithmetic moduli and affine/minor-arc exponents precede the factorization exponent.','Output complexity polylogarithmic; does not invoke Frei–Tinkova as a theorem.',['prop:gf-factorization']),
'prop:gf-factorization':('Generic log-power nilsequence orthogonality from growth, all-progression centered means and power-form mean-zero minor arcs.','Hypotheses eq:gf-sw and eq:gf-ma remain genuine inputs; cell count M^2 log^D, cellwise Haar means, rational quotient changes, B before E(B). Applies to general weights satisfying these conditions.',['V6-GF-FACTORIZATION','V6-GF-CONJUGATED-QUOTIENT','V6-GF-RATIONAL-METRIC-SUPPORT']),
'rem:gf-order':('Noncircular order for factorization exponent and progression thresholds.','B chosen from fixed minor-arc exponents using lower M>=log; upper exponent E(B) only later fixes SW precision and modulus threshold.',['prop:gf-factorization'])}
internals=[]
for label,(statement,hyp,deps) in internal_specs.items():
    r=next(r for r in doc.results if label in r['labels'])
    # V5's consecutive-proof matcher must not attach an explicitly named
    # delayed proof to a different immediately preceding result.
    attached=[]
    for a,z in r['proof_spans']:
        title=re.match(r'\\begin\{proof\}\s*\[([^\]]*)\]',doc.code[a:z])
        targets={x for m in v5.REF_RE.finditer(title.group(1)) for x in m.group(1).split(',')} if title else set()
        if targets and not targets.intersection(r['labels']): continue
        attached.append((a,z))
    text=doc.text[r['start']:r['statement_end']]+'\n'+'\n'.join(doc.text[a:z] for a,z in attached)
    proof=[doc.span(a,z) for a,z in attached]
    internals.append({'label':label,'id':label,'labels':r['labels'],'environment':r['environment'],'reviewed_fragment':'gaussian-analytic','statement_and_map':statement,'hypotheses_conventions_translation':hyp,'declared_dependencies':deps,'status':'independent_application_review_accepted_relative_to_listed_inputs','review_limit':'Human review of the stated derivation; inventory is not a truth oracle, formal proof, or acceptance of unlisted arithmetic inputs.','source_bounds':'Exact current statement and all attached proof spans below; source fragments separately byte-pinned.','statement':doc.span(r['start'],r['statement_end']),'proof_spans':proof,'explicit_citation_keys':sorted({k.strip() for m in v5.CITE_RE.finditer(v5.uncomment(text)) for k in m.group(3).split(',')}),'explicit_internal_dependencies':sorted({k.strip() for m in v5.REF_RE.finditer(v5.uncomment(text)) for k in m.group(1).split(',')})})

# Every classified occurrence is matched by its exact paragraph plus key set.
# This preserves V5 contains-matching semantics without blanket key coverage.
classifications=[]
for m in v5.CITE_RE.finditer(doc.code):
    if not scope_start<=m.start()<scope_end: continue
    a,z=doc.paragraph(m.start()); paragraph=doc.text[a:z]
    key=m.group(3); locator=m.group(2) if m.group(2) is not None else m.group(1)
    part=next(f['source']['path'] for f in fragments if f['current']['start_character']<=m.start()<f['current']['end_character'])
    ids=[];role='source_statement';note='Scoped published input; see the application records.'
    if part.endswith('norm_transfer.tex'):
        if locator is None: role='conventions';note='Definitions of group, quotient, filtration and Lip norm only; no equidistribution conclusion at this occurrence.'
        elif '2.9' in locator: ids=['V6-GN-LEIBMAN']
        elif '6.7' in locator: ids=['V6-GN-COORDINATES']
        else: ids=['V6-GN-HORIZONTAL-METRIC']
    elif part.endswith('type_i_ii.tex'):
        if key=='moebius': role='provenance';note='Section 3 supplies method attribution. Exact Gaussian Vaughan identity and estimates are proved here; no theorem transferred by analogy.'
        elif locator is None: role='conventions';note='Polynomial sequence, lattice and adapted basis conventions only.'
        elif '2.9' in locator and '4.5' in locator: ids=['V6-GI-LEIBMAN-I','V6-GI-LEIBMAN-II','V6-GI-RECURRENCE-I','V6-GI-RECURRENCE-II'];note='Opening declaration of the exact one-parameter inputs used later.'
        elif '2.9' in locator: ids=['V6-GI-LEIBMAN-I','V6-GI-LEIBMAN-II']
        elif '4.5' in locator: ids=['V6-GI-RECURRENCE-I','V6-GI-RECURRENCE-II']
        else: ids=['V6-GI-HORIZONTAL-METRIC']
    elif part.endswith('affine_pullback.tex'):
        ids=['V6-GA-COORDINATES'] if '6.7' in locator else ['V6-GA-LEIBMAN']
    else:
        ids=['V6-GF-CONJUGATED-QUOTIENT'] if key=='moebius' else ['V6-GF-FACTORIZATION'] if '1.19' in locator else ['V6-GF-RATIONAL-METRIC-SUPPORT']
    rec={'keys':[key],'contains':paragraph,'role':role,'application_ids':ids,'scope':note,'occurrence':doc.span(m.start(),m.end()),'paragraph':doc.span(a,z),'locator':locator,'outside_labeled_result_span':doc.enclosing(m.start()) is None}
    assert sum(1 for cm in v5.CITE_RE.finditer(doc.code) if cm.group(3)==key and paragraph in doc.text[slice(*doc.paragraph(cm.start()))])==1,(key,locator)
    classifications.append(rec)

for a in apps:
    a['exact_invocation_occurrences']=[{'citation':c['occurrence'],'paragraph':c['paragraph'],'locator':c['locator']} for c in classifications if a['id'] in c['application_ids']]
    a['citation_scope_rule']='Current result/equation labels bind mathematical context. Exact invocation occurrences, not every citation inside that context, bind this particular source application.'

reviews=[BASE/'norm-independent-review/REVIEW.md',BASE/'norm-independent-review/receipt.json',BASE/'type-i-ii/ROOT_REVIEW.md',BASE/'factorization-independent-review/REVIEW.md',BASE/'factorization-independent-review/receipt.json',BASE/'factorization-independent-review/TEX_FIDELITY.md',BASE/'factorization-independent-review/tex-fidelity-static.json']
out={'schema':'quartic-v5-reviewed-application-inputs-v1','scope':'Scoped authored application inputs for the four NEW Gaussian analytic fragments only. No whole-manuscript proof certification. SW, progression arithmetic and the Gowers bridge have separate inventories.','applications':apps,'citation_classifications':classifications,'internal_results':internals,'current_consumption':[],'external_proof_subaudits':[],'inherited_ledgers':[],'evidence_pins':[pin(p) for p in reviews],'new_source_qualifications':[{'id':'V6-GAUSSIAN-ANALYTIC-SCOPE','text':'Only the one-parameter published GT results and specified rational/metric claim are used. Gaussian ideal convolution, coefficient extrapolation, norm transfer and general-weight recombination are newly proved steps, not quotations of an external theorem. No unrestricted general-number-field result is claimed.'},{'id':'V6-GT-MOBIUS-KEY','text':'The reviewed fragments used GTMobius2012; integrated citation key moebius denotes the same published paper. Its Section 3 is provenance and its p.547 Claim is a scoped theorem input. The paper\u2019s Möbius orthogonality theorem is not invoked for the new von Mangoldt estimates.'}], 'reviewed_fragments':[{'id':'gaussian-analytic','path':pin(reviewed_fragment_path)['path'],'sha256':pin(reviewed_fragment_path)['sha256'],'current':doc.span(scope_start,scope_end),'component_pins_and_bindings':fragments,'review':'Norm/affine/factorization independent reviews and root Type I/II review; final TeX fidelity receipt. Intervening comments are not mathematical changes.','status':'component_derivations_reviewed_relative_to_listed_inputs','integration_note':'Exact contiguous frozen fragment supplied for the V5 full-fragment matcher; all component source/body pins are also supplied.'}],'candidate_pin':pin(M),'classification_policy':'Exact paragraph and exact source key set per occurrence. No global GTOrbits2012 or moebius blanket classification; unrelated retained manuscript citations remain outside this inventory.'}
write('analytic-applications.json',out)
write('analytic-internal-results.json',internals)
print(json.dumps({'applications':len(apps),'internal_results':len(internals),'citation_occurrences':len(classifications),'outside_labeled_result_occurrences':sum(c['outside_labeled_result_span'] for c in classifications),'candidate_sha256':out['candidate_pin']['sha256']},indent=2))


