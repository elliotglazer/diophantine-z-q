from pathlib import Path
import hashlib,json
base=Path(__file__).resolve().parent.parent
src=(base/'baseline.tex').read_text(encoding='utf-8')
frag=''.join(src.splitlines(keepends=True)[17940:18279])
edits=[]
def edit(name,old,new,reason):
    global frag
    assert frag.count(old)==1,(name,frag.count(old))
    frag=frag.replace(old,new)
    edits.append(dict(id=name,kind='proof-explication',reason=reason,old=old,new=new))
edit('explicit-upstream-discharge',r'''Gaussian norm, progression and factorization arguments, specifically
Proposition~\ref{prop:gf-factorization},
Corollary~\ref{cor:ga-centered-primes} and
Corollary~\ref{cor:gaussian-centered-progressions}:''',r'''Gaussian norm, progression and factorization arguments, as assembled in
Corollary~\ref{cor:ga-fixed-centered-nilsequence}:''','Names the exact discharged upstream interface supplied by the weights audit; integration requires its new corollary.')
edit('source-version',r'''We also use Dodos--Kanellopoulos~\cite{v5dk}, Theorem~5.1, in precisely the following
form.''',r'''We also use Dodos--Kanellopoulos~\cite{v5dk}, Theorem~5.1, in the
following form, checked in arXiv:1610.00487v4, pp.~12--13. The final
typeset statement has not been compared.''','Preserves the existing bibliography qualification at the actual theorem application.')
edit('inverse-scaling',r'''Consequently a fixed positive rescaling of
$1_{[L^{3/5},L]}h_{C,V_z,b}$ is dominated by $\nu$ on $[L]$.''',r'''Consequently there is $\alpha>0$, depending only on the fixed
complexities and the fixed factor in the modulus, such that
$\alpha 1_{[L^{3/5},L]}h_{C,V_z,b}$ is dominated in absolute value by
$\nu$ on $[L]$. The same $\alpha$ works for all cutoffs and unit residues.
In applying the inverse theorem to a lower bound $\delta$ for the
unscaled norm, use the lower bound $\alpha\delta/2$ for this truncated,
scaled function, once the truncation error is at most $\delta/2$.''','Makes the exact domination hypothesis and its fixed scaling of inverse thresholds explicit.')
edit('gn-scaling',r'''these at most $t$ weights, truncate as above, and apply the normal-form
extension of Green--Tao Lemma~4.4 and Proposition~7.1. The small factor
has the required norm by \eqref{eq:gaussian-refined-gowers}.''',r'''these at most $t$ weights and truncate as above. Multiply every
factor by a common fixed $\alpha_0>0$ so that each has absolute value
at most that majorant, and apply the normal-form extension of
Green--Tao Lemma~4.4 and Proposition~7.1. Here $\alpha_0$ depends
only on the fixed system, the chosen complexities and the fixed
conductor, not on $z$ or the residue vector. The small factor has
the required norm by \eqref{eq:gaussian-refined-gowers}. Dividing
the resulting estimate by $\alpha_0^t$ changes only a fixed constant.''','The published generalized von Neumann theorem assumes literal domination; fixed rescaling supplies it without a growing loss.')
edit('singleton-local-factors',r'''Away from finitely many primes dividing the nonzero minors of pairs
of linear parts, two distinct output hyperplanes meet with probability
$p^{-2}$, so $\beta_p=1+O_t(p^{-2})$, uniformly in the constant terms.''',r'''Exclude the finitely many primes dividing a chosen nonzero
coefficient of each linear part, and a chosen nonzero two-by-two
minor for each pair of linear parts. At every remaining prime each
output hyperplane has probability $p^{-1}$, and any two meet with
probability $p^{-2}$. Hence $\beta_p=1+O_t(p^{-2})$, uniformly in
the constant terms. This also covers $t=1$, when there are no pair
minors and the good-prime factor is exactly one.''','Closes the written local-factor argument for the singleton system admitted by the lemma.')
edit('model-scaling',r'''\mu_C(b)$, has small global norms; the concatenation and model
approximation give the required local norm bounds.''',r'''\mu_C(b)$, has small global norms. The model is bounded by a fixed
constant depending on the chosen sieve exponent. Divide its difference
from $\mu_C(b)$ by a fixed bound for that difference before applying
Theorem~9, whose hypothesis is a bound by one. After restoring this
fixed factor, concatenation and model approximation give the required
local norm bounds. None of these scaling constants depends on $v$.''','Matches the actual bounded range of the dense model with the bounded-by-one concatenation theorem.')
edit('boundary-scaling',r'''Thus a strip of width $\epsilon N$ has total weight
$[O(\epsilon)+o_{v\to\infty}(1)+o_{v,\epsilon}(1)]NT$.''',r'''The normalized prime weights are bounded by fixed multiples of
their sieve majorants, with constants depending on the fixed sieve
exponent. Thus a strip of width $\epsilon N$ has total weight
$[O(\epsilon)+o_{v\to\infty}(1)+o_{v,\epsilon}(1)]NT$, with that
fixed domination factor included in the implied constants.''','Makes the majorant-to-prime step explicit; no pointwise logarithmic loss enters localization.')
edit('signed-boundary-embedding',r'''Use a fixed enlarged ambient interval, depending only on the fixed
coefficients, and translate it if necessary, so that all actual integer
outputs in these strips are represented without cyclic wrap-around.
All scales change by fixed constants only.''',r'''This argument also covers negative coefficients $c_j$. For the true
integer count use an enlarged period $n_* = \lceil B N/W\rceil$, where
$B>2+\max_j|c_j|$ is fixed. We may assume $T\leq\sqrt N$.
Nonpositive outputs have prime weight zero, and every positive output
is at most $(1+\max_j|c_j|)N$. Discard also tuples for which some
positive output is at most $W\lceil n_*^\rho\rceil+W$. For each $w$
there are $O_k(W n_*^\rho+W)$ such $u$, so their total weight is
$O_k((W n_*^\rho+W)T(\log N)^k)=o_v(NT)$, uniformly in the
allowed $T$ range. All remaining true outputs have their ordinary
prime majorants on $[n_*]$ without wrap-around. Use the same
localization calculation on the original period $n$ to bound the
artificial wrapped terms of the cyclic count. The parameters $n_*$
and $n$ differ by a fixed factor, so both applications satisfy the
same polynomial-forms hypotheses. In the following calculation $n$
denotes either chosen ambient period.''','Gives a literal embedding for negative coefficients and separately controls actual and artificial cyclic boundary terms.')
out=base/'transference'
(out/'replacement.tex').write_text(frag,encoding='utf-8',newline='\n')
(out/'edits.json').write_text(json.dumps({'baseline_sha256':hashlib.sha256((base/'baseline.tex').read_bytes()).hexdigest(),'replace_inclusive_lines':[17941,18279],'requires_weights_fragment_label':'cor:ga-fixed-centered-nilsequence','changes_final_statement':False,'edits':edits},indent=2),encoding='utf-8')
print('Wrote replacement.tex and edits.json with',len(edits),'scoped edits')
