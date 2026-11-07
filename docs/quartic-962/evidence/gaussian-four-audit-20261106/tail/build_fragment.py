from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'baseline.tex'
raw = BASE.read_bytes()
expected = '06f98ff070139c3b6c60589c65867ceb4366b023f7960551abd52f85fa67e30c'
assert hashlib.sha256(raw).hexdigest() == expected
lines = raw.splitlines(keepends=True)
original = b''.join(lines[16388:16531])
text = original.decode('utf-8').replace('\r\n', '\n')

def replace(old, new):
    global text
    assert text.count(old) == 1, old
    text = text.replace(old, new)

replace(r'''We use two exact inputs from Browning--Heath-Brown~\cite{v5bhb}.''',
r'''We use Lemmas~2.1 and 4.1 of Browning--Heath-Brown~\cite{v5bhb}.
The adjacent-norm polynomials are inhomogeneous, so we give the
fixed-coordinate argument rather than invoke their homogeneous
quadric-sieve theorem directly.''')
replace(r'''squarefree $q$ of a rank-$m$ quadratic form by at most''',
r'''squarefree $q$ of a rank-$m$ quadratic form, with $m\geq3$, by at most''')
replace(r'''In this statement every prime dividing $q$ must be odd and preserve the
rank of the form. We include the word ``odd'' explicitly. Rank preservation
alone is not the good-prime convention of the cited lemma.''',
r'''Every prime dividing $q$ must be odd and preserve the rank of the form.
The lattices in that lemma contain $q\mathbb Z^m$; in particular their
largest successive minima are at most $q$.''')
replace(r'''For fixed $\kappa\ne0$ and $\epsilon,\eta\in\{1,-1\}$, the number of
integral vectors of size $O(B)$ satisfying $Q_\kappa=0$ and''',
r'''Fix the implied constant in the box of size $O(B)$.
For fixed $\kappa\ne0$ and $\epsilon,\eta\in\{1,-1\}$, uniformly for
$B,L\geq2$, the number of integral vectors in this box satisfying
$Q_\kappa=0$ and''')
replace(r'''R=\kappa w^2-xz$. Then $x_0x_1=R$.
Parity restrictions can be discarded in an upper bound.''',
r'''R=\kappa w^2-xz$. Then $x_0x_1=R$.
Parity restrictions can be discarded in an upper bound.
For a fixed nonzero value of either $x_0$ or $x_1$, the triple $(x,z,w)$
determines the other coordinate uniquely whenever it gives an integral
solution. We shall use this injection when discarding divisibility
conditions.''')
replace(r'''Summing over $R=h\ell^2\ne0$ gives
$O(B^{3+2\alpha}/(L\log L))$.
The case $R=0$, including $x_0x_1=0$, contributes $O(B^{2+\alpha})$.''',
r'''Since $0<|h|\ll B^2/\ell^2$ and $\ell\ll B$, summation gives
\[
 O_{\kappa,\alpha}\left(
 B^{3+2\alpha}\sum_{\ell>L}\ell^{-2}\right)
 =O_{\kappa,\alpha}(B^{3+2\alpha}/(L\log L)).
\]
The same bound for triples with $R=0$, followed by the $O(B)$ choices
with $x_0x_1=0$, gives $O_{\kappa,\alpha}(B^{2+\alpha})$.
We may discard all these $R=0$ solutions before proceeding.''')
replace(r'''Take $t=x_1$ first. Multiplication by the invertible denominator $4t^2$
turns the two norm congruences into divisibility of''',
r'''Take $t=x_1$ first. Here
$G_1-H_1=\kappa w^2+2t$ and $4t^2G_1=K$.
Thus the two norm congruences are equivalent to divisibility of''')
replace(r'''For $t=x_0$ the pair is''',
r'''For $t=x_0$ we still have $4t^2G_1=K$, whereas
$t(G_1-H_1)=\kappa(t+2)w^2-2xz$. The pair is therefore''')
replace(r'''The coefficient $-2$ of $xz$ excludes a common odd content prime.''',
r'''The coefficient $1$ of $x^2z^2$ in $K$ excludes every common content
prime. In both charts the fixed value $t$ is nonzero.''')
replace(r'''The form $R$ has rank three at every prime in this product, and those primes
are odd. For a fixed $q$, the number of eligible $t=O(B)$ is
$O_{\kappa,\alpha}(B^\alpha)$ after an arbitrarily small adjustment of
$\alpha$. One way to see this is to majorize the count of integers
supported on $S_R\cup\{p:p\mid q\}$ by
$B^\alpha\prod_{p\in S_R\ \text{or}\ p\mid q}(1-p^{-\alpha})^{-1}$,
and absorb its $q^{o(1)}$ factor.''',
r'''The matrix of $R$ has determinant $-\kappa/4$, so $R$ has rank three
at every prime in this product, and those primes are odd. Also $q\ll B$.
For a fixed $q$, every eligible nonzero $t=O(B)$ is supported on
$S_R\cup\{p:p\mid q\}$. For every $\delta>0$, Rankin's bound gives
\[
 \#\{t:q(t)=q,\ 0<|t|\ll B\}
 \ll B^\delta
   \prod_{p\in S_R\ \text{or}\ p\mid q}(1-p^{-\delta})^{-1}
 \ll_{\kappa,\delta} B^\delta q^\delta
 \ll_{\kappa,\delta} B^{2\delta}.
\]
For the middle inequality, remove the finitely many primes with
$p^{-\delta}>1/2$ and bound the remaining factors by $2^{\omega(q)}
\ll_\delta q^\delta$. Renaming the small exponent gives
$O_{\kappa,\alpha}(B^\alpha)$ choices of $t$.''')
replace(r'''Each covering lattice contains $q\mathbb Z^3$, so all its successive minima
are $O(q)=O(B)$. It therefore has $O(B^3/q^2)$ points in the box.
The lattices with largest minimum greater than $T$ contribute, after the
sums over $q$ and $t$,
\[
 O_{\kappa,\alpha}(B^{5+2\alpha}T^{-3}).
\]''',
r'''If $\lambda_1\leq\lambda_2\leq\lambda_3$ are the successive minima,
then $\lambda_3\leq q\ll B$ and
$\lambda_1\lambda_2\lambda_3\asymp q^2$.
A basis comparable to these minima therefore gives
$O(\prod_i(1+B/\lambda_i))=O(B^3/q^2)$ points in the box.
The lattices with $\lambda_3>T$ contribute at most
\[
 B^\alpha\sum_{q\ll B}
 O\left(9^{\omega(q)}q^3T^{-3}\frac{B^3}{q^2}\right)
 \ll_{\kappa,\alpha} B^{5+2\alpha}T^{-3}.
\]''')
replace(r'''The resulting rectangular box has volume $O(B^3/q^2)$
and minimum side parameter $\gg B/T$.''',
r'''The inverse basis matrix bounds the new coordinates by
$O(B/\lambda_i)$, so the resulting rectangular box has volume
$O(B^3/q^2)$ and minimum side parameter $\gg B/T$.
Enlarge its side parameters to at least $2$, as required in
\eqref{eq:v5-box-sieve}; since $\lambda_i\ll B$, this changes volume
only by a fixed factor.''')
replace(r'''There are at most $9^{\omega(q)}q$ lattices. Summation gives
$O(B^{3+3\alpha}/(L\log L)+B^{2+3\alpha}T)$.''',
r'''There are at most $9^{\omega(q)}q$ lattices. Since
$9^{\omega(q)}\ll_\alpha q^\alpha$, summing over $q\ll B$ and the
$O_{\kappa,\alpha}(B^\alpha)$ values of $t$ gives
$O_{\kappa,\alpha}(B^{3+3\alpha}/(L\log L)+B^{2+3\alpha}T)$.''')
replace(r'''For fixed distinct $c_j$ there are $\tau_0,C>0$ such that, for every fixed
$0<\tau\leq\tau_0$, the logarithmically weighted number of pairs''',
r'''For fixed distinct $c_j$ there are $L_*\geq2$ and $\tau_0,C>0$
such that, for every fixed $0<\tau\leq\tau_0$, uniformly for $L\geq L_*$,
the logarithmically weighted number of pairs''')
replace(r'''Take $B=\sqrt N$ and combine the preceding bounds at $L_0=B^{1/100}$.
The medium bound loses at most $(\log B)^k$ on inserting the weight.
The large bound with sufficiently small $\alpha$ is
$O(B^{3-1/200})$ after the logarithmic weight is inserted.
At one position use the polynomial pair $a,b^2+1$ in three variables
in \eqref{eq:v5-box-sieve}.
There are only finitely many pairs of positions and signs, and a split
rational prime has eight Gaussian generators. These factors are absorbed
in $C$. Every vector arising from prime norm is primitive, since a common
integer divisor greater than one would have its square divide that prime.
Weakening the power saving to $B^{3-1/400}$ gives the displayed estimate.''',
r'''Take $B=\sqrt N$ and $L_0=B^{1/100}$, and choose $\tau_0$ so that
every prime value in the displayed region is between fixed positive
multiples of $B^2$. Thus $\prod_j\log p_j\ll (\log B)^k$.
Choose $L_*$ above the fixed exceptional primes in the medium-prime bound.
When $L\leq L_0$, that bound gives
\[
 \frac{C\tau B^3}{L\log L}+O_\tau(B^{27/10}(\log B)^k)
\]
for $L<\ell\leq L_0$. Its proof is uniform in this interval of $L$:
the remainder sum is bounded by the sum over all $\ell\leq L_0$.
When $L>L_0$ this part is empty.

For distinct positions, apply Lemma~\ref{lem:v5-large-sieve} at $L_0$
with $\alpha=1/1000$. After multiplication by the weight, the bound is
\[
 O\left(\left(
   \frac{B^{3+1/1000}}{B^{1/100}\log L_0}
       +B^{11/4+1/1000}\right)(\log B)^k\right)
 =O(B^{3-1/200}).
\]
This bounds all the remaining primes, also when $L>L_0$.
At one position, an odd divisor of both adjacent norms divides
$a$ and $b^2+1$. The coprime pair $a,b^2+1$ in variables $(a,b,w)$,
inserted in \eqref{eq:v5-box-sieve} at $L_0$, gives
\[
 O\left(\left(
 \frac{B^3\log B}{L_0\log L_0}+B^2\log B\right)(\log B)^k\right)
 =O(B^{3-1/200}).
\]
No factor $\tau$ is needed in these power-saving errors.

For a fixed pair of positions, the vector $(a,b,c,d,w)$ determines
$u=a^2+b^2-c_jw^2$; at one position $(a,b,w)$ does so.
Thus the vector counts bound the pattern counts. There are finitely many
pairs of positions and signs. Each split rational prime has eight
Gaussian elements of that norm, so counting all generator choices
changes the bound by at most a fixed factor. Every vector used in the
medium-prime count is primitive, since a common integer divisor greater
than one would have its square divide a prime norm.
All logarithmic factors in the remainders are absorbed for sufficiently
large $B$, with thresholds depending only on the fixed data and $\tau$.
Weakening the error to $B^{3-1/400}=N^{3/2-1/800}$ proves the claim.''')

HERE.joinpath('original-tail.tex').write_bytes(original)
HERE.joinpath('replacement-tail.tex').write_text(text, encoding='utf-8', newline='\n')
old_labels = re.findall(r'\\label\{([^}]+)\}', original.decode())
new_labels = re.findall(r'\\label\{([^}]+)\}', text)
assert old_labels == new_labels
manifest = {
    'baseline_path': str(BASE),
    'baseline_sha256': expected,
    'replace_inclusive_lines': [16389, 16531],
    'original_interval_sha256_exact_bytes': hashlib.sha256(original).hexdigest(),
    'replacement_sha256': hashlib.sha256(HERE.joinpath('replacement-tail.tex').read_bytes()).hexdigest(),
    'labels_preserved': old_labels,
    'status': 'independent tail audit completed; no fatal tail gap found; source access limitation recorded in REPORT.md',
}
HERE.joinpath('handoff.json').write_text(json.dumps(manifest, indent=2)+'\n', encoding='utf-8')
print(json.dumps(manifest, indent=2))
