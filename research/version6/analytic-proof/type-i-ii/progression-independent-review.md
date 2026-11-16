# Independent review of progression main terms

Reviewed `../progression_mainterms.tex` on 2026-11-06. Verdict: the finite
Fourier normalization, field-fiber calculation, Gaussian factor two, and
fixed-W progression cancellation are correct, conditional on the explicitly
stated fixed-field Hecke Siegel--Walfisz input. This review does not establish
that analytic input. No change to the displayed main coefficients is needed.

## Finite normalization and field fibers

For H divisible by 16, Gaussian class number one identifies the ray group
with `(Z[i]/HZ[i])^*/{1,-1,i,-i}`. The four units have distinct reductions.
The extension is stable under complex conjugation, and conjugacy in its
rational Galois group restricts on the abelian subgroup A to the two-element
complex-conjugation action. Thus the assumed invariance of C is exactly what
is needed for a union of rational Frobenius classes.

The Fourier coefficient
`c_C(chi)=|A|^-1 sum_{a in C} conjugate(chi(a))` gives
`1_C(g)=sum_chi c_C(chi)chi(g)`. The Dirichlet coefficient is independently
`conjugate(rho(a))/phi(q)`, as required for a reduced residue class. Neither
conjugation is missing or duplicated.

For `L=K Q(zeta_q)`, restriction identifies `Gal(L/E)` with the pairs
`(g,s)` in `A x Gal(Q(zeta_q)/Q)` having equal restriction to
`J_q=K intersect Q(zeta_q)`. This remains valid when E is not contained in
`Q(zeta_q)`: compatibility already forces s to fix the intersection with E.
For an E-prime ideal, the cyclotomic coordinate of arithmetic Frobenius is
the norm residue, so `chi(g)rho(s)` is the required norm-twisted Hecke
character. Averaging over this finite fiber product therefore produces
exactly the trivial-character indicator in the assumed SW formula.

The denominator of the ideal main term is `[L:E]`. Every split rational
prime contributes two conjugate degree-one prime ideals with weight log p;
C-invariance gives the same indicator on both. Inert primes contribute only
at norms p^2, and ramified/excluded primes belong to the stated error. Hence
division by two changes `[L:E]` to `[L:Q]`, exactly as displayed. For example,
K=E, C={1}, q=1 gives density 1/2, while q=4,a=1 also gives 1/2. Both checks
agree with the formula.

## Primitive and imprimitive characters

The criterion for the coefficient one is that the induced *primitive*
Hecke character be trivial, not that chi and rho each be trivial. The text's
criterion on their induced product includes cancellation between nontrivial
chi and a norm character. This is necessary and is handled correctly by the
finite-group calculation.

For an imprimitive character, omitted prime ideals divide Hq. Each such
prime ideal contributes at most log X through all its powers <=X. There are
at most `2 omega(Hq)` of them. Their total is therefore
`O(log X log(2Hq))`, uniformly for `q<=log^B X`; this justifies the text's
polylogarithmic Euler-factor error. It changes no leading coefficient.

The Hecke SW input itself still requires the separately audited treatment of
primitive real characters and possible exceptional zeros. Nothing in the
finite Fourier calculation establishes that input or removes its possible
ineffectivity. The displayed uniformity in all endpoints Y also belongs to
that input. It can be obtained from an endpoint-at-Y version by using a
trivial bound for `Y<=X/log^M X` and a slightly larger modulus exponent for
the complementary range, but that implication should be part of the analytic
input audit rather than silently assumed here.

## Centered progressions and cutoffs

If W contains the conductor of K^ab then
`K intersect Q(zeta_(Wq))=K^ab` for every q. The intersection is abelian over
Q, so it is contained in K^ab, and the conductor condition gives the reverse
inclusion. Consequently

`[K Q(zeta_(Wq)):Q]=[K:K^ab] phi(Wq)`.

For a unit a modulo Wq with a=b modulo W, the numerator in the progression
lemma is `mu_C(b)[K:K^ab]`. Its main coefficient is therefore
`mu_C(b)/phi(Wq)`, with no missing phi(W) or W factor. Multiplying both prime
weights by phi(W)/W leaves their main terms equal and they cancel.

The large-q cutoff is valid uniformly over all progressions in [N], including
singletons: their size is at most N/q+1, and the extra `log N` from the +1
is negligible compared with `N/log^D N` for fixed D and sufficiently large N.
For nonreduced a modulo Wq, every prime in the class divides Wq, yielding
only a polylogarithmic contribution. Interval endpoints can be subtracted
using the assumed uniform SW error.

One external input should be named explicitly in the final dependency list:
the ordinary rational-prime Siegel--Walfisz theorem used for lambda_(b,W).
It is distinct from the Gaussian Hecke assertion as stated, which concerns
only E=Q(i). The text correctly invokes the ordinary theorem, but its
publication pin should accompany the Gaussian pin. This is a dependency
clarification, not a normalization error.

The corollary is correctly stated for fixed H and fixed W. It does not by
itself give a bound uniform for an arbitrary growing W=W(N). A later diagonal
choice of sufficiently slowly growing W is compatible with this result, or
one can separately track uniform constants. The order of limits must remain
explicit in the eventual cube and cutoff argument.

## Scope of acceptance

Accept the conditional progression lemma and fixed-W centered corollary.
Keep the source gate on Hecke SW open until its separate published-input
audit closes. Keep the ordinary SW source and any growing-W diagonalization
visible in the dependency record. No unconditional FT-removal conclusion
follows from this review alone.
