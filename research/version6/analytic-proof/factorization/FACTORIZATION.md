# Quantitative factorization with a non-circular parameter choice

Date: 2026-11-06. This is a generic analytic implication. Its arithmetic
application is conditional on the stated centered progression estimates
and mean-zero minor-arc estimates. It does not assert that the complete
Frei–Tinkova replacement has been independently accepted.

## 1. Generic lemma

Fix dimensions m and filtration degree d. Write L=log(2N). Let w_N be a
complex weight on [N]. Constants may depend on a fixed arithmetic modulus
and on m,d, but not on the polynomial orbit or on N. Assume:

**Growth.** There is a fixed K>=0 such that |w_N(n)|<=C L^K.

**Centered progression sums.** For every A0,C0>0,

    |sum_{n in P} w_N(n)| <= C_(A0,C0) N L^(-A0)          (SW)

uniformly for every arithmetic progression P contained in [N] whose
common difference is at most L^C0. There is no lower bound on |P|.

**Mean-zero minor arcs.** There are fixed c>0, C1,K1>=0 such that for every
nilmanifold of dimension at most m with a degree-d rational filtration,
a Q-rational adapted Mal'cev basis, and every polynomial sequence h whose
orbit on [N] is totally delta-equidistributed,

    |sum_{n in P} w_N(n) F0(h(n))|
        <= C N delta^c Q^C1 L^K1 ||F0||_Lip,             (MA)

provided F0 has Haar integral zero. Here P may be any progression with
common difference <=Q and length >=N/Q. The stronger version allowing
arbitrary lengths is also sufficient.

The conclusion below is unchanged if (MA) is only supplied in a parameter
regime

    delta >= N^(-sigma),       Q <= delta^(-kappa),       (R)

for fixed positive sigma,kappa. All applications made in the proof will
fall inside (R). Using a power estimate, rather than only a list of
polylogarithmic specializations with unspecified dependence, is important.

Then, for every A,Cinit>0, every initial nilmanifold of dimension at most m
and degree at most d with an L^Cinit-rational adapted Mal'cev basis, every
polynomial sequence g, and every Lipschitz F,

    |sum_{n<=N} w_N(n) F(g(n)Gamma)|
        <= C_(A,Cinit) N L^(-A) ||F||_Lip.               (F)

All groups here use the Green–Tao convention: connected simply connected
nilpotent G, discrete cocompact Gamma, and filtrations of closed connected
rational subgroups. Dimension-zero factors are allowed and contribute
only constants.

## 2. Published factorization and conjugation inputs

We use the one-parameter factorization theorem, Green–Tao, *The quantitative
behaviour of polynomial orbits on nilmanifolds*, Annals 175 (2012),
Theorem 1.19. Given an exponent B and initial rationality M0, it gives

    M0 <= M <= C_(B,m,d) M0^(E(B,m,d)),
    g(n)=epsilon(n) g'(n) gamma(n),

where epsilon is (M,N)-smooth, gamma(n)Gamma has period q<=M, and g' is
totally M^(-B)-equidistributed in a rational subgroup quotient. The new
basis consists of M-rational combinations of the initial basis.

The quantitative conjugation statement used below is exactly the Claim
in Green–Tao, *The Mobius function is strongly orthogonal to nilsequences*,
Annals 175 (2012), printed page 547. Its derivation there uses the published
Appendix A rational-subgroup, rational-element, and metric comparisons.
There are fixed constants a>0 and C2>=1, depending only on m,d, such that:

* Taking a reduced rational representative gamma_j for each periodic
  coset gives coordinates of height <=M^C2.
* H_j=gamma_j^(-1)G'gamma_j has a basis of rationality <=M^C2 relative to
  its lattice Lambda_j=H_j intersect Gamma.
* h_j(n)=gamma_j^(-1)g'(n)gamma_j is totally
  delta=M^(-aB+C2)-equidistributed on H_j/Lambda_j.
* If epsilon is frozen at a value a_cell, the function
  F_cell(x Lambda_j)=F(a_cell gamma_j x Gamma) has Lipschitz norm at most
  M^C2 ||F||_Lip and sup norm at most ||F||_infinity.

Increase C2 to absorb fixed multiplicative constants. These exponents are
independent of B. Conjugation can change the lattice by a commensurable
lattice of index M^O(1); one must use the published rational-lattice
comparison, rather than assert that conjugation gives an isometry of the
original quotients. The power loss a and the term C2 include that step.

Official published sources:

* https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf
* https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p03-p.pdf

Pinned local sources are `GT-orbits-published.pdf` and
`GT-mobius-published.pdf` under `work/quartic-version5-release/sun-proof/sources/`.
The latter's printed pages 544–547 correspond to local text lines 126–311.

## 3. Fixing the smooth factor and counting cells

Normalize ||F||_Lip=1. Choose

    D=A+K+3,       M0=L^max(1,Cinit).

For now leave B unspecified. Split each residue class modulo q into
consecutive balanced blocks with diameter at most C N/(M L^D). Call the
resulting progressions P_cell. For N sufficiently large after B is fixed,
the partition can be chosen so that

    number of cells <= C M² L^D,
    |P_cell| >= N/(C M² L^D),
    common difference(P_cell)=q<=M.                      (C)

For example, cut each of the q residue classes into ceil(M L^D) blocks
of nearly equal cardinality. All floor effects are absorbed in C because
M is a fixed power of log N once B is fixed.

Freeze epsilon at any n_cell in the cell. Smoothness and right invariance
of the ambient group metric give

    |F(epsilon(n)g'(n)gamma_j)-F(epsilon(n_cell)g'(n)gamma_j)|
          <= C L^(-D).

This estimate does not multiply by a coordinate bound for g': right
invariance removes that factor. Growth of w then bounds the total freezing
error by C N L^(K-D)<=C N L^(-A-3).

## 4. Means and minor arcs on the cells

For each cell write F_cell=m_cell+F_cell^0, where m_cell is its Haar mean
on H_j/Lambda_j. Then

    |m_cell|<=1,     ||F_cell^0||_Lip <= 2M^C2.

This subtraction is essential. Haar mean zero for the original F would
not imply Haar mean zero for its restriction to a translated subgroup.
If H_j has dimension zero, F_cell^0 vanishes and only the mean remains.

Choose a fixed exponent

    U=C2+D+5.

Since M>=L, one may take Qstar=M^U. It dominates the new rationality,
the cell modulus, and N/|P_cell| in (C), for large N. Put b=aB-C2, so
the equidistribution parameter is delta=M^(-b). The sum of all applications
of (MA) is at most

    C N L^K1 M^(-bc+C1*U+C2) * M² L^D
      <= C N L^K1 M^(-bc+C1*U+C2+2+D).                  (M)

This counts every cell; it does not replace a global N bound by an
unjustified |P_cell| bound.

Choose B now, before using the upper bound for M, large enough that

    b>1,
    b*c >= C1*U+C2+2+D+A+K1+4,
    b*kappa >= U+1    if the restricted regime (R) is used.       (B)

Then (M) is O(N L^(-A-4)). In the restricted regime the Q condition holds
because Qstar=M^U<=delta^(-kappa). The lower bound delta>=N^(-sigma)
holds for all sufficiently large N, since after B is fixed we know
M<=C L^E for some finite E. There is no additional restriction on B here;
only the eventual threshold in N grows.

Now, and only now, use factorization's upper bound M<=C L^E. Increase E
to absorb C. There are at most C L^(2E+D) cells, each of modulus <=L^E.
Use (SW) with

    C0=E+1,       A0=A+2E+D+4.

The sum of all constant terms m_cell times their progression sums is
O(N L^(-A-4)). Together with the freezing and minor-arc errors, this proves
(F).

## 5. Why this is not a circular parameter choice

The order is

    A,K,Cinit,c,C1,K1,a,C2,(kappa,sigma)
       -> D,U -> B -> E(B) -> the SW exponents C0,A0 -> N0.

The inequalities selecting B are all in powers of the actual output M,
using only M>=L. They never require B to dominate E(B). After B is fixed,
the arbitrary-power centered progression hypothesis allows A0 to be made
larger than the resulting cell-count exponent. Choosing a minor-arc
logarithmic saving first and then trying to make it dominate an unspecified
E(B) would not justify this proof.

## 6. Arithmetic interface

For the intended centered W-tricked Gaussian ray-prime weight, W and the
ray modulus are fixed before N tends to infinity. The expected growth
exponent is K=1. Root's progression main-term computation must prove (SW)
for that exact centered weight, uniformly in every progression modulus
up to a prescribed power of log N.

The independent Type I/II manuscript supplies a mean-zero estimate for
Gaussian ideal von Mangoldt weights of the form

    C_(H,m,d) Q N log(2N)^7 delta^c ||F0||_Lip.

`AFFINE_PULLBACK.md` explains the additional fixed-W interpolation step
needed before applying that result to a W-tricked input. Finite character
expansion, the rational-prime companion estimate, and negligible prime-power
terms then give (MA), possibly with a smaller positive exponent and in
the restricted regime (R). Those losses are explicitly allowed above.

This file proves the generic implication from its hypotheses. It does not
prove or silently assume that the arithmetic centered progression hypothesis
has already been discharged.
