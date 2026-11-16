# Independent local conductor review

Status: accepted at the stated local-representation scope.

Reviewed source: `../height-descent/small-prime-conductor.tex`, SHA256
`1447025bba850d9c33df41046c71357d03c6926b1b3800cbb87becb4bbc8ec9b`.
Reviewer: `/root/astra_exact82_repair`, 2026-11-05.

The bound is `a_p(r) <= 274` for `p=2,3,5,7`. The padded exponent 300 is therefore justified by this argument. This review does not by itself establish modularity, compatibility at coefficient primes, the passage from Artin conductors to a global modular level, or the subsequent height estimate; the main reviewer is checking those separately.

## Galois fields and degrees

The prime-to-11 isogeny construction is valid. At 11, a rational normalizer element is a scalar times a maximal-order unit. Scaling by a rational power of 11 removes that scalar valuation. One can clear its finitely many remaining denominators with an integer prime to 11. The scalar analytic isogeny then has degree a unit at 11 and commutes with the specified quaternion action. The all-homomorphisms hypothesis makes it L-defined. It identifies the two 11-torsion Galois modules, so every conjugate of `L(A[11])` equals that field. Thus E/Q is Galois.

The tower degree divides `576 |GL_4(F_11)|`. The numerical estimate uses only `576<2^10` and `11^2<2^7`, giving `[E:Q]<2^66`. Consequently `v_p(e_E)<=65` for every prime p. No large group order needs to be expanded.

The field of the character epsilon means its kernel field, not its value field. This is essential. It is abelian over Q; its odd-prime ramification is tame, and its ramification index at 2 is at most two. Tame extensions remain tame under base change. Hence adjoining it to E adds no odd p-part to the local ramification index and adds at most one factor of two at 2.

On G_F, the normalized cocycle and d restrict to one, so beta is a quadratic character. To check conjugation invariance explicitly, write `h'=g h g^-1`. Since h and h' lie in G_F and all mixed cocycle values with this kernel are one,

    beta(g) beta(h) = beta(g h) = beta(h' g) = beta(h') beta(g).

Thus beta(h')=beta(h). Its kernel is normal in G_Q, and F'/Q is Galois, with `[F':F]<=2`. The local estimates `v_p(e_F')<=65` at odd small primes and `v_2(e_F')<=67` follow.

## Semistability and potential good reduction

The exact published torsion criterion is Silverberg--Zarhin, *Semistable reduction and torsion subgroups of abelian varieties*, Annales de l'Institut Fourier 45(2) (1995), 403--420, Theorem 3.5 (Raynaud criterion), printed p.406. It was independently read in the [published PDF](https://www.numdam.org/item/AIF_1995__45_2_403_0.pdf). Apply it over a completion of E with n=11 and residue characteristic in {2,3,5,7}; all 11-torsion is rational. Their Theorem 3.3, p.405, states the semistable inertia criterion. These statements suffice for the source's wild-inertia conclusion.

In fact the surface has good reduction over E at these primes. Every quaternionic endomorphism is defined over E and extends to the Neron model, preserving the toric part of its semistable special fiber. If that torus were nonzero, its rational character group would be a nonzero unital module for the division algebra B. Its Q-dimension would be a positive multiple of four. The toric rank of an abelian surface is at most two, a contradiction. This stronger observation is optional; the source needs only semistability and trivial wild inertia.

## Different and upper breaks

The displayed different bound has the correct normalization. Let K/Q_p be the local Galois extension, let K_0 be its maximal unramified subfield, let pi be a uniformizer of K, and let f be its Eisenstein polynomial over K_0, of degree e. The extension is monogenic and the different exponent is `v_K(f'(pi))`. The nonzero derivative terms `i a_i pi^(i-1)` for `1<=i<=e` have valuations congruent to `i-1 modulo e`, because K_0/Q_p is unramified. They cannot cancel at the minimum. In particular the minimum is at most the valuation of `e pi^(e-1)`, giving

    delta <= e v_p(e) + e - 1.

For upper numbering, the full identity is

    delta/e = (1-1/e) + integral_0^infinity (1-1/|G^u|) du.

The extra tame term is nonnegative. Until the largest positive upper break b the ramification group is nontrivial, so its integrand is at least 1/2. Hence `b<=2 delta/e<=2(1+v_p(e))<=136`. In the tame or unramified case take b=0.

By upper-numbering compatibility with quotients, every absolute group `G_Qp^u` for `u>136` lies in G_F'. Since u>0, it also lies in absolute wild inertia. Its intersection with G_F' is contained in wild inertia over F', so the restricted Tate constituent is trivial there. This supplies the otherwise implicit step between the finite extension's break and the representation's break.

It follows from the Swan integral that `Sw(r)<=2*136`; the tame codimension is at most two. Thus `a_p(r)<=274`.

## Character choice and support lemma

The local character construction is correct. At an odd ramified sign prime p, a character modulo p with full 2-primary order has nonzero square-root obstruction. At 2, the odd character modulo four has the required obstruction. The infinite obstruction is its parity; Brauer reciprocity gives precisely the required parity after multiplying the local factors. Equality of the local invariants gives equality of the global two-torsion Brauer classes, so a continuous sign cochain produces the desired beta.

Such a sign cochain can initially add quadratic ramification at extra primes. The appended support lemma explicitly removes those finitely many odd primes by twisting beta with the character of Q(sqrt(D)), where D is their product. At an odd prime there is a unique nontrivial quadratic character on inertia; this cancels it. Only the prime 2 can be newly ramified, and it is already allowed. The twist squares to one, so epsilon and the local index bounds are unchanged.

The appended tame-prime argument is also correct at the representation level. For p>7, the pro-p wild group maps trivially to Gal(L/Q), whose order divides576, and beta restricts there to a quadratic character, hence is trivial. For a surface, choose a prime ell whose residue has order p-1 modulo p. Then p does not divide `|GL_4(F_ell)|`, and a pro-p image in the pro-ell congruence kernel is trivial. This proves trivial wild inertia for the Tate representation. Passing this conclusion between members of the modular compatible family remains within the separate global review.

No heavy computations, polynomial expansion, builds, or modifications to the reviewed source were performed.
