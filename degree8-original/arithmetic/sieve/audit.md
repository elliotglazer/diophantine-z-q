# Original 15671 construction: sieve and shared-J audit

The original 41-position prime pattern and the shared auxiliary point J pass this audit, at the stated arithmetic boundary. A full published-input proof is in original41-proof.tex. The unchanged original generator matches that proof. No cross-prime reduction-order theorem is required, and no change to the original polynomial was made.

The conclusion here does not independently prove the generator assertion 2E(Q(sqrt(2)))=Z P_*, the five-contact height theorem, or the seven-witness parity theorem. Those are separate inputs under review. This packet proves the prime-selection assertion from published inputs and checks exactly how its output supplies the common-J comparison and the hypotheses of specialized parity completeness.

## The exact constants

The fixed computation in check_constants.py confirms

- R=47027=31*37*41;
- W=25878772920=4 times the product of primes at most 29;
- V0=32W=828120733440;
- c=18484837801 is 1 modulo 8 and every odd prime at most 29 except 7, where it is 3.

The outputs and explicit local witnesses at 31, 37 and 41 are in reference-constant-check.json. This was a tiny fixed-integer calculation, not a prime search or polynomial expansion.

For D={0,1,2401,-343/32}, the nonzero integral differences are exactly +/-1, +/-2400 and +/-2401, none divisible by 31. The integral sums are 0,1,2,2401,2402,4802; their residues modulo 31 are 0,1,2,14,15,28, not 3. Consequently A_i=R a_i+3 for distinct integer targets gives disjoint primary and secondary slope families. Deleting repeated targets leaves m=5+4k distinct prime forms, with m<=41.

On the original lattice u=c+Wx, v=V0(c+Wy), every form is integral and congruent to c modulo W, including the forms with denominator 32. At 31,37,41 all A_i reduce to 3, so there are at most eight slopes. At every prime at least 43 there are at most forty slopes. Two missing slope residues therefore exist. The explicit construction in the proof avoids zero and -1 for every numerator and for v/V0. This verifies all local admissibility, including the successor restrictions needed for the same-prime order sieve.

## Published prime-distribution and order inputs

The proof invokes Green--Tao's Main Theorem for finite-complexity affine forms at complexity at most 39. The other forms can be partitioned into singletons, and no linear parts are proportional. The system is integral in x,y; adding an unused z gives the same three-dimensional box framework as the previously audited proof. Green--Tao Mobius orthogonality supplies MN(39), and the published Green--Tao--Ziegler inverse theorem supplies GI(39). The publication records, exact statements and versions were checked in the preceding literature audit; source-ledger.json carries the exact locators and source hashes into this packet. The published 2012 GTZ source is distinguished from the inherited corrected author version and erratum. No new unpublished theorem assumption is introduced.

Unlike the original archive's appeal to an underlying source prime-pattern theorem, original41-proof.tex includes the cutoff dependence explicitly. Its prime lower count is

    c_a X^3 / ((log L)^(2m) (log X)^m).

Here c_a is independent of L. All residue classes, coefficients and moduli are fixed before applying GT as X tends to infinity. The Selberg weights, CRT error, Euler-product truncation and one-prime omission are written out. They give a bad-pattern upper bound

    C_a X^3 / (L (log X)^m) + o_a(X^3/(log X)^m),

with C_a independent of L. Choosing L first and X second is therefore valid. No growing-modulus GT estimate is asserted.

The reduction-order calculation uses the original curve y^2=x^3-(3-sqrt(2))^2 x. Its two twisting factors have product 7, so the selected congruence classes give opposite traces. Silverman's Tate-module injection, trace/determinant formulas, and integral Frobenius equation give d_1,d_2=p+1 +/-2a with a^2+b^2=p. Rational two-torsion gives the exact 2-primary gcd 4. An odd common divisor must divide a and p+1, and its root condition b^2=-1 modulo that divisor permits the same elementary exceptional-prime sieve. The argument controls only the two orders at one prime.

The five published bibliography keys used in the standalone proof are greentao, moebius, gtz, williams-mertens and silverman. These references are new relative to the archive's bibliography of supplied manuscripts, but not new to the previously verified baseline literature. No Sun, Frei--Tinkova, or geometric cross-order sieve is used.

## Why the common J works

Fix one orientation at each distinct selected contact prime p. Write d_{p,1},d_{p,2} for the two reduced group cardinalities. Set j=lcm_p d_{p,2} and J=jP_*. For each p choose its private h_p by

    h_p=0 mod d_{p,1},
    h_p=4 mod d_{p,2},
    h_p=4 mod p^(64+v_p(j)).

The first two congruences are compatible because their modulus gcd is 4. The last is compatible because the two orders at p are both p-units. This remains true if another contact prime contributes a factor p to j. That contribution is handled by the increased local precision v_p(j), not by an additional cross-order congruence. Avoiding h_p=0,4,-4 leaves infinitely many choices.

All primary X_i=h_p n_i P_* are formal at the primary place, while J and Y_i=(h_p-4)n_i P_* are formal at the opposite place. At a split odd good prime, Silverman IV.6.4 and VII.2.1-2.2 identify the reduction kernel with the formal group and give the logarithm homomorphism and valuation isometry. For two formal multiples kP_* and jP_*, the identity

    log(kP_*)/log(jP_*) = k/j

follows by applying the homomorphism law to j(kP_*)=k(jP_*). It does not assume that P_* itself is formal. Hence the conjugate parameter ratio has valuation at least 64, and the primary full-log ratio is exactly n_i.

The archive's intermediate construction with h_q,j_q and t_q can also be completed by taking j_q=d_{q,2} and choosing h_q to be a q-unit. Its short text does not explicitly state that unit choice at that point. The direct construction above removes the ambiguity and avoids any need to assume unspecified source local witnesses. This is a proof completion, not a polynomial change.

For soundness, the same full-log identity gives v_p(m_i-4n_i)>=64 and v_p(h-4)>=64 from the conjugate ratio tests, because j is an integer. Thus h is a p-unit. The original truncation has first omitted degree 65; the proof supplies the coefficient-valuation bound for every omitted term. Consequently the primary truncated ratio is integral and congruent to m_i/h, and then to n_i, modulo p^64. This verifies the original shift 4, with no replacement by the larger shift used in the separate 20371 construction.

## One common theta and the parity prerequisites

Choose the private points first, with a consistent orientation for repeated primes. For every field test A+B sqrt(2) of required order k, approximate its selected square root rho_p by a single integer theta to precision at least k-v_p(B), and at least one. Finitely many CRT conditions suffice. Since theta+rho_p is a unit, both rational tests (theta^2-2)B and A+theta B have order at least k. The converse follows by the same identity. This is exactly the common root passed by the original generator to every q_compare4 call.

Every complete-assignment raw contact r is a positive prime congruent to c modulo W. Therefore r is a square in Q_2, Q_3 and Q_17. The rational norm-tree root is a unit at r, is positive, and is nonzero. The parity input r times that root squared is positive, has a square reduced denominator, and is square at those three local fields. These are precisely the original specialized parity-completeness hypotheses. Integrality of the auxiliary points at the small primes is unnecessary for this argument. That integrality was required by a different baseline-pole replacement and must not be imported into the present verification.

## The five contacts and the unchanged generator

There are ten slopes when all nine targets are used. Their forty finite contacts are separate raw positions, while their infinity contact is represented by the one common position v/V0. In a complete assignment, v=V0 p0 and every numerator form is a prime different from p0. Thus each slope has the same depth-one infinity contact p0 and its four depth-one finite contacts. The fixed denominator primes are all in the original exceptional set S_*.

For arbitrary rational assignments, these raw forms still detect every odd normalized projective contact. If m=min(v_p(U),v_p(v)) is even, the distinguished odd normalized contact has an odd raw valuation. If m is odd and the contact is finite, the raw denominator v/V0 has odd valuation; if it is at infinity, the finite raw forms have odd valuation. The contact differences and V0 are units outside S_*. Thus no missing additional infinity witness is needed.

Read-only inspection of build.py confirms the exact contact signs, the affine factor R a_i+3, one shared J and theta, and private X_0,...,X_4 inside each comparison call. The shared prefix passes the conjugate f(J) and inverse conjugate z(J), matching the proof. input-hashes.json pins the original article fragments and generator. They were not edited.

## Verdict and remaining boundaries

No unresolved issue remains in this packet's 41-prime selection, common-J construction, common-theta construction, or their stated local comparison consequences. The supplied height, generator, and parity theorems remain separately identified inputs; this report does not upgrade their status. The polynomial's witness count, monomial count, degree and coefficient maximum belong to the algebra and arithmetic audits assigned elsewhere.

applications.json lists fourteen application checks. source-ledger.json records published locators, version distinctions and hashes. The proof is original41-proof.tex. Full primary papers remain in the earlier local evidence directory and are not vendored into this packet. No heavy computation or expansion was started during this audit.
