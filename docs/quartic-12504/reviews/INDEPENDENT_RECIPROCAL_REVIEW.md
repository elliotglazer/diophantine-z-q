# Independent review of the reciprocal logarithm proposal

Reviewed 2026-11-05 by the independent guards/review agent. This review is
based on reading the proof, producer, isolated checker, source wrapper,
arithmetic probe, original degree-eight builder and the corresponding
manuscript arguments. No source generation, probe execution, lift, or full
expansion was run for this review. Only file inspection and small file hashes
were used. No shared source or manuscript was edited.

**Conclusion:** I found no mathematical gap or counterexample in the proposed
reciprocal logarithm, its all-prime error estimate, the global nonvanishing
argument, the 64/24 and 64/16/24 arithmetic proofs, or the optional compressed
chart maps. The mathematics supports proceeding to implementation validation.
The present isolated circuit checker is not a certificate of a complete new
source or final quartic. Those remain separate, concrete integration checks.
This conclusion adds no user-approval requirement.

## Exact material reviewed

The reviewed original is
`work/quartic-variable-search-20261105/remote-repo/degree8-original`.
Its builder SHA256 is
`c7ef798894a106e3c6b02816583be2b6e966e4e701f73ee670c9a0de52a70912`.
Its stored `modules/q_compare4.json` SHA256 is
`639574951f42451345b3286a57ca922273567f20a548ee2426939c7a30a07212`;
this agrees with the manifest and the new wrapper's expected digest.
The unchanged old source identity remains
`6e68a9d39573279e894e29d8913b5ade932aa6526d28a2d40bc713c1cca934a2`.

Files in this directory at review time:

| File | SHA256 |
| --- | --- |
| `RECIPROCAL_PROOF.md` | `be5b08dd9ded743606d5c6a5fc869c4e9764575da49e5d80af13aca09950a98a` |
| `reciprocal_kernel.py` | `c4e94463cd59a2418a6502ac7cdcfd713edf9bc1134fe0b4d4bd84700983b304` |
| `build_reciprocal_source.py` | `d9ec8f4788882f37f3a0b7746f8d19c28968f7bf3f09cc06addab92f787098f6` |
| `probe_reciprocal.py` | `0dfe911dbd0f98865116ccd184b709a2b218b707ac8c735b233c00a182f9ee7f` |
| `check_reciprocal_probe.py` | `314f2a240c6c168d3c149fe678e533aadc10d8861bc04b4f0ee47ef1fb3ff860` |
| `check_arithmetic_contract.py` | `cec49a617827310641716632b43bd04b315d6be2543a0883bfec02291914c0d1` |

The manuscript comparison used
`work/private-degree8-20261105/repository/diophantine_zq.tex`, particularly
`hyp:o8-height`, `eq:o8-indexheight`, `eq:o8-anchor-bound`,
`eq:o8-contacts`, `eq:o8-proxies`, `subsec:o8-common-J-proof`,
`subsec:o8-root-proof`, `eq:o8-scalarheight`, `lem:o8-lucas`, and the proof
of `thm:o8-conditional`. `MANUSCRIPT_CHANGES.md` correctly lists the coupled
changes needed if a new source is integrated. This review does not assert
that those manuscript changes have already been made.

## Differential identity and entire infinite tail

I independently checked the sign and factor in the invariant differential.
For `f=1/x`, `z=-x/y`, and `w=D f^2`, the curve equation gives
`f=z^2(1-w)` and

    dx/(2y) = z df/(2f),
    df/dz = 2z(1-w)^2/(1+w),
    dx/(2y) = (1-w)/(1+w) dz,
    z dw/dz = 4w(1-w)/(1+w).

Thus the proposed ODE gives the normalized formal logarithm with zero
constant term. The formal branch is essential; it selects the square root
with constant term one. The convolution formula for `a_j` is consistent with
this ODE and provides an independent coefficient construction. The statement
does not assert equality of the old and new finite polynomials in independent
`z,f`, and such an assertion would be false.

At every selected prime `p>76176`, `D` is a unit because its norm is 49.
The retained formal test has positive valuation on `f`. Together with the
curve identity it puts the point on the infinity branch and gives
`v_p(f)=2r`, `v_p(w)=4r`, where `r=v_p(z)>=1`.
The proof handles the whole infinite tail, including coefficients whose
denominators contain `p`: the denominator of `a_j` divides `(4j+1)!`, and
`v_p((4j+1)!) <= (4j+1)/(p-1)`. When `4j+1<p` integrality suffices. Otherwise
`j>=19044`, `3j>=4m` for all proposed `m<=16`, and
`(4j+1)/(p-1)<=j`. Hence

    v_p(a_j w^j) >= 4jr-j >= 4mr  (j>=m).

The lower bound tends to infinity, so convergence has also been checked.
Formal-logarithm isometry gives a unit after division by `z`, proving relative
precision `4m`, and therefore precision `e` when `m=ceil(e/4)`. In particular,
the 64, 16, 52 and 13 cases have the claimed error orders. This uses the same
formal-group homomorphism/isometry input as the original manuscript; it
introduces no new external arithmetic theorem.

## Global nonvanishing and zero cases

The valuation

    v(a+b sqrt(2)) = (1/2)nu_2(a^2-2b^2)
                   = min(nu_2(a),nu_2(b)+1/2)

is justified by the distinct parity of the two norm-term valuations. Norm
multiplicativity gives multiplicativity of `v`, and the displayed minimum
gives the triangle inequality. Zero coefficients are interpreted using
infinite valuation. This is a valuation of the specified field
`Q(sqrt(2))`, not of an arbitrary coefficient algebra. `v(D)=0`, and
`v(a_j)=1` for all `j>=1`, since every recurrence factor is odd over odd.

For `G_J(Df^2)`, `f=0` gives 1. For `v(f)>=0`, the constant is the unique
least-valuation term. For `v(f)<0`, the half-integral value is at most `-1/2`,
and the final term has unique least valuation `1+2Jv(f)<=1-J<0` for `J>=2`.
All proposed values have `J>=3`. The nonvanishing proof is therefore global,
including off-curve assignments, and needs no good reduction at 2.

It follows that `L_e=zG_J` vanishes exactly when `z` vanishes. The old chart's
`xf=1` and `yz=-x`, or the reduced chart's `pz=-1`, excludes this zero case.
The old single-input `log_inverse` checker does not certify the new polynomial;
its theorem/schema must be replaced with one binding the actual two-coordinate
`f` output identity and the retained source conditions.

## Downstream arithmetic and precision positions

The kernel matches the original four-proxy input layout. There are still
eleven formal field tests, four primary ratios and five alternate ratios.
For label precision `q` and high precision `K`, the order lists are exactly

    field:    [1]*11 + [q] + [K]*3 + [K,q,K,K,K],
    rational: [1]*23 + [q]*2 + [K]*8 + [q]*2 + [K]*6.

The root-error test accounts for the extra rational order-one entry. At
`q=16`, only the beta primary and its alternate test are weakened. The shared
denominator and shared-H alternate test remain at 64. The scalar batch stays
`[1,1,1,1,48,48]`.

In soundness the alternate ratios imply `h=4 mod p^K` and
`m_i=4n_i mod p^(e_i)`: multiplying by the nonzero integer `j` cannot lose
valuation. Thus `h` is a unit. The formal-logarithm ratio is `m_i/h`, an
integral element. Its new finite approximation differs by a relative unit
congruent to one to order `e_i`; the denominator has order `K>=e_i`.
The resulting proxy congruences are the required ones.

The completeness construction can keep the exact original
`64+v_p(j)` CRT modulus and avoid `h_p=0,4,-4`. Neither new denominator
zeros nor a new compatibility condition arise. The common root approximation
can still be chosen last. The contact prime pattern, local-square conditions
at 2, 3 and 17, and scalar/pole arguments are unchanged. No new integrality
condition at these small primes is imposed on private primary points.

The first height contradiction uses the three high Lucas proxies at every
contact, including contacts that bound the abscissa of `A=nP_*`; it does not
use high beta precision. The original 24-squaring anchor gives
`a>(20H)^2` using the displayed exact integer comparison. Hence
`B^2-6<14H B^(3/2)` contradicts `B>=a` when the Lucas defect is nonzero.

For beta precision 16, the second contradiction is also valid:
`B^2<7H N^(3/2)+6` and `N<=2 exp(h(beta))B` imply
`B^(1/2)<32H exp(3h(beta)/2)`. The inherited scalar bound and same anchor
give `h(beta)<a/20` and `log(32H)<a/20`, hence `log B<a/4<a-3`.
The uniform 64 case retains the original stronger estimate.

I also checked the optional 52/13/26 comparison: the first exponent is
`2-96/K`, its anchor comparison uses `K/(2K-96)=13/2`, and the second
estimate is at most `37a/40<a-3` for `a>40`. These observations are not
claims that a 52-source is preferable or that smaller precisions admit
counterexamples. At the stated thresholds the supplied growth proof stops
giving the needed upper bounds.

## Optional primary chart compression

The proposed four chart equations and `y=xp` are the previously derived
reduced chart with its inverse equation omitted. That omission is sound
only when coupled to the new ratio equations. The surrounding equations
give `Lambda p_0=G_0!=0`; for each numerator, `A_i=C_i p_i` and
`A_i Lambda=G_i!=0` force `p_i!=0`. The maps are then

    z_i=-1/p_i, L_i=z_i G_i, Lambda=-L_0,
    C_i=L_i/L_0=G_i/(p_i Lambda).

The sign is correct. From `xf=1` and `p^2=x-Df` one gets
`f p^2=(1-df)(1+df)=v^2(1+df)`, so `v!=0`. The old chart is reconstructed by
`h=up` and `w=up/v`. These formulas also exclude the torsion cases admitted
by the four chart equations alone. Their validity uses the field and
nonvanishing arguments already specified; it does not need the rank theorem.

The original builder's primary `z` coordinates are consumed by their chart
equations and primary logarithms. The subtraction code uses primary `x,y`,
the formal tests use `f`, and alternate ratios use the difference points'
own `z`. The kernel preserves those difference and common-auxiliary
parameters. This source reading supports the intended scope, but actual
candidate incidence and every substituted/fused output row must still be
checked after flattening. Partial compression must not delete a coordinate
with an unhandled outside use.

## Producer and checker findings

The recurrence, the four-term circuit, and the long normalized circuit in
`emit_g` implement the displayed polynomials. Expanding its two block levels
symbolically assigns exactly powers 0 through 15 (or through 12 with trailing
zeros); the scales cancel. The final expression is quadratic in existing
targets and restores the factor `a_6`. The compressed kernel places this
expression in the required ratio row, rather than dropping an output
constraint. Its point order and numerator precision selection are correct.

The updated source wrapper now rejects a wrong original builder digest and
regenerates the complete old comparison module before installing changes.
Its canonical capture includes rows, calls and construction log. The original
`main` resets the intended chart/unit settings but does not overwrite the
installed precision or anchor values. Source generation still needs an
independent comparison of the actual generated modules and flattened rows;
the wrapper is a producer, not that independent checker.

The isolated checker derives coefficients independently, checks every
acyclic quadratic definition, and substitutes through the complete two-input
output polynomials. Its eight mutations exercise relevant individual-circuit
failures. The arithmetic probe is correctly described as finite identities
and sample maps, not a proof over all primes or assignments.

One actual coverage gap was reported to root and the author: the isolated
checker's `main` trusts `index.json`, does not require the intended 18-case
set, and does not check the index's SHA256 fields. An empty or incomplete
index therefore completes successfully with an empty or incomplete report.
This does not invalidate validation of any listed circuit. A claim of complete
probe coverage must separately require the exact case set and bind the input
files, or add those checks. The 13 case is not separately emitted; it shares
the four coefficients/circuit with 16, as the kernel's ceiling rule requires.

The checker deliberately reports `isolated_below_2_80` instead of rejecting a
false value. Callers must inspect it. For direct output, the isolated squares
omit the eventual equation containing that output expression, so even a true
flag is not the coefficient bound for a compressed source. The `bound_output`
and `hscale` labels are also metadata, not separately verified structural
claims. None of these limits justifies skipping the complete final expansion.

## Remaining integration conditions

Before reporting a new source or quartic as verified, bind its exact compiler
parameters and source files; independently compare every generated module,
test order and flattened coordinate map; check the compressed rows and all
removed-coordinate incidences; implement the new nonvanishing/source rule
with malformed-source tests; and run a fresh lift, certificate replay and
complete squared-row expansion. Confirm unchanged root arithmetic, contacts,
scalar order, double operations, and (for the 64 variants) anchor length.
Measure the final active variables and strict coefficient bound on that
candidate. Existing wave11 receipts and nominal savings do not certify it.

This review retains the original arithmetic inputs, including the height,
rank/generator, prime-pattern and pole results. It checks their proposed uses
and the new elementary arguments; it does not claim that a finite circuit
checker proves those inherited arithmetic theorems.
