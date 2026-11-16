# Review of the Version 2 manuscript patch

Reviewed on 2026-11-05 by the independent guards/arithmetic reviewer.

Verdict: PASS for the mathematical fidelity of the frozen patch below to the exact reciprocal64-beta16-compressed-s1 source and its 12,504-variable quartic. The revised text contains the changed arithmetic arguments and explicit compressed-chart maps. I found no unresolved mathematical defect in these snippets. This is a source-level manuscript review, not a TeX build, visual PDF review, fresh polynomial expansion, or new proof of all inherited arithmetic inputs.

## Frozen files

All paths in this table are relative to `work/quartic-12504-release/manuscript-patch/`.

| File | SHA256 |
| --- | --- |
| `OPENING.tex` | `8561046b4f1fcad3bd01e02a97ed6b26c46f93e22666b8921e9636ecf18032a9` |
| `ARITHMETIC.tex` | `1df7901899afa78a8989a4c1b8edbffff09f9bf5cc2886232c7e391e596da1f6` |
| `REDUCTIONS_PREFIX.tex` | `ae2eab2d4c9056cb3303fb2557969e430620b050fb04ecac26312b851b5b0aa2` |
| `REUSED_REDUCTIONS.tex` | `136b24e51d87e50e21c180bdb8494bfa438aa5fdff34b098c53b58e2306a9fa2` |
| `FINAL_VERIFICATION.tex` | `ac7ce457cdfbfded17c2271893ca9fa7b9009e348b6b3165c6f74cbb784b0d83` |
| `apply_patch.py` | `c1ad0a342125f065812f8b286924b9f123a93546125de00ac24a12a31419d9a0` |

The patch author confirmed that these mathematical snippets are frozen. I reread the final `ARITHMETIC.tex` after the corrections below and checked its hash. The input manuscript expected by the assembly script has SHA256 `954d87fe851777672dc46233998e3905a19c3ef463749fc04d6743afeceb4fab`.

The underlying arithmetic review is `work/quartic-12504-release/arithmetic-review/REVIEW.md`, SHA256 `e56b311d5718c8c18f3fc4886c1edc71f340d434bf205cd9c0849cb101fc134e`. I compared the manuscript's actual statements and deductions with that review and the archived source; I did not infer manuscript correctness from its prior PASS verdict.

## Issues found and corrected before freezing

The initial tail lemma stated its local condition using only positive valuation of `z`. That is insufficient as a standalone hypothesis: small `z=-x/y` also occurs near the nonidentity two-torsion branch, where `f=1/x` has negative valuation. The final lemma explicitly requires a nonidentity point in the formal group at the stated place. Its scope is any split prime above 76176, not only ordinary primes produced by the completeness construction.

The initial soundness proof began at a selected ordinary prime. An arbitrary rational solution does not supply the ordinary-prime conditions used in completeness. The final proof instead begins at any prime above 76176 with odd raw-contact valuation. It states the norm/pole deduction excluding negative odd valuation and extracting each assigned order, selects the split place by the root error and Hensel lifting, and transfers each pair of rational tests to the corresponding field test. It then derives the alternate congruences using a nonzero integer auxiliary index. The ordinary-prime assumptions now occur in completeness, where they are available.

The final text also defines `G_J` for every nonnegative `J`, names the inherited Silverman formal-group interface at the new use, and gives the completeness assignments for `j`, `J`, and every private primary point. These changes close the statement and exposition gaps identified during this review.

## Changed arithmetic is actually supplied

`lem:quartic-reciprocal-log` defines the exact recurrence `a_0=1`, `a_1=-2/5`, `a_j=(4j-5)a_(j-1)/(4j+1)`. I checked the coefficient equation, the curve identity `f=z^2(1-Df^2)`, and the derivative `z dw/dz=4w(1-w)/(1+w)`. They give the normalized invariant differential and the formal identity `log_E(z)=zG(Df^2)` with the correct sign and constant term.

The proof bounds the whole infinite tail. Its factorial denominator bound remains valid when the coefficient denominator contains the selected prime. In the large-index case, `j>=19044`, `3j>=4m`, and `(4j+1)/(p-1)<=j` give `v_p(a_j w^j)>=4jr-j>=4mr`; that lower bound also tends to infinity. In the smaller-index case coefficient integrality gives the same needed order. Multiplication by `z` gives the displayed absolute error `(4m+1)r`, and logarithm isometry gives the relative order. Four terms are used at precision 16 and sixteen at precision 64. The final statement now matches every premise used in this deduction.

`lem:quartic-reciprocal-nonzero` is genuinely global over `Q(sqrt(2))`. The displayed valuation has half-integral values because of the opposite parity of the two norm-term valuations. Since `v(D)=0` and every nonconstant `a_j` has valuation one, either the constant term or the final term is uniquely least. The negative case uses `v(f)<=-1/2` and `J>=2`, so the final valuation is at most `1-J<0`. The proof covers `f=0`, off-curve assignments, and both truncations. It does not assume good reduction at two.

`thm:quartic-source-arithmetic` now contains the needed bridge from arbitrary source solutions to local congruences. The root error yields a split prime and a root congruent to `theta`. Since `theta+rho` is a unit, the test `epsilon B` controls `(theta-rho)B` even when `B` is not integral. The order-one reciprocal tests put the primary points and the conjugate auxiliary/difference points in the required formal groups. The alternate valuations are those of `(h-4)/j` and `(m_i-4n_i)/j`; multiplication by an integer `j` cannot lose valuation. Hence `h` is a unit. The common denominator has precision 64 throughout, so its relative error preserves both the precision-16 beta ratio and the three precision-64 ratios.

The order lists in the final text match the actual source:

```
field:    [1]*11 + [16,64,64,64,64,16,64,64,64]
rational: [1]*23 + [16]*2 + [64]*8 + [16]*2 + [64]*6
scalar:   [1,1,1,1,48,48].
```

The common root-error test remains the initial order-one test. The shared denominator and its alternate comparison are not weakened. The source still has 41 contacts, nine rational height targets including the denominator, four proxies in every contact, 24 anchor squarings, the original curve and generator, and the original exponent-24 height constant. No exponent-19 or 37-contact argument is consumed.

Both contradiction chains are correct. The first uses only the three high-order Lucas proxy congruences, at every contact, so it controls the abscissa of `nP_*` as well. The estimate `7*5^(3/8)<14` and the index lower bound give `sqrt(B)<14H+6<=20H`, contradicting the unchanged anchor. After the Lucas growth conclusion, the reduced numerator of `beta-n` has the required sixteenth-power divisibilities. Substitution of `N<=2 exp(h(beta))B` gives `sqrt(B)<32H exp(3h(beta)/2)`. The unchanged scalar order 48 supplies `h(beta)<=H sqrt(a)<a/20`; the stated elementary logarithm inequality gives `log(32H)<a/20`. Thus `log(B)<a/4<a-3`. The anchor makes all required lower bounds on `a`, `B` and `H` available. Rational `X` with integral `X^2` is integral, as used at the end.

The completeness paragraph gives `j=lcm_p d_(p,2)`, `J=[j]P_*`, the exact three congruences for each private `h_p`, and `Q_0=[h_p]P_*`, `Q_i=[h_p n_i]P_*`. It excludes `0,4,-4`, retains one orientation for repeated primes, and chooses `theta` last. The term `v_p(j)` correctly handles factors contributed by other selected primes. There is no cross-prime coprimality assumption. The unchanged scalar choices and integer-target denominator choice precede the prime pattern. The norm/pole completion uses positivity, square reduced denominators and the local square classes at 2, 3 and 17; it does not demand new small-prime integrality of private points.

## Compressed charts and exact circuit

`lem:quartic-compressed-primary` gives both directions of the chart/ratio correspondence. From the full chart, `p=yf` is nonzero and `Lambda=-L_64(Q_0)=G_0/p_0`. In reverse, the globally nonzero `G_i` force `Lambda` and every `p_i` nonzero. The identity `f_i p_i^2=v_i^2(1+df_i)` then forces `v_i!=0`. The displayed assignments

```
z_i=-1/p_i,  y_i=x_i p_i,  h_i=u_i p_i,  w_i=u_i p_i/v_i
```

recover all original chart equations. They recover the ratios with the correct sign, `C_i=L_i/L_0`, and provide the old common inverse. The proof does not discard the `p_i=0` case without justification: it identifies exactly which retained equations exclude it.

The text distinguishes the omitted primary coordinates from the retained difference parameters, common auxiliary parameters and root-point parameters. Substitution of `y_i=x_i p_i` changes the first subtraction line to `x_i(lambda_i-p_i)-eta_i=0`; every guard and other consumer remains accounted for. The statement concerns rational existential projection, not a false identity between the old and new finite approximations.

The displayed scale-one circuit matches `reciprocal_kernel.py`. With `h=w^6`, the inner `t` supplies the terms ultimately occupying degrees 10 through 15; the separate middle block supplies degrees 6 through 9 and the low block supplies degrees 0 through 5. Restoring the outer factor `a_6` gives exactly `G_15`. All powers used in the formulas are represented by the stated bound pairs or quadratic products. The four-term beta circuit gives `G_3` with only `w,w_2` bound. The final expressions are inserted into the ratio equations, not dropped or replaced by unconstrained output coordinates. Their only normalization denominators are fixed nonzero rational constants.

## Remaining algebraic rules and finite assertions

I read `REDUCTIONS_PREFIX.tex` and `REUSED_REDUCTIONS.tex` in full. The definition elimination, product lift, invertible row operation and shear maps preserve the input projection with the stated freshness and complete-incidence conditions. The norm-inverse identity has the correct signs. The private inverse removal uses rational nonsquareness of two and the retained relation `R(F-1)=epsilon^2`. The two root-chart reductions reconstruct their denominators and private coordinates. The parity replacement treats `b=0` and the conic endpoint `u=-b` explicitly; its maps need only preserve existential projection and do not falsely claim bijectivity of private tuples. The bottom-norm identity and assignments preserve the upper norm outputs and parity argument without a square-class invariance assumption.

`OPENING.tex` and `FINAL_VERIFICATION.tex` match the saved coordinates artifact: 12,504 variables including the input, 12,503 witnesses, 11,939 residuals, 135,721 monomials, degree four, 3,239,486 uncompressed coefficient bytes and maximum coefficient 685783949153203534233601. The nine displayed operation counts sum to 1,467 and match the receipt: 205 norm inverses, 41 private inverses, 6 root charts, 2 ordinates, 42 parity blocks, 1 batch absorption, 366 linear rows, 800 definition eliminations and 4 shears. The text correctly places the compressed primary charts and reciprocal circuits in the source, rather than counting them as old logarithm replacement events.

The source, expansion, certificate and checker digests in the snippets match the exact values in the arithmetic review and saved receipts. The source's 12,064 coordinates and 11,499 residuals are distinguished from the final quartic. The coefficient-file convention and occurrence-frequency relabeling agree with the exporter. The statement that every final square weight is one agrees with the independently verified artifact. These are comparisons with the finite evidence; a clean replay remains the separate release check.

## Literature and assembly boundary

The new text explicitly invokes the inherited Silverman formal-group interface at IV.6.4 and VII.2.1-2.2 under good reduction. Its new series, valuation, circuit and chart arguments are elementary deductions supplied in the patch. It refers to the exact existing `hyp:o8-height`, `eq:o8-indexheight`, `eq:o8-anchor-bound`, scalar-height equation, Lucas lemma, common-J proof and common-root/pole proof. Those references are appropriate dependencies, not missing replacements for changed arithmetic. The restricted-converse, H5 and other inherited theorem qualifications remain those identified in the SHA-bound `REVIEW.md`; this patch does not claim finite checks prove them.

The assembly script replaces the old quartic section with the five snippets in their stated order, adds the Version 2 subtitle and updates the abstract/introduction. It also frames the preserved degree-eight construction as the base compiler. Its declared baseline digest and reverse-replacement check are appropriate safeguards. I did not run the assembly, compare its emitted full manuscript, compile TeX, inspect a PDF, or edit a shared manuscript. The final assembled-source preservation receipt, rebuilt theorem inventory, public-path existence checks and PDF review remain release tasks. Any later mathematical change to these snippets requires review of the new bytes.
