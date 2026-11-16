# Original 15671-variable parity audit

The exact seven-witness predicate and scalar correction satisfy their required arithmetic contracts relative to the existing manuscript's restricted converse RC. No additional simultaneous-realization hypothesis is needed. This conclusion does not independently certify RC. It uses RC in its stated domain, twice, after deriving the necessary Selmer hypotheses.

No original polynomial, builder, coefficient, witness allocation, or guard was changed. The audit applies to the original short-polynomial source, not to the later 20371-variable adaptation.

## Source and statement ledger

All source hashes are recorded in `reference-parity-checks.json`. The following source sections were read in full, including the local and simultaneous-matrix proofs, rather than accepted from an audit summary.

| Claim | Source read | Verification and resulting dependency |
| --- | --- | --- |
| Exact seven-witness formula | `short-polynomial-synthesis.tex`, seven-witness parity subsection; `build.py`, `make_parity` | Four residuals match the stated formula. The proof fragment uses those exact residuals. |
| Six-to-seven witness transformation | Balanced source, entire smaller-parity section | Exact polynomial check gives old first curve residual = `B^2` times new first residual; old second residual = `B` times new second residual after `h=e(B-U^2)`. Valid and reversible for `b!=0`. |
| Negative odd valuations excluded | Short source and balanced proof | Reproved directly from valuations, including `p=0`, `s=0`, `e=0`, and zero right-hand factors. No global theorem. |
| Restricted completeness domain | `short-scalar-parity.tex` and focused source, complete parity section | Weak approximation with fixed multipliers 17 and 1 gives the required positive squarefree classes. The proof explicitly covers rational square denominators, not just integer or prime inputs. |
| General simultaneous square-class realization | `parity-frozen-4eaee875.tex`, all 718 lines; `z-in-q-pole-completeness-audit.txt`, all 277 lines | Full local descent and simultaneous matrix argument rechecked. It depends only on the stated class signatures, disjoint support, and mutual local squareness, not on the original particular formula `H=A(A-B^2)`. |
| Global realization of the Selmer class | Current `diophantine_zq.tex`, exact descent reduction and lemmas on corank and forward rank | Replace the frozen source's broader pointwise/unrestricted converse citation by existing RC for positive squarefree `l=11 mod12`. Both constructed parameters satisfy this domain. |
| Local square-class basis | Scalar correction section | Independently recomputed the displayed 7-by-7 matrix, all 128 subset signatures, and all 256 signed multipliers. |
| Scalar local preparation | Scalar correction section; short proof's scalar-height construction; builder's root and height batch | Choose correction first, then deep `J0`, then anchored sufficiently divisible `S`. This order has no circularity. Formal depth at all places over a rational prime controls both rational coefficients. |
| Unguarded norm root | Both batch definitions | At every prime where the raw input has odd valuation, the binary norm is anisotropic. A zero root would force the constant leaf 1 to vanish. Thus no new inverse guard is required for soundness. |
| Original small-degree encoding | `build.py`, `make_batch` | Eight bits, two product witnesses, and the existing seven-witness parity call. All added residuals have degree at most four. The algebraic proof requires no circuit modification. |

The balanced source was read at `work/comparison-freitag-20261105/documents/balanced-natural-formula-source_archive/balanced-natural-formula/balanced-natural-formula.tex`. The short and focused sources are in the pinned `work/freitag-adaptation-20261105/source-records/degree8/short-polynomial-source/` tree. The current baseline manuscript has SHA256 `cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`.

## Exact remaining global input

RC says that for every positive squarefree `l=11 mod12`, two-primary Selmer corank one implies analytic rank one for `E_l: y^2=x(x-l)(x+3l)`.

The simultaneous matrix construction produces two such parameters `n` and `n*theta`, with two-Selmer dimension three. The finite Kummer sequence and the alternating Casselsâ€“Tate pairing modulo the maximal divisible subgroup give full two-primary corank one. RC applies to each parameter. The published forward analytic-rank-one theorem, already used and sourced in the current manuscript, gives rank one and finite Sha. The dimension-three equality then forces `Sha[2]=0`, so the specified Kummer class is represented by an actual rational point.

This is the only global step in parity completeness. The frozen source's `PointwiseTwoConverse` and `UnrestrictedTwoConverse` are not imported as additional hypotheses. The necessary standard ingredients are full two-descent and Kummer exactness, the Casselsâ€“Tate pairing for elliptic curves, and the forward analytic-rank-one theorem. Their roles agree with the current manuscript's proofs; no stronger uniform or simultaneous converse is used.

Exact references in the hash-pinned current `diophantine_zq.tex` are `hyp:RC`, lines 1005â€“1016; the local descent and necessary matrix equations, lines 1033â€“1070; `lem:corank`, lines 1072â€“1084; `lem:forward-rank`, lines 1086â€“1109; and the final realization argument, lines 1111â€“1120. The source's broader local matrix derivation is `par:descent` in `parity-frozen-4eaee875.tex`. The independent integration reviewer checked the entire new parity fragment and accepted its completeness argument relative to these existing RC and baseline lemmas, without detecting any strengthening of their scope.

## Zero and guard ledger

| Case | Exact treatment |
| --- | --- |
| `b=0` | Solutions exist; the equations force `U=p=h=s=0`, while `t,e,q` may be arbitrary. This is permitted by the original predicate. |
| `b!=0` and `1+b*t^2=0` | Impossible from the first residual, whose right side would be `2b`. No denominator inverse is needed. |
| `e=0` under a bad odd valuation | First curve equation would make `B` a square, impossible. |
| `p=0`, including `e=1` or `e=-1/3` | Both values have local valuation zero outside 3. The second equation gives the same contradiction as in the nonzero case. |
| `h=0` under a bad odd valuation | Impossible: `v(B-U^2)=2v(b)` is finite and `e!=0`. Other accepted `h=0` cases do not invalidate the one-sided contract. |
| `s=0` | The second right side is `-3(Bh)^2`; it has even valuation and is nonzero under the bad-valuation hypothesis. |
| `q=0` or a zero second factor | Under the same hypothesis, `s^2` and `Bh` have different valuation parity, so neither second factor can vanish. |
| `W=0` in an arbitrary rational solution | Impossible whenever a relevant odd valuation of `r` exists, by recursive anisotropy and the constant leaf. No additional guard is needed. |
| `W=0` in completeness | Excluded because `W` is a unit at every prime dividing `mu*r`; in the actual integral-input application `abs(r)>1`. |
| `theta=1` | The simultaneous construction allows an empty added support, and one rational point can serve both twists. |
| Negative scalar `r` | The sign bit selects `delta=sign(r)` before choosing auxiliary points. Then `delta*mu*r>0`. |
| Rational denominators in `b` | Outside the fixed primes, any odd valuation of `b` is positive by the square-denominator assumption. At the fixed primes the explicit approximation conditions handle all even valuations, positive or negative. |

## Reproduced finite checks

`check_parity.py` uses only the Python standard library. It performs the local-class enumeration and exact sparse polynomial identities. It completed in less than one second and launched no builder or full polynomial expansion.

The resulting report verifies 128 distinct local signatures, 256 distinct nonzero signed products, correction of every local signature with either prescribed real sign, the exact rescaling identities, and the seven-witness sum's 30 monomials and total degree eight. The global 15671-variable count and maximum coefficient bound are outside this component check; preservation here follows because none of its original equations changes.

`parity-justification.tex` supplies the complete additive proof for manuscript integration. There is no unresolved parity-specific step beyond the existing baseline RC and the other already stated baseline arithmetic inputs. The anchor's subgroup-of-indices property is used only for scalar witness selection and belongs to the separate anchor audit.
