# PR175 (Jose Brox, explicit 175): finite verification of the table lineage

Reviewer: Claude Fable 5.2 (local, not the gate reviewer). Run 27 November 2026, finished about 10:40 UTC.
Head verified: `a75b93f7d68afdaed5ba1769de245b5ea35e5f19`. Package: `research/contributions/brox_explicit175_20261126/`.

## What this is and is not

This is finite verification only. I wrote my own Python (standard library, exact rationals, run with `python -I`) and ran it on the tables in the package. I did not run any program from the pull request; I read `check_all.py`, `check.py` and the five `check-*.js` files as text to learn what each stage claims. I did not read or check any arithmetic proof.

For stages 1 to 3 the precise relation between parent and child tables is written down only in the package's JavaScript checkers (the papers and READMEs describe it in prose). My scripts re-implement those stated relations and test them against the tables. So a "reproduced" verdict below means: **the committed child table is exactly what the stated relation produces from the committed parent table.** It does not mean the relation is mathematically justified. In every stage some rows are carried over from the parent and some are new rows given by formulas; the new rows are new mathematical content, and whether they are the right equations is a question for the arithmetic read.

This addresses the gate finding `45911111761-1-fable-F4-table-chain-unreproduced` in substance (the chain does reproduce), though a local run of mine is not the "eligible exact-head execution" the gate asks for.

## Verdict by stage

| # | Step | Verdict |
|---|---|---|
| 0 | Blob manifests | All 47 files under `source/` match the six blob manifests; manifests cover every file. Both certificates' parent-blob pins match the committed parent tables. |
| 1 | Version 21 195 source -> v74 physical table (162 rows) | Reproduced exactly |
| 2 | v74 -> v78 shared-product 180 -> enhanced 180 | Reproduced (rows equal up to a nonzero constant and a unit monomial) |
| 3 | enhanced 180 -> v82 physical 147 rows -> compiled 179 (151 rows) | Reproduced (same sense) |
| 4 | 179 -> BB-native 179 | Reproduced; the 12 changed rows are exactly the stated conic system |
| 5a | BB-native 179 -> weighted 178 | Reproduced exactly |
| 5b | 178 -> harmonic 177 | Reproduced exactly |
| 5c | harmonic 177 -> depressed 177 | Reproduced exactly (2 new rows proportional to the README formulas) |
| 5d | depressed 177 -> aligned-gate 175 | Reproduced (rows proportional after the stated gauge and substitutions) |
| 5e | aligned 175 -> reciprocal 175 | Reproduced exactly |
| 5f | reciprocal 175 -> projective-contact 175 (final) | Reproduced exactly |
| 6 | Finite side facts | All stated finite facts I could define hold (one is very tight; see below) |

No mismatching row was found at any stage.

## Stage detail

**1. 195 source -> v74.** `source195.json` is the same Git blob (`5d6c4a4b…`) as three files on main at `964d7dd7`: `research/version21/construction/inputs/brox229/source/quadratic195.json`, `research/brox-explicit229-v68/source/quadratic195.json` and `research/version19/.../affine_laurent195_v45/quadratic-family.json`. Of the 162 rows of the v74 physical table, 81 are rows of the 195 source carried over under a fixed dictionary sending eight unit coordinates to monomials in two units; all 81 match term for term. The other 81 rows (families `new1`, `new3`, `new4`, `new`, `cleared`, `input`, `homogeneous`) match the v74 formulas with the assignment in `laurent-certificate.json`. 94 of the 175 rows of the 195 source are not carried. So v74 is half inherited, half new.

**2. v74 -> v78 -> enhanced 180.**
- 41 scalar, input, reference and inverse-Vieta rows of v74 match both the 195 source and the v62 229 table.
- The v78 physical system has 150 rows: v74 rows kept as templates (132 before later deletions), a third detector copied from detector 0 with relabelled coordinates, and new rows: two aggregate rows, twelve contact rows for the arguments 22z-3 with z in {0, -1/2, -1, 1/2399, -32/407}, three pole-input rows, three inverse rows, the norm row, three gate rows, the partial-pair rows and four rebuilt factor rows using `assignment.json`. All 150 match the compiled 152-row table after undoing the weights in `weights.json`; the two extra rows are the literal guards c*c' = 1 and c'' = c'^2.
- One template row carried the old second unit, which the stage sets to 1. The package says this is deliberate (REPAIR section 1). It is a change of the equations, not a rechart.
- Enhanced 180: same coordinates, 6 physical rows changed (two cross terms in each of `new.det0.factor0..2` multiplied by c^4); the other 144 are unchanged.
- The three notes and the three `explicit-physical` files are byte-identical to members of Gabe Conant's `H10-quartic-constructions.zip` (the copy in Elliot's Downloads folder). The enhanced-180 files are not in that zip; they are Jose's project extension, as `ATTRIBUTION.md` says.

**3. enhanced 180 -> v82 179.** 33 rows deleted (inverse-Vieta, the old scalar pole block, parity rows, the old guards); 119 rows carried under the stated substitutions (label 112 -> R^2 scaling, two coordinates recharted in pairs); 28 new rows (`v82.point.*`, `v82.comparison.E2`, `v82.scalar.*`, and a new forced-prime row with a 374-bit constant). The formal parameter C, which occurred in 32 rows, is set to 1. All 147 rows match `source179.json`. The compiled table has 151 rows: these 147 after the gauge in `maps.json`, plus four literal guards (c, c^-2, R^2, R^-1). All match.

**4. BB-native.** 139 rows are literally identical to the v82 compiled table. 12 rows change: first conic, middle row and second conic for detectors 0, 1, 2 and for the scalar pole. Each new row is the old physical row with coefficients (3, -34, -289, 17) -> (9, 0, -9, 7), (17, -1, -17) -> (9, -7, -9), (1, 34, -867, -17) -> (9, 0, -9, -7). In physical form these are e^2 + (7b/9)p^2 = 1, UV = e(1 - 7b/9), U^2 - V^2 = (7b/9)q^2, which is the system of REPAIR section 2 with d = 7b/9. I also checked the 33 pole-related rows of the **final** table directly against the polynomials in REPAIR section 3: all 33 match, and all 12 `bbnative.*` rows of the final table are among them.

**5a. Weighted 178.** Removes the guard R*R^-1 = 1 and coordinate x91. Seven scalar-pole rows are the old rows with nine coordinates rescaled by R (a rechart; I confirmed this as a single substitution). All other rows are unchanged **except the two aggregate rows**, where the term R^-1*x_v becomes x_v (v = 114, 115) while x114 and x115 keep their meaning in six point rows. So this step changes the aggregate equations themselves. That is what the README claims (weights (1, R, 1, 1)); its justification is the weighted height estimate, which is arithmetic and unread.

**5b. Harmonic 177.** The input-square register becomes X^2 itself (old x37 = c*X^2), with the two `input.cleared` rows adjusted consistently. The old scalar block (three rows, private coordinates x77 and x78) is replaced by two new rows defining the new scalar with one private coordinate. 144 rows unchanged after renumbering. The new scalar definition is new arithmetic content.

**5c. Depressed 177.** 147 rows identical; the two scalar rows are replaced by rows proportional to 3WL + 2*1081567619*K = 0 and 1944000000*T*L + 1081567619*K*W*V = 0, with K = 18536*C^2, as in the README.

**5d. Aligned gates 175.** Using `certificate175.json` (30 coordinates regauged by powers of the unit, 24 rows divided by a unit power): the three parent gates take the displayed forms; the substitutions are 2*x72 = 2*x63 + x153 + x158 - x152 - x157 and 2*x171 = 2*x63 - 2*x152 - x153 + x159 + u - x157, as in the README; after substitution all 145 other non-guard parent rows are proportional to their children, both deleted gates become the retained gate, and the two guards are carried literally.

**5e. Reciprocal 175.** 145 rows identical; x76 occurs in no other row; the two scalar rows become W*T = 1 and (W - 3161163*T)(R - K) + 2163135238*K*T^2 = 0. The polynomial identity 2*25920000*r(s) = W^3 - 3161163*W - 2163135238 with W = 36000*s + 34981 holds.

**5f. Projective contacts (final).** 138 rows identical; nine rows (square, combination, relation for each detector) equal the README formulas built from P(r) = prod(r - r_i^2), r_i = 77, 23, 21, 75, 51. The final table is the one I verified earlier: 175 variables, 3,196 monomials, 73,080 bytes, byte-identical to `expanded175.txt`.

## Side facts (item 6)

- J = 2*3*5*7*11*13*17*19*23*37*41*2399 = 811898089212210. Correct.
- The map (973z - 77)/(1632z + 32) sends the five old contacts to (-77, 23, 21, -75, 51)/32; determinant 156800. Correct. The radii and all pairwise sums and differences factor over the twelve listed primes. The ten reflected points are distinct, diameter 77/16.
- Contact polynomial coefficients in `certificate.json`: correct. (The certificate lists the radii as absolute values over 32; signs are only in the README.)
- N = 21, anchor exponent 97 = floor(9*43/4) + 1; 331^97 > 2^810. Correct.
- For all 331 residues of X, r and 25920000*r + 1081567619 are nonzero mod 331. Correct. 1081567619 = 11*47*1019*2053.
- "Contact constant < 2^249": with the constant as defined in the README (c0*2^68*3^16*5^16*7^4*J^2*prod(1+1/p), c0 = 74712001/10^6) the inequality is true exactly, **by a margin of 0.045 percent** (log2 = 248.9994). It therefore depends on c0 being a valid bound to about four significant figures. Where c0 comes from (v68) I did not check.
- Product of (1+1/p) over primes up to 1000 outside the list is 1.905 < 2.1; the endpoint inequality 2^21*(36036-2835) > 526500*36036 holds; the displayed soundness inequality is false at s = 810 log 2 (about 269.9 bits against 268.0), a margin of under two bits.

## Observations for whoever decides

1. **Not every step is a change of coordinates.** Steps 4 (new poles), 5a (aggregate rows), 5b (new scalar), 5f (new contacts), the unit reset in step 2 and the C = 1 specialisation in step 3 change the equations. Table lineage cannot validate those; each rests on the arithmetic in its note. The steps that are pure recharts, where the tables do settle the matter, are 5d, 5e, the gauge compilations in 2 and 3, and the pole-coordinate rescaling in 5a.
2. **Intermediate tables carry other parameters.** The harmonic table says C = 211^(2^1600); depressed, aligned and reciprocal say C = 331^26; only the final table says C = 331^21. The rows are symbolic in C and reproduce regardless. The drop from N = 26 to N = 21 is justified in the final README by the sharper contact constant, the same constant that clears 2^249 by 0.045 percent.
3. **Stages 1 to 3 are specified in code.** For those stages a reader cannot recompute the child from the prose alone; the exact formulas live in `check-v74.js`, `check-v78.js` and `check-v82-bb.js`. I did not compare those formulas with the `.tex` sources (v74, v78, v82).

## Gate note N3 (exceptional reference norms)

The list "41^2/64, 17^2/64, 63^2/64 and 7" appears in prose in three places: `scalar_point163_179_20261120_v82.tex` (after the scalar lemma, about line 186), `shared_product_audit_20261119_v78.tex` (about line 351) and `harmonic_scalar_20261125/README.md` (line 105), where it supports the statement that the forbidden reference strata are excluded because these norms are units at the relevant prime (149 originally; in the harmonic note, every prime outside S). Version 21 lists 7, 41^2/2^6, 2^6*7^2/41^2, 3^4*7^3/17^2, 17^2/(3^4*7). No finite table depends on the list: the reference rows themselves are among the 41 rows that match the Version 21 source exactly. Both lists are supported on the primes 2, 3, 7, 17, 41, all inside S, so the unit claim comes out the same with either list. Which list is the correct set of norms I did not determine; the package's should be corrected to agree with Version 21 or the difference explained.

## Not checked

- Any arithmetic: the group description, H4.1, the prime supplier, the Bhargava-Burungale application, the height estimates, every "new row" as an equation.
- Agreement of the stage 1 to 3 formulas with the papers.
- The origin of c0 and of the other imported numerical constants.
- The 161-variable family and other background material in the notes.
- Whether the package's own checkers run; I never executed them.

## Scripts

Durable copy: `C:\Users\glaze\Documents\fable-pr175-lineage-scripts\` (`lp.py` library; `stage1_v74.py`, `stage2_v78.py`, `stage3_v82bb.py`, `stage4b_poles.py`, `stage5_tail.py`, `stage5a_weighted_subst.py`, `cmp_gabe.py`). Each takes the path of the package's `source` folder as its argument. The final-table expansion check is the earlier `verify175.py`.
