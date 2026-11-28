# Version 22 draft (PR 178): review of the new arithmetic other than the pole step

Reviewer: Claude Fable 5.2. Date: 27 November 2026.
Object: `manuscripts/quartic_v22.tex` at PR 178 head `a735f6b13e56263a82de8b1aad57a98e2b4ffd91`, Part "Version 22", Sections V22.1 and V22.3 to V22.9 (TeX lines 86–159 and 229–1865). Section V22.2 (the pole lemma and its use of Bhargava–Burungale) is excluded; another reviewer has it.

This is a mathematical read of the TeX with my own exact recomputation. Nothing from the pull request was executed. The PDF was not compared with the TeX. Line numbers are TeX lines at this head.

## Verdict

**No blocking error or gap found in the part I reviewed.** Every exact numerical claim I could isolate recomputes. Every row block I tested binds to the equation the proof uses. The new arguments (projective contacts and the height constant, the 331 anchor, the scalar norm/trace argument, the shared-product detector, the weighted height lemma, the two numerical contradictions) are correct as far as I could follow them, but several are written so tersely that I had to reconstruct steps the text does not contain. Those are listed as SHOULD-FIX. The completeness section and all retained inputs are only partly checked; see "Not checked".

| Class | Count |
| --- | --- |
| BLOCKING | 0 |
| SHOULD-FIX | 8 |
| NOTE | 8 |

## What was recomputed (all exact unless marked)

**Contacts and height (V22.3, lines 229–314)**
- Möbius pair `z(t)`, `t(z)` are mutually inverse; determinant −156800 = −2^7·5^2·7^2.
- Images of ∞, 0, 1, 2401, −343/32 are (−77, 23, 21, −75, 51)/32. With reflections: ten distinct points, diameter 77/16.
- All numerators and denominators of the 45 pairwise differences, and of the ten points themselves, have prime support in {2,3,5,7,11,13,17,19,23,37} ⊂ Γ.
- The five retained forms `s, r, r−s, r−2401s, 32r+343s` at `z(t)`, `t=m/n`, are `32m+77n`, `49(23n−32m)`, `50(21n−32m)`, `−2450(32m+75n)`, `1225(51n−32m)` up to a common factor dividing 156800. So outside S the old radical of `z(±t)` is exactly the odd part of the new forms, and `R_+R_- ≤ B_S²(19·23)²M(t) = J_*²M(t)`.
- `J_* = 811898089212210` is the product of the twelve primes of Γ; `log J_* = 34.33 < 35`.
- `c_0 = 8·(9339/1000) + 10^{-6} = 74712001/10^6`.
- `𝒞 = c_0 C_0 J_*² E(J_*)` is an integer and equals the printed 75-digit number. `log2 𝒞 = 248.99935`; `2^249/𝒞 = 1.00045`. So `2^68 < 𝒞 < 2^249` holds, by 0.045%.
- Product of `1+1/p` over primes ≤ 1000 outside the new Γ is 1.9046 < 21/10. `log(1+1/1009) < log(1009)/6006`.
- `(1+x/2)(35+x/2) ≤ (22+x/2)²`; the coarse bound follows with enormous slack.
- `P(r)` expands to the printed coefficients. Eliminating `s, v` from the two contact rows gives `(1+w)P(r) = w r^5`; `w = 1/q` with `q = r^5/P(r) − 1` satisfies it.

**Where `c_0` comes from (question (a))**
- It is derived, not only cited: retained Section `q214:height-supplier`, paragraph H4 (lines 20111–20135), unchanged from Version 21. It sets `k = 9339/1000`, `δ = 10^{-6}`, `c_0 = 8k+δ`.
- I rechecked the two inequalities that fix `k` and `δ`: `4 + K_0/log B_S = 9.33815 < 9.339` (margin 8.5·10^{-4}, floating point, far above rounding error) and `216 + 128/log B_S < δ C_0 B_S²`. I did not re-referee H0–H3.
- **Is the narrow margin sufficient?** Yes. The 0.045% margin of `𝒞 < 2^249` is not where the proof is tight. The contradiction at the endpoint `B = 2^810` (lines 584–591) compares `2^{21−4050/36036}·2^249 ≈ 1.940·10^6·2^249` on the left with `1000·(54 + 5·810·ln2/6)·2^249 ≈ 5.219·10^5·2^249` on the right: a factor 3.72, about 1.9 bits. The text's rational bounds are valid and strict in the right direction: `2^{−x} ≥ 1 − x ln 2` with `ln 2 < 7/10` gives the left side > `2^21(1−2835/36036) = 1.932·10^6`; the right side is < 526500 with `ln 2 < 0.6932`. The prefactor is 845.3 < 1000 and `log J_* + log(14)/6 = 34.77 < 54`. The exponential-over-linear quotient is increasing for `s ≥ 0`. No floating point is needed for any of these.

**Anchor (question (b))**
- `K = 56·331·C² = 18536 C²`, `v_331(K) = 43`.
- For all 331 residues `x`, with `s = 2^20 x²`: `r_s`, `25920000 r_s + 1081567619`, and each of the three linear forms are nonzero mod 331. For `v_331(X) < 0` the leading coefficient 2400·375 ≡ 11 (mod 331) is a unit. Hence `v_331(R) = 43` for every rational `X`, and 331 does not divide the scalar radical.
- 331 ≡ 3 (mod 8): inert in Q(√2), as the text's "same slot twice" remark needs.
- `9·43/4 = 96.75`, so the exponent is 97; `331^97 = 2^811.96 > 2^810`.
- `1081567619 = 11·47·1019·2053`, `25920000 = 2^9·3^4·5^4`, `2400·343 − 2401·375 = −77175 = −3²·5²·7³`.
- Identity `2·25920000 r_s = W_s³ − 3161163 W_s − 2163135238`. Rows 14 and 15 are exactly `W_sT_s = 1` and the linearized row, with all four products by 18536 correct; on six inputs including `X = 0, 331, 1/331` they hold with `R = K r_s/(r_s − e_s)`, `K/2 < R < K`, `v_331(R) = 43`.
- `P_s = 98324329 < 2^27`; `(1+log P_s)² = 376.5 < 2^9`; `c_0C_0B_S²E(B_S) log B_S = 2^236.14 < 2^237`; `log K = 253.5 < 400`; the β and R height constants (22.4 < 30, < 50) hold.

**Contact polynomial and certificate (question (c))**
- `certificate.json` of the final stage gives radii 77, 23, 21, 75, 51, the same ascending coefficients, the same twelve exceptional primes, the same `J`, `N = 21`, anchor exponent 97. The manuscript agrees with all of them.
- "Contact count": ten distinct contacts per detector; a contact root is impossible because it forces `w = 0` against the inverse row; the midpoint `r = 0` forces `w = −1` and is kept.

**Exceptional primes and J (question (d))**
- Γ = S ∪ {19, 23}. Its role is exact: `J_*²` bounds the Γ-part of the two retained radicals and `E(J_*)²` their Euler factors. 41 and 2399 are in S because of the retained modular input, not because of the new contact geometry.

**Reference norms (the PR 175 note N3)**
- I computed them on the actual curve: `Nm x(P_0) = 41²/2^6`, and for `P_0 + T`: `2^6·7²/41²`, `3^4·7³/17²`, `17²/(3^4·7)`; `Nm(±d_0) = 7`. The manuscript's list (line 381) is the correct one, identical to Version 21's. The list in the contribution's intermediate notes was wrong; no table depends on it and both lists are 331-units.
- `Nm z(P_0) = 328/1071 = 2³·41/(3²·7·17)`, as line 512 states.

**Comparison and weighted height (V22.5, lines 430–604)**
- Finite chart: on 168 random pairs of points of `E(Q(√2))` the four equations hold and `x(U−V) = h(h+s+t)`. The identities `Fs²+D_0F² = 1`, `Gt²+D_0G² = 1` are polynomial consequences of the residuals. I checked the tangent case `F = G` and the stratum `d = 0` by hand.
- `ℋ = s_4²𝒢` with `L_2 = A`, `L_3 = 2S_H/s_3`, `L_4 = 4S_H/s_4 + 1` (by hand).
- Factor valuation classes: in each of `F_0..F_3` the four non-constant terms lie in the classes `−μ, −2μ, −3μ (mod 4)` and `4 (mod 8)`; so each factor has a unique minimum. `−11μ+4v > −μ/4` gives `v(E_2^*) > 43μ/16`.
- `g_j`, the three inequalities `v(D) > −μ/4`, `v(c−q_j) > −3μ/4`, `v(c) = −μ`, and the 409 remark.
- `v(a(A−a)) ≥ 3` from `v(aC_2) ≥ 3` and the two order-four relations (by hand), and then `p³ | aΔ` in both cases.
- `Z_w` identity: `S_1 = 4t_1 − 2t_0 − 2t_2 + 8`, constant term `−16+5ρ+Rd_0 = −13+4ρ+(R−1)d_0`. Row sums 25.8 and 34.8 < 64.
- Lemma `v22:weighted`: `1·8·27·4 = 864`; `24 log M − M²/8 ≤ 42.77 < 43`; `6+43+log 864+½log 7 = 56.73 < 57`; `(2M+1)² ≤ 5M²+5`; `40 log 64 + 2285 < 2500`.
- `|aΔ| ≤ 14B^5` is consistent with the definition of Δ.
- `J_X` branch: I re-derived `log B < (23/22) log(960·529·2^304) + (12/11)h(β)` from the coarse bound; the first term is 234.03 < 240.
- `v² | 102 ⇒ v = 1`.

**Completeness numerics (V22.6, lines 606–701)**
- Dyadic: `r_s ≡ 7^7`, `2^9(r_s−e_s) ≡ 3 (mod 8)`, quotient unit 5, `K` odd part ≡ 5, so `R` has depth 12 and unit ≡ 1; `9792 = 64·153`, `153 ≡ 1 (mod 8)`.
- `v_p(τ) = 2t_p − 5v_p(R) − v_p(2)`; the real bound `(R+9792)(R+9)^4/(4R^9)`; its value 24482500 at `R = 1`.
- `κ = 15125/1024`; `(204/409)²` lies in (0,1), has 2-adic depth 4 and is a 2-adic square, 3-adic depth 2, 7-adic unit.
- The "W is one or has a pole" dichotomy at the other slot follows from the valuation classes.

**Table and binding (V22.7–V22.9; questions (e) and 4)**
- Parsing the printed TeX rows with my own parser: 147 rows, exactly `x_1..x_175`, all rows of degree ≤ 2; the sum of squares has 3,196 monomials, degree 4, content 1, `x_1^4` coefficient 1, largest coefficient 802 bits, and renders to 73,080 bytes with SHA-256 `efc0be23…4292`. The printed table therefore is the polynomial I verified for PR 175.
- Rows checked against the stated interpretation, far more than fifteen:
  - algebraically by hand: 1–15, 16–21, 28–35, 44–60, 61–88, 89–102, 108, 114–147;
  - by exact evaluation on real data: the six reference rows 22–27 on `H = [k]R_0` for seven `k` (with a negative control that fails), the chart rows 28–51 on actual point pairs with the stated scalings, the contact rows of all three detectors, the gate and pole-input rows 99–114 including the expanded rows 107 and 113, the scalar rows.
- The scalar chart (lines 391–398), divided by `Z`, is exactly the retained inverse-Vieta chart with `R_2 = 1`; hence `x(Q_2) = P^*/R` and the aggregate rows 52 and 94 carry the weight `R` on `Q_2` as Lemma `v22:weighted` assumes.
- All 175 variables have a role. I found no table variable used with two meanings.
- **Question (e).** The manuscript does not prove that each intermediate system (179 → 178 → 177 → 175 …) is equivalent to its parent, and does not need to: it proves soundness and completeness of the final 147 rows directly. For each block the contribution changed (the two aggregate rows, the scalar pair of rows, the nine contact rows, the unit rows 145–146, the aligned gate) I checked that the printed rows are the equations the direct proof uses. The lineage is then provenance only.

## Findings

### SHOULD-FIX

1. **Lines 503–505: the citation does not contain what is cited.** "The other comparison and Lucas tests gain their denominators' two orders, and the input test gains one order, as in Subsection `v21:local-extraction`." That subsection treats a different detector: five factors `Φ_k` in powers of `q_j`, with quotient tests `C_i, G, I`. The Version 22 detector is the shared product in `c = Σq_j` with cleared tests, and it appears in no retained part. The needed facts are true (I derived them): `E_i = s_i·conj(t_i)·C_i`, `𝒩 = s_1·I`, `ℋ = s_4²𝒢`, whence `v(C_1), v(C_3), v(C_4), v(𝒢) ≥ 4` and `v(I) ≥ 3`. Write these three identities and the resulting orders, then cite the retained label-recovery paragraph for what follows.

2. **Lines 509–516: the opposite-slot step is not justified in the text.** "At the opposite slot `z(H)` is a unit: the norm of `z(P_0)` is 328/1071." The missing reason is that `B_0 = conj(1/x(H−P_0))` has positive depth, so `H ≡ P_0` at the opposite place. Say so. At an inert prime the two places coincide and the hypotheses are contradictory; say that the case is vacuous.

3. **Lines 676–680: completeness depths for four of the six tests are not stated.** Only `E_2^*` and `E_3` are given. `W ≡ 1` also needs `v(c^5𝒩^4), v(c^7E_1^4), v(c^7ℋ^4), v(c^5E_4^4) > 0`, that is `v(𝒩), v(E_1), v(ℋ), v(E_4) ≥ 2` at depth 1. "By the same retained estimates" points at estimates for the Version 21 quotient tests. My own bookkeeping gives `v(𝒩) ≥ 3d`, `v(E_i) ≥ 2d`, `v(ℋ) ≥ 2d`, and `v(E_2^*) = 4d + v(a) − v(h−1)`, which is `≥ 3d` when the opposite reference depth is raised minimally. State these, with the condition on `v(h−1)`.

4. **Theorem `v22:175-fixed`, lines 1831–1841: the proof is a pointer.** The soundness chain is spread over four sections and about fifteen retained results. Assemble it as an ordered list with labels: reference rows give finite `H`, `f ≠ 0`; scalar rows give `R`; the 331 anchor excludes the five strata; scalar chart gives `Z`, `Q_2`, `a`; the three charts; detector extraction; the two divisibilities; weighted height; `Δ = 0`; `J_X = 0`; `X ∈ Z`. I could reconstruct this order, but a reader should not have to.

5. **Notation is overloaded to the point of obstructing verification.** Within Part V22: `R` is the scalar value, the retained radical `B_SM_S(z)` (line 264) and part of `R_0`; `W` is the scalar-chart coordinate (line 390) and the factor product (line 476), besides `W_s`; `M` is `−2S_H−W`, the contact radical `M(t)` and `max|m_i|`; `J` has three meanings besides `J_*` and `J_X`; `U, V` are pole coordinates, chart coordinates and curve points; `s` is `2^20X²`, a chart slope and `r²`; `t` is a contact argument, a chart slope and a Lucas label; `c_0` sits beside `c_0'`. None of this produced an error I could find, but each needed care to rule out. Rename at least the radical `R`, the product `W`, and the lemma's `M`.

6. **Line 252: `M(t)` is defined with "a primitive new contact form".** It must be all ten forms, the five images and their reflections; as written it can be read as five. The later claim that the two old radicals have product `M(t)` needs ten.

7. **Line 640: false remark.** "The last inequality uses the present `R > K/2`, not merely `R > 100`." `24482500/R^4 < 1` already for `R ≥ 71`. Delete the remark or correct it.

8. **The shared-product construction has no self-contained statement.** Line 91–95 attributes it to constructions "developed from Gabe Conant's constructions", but those are not in any retained part. Section V22.5 is therefore the only proof. Give it a numbered proposition with its hypotheses (consumed prime outside Γ, `v_p(q_j) = −μ` odd) and conclusion (`v22:divisibilities`), in place of running prose.

### NOTE

1. Line 437–439: the recipe for `Fs²+D_0F² = 1` is inexact. The actual combinations are `r_4 + (s−t)r_1 − F r_3` and `r_4 + (s−t)r_2 − G r_3`, each using one of the first two residuals, not both.
2. Lines 745–753: the square registers `x_65, x_67, x_73, x_75, x_81, x_83, x_171, x_173` and `x_37` are referred to collectively. A "full field map" should name them.
3. Line 588–590: "greater than `2^21(1−2835/36036) > 526500`" is true but understates the left side by a factor 3.7; saying so would show the reader the real margin.
4. Line 148–149: the duplication constant `log 77` is correct (`½ log(14.06·419.6) = log 76.81`) and sharper than the retained `log 676`; the retained `m²/4 − 3` bound does not depend on which is used.
5. Line 141–143: `ε^4(75−53ρ) = 3−ρ` checked.
6. Lines 150–158 correct a point about the retained 229 table inside the Version 22 overview. It belongs with the retained part or the corrections record; `c_0'` next to `c_0` invites confusion.
7. Stale Version 21 figures (question 5): none in Part V22 or the front matter. The abstract now gives only the 175-variable quartic and no longer mentions the 195-variable Busy Beaver one, which the body still proves. The retained part keeps its historical title "The new explicit quartic"; harmless under its part heading.
8. Differences from the released Version 21 source outside the new part are only: title, date, abstract, "José" → "Jose" (twelve places), and `1--16` → `1\text{--}16` in two exponent tables. No retained mathematics was edited.

## Not checked

- Section V22.2 and anything depending on the Bhargava–Burungale preprint.
- The PDF. No source/PDF comparison was made, and the "PDF pp. 12–31" mapping was not confirmed.
- Retained inputs, taken as stated: the H4.1 height theorem beyond the two inequalities above; the Gaussian simultaneous-prime supplier and its form `u + c w²`, on which the "no zero contact" argument (lines 656–666) depends, including the claim that the selected primes exceed `w²`; the reference-recovery lemma in the soundness direction (that rows 22–27 force a finite `H` with `f ≠ 0`); the order-four logarithm precision; the label-recovery congruences; the residual bound proof; the Lucas descent `log B ≥ (|a|−6) log(|a|−3)`; the real-return and finite-index recurrence used for `1 ≤ |Z^{(i)}| ≤ 3`.
- Completeness as a whole was followed in outline only. I checked each numerical statement and the local parity logic, not the simultaneous satisfiability of all congruence and real conditions.
- The 45 remaining rows that I did not interpret individually are covered only by the finite expansion check.

## Scripts

`C:\Users\glaze\Documents\fable-v22-review-scripts\` (`num1.py`, `num2.py`, `num2lib.py`, `rows.py`, `rowsem.py`). They read a copy of the TeX table extracted to the session scratchpad; the path at the top of `rows.py` and the `sys.path` lines need adjusting to rerun them elsewhere.
