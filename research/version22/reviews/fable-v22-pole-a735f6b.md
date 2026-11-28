# Version 22 draft (PR 178): review of the new pole step

Reviewer: Claude Fable 5.2, as an independent reader, 27 November 2026. This is a local review, not a gate record and not an acceptance.

- Reviewed head: `a735f6b13e56263a82de8b1aad57a98e2b4ffd91`, file `manuscripts/quartic_v22.tex` (TeX line numbers below refer to it).
- Scope: Section V22.2 "The new pole realization" (lines 160–227), the places that consume it (scalar: 360–386; comparison: 468–507; completeness: 606–701), and the pole part of Section V22.7 "Binding the pole and contact rows" (703–753). Also read: `research/version22/ARITHMETIC-AUDIT.md`, `DEPENDENCIES.md`, and `REPAIR.md` §§2–3 of the merged contribution.
- Not in scope and not reviewed: the contact transport and height constant, the weighted height lemma, the Lucas/comparison extraction, the prime supplier, and every retained (Version 21 and earlier) input. Where the pole step leans on one of these I say so.
- PDF pages: I did not open the PDF. Astra's note places this material on pp. 12–31.

**Result: no blocking gap found in the pole step.** The lemma is correct as stated, the external theorem is applied within its printed hypotheses, the printed decoding of the 33 pole rows matches the table exactly, and the exceptional-norm list is the right one. Three should-fix items and five notes follow.

## 1. What the manuscript claims the pole rows achieve

Lemma `v22:native-pole` (lines 161–170). For `d` in Q×, consider the system in rational unknowns `e, p, U, V, q`:

    e² + d p² = 1,    U V = e(1 − d),    U² − V² = d q².

- **Soundness.** If the system has a rational solution, then no prime ℓ (including 2) has `v_ℓ(d)` negative and odd.
- **Completeness.** A rational solution exists if `0 < d < 1`, the reduced denominator of `d` is a square, `d ∈ 7·Q₂ײ`, and `v₂(d) ≥ 4`.

All five unknowns are existential; none is required to be nonzero. The lemma is used four times, with `d = 7b/9` for the scalar input `b_s = R(R+9792)τ²` and the three comparison inputs `b_j = (408/409)² g_j² / [4(1+q_j)]`. Soundness consumers apply the obstruction only at primes outside `S' ⊇ S ∋ 2,3,7,17` (scalar) or outside `Γ = S ∪ {19,23}` (comparison). Completeness prepares `b` as in (`v22:prepared-b`): `0<b<1`, square denominator, `b ∈ Q₂ײ`, `v₂(b) ≥ 4`, `v₃(b) ≥ 2`, `v₇(b) ≥ 0`. The constant `C = 331²¹` plays no part in the lemma; it enters through `R` (`v₃₃₁(R) = 43`).

## 2. The external source

I retrieved and read **version 2**: `https://arxiv.org/html/2611.16130v2` and the abstract page `https://arxiv.org/abs/2611.16130v2`, both on 27 November 2026. The abstract page identifies the text as "this version, v2", revised 19 November 2026; v1 is dated 12 November. Authors: Manjul Bhargava and Ashay Burungale. The listing shows v1 at 59 KB and v2 at 25 KB, so v2 is a substantial rewrite, eight days old. It is an unrefereed preprint.

Paraphrase of the statements used (Section 2 of v2):

- **Definition 2.1.** A rational number has a square denominator if its reduced positive denominator is a square. `E_D : y² = x³ − D²x`.
- **Lemma 2.2.** For `c` in Q×: if `(1−c)(s⁴−c²)(t⁴−c²) = z²` is solvable in Q then `c` has a square denominator; conversely it is solvable if `c` has a square denominator, `0 < c < 1`, `v₂(c) ≥ 3`, and the signed squarefree part of `c` is 7 mod 8. The text says that for the converse "we need only the rational-point assertion of the following theorem".
- **Theorem 2.3.** Hypotheses: `j, k` coprime positive squarefree integers; `j ≡ 7 (mod 8)`; `k ≡ 1 (mod 8)`; each is a square modulo every prime dividing the other. Conclusion: infinitely many positive squarefree `n ≡ 5 (mod 8)`, divisible by `j` and prime to `k`, such that `E_n` and `E_{nk}` each have analytic and algebraic rank one, finite Tate–Shafarevich group of odd order, and a rational point whose x-coordinate lies in `j·Qײ` with nonzero y-coordinate. Printed example: `j=7, k=113, n=21`, points `(28, 98)` and `(23548, 3595130)`.

The proof of Theorem 2.3 in the source uses a 2-descent (Monsky's matrix), a star-graph choice of auxiliary primes, Rédei's formula, and the Tian–Yuan–Zhang genus-point criterion in the form recorded by Smith. **I did not verify that proof, and nobody in this project has.** I checked only the printed example numerically (both points lie on their curves; abscissas are `7·2²` and `7·58²`).

Note that the manuscript does not use Lemma 2.2 or its quartic at all. It uses Theorem 2.3 directly for a different system of three equations. That is legitimate, and the manuscript proves its own system from the theorem's point conclusion.

## 3. Hypothesis-by-hypothesis comparison

Setting (lines 180–188): `d = A/D²` in lowest terms, `A, D > 0`; `j`, `k` the positive squarefree parts of `A` and `D² − A`.

| Hypothesis of Theorem 2.3 | Where established | Checked |
| --- | --- | --- |
| `j, k` positive | `0 < d < 1` gives `A > 0`, `D² − A > 0` | Yes |
| squarefree | by definition | Yes |
| coprime | `gcd(A, D² − A) = gcd(A, D²) = 1` (line 181) | Yes |
| `j ≡ 7 (mod 8)` | `v₂(d) ≥ 4` forces `D` odd, so `D²` is a 2-adic unit square and `A ∈ 7·Q₂ײ`; `v₂(A)` is even, so `j` is odd and `j ∈ 7·Q₂ײ`, hence `j ≡ 7 (mod 8)` (line 183) | Yes |
| `k ≡ 1 (mod 8)` | `D² ≡ 1`, `A ≡ 0 (mod 16)`, so `D² − A ≡ 1 (mod 8)`; its square cofactor is odd (line 184) | Yes |
| `k` a square mod each prime of `j` | for odd `ℓ ∣ j`: `ℓ ∣ A`, `ℓ ∤ D`, so `1 − d ≡ 1 (mod ℓ)` and `k` is a nonzero square mod ℓ (lines 185–187) | Yes |
| `j` a square mod each prime of `k` | for odd `ℓ ∣ k`: `A ≡ D² (mod ℓ)`, `ℓ ∤ AD`, so `j` is a nonzero square mod ℓ (lines 187–188) | Yes |

Field and conventions: both sides work over Q with the same curve family `y² = x³ − l²x`. "Abscissa squareclass `j`" in the manuscript is the theorem's "x-coordinate in `j·Qײ`"; it implies `x ≠ 0` and `x > 0`. The theorem's extra conclusions (`j ∣ n`, `(n,k)=1`, `y ≠ 0`, ranks, Sha) are not used and not needed.

Scaling (lines 197–199): with `1 − d = kη²`, `η = t/D` rational and nonzero, the map `(x, y) ↦ (η²x, η³y)` sends `E_{nk}` to `E_{n(1−d)}` and preserves the squareclass of `x`. Checked by hand and numerically.

Witness formulas (lines 200–209): with points `(d a₁², y₁)` on `E_n` and `(d a₂², y₂)` on `E_{n(1−d)}`, `a₁a₂ ≠ 0`,

    e = n/(d a₁²),  p = y₁/(d² a₁³),  U = a₂/a₁,  V = e(1−d)/U,  q = y₂/(d² a₁³ U²).

I verified the three identities by hand and on 200 random exact instances. Worked example from the source's own data: `d = 112/225` (`j = 7`, `k = 113`, `η = 1/15`, `n = 21`) gives `(e, p, U, V, q) = (3/4, 15/16, 29/15, 113/580, 1265/464)`, which satisfies all three equations exactly. Every division is by `d`, `a₁`, or `U`, all nonzero.

From `b` to `d = 7b/9` (lines 216–227): with `b = N/M²` reduced, `v₃(b) ≥ 2` and `v₇(b) ≥ 0` give `9 ∣ N`, `3 ∤ M`, `7 ∤ M`, so the reduced denominator of `d` is `M²`. `9` is a 2-adic unit square, so `d ∈ 7·Q₂ײ` with the same 2-depth. `0 < d < 7/9`. All four hypotheses of the lemma hold. Checked.

Degenerate cases:
- `p = 0` in soundness: handled (line 174).
- `q = 0` or `dq² = 0`: handled (line 177).
- `d = 0` (a zero input): outside the lemma's stated domain; see N1.
- `k = 1`: see S2.
- midpoint contact (`1 + q_j = 0`): the pole-input row becomes `G_j² = 0` with `B_j` free; no prime is consumed there (lines 733–735). Consistent with the table.

## 4. The manuscript's own arithmetic in this part

Soundness proof (lines 172–178), re-derived: if `v_ℓ(d)` is negative and odd then `e ≠ 0` (else `dp² = 1` gives even valuation), `v(e²)` is even and `v(dp²)` is odd or infinite, their sum has valuation 0, so `e` is a unit and `dp²` is integral. Then `v(1−d) = v(d)`, so `v(UV) = v(d)` is odd; `U, V` are nonzero with different valuations; `v(U² − V²)` is finite and even, while `dq²` is zero or has odd valuation. Contradiction. Valid at every prime including 2, since only the ultrametric inequality is used. **Correct.** This direction does not use the external theorem.

Scalar consumer (lines 360–386):
- Row check: rows 135–136 give `R·L = Z²` with `L = Ĵ − f²`, so `J = Z²/R⁵ + f²/R⁴`; row 137 is `τ̂·Tr(L) = Nm(Ĵ)`, which with `τ = τ̂/R⁴` is `τ·Tr(Z²/R⁵) = Nm(J)`; row 138 is `στ̂ = R⁴`, so `τ = 1/σ`; row 139 gives `b_s = x₈₀/σ = R(R+9792)τ²`. All match the text.
- `v_p(τ) > −μ/2`: at `p ∉ S'` with `μ = v_p(R)` odd, `p ∤ 9792 = 2⁶·3²·17`, so `v_p(b_s) = μ + 2v_p(τ)` is odd; the obstruction for `7b_s/9` (valid since `p ≠ 3, 7`) makes it nonnegative, hence `v_p(τ) ≥ (1−μ)/2`. Correct; see S3 for a missing sentence.
- `v_p(τ) ≤ max(w₁, w₂)`: `v(Tr) ≥ min(a₁, a₂) ≥ min(w₁, w₂)` and `Tr ≠ 0` because `τ > 0`. Correct. The resulting depths `v(Z) > 9μ/4`, `v(f) > 7μ/4` follow.
- At 331: `v₃₃₁(R) = 43` verified for 83 integer `X` and by the 331 residues; 331 is inert in Q(√2), consistent with "the same slot twice".

Exceptional reference norms (lines 380–383). **Version 22 prints the Version 21 list**: `7, 41²/2⁶, 2⁶·7²/41², 3⁴·7³/17², 17²/(3⁴·7)`. I recomputed over Q(√2) with `d₀ = 3 − ρ`, `R₀ = (1+ρ, 2ρ)`, `P₀ = 2R₀`:
- `x(P₀) = 57/8 − (7/2)ρ`; `Nm(d₀) = 7`, `Nm x(P₀) = 41²/64`, `Nm(x(P₀) − d₀) = 17²/64`, `Nm(x(P₀) + d₀) = 63²/64`. These four are the list in the contribution's notes (and appear in the retained text at lines 44889–44891).
- The abscissa norms of the exceptional finite points `(±d₀,0)`, `P₀`, `P₀+(0,0)`, `P₀+(d₀,0)`, `P₀+(−d₀,0)` are `7, 7, 1681/64, 3136/1681, 27783/289, 289/567`, which are exactly the five values Version 22 prints.

So the two lists are not in conflict: the contribution listed the building blocks, Version 21 and 22 list the norms the argument actually excludes. Version 22's list is the correct one for the sentence it appears in. The argument depends only on all of them being 331-units, which holds for both lists (support `{2, 3, 7, 17, 41}`). The earlier review note is resolved. Also verified: `|Nm z(P₀)| = 328/1071` (line 512) and `(1+ρ)⁴(75−53ρ) = 3−ρ` (line 143).

Comparison consumer (lines 486–491): at `p ∣ M(t_j)`, `v_p(1+q_j) = −μ`, so `v_p(b_j) = 2v_p(g_j) + μ − 2v_p(408/409)`; the obstruction gives `v_p(g_j) > −μ/2`, with `p = 409` only strengthening it, as the text says. `p ∈ {2, 3, 17}` are in Γ. Correct. I did not review what follows from line 493 on.

Completeness of the four inputs:
- Scalar (lines 607–640): for integer `X`, `v₂(R) = 12` with odd part 1 mod 8, `(R+9792)/64 ≡ 1 (mod 8)`, numerator of `R(R+9792)` coprime to its denominator, `K/2 < R < K`, and `(R+9792)(R+9)⁴/(4R⁹) ≤ 24482500/R⁴ < 1` all verified exactly for 83 integers `X`; `24482500` is the value of `(R+9792)(R+9)⁴/4` at `R = 1`. The depressed-cubic identity `2·25920000·r_s = W_s³ − 3161163W_s − 2163135238` holds identically. The valuation formula `v_p(τ) = 2t_p − 5v_p(R) − v_p(2)` is consistent with `τ ≈ λ²/(2R⁵)`; it yields every condition in (`v22:prepared-b`) once `t_p` is large at the prepared primes. The existence of the reference and scalar index with those depths and the real bounds `1 ≤ |Z| ≤ 3`, `|f| ≤ 1` is delegated to retained results I did not review.
- Comparison (lines 686–697): `κ = 15125/1024` matches the `r⁴` coefficient of `P(r)`; the limit `(204/409)²` lies in (0,1), is a dyadic square of depth 4, has 3-adic depth 2 and is a 7-adic unit; `7/9` of it satisfies the lemma's hypotheses. Verified.

Field map for the pole rows (lines 704–753): I compared all 147 printed rows with the merged contribution's table symbolically in `C`: no difference. For the pole rows I checked, on random exact rational points, that with the printed decoding each table row equals a nonzero monomial in `u, R, σ` times the corresponding native equation, for detectors 0, 1, 2 and the scalar pole (rows 4–13, 89–93, 137–144), that row 102 is `2G₀ = u² + x₁₅₅² + w₀ − 2u + Q₀`, and that rows 99, 107, 113 are `167281·B_j(Q_j + u²) = 166464·G_j²`. All hold, including the mixed `R²`/`u²` scales and the different `q` scale in detector 1. Each native coordinate occurs only in its own pole rows, so the decoding imposes no extra condition on a pole witness, as claimed at lines 802–804.

## 5. Both directions

- **Soundness** (a solution forces the valuation condition): proved directly in the manuscript, independent of the external preprint, and correct. It is applied only at primes where `7/9` and the fixed coefficients are units, and the consumers account for the prime 7 being lost and the prime 3 being shifted.
- **Completeness** (prepared inputs admit witnesses): correct given Theorem 2.3 of the preprint. The witnesses never need a nonzero native coordinate beyond `a₁, a₂`, which the theorem supplies.

## Findings

### Blocking

None found.

### Should fix

**S1. The record's status should say that completeness rests on an unrefereed external theorem.** Theorem `v22:175-fixed` (lines 1817–1832) and the abstract (lines 75–79) state the 175-variable equivalence without qualification. The direction "`X ∈ Z` implies a rational zero exists" uses Lemma `v22:native-pole`, whose completeness is Theorem 2.3 of arXiv:2611.16130v2, a preprint revised eight days ago and cut from 59 KB to 25 KB between versions. Line 98–101 says the realization "uses" it, and `DEPENDENCIES.md` records it, but the theorem and abstract do not. The soundness direction (every rational zero has integer `X`) does not depend on it; that asymmetry is worth stating, because it means a failure of the external theorem could not make the polynomial accept a non-integer. This is a statement-of-status issue, not a gap in the argument.

**S2. Do not lean on the external theorem for `k = 1` (line 195).** The text says the case `k = 1` "is allowed by the printed hypotheses". Literally true: 1 is a positive squarefree integer congruent to 1 mod 8. But the source's own Lemma 2.2 avoids applying the theorem when `k = 1` and gives a direct solution instead, and in the theorem's proof `k = 1` is the corner where the second star has no leaves and `E_n = E_{nk}`. The manuscript needs no theorem there: if `1 − d = η²` then `(e, p, U, V, q) = (1, 0, η, η, 0)` solves all three equations (checked). Replacing the sentence with this witness removes a dependence on an edge case its authors did not exercise.

**S3. Line 372 needs its one-line justification.** "The pole obstruction for `7b_s/9` gives `v_p(τ) > −μ/2`" is correct but uses three unstated facts: `p ≠ 3, 7` (so the obstruction for `7b/9` is the obstruction for `b`), `p ∤ 9792` (so `v_p(R+9792) = 0`), and the parity of `μ`. All hold because `p ∉ S'`. Say so; as written a reader must reconstruct why the factor `R + 9792` does not interfere.

### Notes

**N1. Domain of the lemma.** The lemma is stated for `d ∈ Q×` (line 162) but is invoked where the input may vanish (`g_j = 0`, lines 226–227 and 487). The use is harmless, since the conclusion is vacuous at `d = 0`, but either state the lemma for all rational `d` or say at the point of use that `d = 0` needs nothing.

**N2. Exceptional norms.** Resolved as described in §4: Version 22 uses the Version 21 list, it is correct, and no table depends on the choice. `ARITHMETIC-AUDIT.md` already calls the other list wrong "in intermediate notes"; more exactly it is a list of different quantities.

**N3. "We use only that point conclusion" (lines 193–194).** True of what is consumed, but in the source the point conclusion is obtained from positive rank via the genus-point criterion. The sentence should not be read as reducing the dependence to an elementary statement.

**N4. Square denominator of `b_j` is asserted compactly (lines 656–666, 683–684, 696–697).** The text proves `v_p(b_j) = 1` at a detector's own selected prime and then says the "selected-prime parity and the square rational gate factor" give every prepared condition. The parity logic is sound as far as I can follow it: `b_j` is a rational square times `1/(1+q_j)`, and `1+q_j = r_j⁵/P(r_j)` has odd valuation only where a contact form of detector `j` does, so at another detector's selected prime `v_p(b_j)` is even even though `g_j` has a pole there. That last case is not written out and would be worth one sentence. I could not check the underlying claim that the contact numerators have exactly the selected prime factors; it comes from the retained prime supplier.

**N5. The preprint's own position.** Outside this review's scope, but the editor should know: the cited preprint proves that Z is Diophantine in Q by its own route, and its introduction lists this project's manuscript among other approaches with the remark that its details were not examined.

## What I did not check

- The proof of Theorem 2.3 in the preprint, and the results it cites (Tian–Yuan–Zhang, Monsky, Rédei, Smith).
- Everything retained from Version 21 and earlier that the pole step calls on: the reference recovery that gives `f ≠ 0`, the scalar and reference index construction and real bounds, the Gaussian prime supplier, the formal-group comparison.
- The remainder of Section V22.5 after line 492, the contact section, the weighted height lemma and the final numerical contradiction.
- The PDF. I reviewed the TeX source only.

## Scripts

My own, standard library, exact arithmetic; nothing from the pull request was executed.
`C:\Users\glaze\AppData\Local\Temp\claude\7fbd96b289b0830c\673e4698-d945-4239-ad78-c5f5e062f088\scratchpad\v22\scripts\` — `polecheck.py` (row decoding), `texrows.py` (printed rows against the table), `numeric.py` (source example, witness formulas, dyadic and real claims, 331 residues, norms). The scratchpad may be cleared; the scripts are short and reproducible from this report.
