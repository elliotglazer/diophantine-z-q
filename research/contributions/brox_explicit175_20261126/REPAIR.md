# PR 175 repair: fixed 175-variable member only

Original head: `16d6c0d88acb91eeeb76ede6ec87edb4e3749933`. Receiving base: `964d7dd71f253091dbc5eac793b78cc56d1fcc73`. Source snapshot: `JoseBrox/diophantine-z-q_improvements@6864691d536057574be873667936610da6a4ea99`.

This supplement addresses the [failed review round](https://github.com/elliotglazer/diophantine-z-q/pull/175#issuecomment-7205829472). It does not change any of the 147 final quadrics or the 73,080-byte expanded polynomial. It does not assert an independently established arithmetic theorem, a new official record or acceptance of any finding. The copied ineffective families, other routes, numerical targets and geometric obstructions are historical background, not claims for review in this PR.

## 1. Parent and table lineage (F1, F4)

The original submission did not include enough of the parent lineage. The following is the review path through the copied sources. All paths below are relative to this contribution. The original source notes are unchanged; the new repair manifests identify the additional exact Git blobs.

| Step | Mathematical source / finite binding |
|---|---|
| Receiving Version 21 common 195-variable source | `source/computation/quartic/seven_units193_v74/source/source195.json`, identical Git blob `5d6c4a4b482a4065b87a79d03426b0dcfff0f593` to receiving `research/version21/construction/inputs/brox229/source/quadratic195.json`. |
| v74 physical finite-pair chart and comparison factors | `source/papers/quartic/quartic193_20261117_v74.tex`; the inverse-Vieta parent argument and uniformity interfaces are in `source/sources/h10_quartic198/arithmetic/inverse_vieta_198.tex` and `source/sources/h10_quartic198/audit/source-uniform-existence.md`; v27 quartic and prime selection sources are also included. `check-v74.js` reconstructs 81 physical field/detector rows and matches all 81 other physical rows to the common 195 source, including the unit exponents. It reads the physical Laurent table and its certificate, rather than relying on a separately compiled 193-coordinate table. |
| v78 shared product, fixed 180-coordinate route | `source/papers/quartic/shared_product_audit_20261119_v78.tex` (common-slot gate and strengthened extraction), and `source/computation/coauthor_audit_v78/H10-quartics/quartics/{local-transfer,effective-transfer,three-contact-audit}.md`. `check-v78.js` additionally matches 41 common scalar/reference/Vieta equations to v74, v62 and the common source, reconstructs all 150 shared-product physical rows, verifies the two literal unit guards and all 152 compiled rows, then verifies the six enhanced factor replacements and all unchanged rows. The v78 physical detector templates reset the old second relative-weight unit to 1; the new shared-product gate determines the actual input. This is not a claim that the entire v74 system is equivalent to its restriction at that unit. The direct final-pole binding in §3 below checks the actual consumer. |
| v82 fixed 179-coordinate parent | `source/papers/quartic/scalar_point163_179_20261120_v82.tex`, particularly reference exclusion, point reconstruction, weighted comparison and synchronized completeness; `source/computation/variable_reductions_v82/general/source179.json` and `quartic179/{maps,quadrics}.json` in the same directory. `check-v82-bb.js` derives 147 physical rows from enhanced180 and the changed formulas and verifies all 151 compiled rows, including four literal guards. |
| Native BB replacement | `source/papers/quartic/bb_native_quartics_20261124.tex`, supplemented by §2 below. `check-v82-bb.js` checks all twelve changed conic rows and every other unchanged row. |
| Weighted 178, harmonic 177, depressed 177, aligned 175, reciprocal 175 | The five corresponding computation README files already included in the original submission. `check-tail.js` verifies each step coefficient-by-coefficient, including the affine gate substitutions before eliminating two gates, and the reciprocal scalar rechart. The effective weighted bound uses `source/papers/effective_sums/effective_torsion_sums_20261117_v62.tex`; the modular height constants and effective inputs use `source/papers/quartic/quartic229_compact_20261117_v68.tex`. The full earlier v62 229 argument is now also supplied. |
| Projective 175 | `source/computation/projective_contacts_20261126/README.md` §§1–3 and §5 only. `check-tail.js` reconstructs the nine changed rows (three per detector; the fourth-power row in each block is unchanged), checks all unchanged rows, sums the squares and specializes to C=331^21, obtaining the exact committed ASCII literal. It checks the 331 anchor residues, exceptional prime supports, contact constant and small-prime Euler product. Original `check.py` is an additional independent final-step implementation. |

The chain preserves the common arithmetic interfaces described in the original README; it does not reprove them merely by matching coefficient tables. The fixed route uses the effective torsion-inclusive positive-weight bound, not an effectiveness assertion for the ineffective family. The copied weighted-trace and other background arguments do not enlarge the review claim. The external theorem-application inventory remains for maintainer integration (Fable N1); this note corrects the row-count and scope wording (N2/N3) without altering the original source blobs.

## 2. BB theorem application and explicit native conic witnesses (F2, F3, Astra N1)

For clarity, write the native input as d and the five unknowns as e,p,U,V,q. The required equations are

```
e^2 + d p^2 = 1,
U V = e(1-d),
U^2 - V^2 = d q^2.
```

Soundness does not use the external theorem. If a prime has negative odd valuation n of d, the first equation forces both summands integral, with e a unit (their finite valuations have distinct parity). Then v(UV)=n is finite and odd; the valuations of U and V differ. The last left-hand side has finite even valuation, while d q^2 is either zero or has odd valuation. This is impossible.

For completeness, the prepared conditions are 0<d<1, square reduced denominator, d in 7 Q_2^{*2}, and v_2(d)>=4. Write d=A/D^2 reduced, with A,D positive integers. Then D is odd, 16 divides A, and A and D^2-A are coprime. Put j=sqf(A), k=sqf(D^2-A), the positive squarefree parts. Thus j=7 mod 8 and k=1 mod 8, with gcd(j,k)=1. For each odd prime dividing j, 1-d is a unit congruent to 1, so k is a local square. For each odd prime dividing k, d is a unit congruent to 1, so j is a local square.

The external arithmetic input is the simultaneous congruent-number rational-point conclusion of Bhargava–Burungale, [arXiv:2611.16130v2](https://arxiv.org/abs/2611.16130v2), Theorem 2.3, used in Lemma 2.2: for such mutually locally square coprime positive squarefree j and k in the indicated congruence classes, there is a positive squarefree n=5 mod 8 for which E_n and E_{nk}, with E_l: y^2=x^3-l^2 x, have positive rank and points of abscissa class j. The same input is spelled out in the older v1 Theorem B formulation in the copied intrinsic-pole note §2. Here no positive-rank conclusion beyond the existence/non-torsion witness needed in that argument is required. The full statement and applicability should be checked against the cited edition by the reviewers.

Write 1-d=k eta^2. The scaling (x,y) -> (eta^2 x,eta^3 y) takes E_{nk} to E_{n(1-d)}, preserving the nonzero abscissa squareclass. Consequently choose points (d a_1^2,y_1) on E_n and (d a_2^2,y_2) on E_{n(1-d)}, with nonzero a_1,a_2. Put

```
e = n/(d a_1^2),
p = y_1/(d^2 a_1^3),
U = a_2/a_1,
V = e(1-d)/U,
q = y_2/(d^2 a_1^3 U^2).
```

The first curve equation gives d p^2=1-e^2. The definition gives U V=e(1-d). The second curve equation gives d q^2=U^2-e^2(1-d)^2/U^2=U^2-V^2. This proves the required native witness implication directly. In the intrinsic-pole note's notation (§2, not §3), these are p=p_0/d, U=s, V=e(1-d)/s, q=q_0/(d s). Where desired the non-torsion witnesses are obtained by avoiding finite torsion in the given squareclass coset, as in that section. No new finite-algebra density condition is needed for these five unrestricted native witnesses.

For the actual input b of each of the four poles, the native replacement uses d=7b/9. The BB-native preparation proves b has square reduced denominator, 0<b<1, dyadic squareclass 1 with v_2(b)>=4, v_3(b)>=2, v_7(b)>=0. The comparison inputs have the prescribed fixed-place limits (204/409)^2 at the prepared places; the scalar input has the separate preparation proved in the BB-native/harmonic/depressed notes. The stated conditions imply all the prepared conditions for d: multiplying by 7/9 changes the squareclass to 7 at 2 and preserves the 2-depth; the only possible new denominators at 3 are removed by its prepared depth; at 7 the valuation remains nonnegative. For soundness at any prime other than 7, negative odd valuation of b would give negative odd valuation of d. The prime 7 is already excluded in the comparison and scalar extraction. A zero comparison input can occur on a zero-gate boundary; the local pole obstruction is applied only when its valuation is negative odd.

**Source access:** the repair does not reproduce or claim a fresh reading of the arXiv paper. In the [final Astra report](https://github.com/elliotglazer/diophantine-z-q/pull/175#issuecomment-7205701700), under “External source application”, the reviewer expressly records later successful retrieval of v2, reading Definition 2.1, Lemma 2.2 and its proof, and Theorem 2.3, checking this application, and superseding the temporary access limitation. The [final Fable report](https://github.com/elliotglazer/diophantine-z-q/pull/175#issuecomment-7205826874) reports access only to v1. We ask the reviewers to apply the documented cross-review source-access rule to F3 if applicable; this is not a requested override or a claim of review acceptance. The preceding formulas are included so that the application can now be checked directly, without reliance on an unexpanded reference to §3.

## 3. Direct binding to the final 175-coordinate pole rows

The exact additional checker `check-poles.js` checks 33 final rows against the following equations, independently of the historical gauge maps. Use u=x160, x159=1/u, x161=u^2 and R=x88, x87=R^2. The scalar rechart forces R>0 as established in the depressed/reciprocal scalar notes; u is a unit by the literal inverse equation. Let Q_0=x151, Q_1=x152, Q_2=u-x151-x152 and w_j=x(156+j). The inverse equations are Q_j w_j=u^2; thus q_j=Q_j/u^2=1/w_j and sum q_j=1/u. Define W=(x153+sqrt(2)x154)/u, D=x155/u. The norm row gives D Tr(W)=Nm(W-1).

Let G_0=x63, G_1=x63+(x152+x157-x151-x156)/2, G_2=x63+(-2x151-x152+x158+u-x156)/2. From the single retained gate row and these affine definitions,

```
2 G_j = u^2 + x155^2 + w_j - 2u + Q_j
      = u^2 [1+D^2+(c-q_j)^2/q_j],   c=1/u.
```

Write g_j for the bracket. The three actual pole input rows are exactly

```
167281 B_j(Q_j+u^2) = 166464 G_j^2,
(B_0,B_1,B_2)=(x64,x72,x170).
```

Since the contact relation (1+w_j)P(r_j)=w_j r_j^5 forbids a contact root and implies 1+q_j = r_j^5/P(r_j), division by 1+q_j is legitimate for nonzero r_j; there the physical b_j=B_j/u^2=(408/409)^2 g_j^2/[4(1+q_j)]. At the midpoint r_j=0, the pole equation forces G_j=0 and should instead be retained in its cleared form; there is no consumed prime at that argument. No division by 1+q_j at this boundary is needed for the soundness implication. Canonical witnesses avoid the midpoint.

The native equation input is d_j=7B_j/(9u^2). The five ordinary native coordinates (e,p,U,V,q) recovered from the final table are:

| j | e | p | U | V | q |
|---|---|---|---|---|---|
| 0 | x3/R^2 | u x5/R^2 | x4/(R u) | x66/(R u) | x6/R^2 |
| 1 | x7/R^2 | u x9/R^2 | x8/(R u) | x74/(R u) | x10/(R u) |
| 2 | x163/u^2 | x165/u | x164/u^2 | x172/u^2 | x166/u^2 |

All scalings use nonzero units. Substitution of the checked p2 and q2 rows gives the three native equations of §2 for each row of this table; conversely the displayed nonzero scalings and the square-register equations recover the five stored rows from any ordinary solution. In particular the mixed R^2 and u^2 scales are intentional, not a missing equality between R and u.

For the scalar pole let sigma=x79, tauhat=x86. Its inverse row gives sigma tauhat=R^4, hence sigma nonzero. The actual b_s=x80/sigma=R(R+9792)/sigma^2. The native coordinates are (x11,x13,x12,x82,x14)/sigma, in order (e,p,U,V,q). The two square rows and three native rows give the same equations with d_s=7b_s/9. These formulas agree with the scalar preparation using tau=tauhat/R^4=1/sigma.

## 4. Replay and review status

From the repository root, run:

```sh
python -B research/contributions/brox_explicit175_20261126/check_all.py
```

Only Python 3 and Node.js (BigInt) standard libraries are needed. The runner binds all copied original files by their Git blob hashes, compares the common source with the receiving Version 21 source file, executes the five new independent exact checkers, compares their outputs against the reported receipts, and runs the original final-step checker with assertions enabled. No construction generator, symbolic library, network request or frozen-source mutation is needed.

The five new verifier functions were actually run in a V8 BigInt tool environment against the fetched pinned source bytes. The per-stage JSON receipts record the exact results. These are contributor-side replays, not an independently authenticated GitHub Actions run. The new file-loading/runner entry point is supplied for reproducibility; it has not been executed as a whole in a checkout of the amended head. In particular the first round's ordinary green CI jobs did not run this contribution checker. An eligible exact-head direct run in the receiving repository, or equivalent complete independent reviewer inspection allowed by the policy, remains necessary for table coverage. Please arrange that run and the next authorized Protocol B review before merging. No override is requested.

The mathematical proof and its imported arithmetic inputs remain subject to that review. Both incomplete scope findings remain pending reviewer disposition. The candidate submission does not edit the receiving release, manuscript, audit contracts, workflow or policy. The unrelated prior manifest mismatch in the improvements repository's workflow remains outside this repair.
