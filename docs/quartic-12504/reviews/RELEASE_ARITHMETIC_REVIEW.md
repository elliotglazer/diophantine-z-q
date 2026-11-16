# Arithmetic review of the 12,504-variable candidate

Reviewed on 2026-11-05 by the independent guards/arithmetic reviewer.

Verdict: PASS for the arithmetic interpretation of the exact reciprocal64-beta16-compressed-s1 source identified below, using the unchanged inherited mathematical inputs listed in this review. I found no new mathematical gap in the reciprocal logarithm, its entire infinite tail, global nonvanishing, compressed-chart reconstruction, mixed precision, either contradiction, or completeness. This review rederives those arguments and checks their actual source consumers. It does not infer them from a previous PASS receipt.

The associated final candidate is `work/quartic-variable-search-20261105/wave13/reciprocal-stages/coordinates`. Its saved finite verification reports 12,504 total variables, 12,503 existential witnesses, 11,939 residuals, 135,721 nonzero monomials, degree four, and maximum absolute coefficient 685783949153203534233601. Those numerical assertions come from the separate finite verification. This arithmetic review does not rerun the full expansion or replace the independent certificate audit.

No exponent-19 estimate, 37-contact construction, scalar order 32, shortened high-precision logarithm, or new anchor is used here. The abandoned combined-source drafts are outside this review.

## Exact source and artifact binding

The source identifier is `reciprocal64-beta16-compressed-s1-b5e836d77643`. In the following table, `W13` means `work/quartic-variable-search-20261105/wave13`, and `SRC` means `W13/reciprocal64-beta16-compressed`.

| File | SHA256 |
| --- | --- |
| `SRC/residuals.jsonl` | `b5e836d7764363fcbfdafbacefe80a5f53e0979eba73af990827942b0fa9351d` |
| `W13/reciprocal-adapter/source-residuals.jsonl.gz` | `ce9eeac7c4730aced8cfb70a1ab3b1b6a7fb2110c597afad1f56ddc92aeea73f` |
| `SRC/PROPOSED_SOURCE.json` | `93df4b4c2f8aba4dd74c93d64a95347e2494d804752dc3647907e14b91f1a9bb` |
| `SRC/compiler/archive_build.py` | `c7ef798894a106e3c6b02816583be2b6e966e4e701f73ee670c9a0de52a70912` |
| `SRC/compiler/build_reciprocal_source.py` | `d9ec8f4788882f37f3a0b7746f8d19c28968f7bf3f09cc06addab92f787098f6` |
| `SRC/compiler/reciprocal_kernel.py` | `c4e94463cd59a2418a6502ac7cdcfd713edf9bc1134fe0b4d4bd84700983b304` |
| `SRC/modules/q_compare4.json` | `0c529d02717b4300bb76525f3eb13524abfc99a6156a96c18b4ba5492cc31482` |
| `SRC/modules/q_batch41.json` | `2f9e8adfdabb3a224ddb0599c99c8e39877d27ac28516feec1a3df831aae96e2` |
| `SRC/modules/Z_definition.json` | `3481dc07810493980b94071aab3e728ead885710213d1fef337199e8d2f73885` |
| `W13/reciprocal64-beta16-compressed-audit.json` | `7c67ff1736e4a4f0e1f7e70e7f5e47c956dfb0c644fd5264acd0c224bbd60e01` |
| `W13/reciprocal64-beta16-compressed-mutations.json` | `adceded361a6803dafb26df0b358b7bf0b56c356d58f3fc5c2d9e4957eed4bd4` |
| `W13/reciprocal64-beta16-compressed-map.json` | `edad166ce99d33fe50271e2afdc1628bbec0361d812762212240cadd30f93cfe` |
| `W13/reciprocal-adapter/source-entry.json` | `c0fc67ef6ead31dd018ca92643dc4988fcf28f9755dd9be7e017651bf4b14abc` |
| `W13/reciprocal-stages/coordinates/polynomial.expanded.txt` | `7f5aa3117af82a0b323f0a4e74a18599204f5540408106d3ce99612b5ed830ca` |
| `W13/reciprocal-stages/coordinates/certificate.jsonl.gz` | `9f7979c1e786bebad624b9ea4631b7eccd879f4bebb5b9ab69250b945973b268` |
| `W13/reciprocal-stages/coordinates/verification.json` | `06424ae5fcd9de6d2e5674bf7927c665ed1096a85dde463d456feaadc352a400` |

I independently recomputed the file hashes. All fourteen source-file hashes listed by the source audit matched the actual source files. The raw source hash and compressed source hash name different serializations; they must not be interchanged. The source audit identifies 12,064 source variables and 11,499 source residuals before the fresh quadratic lift. These are not the final quartic counts.

The proof under review is `work/quartic-astra-search-20261105/precision-next/RECIPROCAL_PROOF.md`, SHA256 `be5b08dd9ded743606d5c6a5fc869c4e9764575da49e5d80af13aca09950a98a`. I reread the archived kernel, the original comparison/root/norm code, and the relevant manuscript arguments. I also inspected the independent source checker `work/quartic-astra-search-20261105/reciprocal-source-audit/check_source.py`, SHA256 `495ca32737687fca335704c6bdbabacf8f20a7698839aa680639e8e1b60a948f`, including its coefficient formula, complete core-equation comparison, ordered calls, frozen-module comparison and flattening checks. Its saved source report and 38 semantic mutation cases are relevant finite evidence, not proofs of the universal arithmetic claims below.

The inspected manuscript is `work/private-degree8-20261105/repository/diophantine_zq.tex`, SHA256 `954d87fe851777672dc46233998e3905a19c3ef463749fc04d6743afeceb4fab`. This is the inherited manuscript used for comparison, not a claim that the Version 2 public manuscript has already been revised or reviewed.

## Source-to-theorem contract

All coordinates are rational. Heights are absolute logarithmic Weil heights; `log` is natural and `log2` has base two. Field pairs represent exactly `K=Q(sqrt(2))`, with multiplication `(a,b)(c,d)=(ac+2bd,ad+bc)`. Put `d=3-sqrt(2)`, `D=d^2=11-6sqrt(2)`, and use the unchanged curve `E:y^2=x^3-Dx` and normalized generator

```
P_*=(57/8-7sqrt(2)/2, -165/8+417sqrt(2)/32),
2E(K)=Z P_*.
```

The source retains the four nonzero root points `A=nP_*`, `S=sP_*`, `T=tP_*`, `Z=zP_*`, with nonzero integer indices. Its nine rational height targets are a nonzero common coordinate denominator `e` and the eight coefficients of `e*x(A), e*x(S), e*x(T), e*x(Z)`. Its 41 raw contacts, the constants `47027`, `3`, `25878772920`, and `V0=32*25878772920`, and all 41 calls with the same four proxies are unchanged. There is no direct-eight-coefficient substitution.

The scalar relation is `beta=X^2+2`. Its contact polynomial remains

```
r(beta)=beta(beta-1)(beta-2401)(32beta+343)(2beta-1).
```

Its six coefficient orders remain `[1,1,1,1,48,48]`, applied to `f(J0), f(S), z(S)/z(J0)`. The small-prime sign and square-class correction and the seven-witness pole predicate are retained. The anchor has 24 squarings starting at 3, with `C=3^(2^24)` computed by variables rather than inserted as a coefficient. Two doublings still form each shift `4Q`.

For each raw contact, write mathematical primary indices `X_0=H` and `X_1,...,X_4` for the points comparing with `A,S,T,Z`. The implementation names these `H,X0,X1,X2,X3`. It uses `G_15` for `H` and the three Lucas numerators, and `G_3` for the beta numerator. The scale is the fixed rational constant one.

| Field-test positions, zero based | Meaning | Order |
| --- | --- | --- |
| 0 through 4 | `f(X_i)` | 1 |
| 5 | conjugate `f(J)` | 1 |
| 6 through 10 | conjugate `f(Y_i)`, where `Y_i=X_i-4Q_i` and `Q_0=P_*` | 1 |
| 11 | `L_16(X_1)/L_64(X_0)-beta` | 16 |
| 12 through 14 | the other three primary ratios minus `xi,tau,zeta` | 64 |
| 15 | conjugate `z(Y_0)/z(J)` | 64 |
| 16 | conjugate `z(Y_1)/z(J)` | 16 |
| 17 through 19 | the other three alternate ratios | 64 |

Thus the exact field list is `[1]*11+[16,64,64,64,64,16,64,64,64]`. The root-error test followed by two rational tests per field expression gives `[1]*23+[16]*2+[64]*8+[16]*2+[64]*6`. Both the archived source construction and its module metadata have this assignment. The denominator and the `H-4P_*` alternate test have order 64.

## Exact logarithm and entire infinite tail

For a curve point put `f=1/x`, `z=-x/y`, and `w=Df^2`. The exact curve identity gives

```
z^2=f/(1-w),             f=z^2(1-w),
Dz^4=w/(1-w)^2,
dx/(2y)=z df/(2f)=(1-w)/(1+w) dz,
z dw/dz=4w(1-w)/(1+w).
```

The differential sign and factor follow directly by differentiating `x=1/f` and using `y=-1/(fz)`. They agree with the invariant differential for this Weierstrass equation and the parameter `z=-x/y`.

Define `a_0=1`, `a_1=-2/5`, and `a_j=(4j-5)a_(j-1)/(4j+1)` for `j>=2`. Comparing coefficients proves

```
4w(1-w)G'(w)+(1+w)G(w)=1-w,
G(w)=sum_(j>=0) a_j w^j.
```

It follows that `d(zG(w))/dz=(1-w)/(1+w)`. Its constant term is zero and its linear coefficient is one. Therefore `log_E(z)=zG(Df^2)` as a formal series on the curve. The finite expression `zG_J(Df^2)` is not equal to the old finite polynomial in `z`. The new arithmetic proof is necessary.

At every relevant prime `p>76176`, `D` is a unit since its norm is 49. The primary formal test places the point in the formal group; for `r=v_p(z)>=1`, the curve gives `v_p(f)=2r` and `v_p(w)=4r`. The denominator of `a_j` divides

```
5 product_(k=2)^j(4k+1),
```

which divides `(4j+1)!`. Hence `v_p(a_j)>=-(4j+1)/(p-1)`. For `4j+1<p`, the coefficient is integral. For `4j+1>=p`, one has `j>=19044`, `(4j+1)/(p-1)<=j`, and `3j>=4m` for each `m<=16`. For every omitted `j>=m`, both cases give

```
v_p(a_j w^j)>=4mr.
```

In the second case the stronger lower bound `4jr-j` tends to infinity; convergence of the entire tail, including coefficients with `p` in their denominators, follows. For `m=16` or `m=4`, respectively, the tail of `G` is in `p^(64r)` or `p^(16r)`. Formal-logarithm isometry makes `log_E(z)/z` a unit, so

```
L_64/log_E in 1+p^64 Z_p,
L_16/log_E in 1+p^16 Z_p.
```

No assumption that all infinitely many coefficients are `p`-integral was made. No stronger order-one point test, extra height guard, or altered prime cutoff is needed.

## Global nonvanishing and compressed reconstruction

For nonzero `a+b sqrt(2)` define

```
v(a+b sqrt(2))=(1/2)nu_2(a^2-2b^2)
              =min(nu_2(a),nu_2(b)+1/2).
```

The norm-term valuations have opposite parity, which proves the second equality, including zero coefficients with infinite valuation. Norm multiplicativity and the displayed minimum show that this is a valuation with values in `(1/2)Z`. Here `v(D)=0`, and `v(a_j)=1` for every `j>=1`, because all recurrence factors after `a_1` are odd over odd.

For any `f` in `K`, `G_J(Df^2)` is nonzero when `J>=2`. At `f=0` its value is one. If `t=v(f)>=0`, the constant is the unique term of least valuation. If `t<0`, then `t<=-1/2`, and the nonconstant term valuations `1+2jt` strictly decrease. The last one is at most `1-J<0`, below the constant. It is uniquely least, so the sum cannot vanish. This proves the required statement for both `J=3` and `J=15`, even off the curve. It uses neither good reduction at two nor any local condition on the assigned point.

This off-curve statement avoids a circular argument when restoring a compressed chart. Each private primary point satisfies

```
f=u^2,    v^2+df=1,    p^2=x-Df,    xf=1.
```

The ratio system is

```
Lambda*p_0=G_0,
A_i=C_i*p_i,    A_i*Lambda=G_i,    1<=i<=4.
```

Every `G_i` is globally nonzero. Thus `Lambda,p_0,A_i,p_i,C_i` are nonzero. Also `x,f,u` are nonzero. The identity

```
f p^2=1-Df^2=v^2(1+df)
```

then proves `v!=0`. Set

```
z=-1/p,   y=xp,   h_old=up,   w_old=up/v.
```

These restore all seven original field-chart equations: in particular `w_old^2=1+df`, `w_old^2+v^2=2`, `v*w_old=h_old`, `z*h_old=-u`, and `yz=-x`. They also give `y^2=x^3-Dx`. Thus the original chart membership theorem applies, with no extra torsion component and no lost denominator condition.

For the logarithms `L_i=z_i G_i`, the first equation says `Lambda=-L_0`. The others give exactly

```
C_i=G_i/(p_i Lambda)=L_i/L_0.
```

The sign is correct. Conversely an original chart equipped with these new finite logarithms maps to the compressed chart by `p=y/x`, `Lambda=-L_0`, and `A_i=C_i p_i`. All these maps are rational over `K`; each field division expands to rational operations because the norm of a nonzero element of `Q(sqrt(2))` is nonzero.

The archived implementation supplies `y=xp` to the unchanged subtraction routine. Its first equation becomes `x(lambda-p)-nu=0`. The second equation, output equation, reciprocal output equation, and norm guard on distinct abscissas remain. All five difference-parameter pairs `z(Y_i)` remain, as do root-point parameters and the common `z(J)` used by the alternates. The independent source checker compares these equations and every consumer after expanding the acyclic arithmetic definitions. The global nonvanishing proof concerns the full returned `G`, including its restored factor `a_6`; a normalized intermediate alone would not be a sufficient interface.

## Norm extraction, scalar height and local comparison

Let a raw contact have odd valuation `R` outside the exceptional set. At every norm node `a^2+r b^2`, nonzero summands have different valuation parity. The norm cannot vanish unless both inputs vanish, and descent to the constant leaf excludes a zero norm root. If `R<0`, the constant leaf on the all-left path forces root valuation at most zero, so `rW^2` has negative odd valuation, contrary to the pole predicate. Hence `R>0`.

The pole predicate then forces `v(rW^2)>0`, so `v(W)>-R/2`. Descent through a norm node sends a bound `v(N_r(a,b))>-cR`, with `c<1`, to bounds with constants `c/2` and `(c+1)/2`, still less than one. Every normalized leaf has valuation greater than `-R`. Thus an order-`L` test obeys

```
v(X/r^L)>-R,    v(X)>(L-1)R>=L-1,    v(X)>=L.
```

This applies to the mixed orders 1, 16 and 64 and to the unchanged scalar order 48. The odd-negative case is excluded before any positive-contact argument. The scalar correction is a unit outside the fixed exceptional set and does not change this reasoning.

For comparison batches the order-one test `theta^2-2` makes `p` split and selects a root `rho` of two. Since `theta+rho` is a unit, the two rational tests `(theta^2-2)B` and `A+theta B` imply `v_p(A+rho B)>=L`. This does not require `A` or `B` individually integral. Hence the indicated primary and opposite-place formal tests really follow for arbitrary rational source assignments.

Write `J=jP_*`, `X_0=hP_*`, `X_i=m_iP_*`, with `j!=0` an integer. At the opposite place formal-logarithm isometry gives the valuations of the alternate ratios as those of `(h-4)/j` and `(m_i-4n_i)/j`. Multiplication by the integer `j` loses no valuation. Consequently

```
h=4 mod p^64,
m_1=4n mod p^16,
(m_2,m_3,m_4)=(4s,4t,4z) mod p^64.
```

In particular `h` is a unit. The exact formal-log ratio is `m_i/h`, which is integral. If its numerator finite-log error is `u_i in 1+p^(e_i)Z_p` and denominator error is `u_0 in 1+p^64 Z_p`, the finite ratio is `(m_i/h)(u_i/u_0)`. It is integral and congruent to `n_i` to order `e_i`, where `(e_1,e_2,e_3,e_4)=(16,64,64,64)`. The primary tests therefore give beta congruent to `n` modulo `p^16` and the other three proxies congruent to `s,t,z` modulo `p^64`.

For the separate scalar batch, coefficientwise order-one tests put both `J0=j0P_*` and `S=sP_*` in the formal group at every place over a relevant prime. Its order-48 ratio tests imply `v(z(S)/z(J0))=v(s/j0)>=48`, hence `v_p(s)>=48` since `j0` is a nonzero integer. This remains true at inert primes; the extension is unramified for `p>2`. The unchanged scalar polynomial detects every odd five-contact of beta, including odd negative valuation at infinity. It is nonzero for rational `X`: the only possible vanishing factor not excluded by `beta=X^2+2>=2` would require `X^2=2399`, which has no rational solution. Therefore

```
M_5(beta)^48 divides s,     h(beta)<=H_* sqrt(|s|).
```

No reciprocal finite logarithm is used by the scalar batch.

## Both global contradictions with the original constants

The unchanged height input is

```
H_*=2(4608^165888+6^100)(product_(p<=76176) p)^24+128,
h(b)<=H_* M_5(b)^24,       log2(H_*)<4783227.
```

Let `a=|s|`. The unchanged anchor gives `a>=3^(2^23-1)>(20H_*)^2`. The numerical step is exact: `3(2^23-1)=25165821>19132928=4(5+4783227)`, together with `log2(3)>3/2` and `log2(20)<5`.

The old parity-of-the-common-minimum argument sends every odd normalized contact of each height slope to an odd valuation of some listed raw contact. All four proxies are tested at every one of the 41 contacts, including the contacts arising from `A`. For a nonzero integer `N` divisible by the relevant `k`th powers of the radicals, the unchanged nine-target argument gives

```
h(x(Q))<7H_* |N|^(24/k),  Q in {A,S,T,Z}.
```

It still includes the height of `e` when dividing the two scaled coefficients by the common denominator. This review does not replace it by the direct-coefficient height estimate from the excluded 37-contact proposal.

Put `B=max(|n|,|s|,|t|,|z|)` and

```
Delta=t^2-s(s-2)tz+(s-2)^2 z^2-1.
```

If `Delta!=0`, the three high proxy congruences and the source Lucas equation imply every required 64th-power radical divisibility. The index-height estimate and `|Delta|<5B^4` give

```
B^2-6<7H_* |Delta|^(3/8)<14H_* B^(3/2).
```

Here `7*5^(3/8)<14`, since `5^3<2^8`. Thus `sqrt(B)<14H_*+6<=20H_*`, contradicting `B>=a>(20H_*)^2`. This first contradiction never uses beta precision 64. Hence `Delta=0`, and the unchanged Lucas lemma, with `z!=0`, gives `log(B)>a-3`.

If `beta!=n`, let `N=|num(beta-n)|>0` in lowest terms. Local integrality makes the reduced denominator a unit at each relevant prime, so the beta congruence gives the required sixteenth-power divisibility of `N`. Also

```
N<=exp(h(beta))(1+|n|)<=2 exp(h(beta))B.
```

The height estimate now gives

```
B^2<7H_* N^(3/2)+6,
sqrt(B)<(7*2^(3/2)+6)H_* exp(3h(beta)/2)
       <32H_* exp(3h(beta)/2).
```

The scalar height and anchor imply `h(beta)<a/20`. Also `log(32H_*)<a/20`: for `H>=1`, the function `400H^2-20log(40H)` is positive at one and has derivative `800H-20/H>0`, while `a>400H_*^2`. Taking logarithms yields

```
log(B)<2log(32H_*)+3h(beta)<a/4<a-3,
```

contrary to Lucas growth. Thus `beta=n` is an integer. For rational `X`, the relation `X^2=beta-2` then forces `X` integral by reduction to coprime numerator and denominator.

## Completeness and order of choices

For an integer input `X`, first retain the old scalar construction and put `A=beta P_*`. Choose the sign and small-prime correction, then `J0`, and then a positive index `s` in the anchor subgroup with all scalar formal divisibilities. Apply the unchanged Lucas existence argument to obtain `T` and `Z`. These choices occur before the contact primes are chosen.

Choose a positive integer `e` clearing the eight root abscissa coefficients. The resulting nine targets are integers, so the original 41-prime-pattern theorem applies without a rational-target extension. It supplies positive ordinary prime values above 76176 for the distinct raw contacts, each congruent to the fixed `c` modulo `W`. At each prime the two reduction orders have gcd four and neither is divisible by that prime. Repeated contacts use the same prime and orientation.

Set `j=lcm_p d_(p,2)` and `J=jP_*`. For each selected prime choose a private `h_p` with

```
h_p=0 mod d_(p,1),
h_p=4 mod d_(p,2),
h_p=4 mod p^(64+v_p(j)).
```

These congruences are compatible by the same-prime gcd and prime-to-`p` conditions. Avoid `h_p=0,4,-4`; an infinite arithmetic progression permits that. Take `X_0=h_p P_*` and `X_i=h_p n_i P_*`. The exclusions preserve the distinct-abscissa guards and nonzero differences. At the primary place the `X_i` are formal, and at the opposite place `J,Y_i` are formal. The term `v_p(j)` accounts for factors contributed by other selected primes' reduction orders. No cross-prime order theorem is assumed.

The retained modulus already gives every alternate test order. The relative finite-log estimates give the primary orders 16 and 64 with integer proxy values. Global nonvanishing makes all evaluated ratios defined. The explicit forward compression map then supplies the new primary coordinates.

Choose the one common rational integer `theta` last, close to the selected root of two at each distinct prime. The finite set of requirements `v_p(theta-rho_p)>=k-v_p(B)` for every field coefficient `B`, and at least one, is compatible by CRT. It gives both rational tests at their respective orders, even when a coefficient has a denominator. Repeated primes impose compatible additional precision requirements.

At a positive raw prime `r=p`, these orders make every nonconstant normalized norm leaf integral. The constant all-left leaf gives a unit norm root. The parity argument `pW^2` is positive, has square reduced denominator, and is a square in `Q_2,Q_3,Q_17`, since the selected prime is a local square there. The same seven-witness completeness lemma applies. No local integrality of the private comparison points at those three small primes is required. Scalar pole completeness and its correction factors are unchanged. This constructs a witness for every integer input.

## Exact inventory of inherited mathematical obligations

In this section `R` means `work/private-degree8-20261105/repository`. These are inherited proofs and source applications, not conclusions of finite polynomial checks.

| Obligation used here | Exact inherited location and scope |
| --- | --- |
| Five-contact height with the displayed exponent 24 and constant | Manuscript `hyp:o8-height`, including the exact branch set, normal fiber field, original stable Faltings metric, non-CM modular-level transfer and same-field CM estimate. Current status is in `R/degree8-original/arithmetic/current-proof.json` and `assumption-status.json`. The accepted H5 source applications are in `R/docs/degree8-original/research/accepted-h5/author/h5-integration/source-applications-v3.json`, with the acceptance qualifications in `review/H5_FINAL_ACCEPTANCE.md` and `review/SMALLER_ONLY_ACCEPTANCE.md`. The historical pending statuses in component drafts are not new open H5 gaps. |
| Generator, rank, torsion and index-height | Manuscript `prop:generator`, `lem:o8-chart`, `eq:o8-indexheight`, and the unit change to the specified `P_*`. Frozen baseline applications `A058`, `A059`, `A060` identify quadratic-field descent, Mordell-Weil/torsion reduction and canonical-height inputs. The proof of the index estimate remains necessary; finite point evaluations alone do not prove generation. |
| Formal group, logarithm homomorphism/isometry and reduction criteria | Frozen baseline application `A071`; `R/degree8-original/arithmetic/sieve/source-ledger.json`, entry `EC`, specifically Silverman IV.6.4 and VII.2.1-2.2. The reciprocal differential and entire-tail arguments above are new elementary uses of this unchanged formal-group input. |
| Literal anchor and its compatibility with further divisibilities | `R/degree8-original/arithmetic/anchor/source-application-ledger.json`, entries `A23-1` through `A23-4`, and `anchor/anchor-proof.tex`. These include Koenigsmann Proposition 6 for the exact trace-sum predicate, local multiplication at two and three, the subgroup `2*3^(2^23-1)Z`, and the numerical cutoff using the separate height theorem. |
| Original prime pattern, same-prime orders, private shifts and root approximation | `R/degree8-original/arithmetic/sieve/applications.json`, entries `OP01` through `OP14`, and `sieve/original41-proof.tex`. `OP01`-`OP08` retain constants, finite-complexity prime asymptotics, cutoff/fiber bounds and CM orders. `OP09`, `OP10`, `OP12`, `OP13` retain common-J, formal index ratios, common theta and parity consumption. This review replaces the finite-log portion of `OP11` by the reciprocal/mixed proof above. `OP14` still requires the new finite compilation, supplied separately for this candidate. |
| Exact seven-witness pole predicate and scalar corrections | Manuscript `hyp:o8-pole`, `lem:original-seven-parity-soundness`, `lem:original-seven-parity-completeness` and `lem:original-seven-simultaneous-realization`; `R/degree8-original/arithmetic/parity/parity-justification.tex`. Completeness consumes the existing restricted-converse theorem `hyp:RC` and corank lemma `lem:corank` at their inherited proof status. The pole predicate is not replaced by the different predicate `hyp:PC`. No independent assumption of simultaneous realization is added. |
| Lucas growth and existence | Manuscript `lem:o8-lucas`, including both signs of `s`, nonzero `z`, and existence after selecting `s`. This is the same elementary lemma used by the original source. |
| Baseline external applications upstream of the restricted converse and other inherited results | The complete frozen inventory is `R/docs/theorem-application-audit/applications.json`, entries `A001` through `A082`, with its source, citation and evidence records. `BASELINE_FREEZE.json` attaches these records to baseline manuscript SHA256 `cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`. This review does not treat all 82 records as direct new quartic applications or upgrade their stated scope to a whole-proof certificate. |

The H5 ledger includes Gonzalez-Rotger's published quotient models, Yuan's author-attested English translation, Deligne's canonical model action, the published Voight chapter, Silverberg-Zarhin and Serre local inputs, the inherited splitting/de Rham arguments, modularity via the stated Calegari/Pan interface, Li/Shimura and Carayol/Casselman, Faltings, Gaudron-Remond 2023, Javanpeykar, von Kanel and the CM height formula. This source change does not replace any of those applications with the later nebentypus-kernel proposal. The recorded limits concerning Pan's version of record and the Chinese typesetting of Yuan remain.

The prime-pattern ledger uses the published Green-Tao finite-complexity theorem with MN and GI, Williams' fixed-modulus Mertens result, and the specified elliptic-curve inputs. Its inherited GI corrected-author-version and erratum convention remains explicit. It is inaccurate to say this review newly establishes all of those sources, or to conceal that convention under a claim that every proof version was independently checked in journal typesetting.

| Inventory file relative to `R` | SHA256 |
| --- | --- |
| `degree8-original/arithmetic/current-proof.json` | `af4570f0f20c0e1895b3567f2c18a13d0cc40d939ac051047a757a3c145d753e` |
| `degree8-original/arithmetic/assumption-status.json` | `79ab37c5b822300ae0472ad391dcc02e2ff15e6020f21b4dad58986b08816101` |
| `degree8-original/arithmetic/sieve/applications.json` | `28b8f85d33be96b7148de22214dbe7fd39d221a99ab56c75534ad47edc18b062` |
| `degree8-original/arithmetic/sieve/source-ledger.json` | `e98599849e678182edac7c825a58ec9d86604198fbdd277e64faa128eae2b125` |
| `degree8-original/arithmetic/anchor/source-application-ledger.json` | `2f81ceea6b525913b1790c2695da9fb3cc3c9c8b63bfbe7e16bc26d0a227e5ef` |
| `degree8-original/arithmetic/parity/parity-justification.tex` | `df67c17520d942a4a5d8505b5ed1d97bf2bd3d18f8d13cbf514f758d7286075d` |
| `docs/degree8-original/research/accepted-h5/author/h5-integration/source-applications-v3.json` | `7a048ffecfe56d88fa291d9479c776f4bc0f7474fc243351f2afceaf931b12d3` |
| `docs/degree8-original/research/accepted-h5/review/H5_FINAL_ACCEPTANCE.md` | `db62a7fa5fbcd2d4bc711436f2fb4f98c37de9122751ea7aeb097d96680905eb` |
| `docs/theorem-application-audit/BASELINE_FREEZE.json` | `447d398ed2cf8768bf1ae5162b9f8a5a1c5f97a1fe9d8594a6a8b58d740d0b37` |
| `docs/theorem-application-audit/applications.json` | `1d53028414eefe1eeed85db566aae47b2b00d4206f3eaffeec8625f0e3c089bb` |

## Release implications and limits

There is no unresolved new arithmetic defect from this review. The exact source has the same rational input projection as the original integer definition by its own soundness and completeness proof. Only the compressed-chart step has the explicit rational witness maps above. Replacing the old finite logarithm or lowering beta precision is not a pointwise polynomial identity on the original witness tuple.

The current `R/docs/quartics/theorem-applications.json`, SHA256 `7d89a0f9313b8c617a1ac51d55c7270c88d89d2afc7ebf001fb9501df15479a2`, still inventories the 13,609-variable Version 6 construction. It is not the new release inventory. The release needs an added source-arithmetic statement with the reciprocal series, entire-tail bound, global nonvanishing, compressed maps, mixed order assignment and both contradictions. The final quartic theorem must then consume this new source statement and the exact new finite certificate. Merely replacing the old counts or source hash while retaining the assertion of an unchanged finite logarithm would be incorrect.

The source's historical `source_pin_authorized=false` metadata describes its proposal stage. It is not a mathematical counterexample or a request for an extra user permission gate. This review supplies the separate arithmetic assessment; final finite replay, public manuscript revision, inventory revision and packaging are different work items.

No heavy local computation, source regeneration, remote launch, or manuscript edit was performed for this review. I inspected the saved source and proof material and recomputed small-file/artifact hashes. The finite source and quartic receipts still need the clean reproduction assigned by root. This is an AI mathematical review with the stated inherited dependencies, not a formal proof certificate or independent human peer review.
